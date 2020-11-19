import data.list.basic
import data.bool
import data.nat.basic
import init.meta.tactic
open set 
open bool
open list
open nat

-- TACTIC UNITS 

  variables {α β γ  : Type}

  meta def tac : tactic unit :=
         `[ { repeat {{left, exact rfl}  <|> right <|> exact rfl}} <|>             
            solve1 { repeat {{left, assumption}  <|> right <|> assumption}}]

 meta def mt_ax : tactic unit := 
  `[ solve1 {repeat{ {left, refine (exintro2 _ _ rfl)}   <|>
            {left, refine (exintro3 _ _ _ rfl)}  <|>
            right}} ]

 meta def mt_assump0 : tactic unit := 
  `[ repeat{{left, exact rfl} <|> right} <|> assumption ]

 meta def mt_assump : tactic unit := 
  `[ iterate 6 {right}, left, {simp, try{exact rfl}} <|>
     assumption ]

 meta def mt_mp : tactic unit := 
  `[ {repeat{right}, existsi _,
    split, swap, mt_assump0} ]

 -- TAUT, RULES
 meta def mt_rules :tactic unit :=
    --rules with more than 1 assumption
  `[   
    apply (@provable1 _ _) <|>
    apply (@provable5 _ _) <|>
    apply (@double_neg_law _) <|>
    apply (@transitivity _ _ _) <|>
    apply (@RAA _ _) <|> 
    apply (@contraposition _ _) <|>
    assumption
    ]

 meta def mt_uncut : tactic unit :=
  `[ right, left, existsi _, 
  split, swap ]

 meta def mt_bicut : tactic unit :=
  `[ left, existsi _, existsi _, 
  split, tactic.swap, split, tactic.swap ]

 meta def mt_cut_or_taut : tactic unit :=
    --binary cut
  `[ solve1{left, existsi [_, _], 
  split, swap, split, swap, mt_rules, try{mt_assump0}, done } <|>
    -- unary cut
  solve1 {right, left, existsi _, 
  split, tactic.swap, mt_rules, try{mt_assump0}, done} <|>
    -- tautologies
  solve1 {right, right, left, mt_rules, try{assumption}, done} <|>

  assumption ]

 meta def mt_verifier : tactic unit :=
  `[try{apply provable_no_cutR}, try{existsi prf},
   repeat{split, solve1 {mt_assump} <|>
                 solve1 {mt_ax}     <|>
                 solve1 {mt_mp}     <|>
                 solve1 {mt_cut_or_taut} <|> 
                 swap},
    try{exact rfl}]

--

-- EXISTS INTRO ELIM RULES

  lemma exintro2{P: α → β → Prop}(A: α)(B:β): 
    P A B →  ∃ A:α, ∃ B: β, P A B :=
  begin intro a, repeat{apply exists.intro}, exact a end

  lemma exintro3{P: α → β →γ →  Prop}(A: α)(B:β)(C:γ): 
    P A B C →  ∃ A:α, ∃ B: β,∃ C:γ, P A B C :=
  begin intro a, repeat{apply exists.intro}, exact a end

  lemma exelim2{P: α → β → Prop}{Q:Prop}: 
    (∃ A:α, ∃ B:β, P A B) → (∀ A:α, ∀ B:β, P A B → Q) → Q :=
  begin intros a a_1, apply exists.elim a, intros _ a_3, 
  apply exists.elim a_3, intros a_4 a_5, 
  exact a_1 a_2 a_4 a_5 end 

  lemma exelim3{P: α → β → γ → Prop}{Q:Prop}: 
    (∃ A:α, ∃ B:β, ∃ C:γ, P A B C) → (∀ A:α, ∀ B:β, ∀ C:γ, P A B C → Q) → Q :=
  λ hex hall, exists.elim hex 
  (λ A hex1, exists.elim hex1 
  (λ B hex3, exists.elim hex3 
  (λ C hP, hall A B C hP)))
--

-- FORM (inducive)

  -- definition of formulae
  inductive Form : Type
  | p : ℕ → Form
  | imp : Form → Form → Form
  | neg : Form → Form

  local infixr ⇒ : 80 := Form.imp
  local prefix `~` : 100 := Form.neg
  open Form
--

-- GLOBAL_VARIABLES

  -- definition of evaluation
  def eval := ℕ → bool 
  -- variables
  variables {v v₁ v₂:eval}
  variables {A B C D:Form}
  variables {Γ Δ:set Form}
  variables {m n:ℕ} 
  variables {a b:bool}
  variables {l li:list Form}

--

-- HK AXIOMS
  -- axioms of hilbert calculus
  def A1 (A B:Form) := A ⇒ (B ⇒ A)
  def A2 (A B C:Form) := (A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))
  def A3 (A B:Form) := (~B ⇒ ~A) ⇒ ((~B ⇒ A) ⇒ B)
-- 

-- PROOF
  -- formula in proof is either axiom, assumption or comes from modus ponens
  def in_proof (A:Form)(Γ:set Form)(l:list Form) : Prop :=
    (∃ B C, A = A1 B C)  ∨ 
    (∃ B C D, A = A2 B C D)  ∨ 
    (∃ B C, A = A3 B C)  ∨ 
    (A ∈ Γ)  ∨ 
    (∃ B, B ∈ l ∧ (B ⇒ A) ∈ l) 

  -- list l is a proof from set of assumptions Γ
  def is_proof (Γ:set Form)(l:list Form) : Prop := 
    list.rec_on l tt (λ A li IH, in_proof A Γ li ∧ IH)            
  
  -- formula A is provable from set of assumptions Γ
  def is_provable (Γ:set Form)(A:Form) : Prop :=  
    ∃ l: list Form, is_proof Γ (A::l)                                   
  
  infixr ` ⊢ ` : 40 := is_provable
  prefix ` ⊢ ` : 40 := is_provable {}

  -- list l is a proof with either binary/unary cut or tautology (or none) used
  def is_proof_with_cut (Γ:set Form)(l:list Form) : Prop := 
    list.rec_on l tt 
    (λ A li IH, ((∃ B C, B ∈ li ∧ C ∈ li ∧ {B,C} ⊢ A) ∨ 
                  (∃ B, B ∈ li ∧ {B} ⊢ A) ∨
                  ({} ⊢ A) ∨
                   in_proof A Γ li) 
                   ∧ IH )
  -- formula A is provable from Γ using mentioned cut rules
  def is_provable_with_cut (Γ:set Form)(A:Form) : Prop :=  
    ∃ l: list Form, is_proof_with_cut Γ (A::l)

  infixr ` ⊢cut ` : 40 := is_provable_with_cut
  prefix ` ⊢cut ` : 40 := is_provable {}
--   

-- PROOF lemmas
  -- useful lemmas about proof definitions

  lemma is_proof_ind : is_proof Γ (A::l) → is_proof Γ l := and.right      
  lemma in_proof_extend : in_proof A Γ l → l <+ li → in_proof A Γ li :=
    begin 
     intros a a_1, repeat {cases a, tac},
     cases a with hl hr, repeat {right},
     have hp: l ⊆ li, exact list.sublist.subset a_1,
     existsi hl, split, exact hp hr.1, exact hp hr.2        
    end

  lemma is_proof_concat : is_proof Γ l → is_proof Γ li → is_proof Γ (l++li) :=
    list.rec_on l
      (λ h hp, hp)
      (assume A lis IH Hl Hli, 
        ⟨ in_proof_extend Hl.1 (list.sublist_append_left lis li),
        IH (is_proof_ind Hl) Hli ⟩)

  lemma is_proof_extend : is_proof Γ l → A ∈ l → in_proof A Γ l :=
    list.rec_on l  
    (λ h hp, absurd rfl (list.ne_nil_of_mem hp))
    (λ D lis IH h hp,         
    have lem: A ∈ D::lis → A=D ∨ A∈ lis, from 
      λ h, or.elim (list.eq_or_ne_mem_of_mem h) (λ hp, or.inl hp) (λ hp, or.inr hp.2),
    have sub: lis<+D::lis, from by simp,
    or.elim (lem hp)                    
      (assume H, H.symm ▸ in_proof_extend h.1 sub)         
      (λ H, in_proof_extend  (IH (is_proof_ind h) H) sub))
 --

--

--SEMANTICS   

  -- definition of evaluation
  def val (v:eval) : Form → bool :=
    λ A:Form, Form.rec_on A (λ n:ℕ, v n) 
                            (λ A B:Form, λ a b:bool, !a || b) 
                            (λ A:Form, λ a:bool, !a)
  
  notation v `∗` := val v

  -- A is tautology
  def is_taut (A:Form) : Prop := ∀ v:eval, v∗ A = tt
  
  notation `⊧` := is_taut
--

-- SOUNDNESS 
  -- axioms are tautologies
  lemma A1_taut : ⊧ (A1 A B) :=
    λ v, have A1_bool: ∀ a b: bool, !a || (!b || a) = tt, 
    from by simp, A1_bool (v∗A) (v∗B)
    
  lemma A2_taut : ⊧ (A2 A B C) :=
    λ v, 
    have A2_bool: ∀ a b c: bool, 
    !(!a || (!b || c)) || (!(!a || b) || (!a || c)) = tt,
    from by simp, A2_bool (v∗ A) (v∗ B) (v∗ C) 
    
  lemma A3_taut : ⊧ (A3 A B):=
    λ v, 
    have A3_bool: ∀ a b:bool, !((!!b) || (!a)) || ((!(!!b || a)) || b) = tt, 
    from by simp, A3_bool (v∗ A) (v∗ B)      
    
  lemma MP_taut (h1:⊧ A)(h2:⊧ (A ⇒ B)) : ⊧ B :=
    λ v, have MP_bool: (∀ (a b:bool), (a = tt ∧ !a || b = tt) → b = tt), from  
      ( λ a b p1,
      have p2: ff || b = tt, from @eq.subst bool (λ x, bnot x || b = tt) a tt p1.1 p1.2,
      or.elim (bool.dichotomy b)
      (λ i, false.elim 
        (bool.ff_ne_tt (calc ff = ff || ff : rfl 
                             ...= tt : @eq.subst bool (λ x, ff || x = tt) b ff i p2)))
      (λ i, i) ),
    MP_bool (v∗A) (v∗(B)) ⟨h1 v, calc bnot (v∗A) || (v∗B) = (v∗(A ⇒ B)) : rfl 
                                                     ... = tt : (h2 v)⟩
  
  lemma soundness_lemma : ∀ A:Form, is_proof {} l ∧ A ∈ l → ⊧ A :=
    list.rec_on l
    (λ A i, forall_mem_nil ⊧ A i.2)
    (λ B k IH,
      (λ A, λ i_Bk: is_proof {} (B::k) ∧ A ∈ (B::k),
      or.elim i_Bk.2
      (begin intro j, cases i_Bk.1.1 with h,    
            
            apply exelim2 h, intros a b q, 
            rw [j, q], apply A1_taut, cases h,

            apply exelim3 h, intros a b c r,
            simp [j,r], apply A2_taut, cases h,

            apply exelim2 h, intros a b q, 
            rw [j, q], apply A3_taut, cases h,

            apply false.elim h,
                
            apply exists.elim h, intros b c, rw j, 
            have hb: ⊧ b, apply IH b ⟨is_proof_ind i_Bk.1, c.1⟩,
            have hbB: ⊧ (b ⇒ B), apply IH (b ⇒ B) ⟨is_proof_ind i_Bk.1, c.2⟩,  
            apply MP_taut hb hbB
      end)
    (λ j, IH A ⟨is_proof_ind i_Bk.1, j⟩)))

  theorem CPL_soundness : ∀ A:Form, ⊢ A → ⊧ A :=
    begin 
      intros a a_1, 
      apply exists.elim a_1, intros a_2 a_3, 
      exact soundness_lemma a ⟨a_3, by simp⟩ 
    end

-- 

-- PROVABLE lemmas
  -- monotony, cut rules, other rules
  -- provable with cut → provable without cut

  lemma modus_ponens_rule : {A, A ⇒ B} ⊢ B :=
    let prf:= [A, A ⇒ B] in 
    by{existsi prf, 
    split, mt_mp,
    split, iterate 3 {right}, left, simp, 
    split, iterate 3 {right}, left, simp, exact rfl}

  theorem binary_cut {A B C:Form}: 
  (Γ ⊢ A) → (Γ ⊢ B) → ({A, B} ⊢ C) → (Γ ⊢ C) := 
    begin 
      intros hA hB hAB,
      apply exists.elim hA, intros prfA is_prfA,
      apply exists.elim hB, intros prfB is_prfB, 
      apply exists.elim hAB, intro prfAB, 
      let pr:= (A::prfA++B::prfB), 
      let prA:= (A::prfA),
      let prB:= (B::prfB),

      have lem: ∀ l:list Form, is_proof {A,B} l → is_proof Γ (l++pr), 
      intro l, apply list.rec_on l, intro a,  
      exact (@is_proof_concat Γ (A::prfA) (B::prfB) is_prfA is_prfB),

      intros D li IH hp, split,
      cases hp.1,
      --repeat{{left, exact h} <|> right, try{cases h}},   
      left, exact h, 
      cases h, right, left, exact h,
      cases h, right, right, left, exact h, 
      cases h, simp at h, cases h, 
      rw[h], 
      have ha: A ∈ li++pr, by simp,  
      exact is_proof_extend (IH (is_proof_ind hp)) ha, 
      rw[h], 
      have ha: B ∈ li++pr, by simp,  
      exact is_proof_extend (IH (is_proof_ind hp)) ha, 
      
      repeat{right},
      apply exists.elim h,
      have s: li ⊆ (li ++ pr), by simp, 
      intros Q hQ, 
      existsi Q, split,
      exact s hQ.1,
      exact s hQ.2,
      exact IH (is_proof_ind hp),
      intro a,
      existsi (prfAB++pr),
      exact lem (C::prfAB) a
    end 

  lemma unary_cut {A B:Form}: (Γ ⊢ A) → ({A} ⊢ B) → (Γ ⊢ B) := 
    begin  
    have h: {A, A} = {A}, exact pair_eq_singleton A, rw[symm h],
    intros a a_1, exact binary_cut a a a_1 
    end

  lemma monotony_help : Γ ⊆ Δ → is_proof Γ l → is_proof Δ l := 
    begin 
    intro a,
    apply list.rec_on l, intro, exact rfl,
    intros _ _ _ a_2, split, swap, 
    exact ih (is_proof_ind a_2), 
    cases a_2, repeat {cases a_2_left, solve1{repeat{{left, exact a_2_left} <|> right}}},
    cases a_2_left, have h: hd ∈ Δ, exact mem_of_subset_of_mem a a_2_left, 
    all_goals {solve1{repeat{{left, assumption} <|> right <|> assumption}}}
    end 

  lemma monotony : Γ ⊆ Δ → Γ ⊢ A →  Δ ⊢ A := 
    begin 
    intros a a_1, 
    apply exists.elim a_1, intros a_2 a_3, 
    existsi a_2, exact monotony_help a a_3
    end
 /- MONOTONY, 2. way

  theorem monotony : Γ ⊆ Δ  →  Γ ⊢ A  →  Δ ⊢ A :=   
    λ sub, have lem: ∀ l, is_proof Γ l → is_proof Δ l, from
      λ l, list.rec_on l
      (λ hp, rfl)
      (λ B lis IH hp, ⟨begin cases hp.1,
                       proof, cases h, proof, cases h, proof, cases h, 
                       have hpp: B ∈ Δ, from sub h, repeat {proof} end, 
                       IH hp.2 ⟩ ),
    λ pr, exists.elim pr (λ li hp, ⟨li, lem (A::li) hp⟩)
 -/
  lemma provable_no_cutR : Γ ⊢cut A → Γ ⊢ A := 
    begin 
      have lem : ∀ l A, (is_proof_with_cut Γ l) → (A ∈ l) → (Γ ⊢ A),
      intro l, induction l with B lis IH, 
      --empty list:
      intros A a a_1, exact absurd rfl (list.ne_nil_of_mem a_1), 
      --list indukce
      intros E hp ha, cases ha, rw[ha], cases hp.1, 
      --binární
      apply exelim2 h, intros C D a,  
      have HC: Γ ⊢ C, from IH C hp.2 a.1 ,
      have HD: Γ ⊢ D, from IH D hp.2 a.2.1,
        exact binary_cut HC HD a.2.2, 
      --unární
      cases h, apply exists.elim h, intros C hC,  
      have HC: Γ ⊢ C, from IH C hp.2 hC.1 ,       
        exact unary_cut HC hC.2, 
      --nulární
      cases h, 
      have hyp: ∅ ⊆ Γ, from λ A hp, false.elim hp, 
        exact monotony hyp h,
      --norm proof
      cases h, apply exelim2 h, intros C D h_1,  
      rw[h_1], let prf:=[], focus{mt_verifier}, 
      cases h, apply exelim3 h, intros C D E h_1,  
      rw[h_1], let prf:=[], focus{mt_verifier},
      cases h, apply exelim2 h, intros C D h_1,  
      rw[h_1], let prf:=[], focus{mt_verifier}, 
      cases h, let prf:=[], existsi prf, split, 
      swap, exact rfl, iterate 3 {right}, left, assumption, 
      apply exists.elim h, intros G hG, 
      have Ha: Γ ⊢ G, exact  IH G hp.2 (hG.1),
      have Hb: Γ ⊢ G ⇒ B, exact  IH (G ⇒ B) hp.2 (hG.2),
      exact binary_cut Ha Hb modus_ponens_rule,
      --indukční krok
      exact IH E hp.2 ha,
      intros a, cases a with l hpp, have h: A∈ A::l, from by simp,
      exact lem (A::l) A hpp h  
    end
  . 
  lemma provable1 : Γ ⊢ A ⇒ A :=
    let prf:= [ (A ⇒ (A ⇒ A)) ⇒ (A ⇒ A), 
               A2 A (A ⇒ A) A,
               A1 A A, 
               A1 A (A ⇒ A) ] in
    by mt_verifier

  lemma exchange : {A ⇒ B, A ⇒ B ⇒ C} ⊢ A ⇒ C:= 
    let prf:= [(A ⇒ B) ⇒ A ⇒ C, A ⇒ B, A ⇒ B ⇒ C, A2 A B C] in
    by mt_verifier

  theorem deduction_theorem : (Γ ∪ {A} ⊢ B) → (Γ ⊢ A ⇒ B) :=
   have lem: ∀ l: list Form, is_proof (Γ ∪ {A}) l → 
                             ∀ B, B ∈ l →  
                             (Γ ⊢ A ⇒ B), from
   begin
    intro l, induction l with C li IH, 
    --prázdný list
    intros _ a a_1, exact absurd rfl (list.ne_nil_of_mem a_1),
    --indukční krok
    intros h B hp, cases hp,
    --B=C
    rw[hp],                          
    --když je C axiom
    cases h.1, 
    apply exelim2 h_1, intros _ _ ax, rw[ax],   
    focus{existsi ([_, A1 _ A]), mt_verifier}, cases h_1,
    apply exelim3 h_1, intros _ _ _ ax, rw[ax],   
    focus{existsi ([_, A1 _ A]), mt_verifier}, cases h_1, 
    apply exelim2 h_1, intros _ _ ax, rw[ax],   
    focus{existsi ([_, A1 _ A]), mt_verifier}, cases h_1, 
    --když C ∈ Γ ∪ {A}
    cases h_1, focus{let prf:= [C, A1 C A], mt_verifier},     
    cases h_1, exact provable1, 
    --modus ponens
    cases h_1 with B hB, 
     have Hd: Γ ⊢ A ⇒ B, exact IH h.2 B hB.1, 
     have Himp: Γ ⊢ A ⇒ B ⇒ C, exact IH h.2 (B ⇒ C) hB.2,
    exact (binary_cut Hd Himp exchange),
    --Indukční krok
    exact IH h.2 B hp  
   end,       
   assume h, exists.elim h (λ list hyp, 
   have is_in: B∈ B::list, from by simp,
   lem (B::list) hyp B is_in)
  
  theorem deduction_theoremR : (Γ ⊢ A ⇒ B) → (Γ ∪ {A} ⊢ B) := 
    begin 
      intro h, 
      have h3: Γ ⊆ Γ ∪ {A}, simp,
      have h21: Γ ∪ {A} ⊢ (A ⇒ B),
      exact monotony h3 h, 
      apply exists.elim h21, intros l h2,
      let prf:=(A::(A ⇒ B)::l), 
      existsi prf, 
      split, mt_mp, split, 
      iterate 3 {right}, left, simp,
      exact h2
    end 
 
  lemma double_neg_law: ⊢ ~~A ⇒ A :=
   begin 
    apply deduction_theorem, simp,
    let prf := 
    [
    (~A ⇒ ~A) ⇒  A,
    ~A ⇒ ~A,
    ~A ⇒ ~~A, 
    A3 (~A) A, 
    A1 (~~A) (~A),
    ~~A], mt_verifier 
   end

  lemma provable2 : Γ ⊢ A ⇒ ~~A := 
    let prf := [
                (~~~A ⇒ A) ⇒ ~~A, 
                A3 A (~~A),
                ~~~A ⇒ ~A,
                ~~~A ⇒ A, 
                A1 A (~~~A),
                A] in
    begin 
      apply monotony, 
      have h: {} ⊆ Γ, focus{simp}, exact h, 
      apply deduction_theorem, simp,
      mt_verifier
    end

  lemma transitivity : {A ⇒ B, B ⇒ C} ⊢ A ⇒ C :=
    let prf:= [
      (A ⇒ B) ⇒ (A ⇒ C),
      A ⇒ B, 
      A2 A B C, 
      A ⇒ (B ⇒ C), 
      A1 (B ⇒ C) A,
      B ⇒ C
    ] in by mt_verifier

  lemma RAA: {A ⇒ B, A ⇒ ~B} ⊢ ~A:= 
    have h1: {A ⇒ B} ⊢ ~~A ⇒ B, from 
      by{let prf:= [~~A ⇒ A, A ⇒ B], mt_verifier},
    have h2: {A ⇒ ~B} ⊢ ~~A ⇒ ~B, from 
      by{let prf:= [ ~~A ⇒ A, A ⇒ ~B ], mt_verifier}, 
    by{let prf:= [(~~A ⇒ B) ⇒ ~A, A3 B (~A), ~~A ⇒ ~B,~~A ⇒ B, A ⇒ B, A ⇒ ~B], mt_verifier}

  lemma contraposition : {A ⇒ B} ⊢ ~B ⇒ ~A := 
    by{apply deduction_theorem, 
    let prf:= [A ⇒ ~B, ~B ⇒ (A ⇒ ~B), ~B, A ⇒ B], mt_verifier}
                         
  lemma provable5 : {A ⇒ B, ~A ⇒ B} ⊢ B:= 
    let prf:= [                  
                        (~B ⇒ ~A ) ⇒ B, -- MP
                        (~B ⇒ ~~A) ⇒ (~B ⇒ ~A) ⇒ B, -- RAA {A ⇒ B, A ⇒ ~B} ⊢ ~A             
                        ~B ⇒ ~~A, -- {~A ⇒ B} ⊢ (~B ⇒ ~~A)
                        ~A ⇒ B, --assump
                        ~B ⇒ ~A, -- {A ⇒ B} ⊢ (~B ⇒ ~A)
                        A ⇒ B --assump
                    ] in
    by{mt_verifier}

 
 

  theorem PCP : (Γ ∪ {A} ⊢ B) → (Γ ∪ {~A} ⊢ B) → (Γ ⊢ B) := 
    assume h hneg, 
    have hp: Γ ⊢ A ⇒ B, from deduction_theorem h,
    have hpp: Γ ⊢ ~A ⇒ B, from deduction_theorem hneg,        
    binary_cut hp hpp (provable5)
  
  lemma modus_ponens : (Γ ⊢ A) → (Γ ⊢ (A ⇒ B)) → (Γ ⊢ B) :=
    begin 
      intros a a_1, 
      apply exists.elim a, intros la prfa, 
      apply exists.elim a_1, intros lab prfab,
      have h: is_proof Γ (A::la ++ (A⇒B)::lab), 
        from by {exact is_proof_concat prfa prfab},
      have h3: in_proof B Γ (A::la ++ (A⇒B)::lab), 
        from by {repeat{right}, exact exists.intro A ⟨by simp, by simp⟩},
      exact exists.intro (A::la ++ (A⇒B)::lab) ⟨h3, h⟩
    end

  lemma provable6 : (Γ ⊢ A) → (Γ ⊢ B ⇒ A) :=
    λ hA, have p1: Γ∪{B} ⊢ A, from monotony (subset_union_left Γ {B}) hA,
    deduction_theorem p1  

  lemma provable3 : (Γ ⊢ ~A) → (Γ ⊢ A ⇒ B):= 
    λ h, 
    have h0: Γ ⊆ Γ ∪ {A}, from by simp,
    have h1: Γ ∪ {A} ⊢ ~A, from monotony h0 h,
    have h2: Γ ∪ {A} ⊢ A, from let prf:= [A] in by mt_verifier,
    have h3: {~A, A} ⊢ B, from
    let prf:= [(~B ⇒ A) ⇒ B, A3 A B, ~B ⇒ A, A, A1 A (~B), 
    (~B ⇒ ~A), ~A, A1 (~A) (~B)] in by mt_verifier,
    deduction_theorem (binary_cut h1 h2 h3)

  lemma sets_eqv: ({A,B}:set Form) = {A} ∪ {B}:= 
    begin 
      apply funext, intro x, 
      apply propext, 
      split, 
      intro a, cases a, 
      repeat{cases a, mt_assump0}, exact rfl, 
      intro a, cases a, cases a, mt_assump0, cases a, mt_assump0,
      exact a    
    end

  lemma provable4_hlp : {A, ~B} ⊢ ~(A ⇒ B) := 
    begin 
      apply (@deduction_theoremR (~B) (~(A ⇒ B)) {A}),
      apply unary_cut, swap, exact contraposition, 
      have h: {A} = {} ∪ {A}, exact (@empty_union Form {A}).symm, rw[h], 
      apply (@deduction_theoremR A ((A ⇒ B) ⇒ B) {}), 
      apply deduction_theorem, apply deduction_theorem, 
      have h2: {A} ∪ {A ⇒ B} = {A, A ⇒ B}, exact sets_eqv.symm,  
      rw[h.symm, h2], 
      exact modus_ponens_rule
    end 

  lemma provable4 : (Γ ⊢ A) → (Γ ⊢ ~B) → (Γ ⊢ ~(A ⇒ B)):= 
    by{intros a b, exact binary_cut a b provable4_hlp}
--

-- COMPLETENESS preparation
 
 -- swap, lemmas
 -- lemmas for evaluating negation and implication
  @[simp] def swap (A:Form)(v:eval) : Form := 
    if v∗A = tt then A else ~A

  @[simp] def swap_var (n:ℕ)(v:eval): Form :=
    if v n = tt then p n else ~(p n)

  @[simp] theorem swap_tt : (v∗A = tt) → (swap A v = A) := 
    λ h, by simp [h]

  @[simp] theorem swap_ff : (v∗A = ff) → (swap A v = ~A) :=
    λ h, by simp [h]

  @[simp] lemma pswap_neg_tt: (v∗A = tt) → (v∗(~A) = ff) := 
    λ h, @eq.subst bool (λ x, (v∗(~A)) = bnot x) (v∗A) tt h rfl
  
  @[simp] lemma pswap_neg_ff: (v∗A = ff) → (v∗(~A) = tt) := 
    λ h, @eq.subst bool (λ x, (v∗(~A)) = bnot x) (v∗A) ff h rfl

  @[simp] theorem swap_neg_ff : (v∗A = ff) → swap (~A) v = ~A :=
    λ h, by simp [h]
 
  theorem swap_neg_tt : (v∗A = tt) → swap (~A) v = ~~A := 
    λ h, by simp[h]

  @[simp] lemma pswap_imp_tt_ff : (v∗A = tt) → (v∗B = ff) → (v∗(A ⇒ B) = ff) :=
    λ ha hb, have h2: (v∗(A ⇒ B)) = bnot (v∗A) || ff, from hb ▸ rfl,
    @eq.subst bool (λ x, (v∗(A ⇒ B)) = bnot x || ff) (v∗A) tt ha h2

  @[simp] lemma pswap_imp_tt_tt : (v∗A = tt) → (v∗B = tt) → (v∗(A ⇒ B) = tt) :=
    λ ha hb, have h2: (v∗(A ⇒ B)) = bnot (v∗A) || tt, from hb ▸ rfl,
    @eq.subst bool (λ x, (v∗(A ⇒ B)) = bnot x || tt) (v∗A) tt ha h2

  theorem swap_imp_tt_ff : 
      (v∗A = tt) → (v∗B = ff) → (swap (A ⇒ B) v = ~(A ⇒ B)) :=
    λ h h1, by simp[h, h1] 

  theorem swap_imp_tt_tt: 
      (v∗A = tt) → (v∗B = tt) → (swap (A ⇒ B) v = A ⇒ B) :=
    λ h p, by simp[h, p] 

  theorem swap_imp_ff : (v∗A = ff) → (v∗(A ⇒ B)) = tt := 
    λ h, calc v∗(A ⇒ B) = bnot ff || (v∗B) : h ▸ rfl

  lemma swap_var_tt : v n = tt → (swap_var n v = p n) := 
    λ h, by simp [h]

  lemma swap_var_ff : v n = ff → (swap_var n v = ~p n) :=
    λ h, by simp [h]
 
 -- svar_set set
  def svar_set (n:ℕ)(v:eval) : set Form :=
    { A | ∃ i:ℕ, i < n ∧ A = (swap_var i v)}

  def form_index (A:Form) : ℕ := 
    Form.rec_on A (λ n:ℕ, n+1) 
                  (λ A B:Form, λ na nb:ℕ, max na nb) 
                  (λ A:Form, λ m:ℕ, m)

  lemma swap_in_flae : (swap (p n) v) ∈  svar_set (form_index (p n)) v :=
    have h: form_index (p n) = n+1, from rfl,
    exists.intro n ⟨lt_succ_self n, rfl⟩   

  lemma flae_inclusion : (∀ n ≤ m,  svar_set n v ⊆  svar_set m v) := 
    λ n h A h', exists.elim h'
    (λ i h1, exists.intro i (show i < m ∧ A = swap_var i v, from 
    ⟨nat.le_trans h1.1 h, h1.2⟩))

  lemma flae_empty :  svar_set 0 v = {} := 
    funext (λ A:Form, show  svar_set 0 v A = false, from 
    propext ⟨ (λ h: svar_set 0 v A, exists.elim h (λ i h1, 
    (nat.succ_ne_zero i (nat.eq_zero_of_le_zero h1.1 )))),
    false.elim ⟩)
    
  lemma var_index_max_left : form_index A ≤ form_index (A ⇒ B) :=
    le_max_left (form_index A) (form_index B)

  lemma var_index_max_right : form_index B ≤ form_index (A ⇒ B) :=
    le_max_right (form_index A) (form_index B)

 -- truth eval 
  @[simp] def g₁ (n:ℕ)(v:eval) : ℕ → bool := 
   λ m, if m<n then v m else tt

  @[simp] def g₂ (n:ℕ)(v:eval) : ℕ → bool := 
   λ m, if m<n then v m else ff

  lemma g₁_eq_tt (h: m = n) : (g₁ n v) m = tt := 
    have ¬( m < n), from λ h', ne_of_lt h' h,
    by simp [this]
 
  lemma g₂_eq_ff (h: m = n) : (g₂ n v) m = ff := 
    have ¬  m < n, from λ h', ne_of_lt h' h,
    by simp [this]

  lemma g₁_v_eq_ite (v g:eval)(n:ℕ) : v n = g n → 
    ite (v n = tt) (p n) (~ p n) = ite (g n = tt) (p n) (~ p n) := 
   λ h, (@eq.subst bool (λ x, ite (v n = tt) (p n) (~ p n) = ite (x = tt) (p n) (~ p n)) 
   (v n) (g n) h) rfl 

  lemma g₁_v_eq: ∀ m < n, v m = (g₁ n v) m :=
   λ m n, by simp [n]

  lemma g₂_v_eq: ∀ m < n, v m = (g₂ n v) m :=
   λ m n, by simp [n]

  lemma g₁_v_swap_var_eq (v:eval) : m < n → swap_var m v = swap_var m (g₁ n v) := 
   λ h , have h1: v m = (g₁ n v) m, from g₁_v_eq m h,
   g₁_v_eq_ite v (g₁ n v) m h1

  lemma g₂_v_swap_var_eq (v:eval) : m<n → swap_var m v = swap_var m (g₂ n v) :=
   λ h , have h1: v m = (g₂ n v) m, from g₂_v_eq m h,
   g₁_v_eq_ite v (g₂ n v) m h1

  meta def flae_ind_tac : tactic unit := 
  `[  
      apply funext, intro A, 
      apply propext, split, 

      intro h, cases h, 
      cases h, existsi h_w, 
      split, exact nat.lt_trans h_h.1 (lt_add_one n), 
      rw[h_h.2], 
      {exact g₁_v_swap_var_eq v h_h.1} <|> {exact g₂_v_swap_var_eq v h_h.1}, 

      cases h, 
      existsi n, split, 
      exact lt_add_one n,
      have hp1: g₁ n v n = tt, from @g₁_eq_tt v n n rfl,
      have hp2: g₂ n v n = ff, from @g₂_eq_ff v n n rfl, 
      {rw[(@swap_var_tt (g₁ n v) n hp1).symm]} <|> 
      {rw[(@swap_var_ff (g₂ n v) n hp2).symm]},  

      intro h, cases h, 
      apply (@nat.lt_by_cases h_w n _), 
      intro h2, left, existsi _, 
      split, exact h2, 
      {rw[(g₁_v_swap_var_eq v h2)], exact h_h.2} <|> 
      {rw[(g₂_v_swap_var_eq v h2)], exact h_h.2},

      intro h2, right, 
      {rw[(swap_var_tt (@g₁_eq_tt v h_w n h2)), h2] at h_h, exact h_h.2} <|> 
      {rw[(swap_var_ff (@g₂_eq_ff v h_w n h2)), h2] at h_h, exact h_h.2}, 

      intro h2, have h5: h_w ≤ n, from iff.elim_left lt_succ_iff h_h.1,
      have h6: h_w ≤ n ∧ ¬h_w ≤ n, from ⟨h5, (iff.elim_left (lt_iff_not_ge n h_w)) h2⟩,
      exact false.elim (iff.elim_left (and_not_self (h_w ≤ n)) h6)
  ]

  lemma flae_ind : (svar_set n v) ∪ {p n} =  svar_set (n+1) (g₁ n v) :=
    by flae_ind_tac

  lemma flae_ind_neg : (svar_set n v) ∪ {~p n} =  svar_set (n+1) (g₂ n v) :=
    by flae_ind_tac

 
 -- induction formalization 
  def nprovable (A:Form)(n:ℕ) : Prop :=
    ∀ v:eval, (svar_set n v) ⊢ A

  lemma PCP_app : ∀ n:ℕ, nprovable A (n+1) → nprovable A n:=
    λ n hp f, show  (svar_set n f) ⊢ A, from PCP
    (@eq.subst (set Form) (λ Γ, Γ ⊢ A) (svar_set (n+1) (g₁ n f)) ((svar_set n f) ∪ {p n}) 
      (@flae_ind f n).symm (hp (g₁ n f)))        
    (@eq.subst (set Form) (λ Γ, Γ ⊢  A) (svar_set (n+1) (g₂ n f)) ((svar_set n f) ∪ { ~(p n)}) 
      (@flae_ind_neg f n).symm (hp (g₂ n f)))

  theorem nprov_theorem : nprovable A n → (⊢ A) :=
    λ h, have H: nprovable A n → nprovable A 0, from  
      nat.rec_on n (λ h, h) (assume n IH hp, IH (PCP_app n hp)), 
    (@flae_empty (λ n:ℕ, tt)) ▸ (H h) (λ n:ℕ, tt)

 --
--

-- COMPLETENESS

  lemma main_lemma : ∀ v:eval, (svar_set (form_index A) v) ⊢ swap A v := 
    λ v,
    Form.rec_on A 
    -- p constructor     
    (λ n, exists.intro []
      ⟨or.inr (or.inr (or.inr (or.inl swap_in_flae))), rfl⟩)
    -- imp constructor
    (λ A B, let Γa := (svar_set (form_index A) v),
                Γb:set Form := (svar_set (form_index B) v),
                Γimp := (svar_set (form_index (A ⇒ B)) v) in
   λ IHa: Γa ⊢ swap A v, 
   λ IHb: Γb ⊢ swap B v,
   have h: Γa ⊆ Γimp, from flae_inclusion (form_index A) var_index_max_left,
   have hbb: Γb ⊆ Γimp, from flae_inclusion (form_index B) var_index_max_right, 
   or.elim (bool.dichotomy (v∗A))
    -- v∗A=ff                          
     (λ hpa, have himp: swap (A ⇒ B) v = (A ⇒ B), from swap_tt (swap_imp_ff hpa),                          
     (calc (Γa ⊢ swap A v) → (Γa ⊢ ~A)                :  λ h, swap_ff hpa ▸ IHa
                 ...       → (Γa ⊢ A ⇒ B)             :  λ h, provable3 h 
                 ...       → (Γimp ⊢ A ⇒ B)           :  λ hp, monotony h hp    
                 ...       → (Γimp ⊢ swap (A ⇒ B) v)  :  λ h, himp.symm ▸ h) 
     IHa)
              
    -- v∗A=tt 
     (λ hpa, or.elim (bool.dichotomy (v∗ B))
      -- v∗B=ff
      (λ hpb, have ha: (Γimp ⊢ A), from  
              (calc (Γa ⊢ swap A v) → (Γa ⊢ A)    : λ h5, swap_tt hpa ▸ IHa
                          ...       → (Γimp ⊢ A)  : λ h5, monotony h h5) IHa, 
              have hb: (Γimp ⊢ ~B), from 
              (calc (Γb ⊢ swap B v) → (Γb ⊢ ~B)   : λ h5, swap_ff hpb ▸ IHb
                           ...      → (Γimp ⊢ ~B) : λ h5, monotony hbb h5) IHb, 
              have hab: (Γimp ⊢ ~(A ⇒ B)), from provable4 ha hb, 
              (calc (Γimp ⊢ ~(A ⇒ B)) → (Γimp ⊢ swap (A ⇒ B) v) : 
               λ h5, eq.substr (swap_imp_tt_ff hpa hpb) h5) hab)
      -- v∗B=tt
      (λ hpb, have hb: (Γimp ⊢ B), from 
              (calc (Γb ⊢ swap B v) → (Γb ⊢ B)   : λ h5, swap_tt hpb ▸ IHb
                           ...      →  (Γimp ⊢ B) : λ h5, monotony hbb h5) IHb, 
              have hab: (Γimp ⊢ (A ⇒ B)), from (@provable6 B A Γimp) hb, 
              (calc (Γimp ⊢ (A ⇒ B)) → (Γimp ⊢ swap (A ⇒ B) v) : 
               λ h5, (swap_imp_tt_tt hpa hpb).symm ▸ h5) hab)))
    -- neg₁ constructor
    (λ A,   let Γa := ( svar_set (form_index A) v) in              
     λ ha: Γa ⊢ swap A v, 
     show Γa ⊢ swap (~A) v, from 
     or.elim (bool.dichotomy (v∗A))
    -- v∗A=ff
    (λ h, (calc (Γa ⊢ swap A v) → (Γa ⊢ ~A)          : λ h1, swap_ff h ▸ ha
                       ...      → (Γa ⊢ swap (~A) v) : λ h1, (swap_neg_ff h).symm ▸ h1) ha) 
    -- v∗A=tt 
    (λ h, (calc (Γa ⊢ swap A v) → (Γa ⊢ A)           : λ h1, swap_tt h ▸ ha
                       ...      → (Γa ⊢ ~~A)         : λ h1, modus_ponens h1 provable2
                       ...      → (Γa ⊢ swap (~A) v) : λ h1, (swap_neg_tt h).symm ▸ h1) ha))
  
  theorem CPL_completeness: ⊧ A → ⊢ A :=
    λ h, have H: nprovable A (form_index A), from             
      (λ v:eval, @eq.subst Form 
      (λ B:Form, is_provable (svar_set (form_index A) v) B) 
      (swap A v) A (swap_tt (h v)) (main_lemma v)),
    nprov_theorem H
    
-- 
