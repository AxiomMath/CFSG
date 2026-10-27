module

public import CFSG.Quasithin.Background.B3ThreeBasic
public import CFSG.Quasithin.Background.B3VMod
public import CFSG.Quasithin.Background.B3Sign
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.Quasithin.B3

open CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ}

abbrev LG (n : ℕ) : Type := ↥(alternatingGroup (Fin n))

@[expose] noncomputable def actL (n : ℕ) (k : Mod) : LG n →* MulAut (Mod.V n k) :=
  (Mod.act n k).comp (alternatingGroup (Fin n)).subtype

theorem actL_apply (n : ℕ) (k : Mod) (x : LG n) (v : Mod.V n k) :
    actL n k x v = Mod.act n k x.1 v := rfl

@[expose] def genTab (n : ℕ) : Bool → Tab
  | false => 1 :: 2 :: 0 :: (List.range n).drop 3
  | true => if n % 2 = 1 then (List.range n).map (fun i => (i + 1) % n)
            else 0 :: (List.range (n - 1)).map (fun j => (j + 1) % (n - 1) + 1)

@[expose] def wordTab (n : ℕ) : List Bool → Tab
  | [] => idT n
  | g :: w => mulT (genTab n g) (wordTab n w)

@[expose] def GoodGen (n : ℕ) : Prop :=
  ∀ g : Bool, isTab n (genTab n g) = true ∧ isEvenT (genTab n g) = true

theorem goodGen_of (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) : GoodGen n := by
  rcases hn with rfl | rfl | rfl | rfl <;> (unfold GoodGen; decide)

@[expose] noncomputable def genElt (n : ℕ) (g : Bool) : LG n :=
  if h : isTab n (genTab n g) = true ∧ isEvenT (genTab n g) = true then
    ⟨(exists_tab_eq h.1).choose, (mem_alternatingGroup_iff _).2
      (by rw [(exists_tab_eq h.1).choose_spec]; exact h.2)⟩
  else 1

theorem tab_genElt {n : ℕ} (hg : GoodGen n) (g : Bool) : tab (genElt n g).1 = genTab n g := by
  unfold genElt
  split_ifs with h
  · exact (exists_tab_eq h.1).choose_spec
  · exact absurd (hg g) h

@[expose] noncomputable def evalG (n : ℕ) : List Bool → LG n
  | [] => 1
  | g :: w => genElt n g * evalG n w

theorem tab_evalG {n : ℕ} (hg : GoodGen n) (w : List Bool) :
    tab (evalG n w).1 = wordTab n w := by
  induction w with
  | nil => exact tab_one
  | cons g w ih =>
    show tab ((genElt n g * evalG n w : LG n) : Gp n) = mulT (genTab n g) (wordTab n w)
    rw [Subgroup.coe_mul, tab_mul, tab_genElt hg, ih]

theorem evalG_eq_of_wordTab {n : ℕ} (hg : GoodGen n) {w₁ w₂ : List Bool}
    (h : wordTab n w₁ = wordTab n w₂) : evalG n w₁ = evalG n w₂ := by
  apply Subtype.ext
  apply tab_injective
  rw [tab_evalG hg, tab_evalG hg, h]

theorem evalG_mem_closure (n : ℕ) (w : List Bool) :
    evalG n w ∈ Subgroup.closure {genElt n false, genElt n true} := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons g w ih =>
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) ih
    cases g <;> simp

@[expose] def cw : ℕ → ℕ → List Bool
  | 5, 0 => [false]
  | 5, 1 => [false, true, true, true, false, true]
  | 5, 2 => [true, true, true, true, false, true]
  | 6, 0 => [false]
  | 6, 1 => [false, true, true, false, true, false, true]
  | 6, 2 => [true, false, true, true, false, true, false, false]
  | 6, 3 => [false, true, false, true, false, true, true]
  | 7, 0 => [false]
  | 7, 1 => [false, true, true, true, false, true, true, false, true]
  | 7, 2 => [false, true, true, false, true, false, true, true, false, true]
  | 7, 3 => [false, true, true, false, true, true, true, false, true]
  | 7, 4 => [true, true, true, true, true, true, false, true]
  | 8, 0 => [false]
  | 8, 1 => [true, false, true, true, true, true, true, true, false]
  | 8, 2 => [true, false, true, true, false, true, false, true, false, true, false, false]
  | 8, 3 => [false, true, false, true, false, true, true, false, true, false, true]
  | 8, 4 => [true, true, true, true, true, false, false, true, false, false, true]
  | 8, 5 => [true, true, true, true, true, true, false, false, true]
  | _, _ => []

theorem cw_spec_five : ∀ i : Fin 3, tab (altThreeCyclePerm i) = wordTab 5 (cw 5 i) := by decide
theorem cw_spec_six : ∀ i : Fin 4, tab (altThreeCyclePerm i) = wordTab 6 (cw 6 i) := by decide
theorem cw_spec_seven : ∀ i : Fin 5, tab (altThreeCyclePerm i) = wordTab 7 (cw 7 i) := by decide
theorem cw_spec_eight : ∀ i : Fin 6, tab (altThreeCyclePerm i) = wordTab 8 (cw 8 i) := by decide

theorem closure_genElt_of {m : ℕ} (hg : GoodGen (m + 2))
    (hcw : ∀ i : Fin m, tab (altThreeCyclePerm i) = wordTab (m + 2) (cw (m + 2) i)) :
    Subgroup.closure {genElt (m + 2) false, genElt (m + 2) true} = ⊤ := by
  rw [eq_top_iff, ← closure_altThreeCycle (n := m)]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  have h1 : altThreeCycle i = evalG (m + 2) (cw (m + 2) i) := by
    apply Subtype.ext
    apply tab_injective
    rw [tab_evalG hg, ← hcw i]
    rfl
  rw [h1]
  exact evalG_mem_closure _ _

theorem closure_genElt (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    Subgroup.closure {genElt n false, genElt n true} = ⊤ := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact closure_genElt_of (m := 3) (goodGen_of (Or.inl rfl)) cw_spec_five
  · exact closure_genElt_of (m := 4) (goodGen_of (Or.inr (Or.inl rfl))) cw_spec_six
  · exact closure_genElt_of (m := 5) (goodGen_of (Or.inr (Or.inr (Or.inl rfl)))) cw_spec_seven
  · exact closure_genElt_of (m := 6) (goodGen_of (Or.inr (Or.inr (Or.inr rfl)))) cw_spec_eight

theorem eq_of_der_eq_on_gens {Γ : Type*} [Group Γ] {V : Type*} [CommGroup V] {ρ : Γ →* MulAut V}
    {S : Set Γ} (hS : Subgroup.closure S = ⊤) {d e : Γ → V} (hd : IsDer ρ d) (he : IsDer ρ e)
    (h : ∀ x ∈ S, d x = e x) : d = e := by
  let K : Subgroup Γ :=
    { carrier := {x | d x = e x}
      one_mem' := by
        show d 1 = e 1
        rw [hd.map_one, he.map_one]
      mul_mem' := fun {x y} hx hy => by
        show d (x * y) = e (x * y)
        rw [hd x y, he x y]
        have hx' : d x = e x := hx
        have hy' : d y = e y := hy
        rw [hx', hy']
      inv_mem' := fun {x} hx => by
        show d x⁻¹ = e x⁻¹
        have hx' : d x = e x := hx
        have h1 := hd x x⁻¹
        have h2 := he x x⁻¹
        rw [mul_inv_cancel, hd.map_one] at h1
        rw [mul_inv_cancel, he.map_one] at h2
        have h3 : ρ x (d x⁻¹) = (d x)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
        have h4 : ρ x (e x⁻¹) = (e x)⁻¹ := eq_inv_of_mul_eq_one_right h2.symm
        apply (ρ x).injective
        rw [h3, h4, hx'] }
  have hle : Subgroup.closure S ≤ K := (Subgroup.closure_le K).2 h
  funext x
  exact hle (hS ▸ Subgroup.mem_top x)

section Masks

variable {n : ℕ}

theorem actM_lt (σ : Gp n) (m : ℕ) : actM n (tab σ) m < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  unfold actM
  rw [testBit_foldl_aux, Nat.zero_testBit, Bool.false_or, Bool.eq_false_iff]
  intro hany
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hany
  obtain ⟨i, hi, -, hgd⟩ := hany
  have h1 : (tab σ).getD i 0 = (σ ⟨i, hi⟩ : ℕ) := getD_tab σ ⟨i, hi⟩
  have h2 := (σ ⟨i, hi⟩).isLt
  omega

theorem actM_mul (σ τ : Gp n) (m : ℕ) :
    actM n (tab (σ * τ)) m = actM n (tab σ) (actM n (tab τ) m) := by
  apply vecOfNat_injective (actM_lt _ _) (actM_lt _ _)
  rw [vecOfNat_actM, vecOfNat_actM, vecOfNat_actM, map_mul]
  rfl

theorem actM_xor (σ : Gp n) (a b : ℕ) :
    actM n (tab σ) (a ^^^ b) = actM n (tab σ) a ^^^ actM n (tab σ) b := by
  apply vecOfNat_injective (actM_lt _ _) (Nat.xor_lt_two_pow (actM_lt _ _) (actM_lt _ _))
  rw [vecOfNat_actM, vecOfNat_xor, map_mul, vecOfNat_xor, vecOfNat_actM, vecOfNat_actM]

end Masks

@[expose] def dEval (n m1 m2 : ℕ) : List Bool → ℕ
  | [] => 0
  | g :: w => (if g then m2 else m1) ^^^ actM n (genTab n g) (dEval n m1 m2 w)

theorem inWk_zero (n : ℕ) (k : Mod) : inWk n k 0 = true := by
  cases k <;> simp [inWk, popPar]

theorem toV_zero (n : ℕ) (k : Mod) : toV n k 0 = 1 := by
  rw [toV_eq_one_iff (inWk_zero n k)]
  cases k <;> simp [inNk]

theorem dEval_spec {n : ℕ} (hg : GoodGen n) {k : Mod} {d : LG n → Mod.V n k}
    (hd : IsDer (actL n k) d) {m1 m2 : ℕ} (h1 : inWk n k m1 = true) (h2 : inWk n k m2 = true)
    (e1 : toV n k m1 = d (genElt n false)) (e2 : toV n k m2 = d (genElt n true))
    (w : List Bool) :
    inWk n k (dEval n m1 m2 w) = true ∧ toV n k (dEval n m1 m2 w) = d (evalG n w) := by
  induction w with
  | nil => exact ⟨inWk_zero n k, by rw [show dEval n m1 m2 [] = 0 from rfl, toV_zero]; exact hd.map_one.symm⟩
  | cons g w ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hmg : inWk n k (if g then m2 else m1) = true := by cases g <;> simpa using ‹_›
    have hdg : toV n k (if g then m2 else m1) = d (genElt n g) := by cases g <;> simpa using ‹_›
    have hact : inWk n k (actM n (genTab n g) (dEval n m1 m2 w)) = true := by
      rw [← tab_genElt hg g]
      exact inWk_actM (genElt n g).1 ih1
    refine ⟨inWk_xor hmg hact, ?_⟩
    show toV n k ((if g then m2 else m1) ^^^ actM n (genTab n g) (dEval n m1 m2 w)) =
      d (genElt n g * evalG n w)
    rw [toV_xor hmg hact, hdg, hd, actL_apply, ← tab_genElt hg g, ← act_toV (genElt n g).1 ih1, ih2]

@[expose] def relPairs : ℕ → List (List Bool × List Bool)
  | 5 => [([false, false, false], []), ([false, true, true, false], [true, true, true])]
  | 6 => [([false, false, false], []), ([true, true, true, true, true], []),
      ([false, true, false, true, false, true, false], [true, true, true, true])]
  | 7 => [([false, false, false], []),
      ([true, true, false, true, true, false, true, true], [false, false])]
  | 8 => [([false, false, false], []), ([true, true, true, true, true, true, true], []),
      ([true, true, false, true, true, true, true, true, false, true, true],
        [false, true, false, true, false])]
  | _ => []

@[expose] def relsOK (n : ℕ) : Bool := (relPairs n).all fun p => wordTab n p.1 == wordTab n p.2

theorem relsOK_of (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) : relsOK n = true := by
  rcases hn with rfl | rfl | rfl | rfl <;> decide

@[expose] def relHolds (n : ℕ) (k : Mod) (m1 m2 : ℕ) : Bool :=
  (relPairs n).all fun p => inNk n k (dEval n m1 m2 p.1 ^^^ dEval n m1 m2 p.2)

@[expose] def princPair (n : ℕ) (k : Mod) (m1 m2 : ℕ) : Bool :=
  (List.range (2 ^ n)).any fun w => inWk n k w &&
    inNk n k (actM n (genTab n false) w ^^^ w ^^^ m1) &&
    inNk n k (actM n (genTab n true) w ^^^ w ^^^ m2)

@[expose] def d0m (n : ℕ) (g : Bool) : ℕ := actM n (genTab n g) 1 ^^^ 1

@[expose] def relA (n : ℕ) (k : Mod) (m1 : ℕ) : Bool :=
  inNk n k (dEval n m1 0 [false, false, false] ^^^ dEval n m1 0 [])

@[expose] def cands (n : ℕ) (k : Mod) : List ℕ :=
  (List.range (2 ^ n)).filter fun m1 => inWk n k m1 && relA n k m1

@[expose] def chkRow (n : ℕ) (k : Mod) (two : Bool) (m1 : ℕ) : Bool :=
  (List.range (2 ^ n)).all fun m2 =>
    !(inWk n k m2 && relHolds n k m1 m2) || princPair n k m1 m2 ||
      (two && princPair n k (m1 ^^^ d0m n false) (m2 ^^^ d0m n true))

@[expose] def chkH1 (n : ℕ) (k : Mod) (two : Bool) : Bool := (cands n k).all (chkRow n k two)

@[expose] def chkNP (n : ℕ) (k : Mod) : Bool :=
  !((List.range (2 ^ n)).any fun w => inWk n k w &&
    inNk n k (actM n (genTab n false) w ^^^ w ^^^ d0m n false) &&
    inNk n k (actM n (genTab n true) w ^^^ w ^^^ d0m n true))

theorem toV_eq_of_inNk {n : ℕ} {k : Mod} {a b : ℕ} (ha : inWk n k a = true)
    (hb : inWk n k b = true) (h : inNk n k (a ^^^ b) = true) : toV n k a = toV n k b := by
  have h1 : toV n k (a ^^^ b) = 1 := (toV_eq_one_iff (inWk_xor ha hb)).2 h
  rw [toV_xor ha hb] at h1
  have h2 : toV n k b * toV n k b = 1 := by rw [← pow_two]; exact V_sq k _
  exact (mul_eq_one_iff_eq_inv.1 h1).trans (inv_eq_of_mul_eq_one_right h2)

theorem relOne_of_der {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) {k : Mod}
    {d : LG n → Mod.V n k} (hd : IsDer (actL n k) d) {m1 m2 : ℕ} (h1 : inWk n k m1 = true)
    (h2 : inWk n k m2 = true) (e1 : toV n k m1 = d (genElt n false))
    (e2 : toV n k m2 = d (genElt n true)) {p : List Bool × List Bool}
    (hw : wordTab n p.1 = wordTab n p.2) :
    inNk n k (dEval n m1 m2 p.1 ^^^ dEval n m1 m2 p.2) = true := by
  have hg := goodGen_of hn
  have he : evalG n p.1 = evalG n p.2 := evalG_eq_of_wordTab hg hw
  obtain ⟨a1, b1⟩ := dEval_spec hg hd h1 h2 e1 e2 p.1
  obtain ⟨a2, b2⟩ := dEval_spec hg hd h1 h2 e1 e2 p.2
  exact (toV_eq_one_iff (inWk_xor a1 a2)).1 (by
    rw [toV_xor a1 a2, b1, b2, he, ← pow_two]
    exact V_sq k _)

theorem relHolds_of_der {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) {k : Mod}
    {d : LG n → Mod.V n k} (hd : IsDer (actL n k) d) {m1 m2 : ℕ} (h1 : inWk n k m1 = true)
    (h2 : inWk n k m2 = true) (e1 : toV n k m1 = d (genElt n false))
    (e2 : toV n k m2 = d (genElt n true)) : relHolds n k m1 m2 = true := by
  have hrel := relsOK_of hn
  unfold relHolds
  simp only [List.all_eq_true]
  intro p hp
  have hw : wordTab n p.1 = wordTab n p.2 := by
    unfold relsOK at hrel
    simp only [List.all_eq_true, beq_iff_eq] at hrel
    exact hrel p hp
  exact relOne_of_der hn hd h1 h2 e1 e2 hw

theorem relA_of_der {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) {k : Mod}
    {d : LG n → Mod.V n k} (hd : IsDer (actL n k) d) {m1 m2 : ℕ} (h1 : inWk n k m1 = true)
    (h2 : inWk n k m2 = true) (e1 : toV n k m1 = d (genElt n false))
    (e2 : toV n k m2 = d (genElt n true)) : relA n k m1 = true := by
  have hw : wordTab n ([false, false, false], ([] : List Bool)).1 =
      wordTab n ([false, false, false], ([] : List Bool)).2 := by
    rcases hn with rfl | rfl | rfl | rfl <;> decide
  exact relOne_of_der hn hd h1 h2 e1 e2 hw

theorem eq_pder_of_match {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) {k : Mod}
    {d : LG n → Mod.V n k} (hd : IsDer (actL n k) d) {m1 m2 w : ℕ} (hw : inWk n k w = true)
    (hm1 : inWk n k m1 = true) (hm2 : inWk n k m2 = true)
    (e1 : toV n k m1 = d (genElt n false)) (e2 : toV n k m2 = d (genElt n true))
    (h1 : inNk n k (actM n (genTab n false) w ^^^ w ^^^ m1) = true)
    (h2 : inNk n k (actM n (genTab n true) w ^^^ w ^^^ m2) = true) :
    d = pder (actL n k) (toV n k w) := by
  have hg := goodGen_of hn
  refine eq_of_der_eq_on_gens (closure_genElt hn) hd (isDer_pder _ _) ?_
  have key : ∀ g : Bool, ∀ m : ℕ, inWk n k m = true → toV n k m = d (genElt n g) →
      inNk n k (actM n (genTab n g) w ^^^ w ^^^ m) = true →
      d (genElt n g) = pder (actL n k) (toV n k w) (genElt n g) := by
    intro g m hm hdm hmem
    have hX : inWk n k (actM n (genTab n g) w) = true := by
      rw [← tab_genElt hg g]
      exact inWk_actM (genElt n g).1 hw
    have := toV_eq_of_inNk (inWk_xor hX hw) hm hmem
    rw [← hdm, ← this, toV_xor hX hw]
    simp only [pder, actL_apply]
    rw [← tab_genElt hg g, act_toV (genElt n g).1 hw]
    have hi : (toV n k w)⁻¹ = toV n k w := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_two]
      exact V_sq k _
    rw [hi]
  rintro x (rfl | rfl)
  · exact key false m1 hm1 e1 h1
  · exact key true m2 hm2 e2 h2

theorem exists_match_of_chk {n : ℕ} {k : Mod} {m1 m2 : ℕ} (h : princPair n k m1 m2 = true) :
    ∃ w, inWk n k w = true ∧ inNk n k (actM n (genTab n false) w ^^^ w ^^^ m1) = true ∧
      inNk n k (actM n (genTab n true) w ^^^ w ^^^ m2) = true := by
  unfold princPair at h
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨w, -, ⟨h1, h2⟩, h3⟩ := h
  exact ⟨w, h1, h2, h3⟩

theorem zeroClass_of_chk {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) (k : Mod)
    (hchk : chkH1 n k false = true) : ZeroClass (actL n k) := by
  intro d hd
  obtain ⟨m1, hm1lt, hm1, e1⟩ := toV_surj k (d (genElt n false))
  obtain ⟨m2, hm2lt, hm2, e2⟩ := toV_surj k (d (genElt n true))
  have hrel := relHolds_of_der hn hd hm1 hm2 e1 e2
  have hrA := relA_of_der hn hd hm1 hm2 e1 e2
  have hm1mem : m1 ∈ cands n k := by
    unfold cands
    rw [List.mem_filter, List.mem_range]
    exact ⟨hm1lt, by simp [hm1, hrA]⟩
  unfold chkH1 at hchk
  have hrow := List.all_eq_true.1 hchk m1 hm1mem
  unfold chkRow at hrow
  have h := List.all_eq_true.1 hrow m2 (List.mem_range.2 hm2lt)
  have h' : princPair n k m1 m2 = true := by simpa [hm1, hm2, hrel] using h
  obtain ⟨w, hw, h1, h2⟩ := exists_match_of_chk h'
  exact ⟨toV n k w, eq_pder_of_match hn hd hw hm1 hm2 e1 e2 h1 h2⟩

@[expose] noncomputable def d0 (n : ℕ) (k : Mod) (x : LG n) : Mod.V n k :=
  toV n k (actM n (tab x.1) 1 ^^^ 1)

theorem inWk_d0m {n : ℕ} {k : Mod} (hk : k = Mod.u0 ∨ k = Mod.ut0) (h1 : popPar n 1 = false)
    (σ : Gp n) : inWk n k (actM n (tab σ) 1 ^^^ 1) = true := by
  have hW : ∀ m, inWk n k m = popPar n m := by
    intro m
    rcases hk with rfl | rfl <;> rfl
  rw [hW, ← vecOfNat_mem_U0, vecOfNat_xor, vecOfNat_actM]
  refine mul_mem_U0_of_not_mem ?_ ?_
  · intro h
    have h2 := isInv_U0 n σ⁻¹ _ h
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h2
    have h3 : vecOfNat n 1 ∈ U0 n := h2
    rw [vecOfNat_mem_U0, h1] at h3
    exact Bool.noConfusion h3
  · intro h
    rw [vecOfNat_mem_U0, h1] at h
    exact Bool.noConfusion h

theorem isDer_d0 {n : ℕ} {k : Mod} (hk : k = Mod.u0 ∨ k = Mod.ut0) (h1 : popPar n 1 = false) :
    IsDer (actL n k) (d0 n k) := by
  intro x y
  have hx : inWk n k (actM n (tab x.1) 1 ^^^ 1) = true := inWk_d0m hk h1 x.1
  have hy : inWk n k (actM n (tab y.1) 1 ^^^ 1) = true := inWk_d0m hk h1 y.1
  have hxy : inWk n k (actM n (tab x.1) (actM n (tab y.1) 1 ^^^ 1)) = true := inWk_actM x.1 hy
  show toV n k (actM n (tab (x * y).1) 1 ^^^ 1) = toV n k (actM n (tab x.1) 1 ^^^ 1) *
    Mod.act n k x.1 (toV n k (actM n (tab y.1) 1 ^^^ 1))
  rw [act_toV x.1 hy, ← toV_xor hx hxy]
  congr 1
  rw [Subgroup.coe_mul, actM_mul, actM_xor]
  generalize actM n (tab x.1) (actM n (tab y.1) 1) = A
  generalize actM n (tab x.1) 1 = B
  rw [Nat.xor_comm B 1, Nat.xor_assoc, ← Nat.xor_assoc B, Nat.xor_comm B A, Nat.xor_assoc A,
    Nat.xor_self, Nat.xor_zero, Nat.xor_comm]

theorem d0_gen {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) (k : Mod) (g : Bool) :
    d0 n k (genElt n g) = toV n k (d0m n g) := by
  unfold d0 d0m
  rw [tab_genElt (goodGen_of hn) g]

theorem popPar_one_false (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) : popPar n 1 = false := by
  rcases hn with rfl | rfl | rfl | rfl <;> decide

theorem inWk_d0m_gen {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) {k : Mod}
    (hk : k = Mod.u0 ∨ k = Mod.ut0) (g : Bool) : inWk n k (d0m n g) = true := by
  have := inWk_d0m hk (popPar_one_false hn) (genElt n g).1
  rwa [tab_genElt (goodGen_of hn) g] at this

theorem inNk_of_toV_eq {n : ℕ} {k : Mod} {a b : ℕ} (ha : inWk n k a = true)
    (hb : inWk n k b = true) (h : toV n k a = toV n k b) : inNk n k (a ^^^ b) = true := by
  refine (toV_eq_one_iff (inWk_xor ha hb)).1 ?_
  rw [toV_xor ha hb, h, ← pow_two]
  exact V_sq k _

theorem twoClass_of_chk {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) {k : Mod}
    (hk : k = Mod.u0 ∨ k = Mod.ut0) (hchk : chkH1 n k true = true) (hnp : chkNP n k = true) :
    TwoClass (actL n k) (d0 n k) := by
  have hg := goodGen_of hn
  have hd0 : IsDer (actL n k) (d0 n k) := isDer_d0 hk (popPar_one_false hn)
  refine ⟨hd0, ?_, ?_⟩
  · rintro ⟨v, hv⟩
    obtain ⟨m, hmlt, hm, rfl⟩ := toV_surj k v
    unfold chkNP at hnp
    simp only [Bool.not_eq_true', List.any_eq_false, List.mem_range, Bool.and_eq_true] at hnp
    apply hnp m hmlt
    have key : ∀ g : Bool, inNk n k (actM n (genTab n g) m ^^^ m ^^^ d0m n g) = true := by
      intro g
      have hX : inWk n k (actM n (genTab n g) m) = true := by
        rw [← tab_genElt hg g]
        exact inWk_actM (genElt n g).1 hm
      have h1 := congrFun hv (genElt n g)
      rw [d0_gen hn k g] at h1
      simp only [pder, actL_apply] at h1
      rw [toV_ratio (genElt n g).1 hm, tab_genElt hg g] at h1
      exact inNk_of_toV_eq (inWk_xor hX hm) (inWk_d0m_gen hn hk g) h1.symm
    exact ⟨⟨hm, key false⟩, key true⟩
  · intro d hd
    obtain ⟨m1, hm1lt, hm1, e1⟩ := toV_surj k (d (genElt n false))
    obtain ⟨m2, hm2lt, hm2, e2⟩ := toV_surj k (d (genElt n true))
    have hrel := relHolds_of_der hn hd hm1 hm2 e1 e2
    have hrA := relA_of_der hn hd hm1 hm2 e1 e2
    have hm1mem : m1 ∈ cands n k := by
      unfold cands
      rw [List.mem_filter, List.mem_range]
      exact ⟨hm1lt, by simp [hm1, hrA]⟩
    unfold chkH1 at hchk
    have hrow := List.all_eq_true.1 hchk m1 hm1mem
    unfold chkRow at hrow
    have h := List.all_eq_true.1 hrow m2 (List.mem_range.2 hm2lt)
    have h' : princPair n k m1 m2 = true ∨
        princPair n k (m1 ^^^ d0m n false) (m2 ^^^ d0m n true) = true := by
      simpa [hm1, hm2, hrel] using h
    rcases h' with h' | h'
    · left
      obtain ⟨w, hw, h1, h2⟩ := exists_match_of_chk h'
      exact ⟨toV n k w, eq_pder_of_match hn hd hw hm1 hm2 e1 e2 h1 h2⟩
    · right
      obtain ⟨w, hw, h1, h2⟩ := exists_match_of_chk h'
      have hdd : IsDer (actL n k) (d * d0 n k) := hd.mul hd0
      have hc1 := inWk_d0m_gen hn hk false
      have hc2 := inWk_d0m_gen hn hk true
      refine ⟨toV n k w, eq_pder_of_match hn hdd hw (inWk_xor hm1 hc1) (inWk_xor hm2 hc2) ?_ ?_
        h1 h2⟩
      · rw [toV_xor hm1 hc1, e1, Pi.mul_apply, d0_gen hn k false]
      · rw [toV_xor hm2 hc2, e2, Pi.mul_apply, d0_gen hn k true]

end CFSG.Quasithin.B3
