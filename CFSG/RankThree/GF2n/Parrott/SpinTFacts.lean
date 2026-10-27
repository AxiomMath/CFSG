module

public import CFSG.RankThree.GF2n.Parrott.SpinE27Fixed
public import CFSG.RankThree.GF2n.Parrott.SylowHFacts
public import CFSG.RankThree.GF2n.Parrott.QA45InvolutionClasses
public import CFSG.RankThree.GF2n.Parrott.SpinForms
public import CFSG.RankThree.GF2n.Parrott.SpinTChecks

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid
open CFSG.LinearAlgebra.F2Cube (fixedCount)
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a1A" => (⟨alpha1, alpha1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b1A" => (⟨beta1, beta1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b2A" => (⟨beta2, beta2_mem_A⟩ : A45)
local notation "P45" => Equiv.Perm (Fin 45)

@[expose] noncomputable def spinR0 : A45 := spinE27a * spinE27b

theorem coe_spinR0 : ((spinR0 : A45) : P45) = sigma1 * sigma2 := by
  unfold spinR0
  rw [Subgroup.coe_mul, spinE27a_coe, spinE27b_coe]

theorem permTab_spinR0 : permTab ((spinR0 : A45) : P45) = tcomp tM1 tM2 := by
  have ha : permTab ((spinE27a : A45) : P45) = tM1 := permTab_spinG5 2
  have hb : permTab ((spinE27b : A45) : P45) = tM2 := permTab_spinG5 3
  unfold spinR0
  rw [permTab_coe_mul, ha, hb]

theorem comm_of_tab {w : List (Fin 3 × ℕ)} {a : A45} {ta : List ℕ}
    (ha : permTab (a : P45) = ta) (h : tcomp (evalT t3 w) ta = tcomp ta (evalT t3 w)) :
    evalSpinWord spinGenA w * a = a * evalSpinWord spinGenA w := by
  apply eq_of_permTab_eq
  rw [permTab_coe_mul, permTab_coe_mul, permTab_coe_evalSpinWord,
    show (fun i => permTab ((spinGenA i : A45) : P45)) = t3 from funext permTab_spinGenA, ha]
  exact h

theorem eq_evalSpinWord_of {a : A45} {w : List (Fin 3 × ℕ)}
    (h : permTab (a : P45) = evalT t3 w) : a = evalSpinWord spinGenA w := by
  apply eq_of_permTab_eq
  rw [permTab_coe_evalSpinWord,
    show (fun i => permTab ((spinGenA i : A45) : P45)) = t3 from funext permTab_spinGenA]
  exact h

theorem n_u : (sigma1 * sigma2) * u = u * (sigma1 * sigma2) := by decide +kernel

theorem n_al : (sigma1 * sigma2) * (alpha1 * alpha2) = (beta1 * beta2) * (sigma1 * sigma2) := by
  decide +kernel

theorem n_be : (sigma1 * sigma2) * (beta1 * beta2) =
    ((alpha1 * alpha2) * (beta1 * beta2)) * (sigma1 * sigma2) := by
  decide +kernel

theorem n_t : (sigma1 * sigma2) * t = t * (sigma1 * sigma2) := by decide +kernel

section Perm5


theorem permTab_tA : permTab ((tA : A45) : P45) = tx := permTab_x45

theorem tA_eq : tA = evalSpinWord spinGenA (toW lT) :=
  eq_evalSpinWord_of (by
    show permTab x45 = evalT t3 (toW lT)
    decide +kernel)

theorem tA_ne_one : tA ≠ 1 := by
  intro h
  apply t_ne_one
  have h' := congrArg Subtype.val h
  rwa [Subgroup.coe_one] at h'

theorem tA_mul_self : tA * tA = 1 := Subtype.ext t_sq

theorem r0_comm_t : spinR0 * tA = tA * spinR0 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_spinR0]
  exact n_t

end Perm5

section Perm25


theorem uA_eq : uA = evalSpinWord spinGenA (toW lU) :=
  eq_evalSpinWord_of (by
    show permTab u = evalT t3 (toW lU)
    decide +kernel)

theorem alA_eq : a1A * a2A = evalSpinWord spinGenA (toW lAl) :=
  eq_evalSpinWord_of (by
    rw [permTab_coe_mul]
    show tcomp (permTab alpha1) (permTab alpha2) = evalT t3 (toW lAl)
    decide +kernel)

theorem beA_eq : b1A * b2A = evalSpinWord spinGenA (toW lBe) :=
  eq_evalSpinWord_of (by
    rw [permTab_coe_mul]
    show tcomp (permTab beta1) (permTab beta2) = evalT t3 (toW lBe)
    decide +kernel)

theorem tA_mem_S : tA ∈ sQA45 := Subgroup.subset_closure (by simp)

theorem uA_mem_S : uA ∈ sQA45 := Subgroup.subset_closure (by simp)

theorem alA_mem_S : a1A * a2A ∈ sQA45 := Subgroup.subset_closure (by simp)

theorem beA_mem_S : b1A * b2A ∈ sQA45 := Subgroup.subset_closure (by simp)

theorem r0_comm_u : spinR0 * uA = uA * spinR0 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_spinR0]
  exact n_u

theorem r0_comm_al : spinR0 * (a1A * a2A) = (b1A * b2A) * spinR0 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, coe_spinR0]
  exact n_al

theorem r0_comm_be : spinR0 * (b1A * b2A) = ((a1A * a2A) * (b1A * b2A)) * spinR0 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [coe_spinR0]
  exact n_be

theorem conj_mem_of_gens :
    ∀ x ∈ ({uA, a1A * a2A, b1A * b2A, tA} : Set A45), spinR0 * x * spinR0⁻¹ ∈ sQA45 := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h | h
  · rw [h, mul_inv_eq_iff_eq_mul.2 r0_comm_u]
    exact uA_mem_S
  · rw [h, mul_inv_eq_iff_eq_mul.2 r0_comm_al]
    exact beA_mem_S
  · rw [h, mul_inv_eq_iff_eq_mul.2 r0_comm_be]
    exact Subgroup.mul_mem _ alA_mem_S beA_mem_S
  · rw [h, mul_inv_eq_iff_eq_mul.2 r0_comm_t]
    exact tA_mem_S

theorem spinNormFact : ∀ s ∈ sQA45, spinR0 * s * spinR0⁻¹ ∈ sQA45 := by
  intro s hs
  have hs' : s ∈ Subgroup.closure ({uA, a1A * a2A, b1A * b2A, tA} : Set A45) := hs
  clear hs
  induction hs' using Subgroup.closure_induction with
  | mem x hx => exact conj_mem_of_gens x hx
  | one =>
    have h1 : spinR0 * (1 : A45) * spinR0⁻¹ = 1 := by group
    rw [h1]
    exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have h1 : spinR0 * (x * y) * spinR0⁻¹ = (spinR0 * x * spinR0⁻¹) * (spinR0 * y * spinR0⁻¹) := by
      group
    rw [h1]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have h1 : spinR0 * x⁻¹ * spinR0⁻¹ = (spinR0 * x * spinR0⁻¹)⁻¹ := by group
    rw [h1]
    exact Subgroup.inv_mem _ hx

end Perm25

theorem q_val_eq_qTab : ∀ v : V, (q v).val = qTab.getD (bitmask v) 0 := by
  decide +kernel

theorem q_eq_zero_iff (v : V) : q v = 0 ↔ qTab.getD (bitmask v) 0 = 0 := by
  rw [← ZMod.val_eq_zero, q_val_eq_qTab]

theorem b_eq_zero_iff (v w : V) : b v w = 0 ↔ bq (bitmask v) (bitmask w) = 0 := by
  rw [← ZMod.val_eq_zero]
  have h : (b v w).val = bq (bitmask v) (bitmask w) := by
    unfold b bq
    rw [ZMod.val_add, ZMod.val_add, q_val_eq_qTab, q_val_eq_qTab, q_val_eq_qTab, bitmask_add]
    omega
  rw [h]

section Spin


@[expose] def SpinFixes (g : A45) (v : V) : Prop := (rhoA g : Mat8) *ᵥ v = v

theorem rhoA_mulVec_mul (a a' : A45) (v : V) :
    ((rhoA (a * a') : GL8) : Mat8) *ᵥ v =
      ((rhoA a : GL8) : Mat8) *ᵥ (((rhoA a' : GL8) : Mat8) *ᵥ v) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem rhoA_mulVec_one (v : V) : ((rhoA (1 : A45) : GL8) : Mat8) *ᵥ v = v := by
  rw [map_one, Units.val_one, Matrix.one_mulVec]

theorem rhoA_mulVec_inv (a : A45) (v : V) :
    ((rhoA a⁻¹ : GL8) : Mat8) *ᵥ (((rhoA a : GL8) : Mat8) *ᵥ v) = v := by
  rw [← rhoA_mulVec_mul, inv_mul_cancel, rhoA_mulVec_one]

theorem rhoA_mulVec_mul_inv (a : A45) (v : V) :
    ((rhoA a : GL8) : Mat8) *ᵥ (((rhoA a⁻¹ : GL8) : Mat8) *ᵥ v) = v := by
  rw [← rhoA_mulVec_mul, mul_inv_cancel, rhoA_mulVec_one]

theorem spinB_invariant (a : A45) (v w : V) :
    b (((rhoA a : GL8) : Mat8) *ᵥ v) (((rhoA a : GL8) : Mat8) *ᵥ w) = b v w := by
  unfold b
  rw [← Matrix.mulVec_add, spinQuad_invariant, spinQuad_invariant, spinQuad_invariant]

theorem spinFixes_mulVec_of_conj {a g : A45} {u : V} (hu : SpinFixes (g⁻¹ * a * g) u) :
    SpinFixes a (((rhoA g : GL8) : Mat8) *ᵥ u) := by
  unfold SpinFixes at hu ⊢
  have h1 : a * g = g * (g⁻¹ * a * g) := by group
  rw [← rhoA_mulVec_mul, h1, rhoA_mulVec_mul, hu]

theorem spinFixes_mulVec_inv_of_conj {a g : A45} {u : V} (hu : SpinFixes (g * a * g⁻¹) u) :
    SpinFixes a (((rhoA g⁻¹ : GL8) : Mat8) *ᵥ u) :=
  spinFixes_mulVec_of_conj (g := g⁻¹) (by rw [inv_inv]; exact hu)

theorem spinFixes_mul {a b : A45} {v : V} (ha : SpinFixes a v) (hb : SpinFixes b v) :
    SpinFixes (a * b) v := by
  have ha' : ((rhoA a : GL8) : Mat8) *ᵥ v = v := ha
  have hb' : ((rhoA b : GL8) : Mat8) *ᵥ v = v := hb
  show ((rhoA (a * b) : GL8) : Mat8) *ᵥ v = v
  rw [rhoA_mulVec_mul, hb', ha']

theorem spinFixes_one (v : V) : SpinFixes (1 : A45) v := rhoA_mulVec_one v

@[expose] def spinStab (v : V) : Subgroup A45 where
  carrier := {s | SpinFixes s v}
  mul_mem' := fun ha hb => spinFixes_mul ha hb
  one_mem' := spinFixes_one v
  inv_mem' := by
    intro a ha
    have ha' : ((rhoA a : GL8) : Mat8) *ᵥ v = v := ha
    show ((rhoA a⁻¹ : GL8) : Mat8) *ᵥ v = v
    calc ((rhoA a⁻¹ : GL8) : Mat8) *ᵥ v
        = ((rhoA a⁻¹ : GL8) : Mat8) *ᵥ (((rhoA a : GL8) : Mat8) *ᵥ v) := by rw [ha']
      _ = v := rhoA_mulVec_inv a v

theorem mem_spinStab_iff {s : A45} {v : V} : s ∈ spinStab v ↔ SpinFixes s v := Iff.rfl

theorem spinFixes_iff (s : A45) (v : V) :
    SpinFixes s v ↔ bapply (colsOf (spinMat s)) (bitmask v) = bitmask v := by
  rw [bapply_colsOf, spinMat_apply]
  constructor
  · intro h
    unfold SpinFixes at h
    rw [h]
  · intro h
    exact bitmask_injective h

theorem bitmask_rhoA_mulVec_word (w : List (Fin 3 × ℕ)) (v : V) :
    bitmask (((rhoA (evalSpinWord spinGenA w) : GL8) : Mat8) *ᵥ v) =
      bapply (evalB b3 w) (bitmask v) := by
  rw [← spinMat_apply, ← bapply_colsOf, colsOf_spinMat_word]

end Spin

section Facts


theorem cols_uA : colsOf (spinMat uA) = evalB b3 (toW lU) := by
  rw [uA_eq]
  exact colsOf_spinMat_word _

theorem cols_alA : colsOf (spinMat (a1A * a2A)) = evalB b3 (toW lAl) := by
  rw [alA_eq]
  exact colsOf_spinMat_word _

theorem cols_beA : colsOf (spinMat (b1A * b2A)) = evalB b3 (toW lBe) := by
  rw [beA_eq]
  exact colsOf_spinMat_word _

theorem cols_tA : colsOf (spinMat tA) = evalB b3 (toW lT) := by
  rw [tA_eq]
  exact colsOf_spinMat_word _

theorem spinFixes_of_gens {v : V} (hu : SpinFixes uA v) (ha : SpinFixes (a1A * a2A) v)
    (hb : SpinFixes (b1A * b2A) v) (ht : SpinFixes tA v) : ∀ s ∈ sQA45, SpinFixes s v := by
  have hle : sQA45 ≤ spinStab v := by
    unfold sQA45
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mem_spinStab_iff.2 hu
    · exact mem_spinStab_iff.2 ha
    · exact mem_spinStab_iff.2 hb
    · exact mem_spinStab_iff.2 ht
  exact fun s hs => mem_spinStab_iff.1 (hle hs)

theorem fixesS_iff (v : V) : (∀ s ∈ sQA45, SpinFixes s v) ↔ fixesS (bitmask v) = true := by
  have hS : fixesS (bitmask v) = true ↔
      bapply (evalB b3 (toW lU)) (bitmask v) = bitmask v ∧
      bapply (evalB b3 (toW lAl)) (bitmask v) = bitmask v ∧
      bapply (evalB b3 (toW lBe)) (bitmask v) = bitmask v ∧
      bapply (evalB b3 (toW lT)) (bitmask v) = bitmask v := by
    simp [fixesS, sCols]
  rw [hS]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← cols_uA]; exact (spinFixes_iff _ _).1 (h _ uA_mem_S)
    · rw [← cols_alA]; exact (spinFixes_iff _ _).1 (h _ alA_mem_S)
    · rw [← cols_beA]; exact (spinFixes_iff _ _).1 (h _ beA_mem_S)
    · rw [← cols_tA]; exact (spinFixes_iff _ _).1 (h _ tA_mem_S)
  · rintro ⟨h1, h2, h3, h4⟩
    refine spinFixes_of_gens ?_ ?_ ?_ ?_
    · rw [spinFixes_iff, cols_uA]; exact h1
    · rw [spinFixes_iff, cols_alA]; exact h2
    · rw [spinFixes_iff, cols_beA]; exact h3
    · rw [spinFixes_iff, cols_tA]; exact h4

theorem fixesT_iff (v : V) : SpinFixes tA v ↔ fixesT (bitmask v) = true := by
  rw [spinFixes_iff, cols_tA]
  simp [fixesT]

theorem spinOddFact : spinR0 ^ 3 = 1 ∧ spinR0 ≠ 1 ∧ spinR0 * tA = tA * spinR0 ∧
    fixedCount ((rhoA spinR0 : GL8) : Mat8) = 1 := by
  refine ⟨?_, ?_, r0_comm_t, fixedCount_rhoA_spinE27ab⟩
  · have ha : spinE27a ∈ spinE27 := Subgroup.subset_closure (by simp)
    have hb : spinE27b ∈ spinE27 := Subgroup.subset_closure (by simp)
    exact isElemAbelian_spinE27.2 spinR0 (Subgroup.mul_mem _ ha hb)
  · unfold spinR0
    rw [← spinE27Elt_one_one_zero]
    exact spinE27Elt_ne_one (by decide)

theorem spinIsotropicFact : ∀ v v' : V, (∀ s ∈ sQA45, SpinFixes s v) →
    (∀ s ∈ sQA45, SpinFixes s v') → b v v' = 0 := by
  intro v v' hv hv'
  rw [b_eq_zero_iff]
  exact iso_check _ (bitmask_lt v) _ (bitmask_lt v') ((fixesS_iff v).1 hv) ((fixesS_iff v').1 hv')

theorem spinRestFact : ∀ w : V, SpinFixes tA w → q w = 0 →
    ∃ g : A45, g * tA = tA * g ∧ g * spinR0 = spinR0 * g ∧
      ∀ s ∈ sQA45, SpinFixes s ((rhoA g : Mat8) *ᵥ w) := by
  intro w hwT hwq
  have h := rest_check (bitmask w) (bitmask_lt w) ((fixesT_iff w).1 hwT)
    ((q_eq_zero_iff w).1 hwq)
  rcases h with h | h | h
  · refine ⟨1, by simp, by simp, ?_⟩
    intro s hs
    rw [rhoA_mulVec_one]
    exact (fixesS_iff w).2 h s hs
  · refine ⟨evalSpinWord spinGenA (toW lGA), comm_of_tab permTab_tA gA_comm.1,
      comm_of_tab permTab_spinR0 gA_comm.2, ?_⟩
    rw [fixesS_iff, bitmask_rhoA_mulVec_word]
    exact h
  · refine ⟨evalSpinWord spinGenA (toW lGB), comm_of_tab permTab_tA gB_comm.1,
      comm_of_tab permTab_spinR0 gB_comm.2, ?_⟩
    rw [fixesS_iff, bitmask_rhoA_mulVec_word]
    exact h

theorem spinZsFact : ∀ w : V, SpinFixes tA w →
    ∀ g : A45, g * tA = tA * g →
      (∀ v : V, SpinFixes tA v → b v w = 0 → SpinFixes g v) → g = 1 ∨ g = tA := by
  intro w hwT g hgt hfix
  by_contra hcon
  have hg1 : g ≠ 1 := fun h1 => hcon (Or.inl h1)
  have hgt' : g ≠ tA := fun h1 => hcon (Or.inr h1)
  have hC : Nat.card (Subgroup.centralizer ({tA} : Set A45)) = 1152 :=
    (qa45_involution_centralizers).1
  set C : Subgroup A45 := Subgroup.centralizer ({tA} : Set A45) with hCdef
  have hmemC : ∀ x : A45, x * tA = tA * x → x ∈ C := by
    intro x hx
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hx.symm
  obtain ⟨p, hp, hpw⟩ := zPairs_cover (bitmask w) (bitmask_lt w) ((fixesT_iff w).1 hwT)
  obtain ⟨-, hp1, hp2, -, hfT1, hfT2, hb1, hb2⟩ := zPairs_ok p hp
  have hnd := nodup_of_distinctPairs (zKeys_distinct p hp)
  obtain ⟨v₁, hv₁⟩ : ∃ v : V, bitmask v = p.2.1 := ⟨vecOfNat p.2.1, bitmask_vecOfNat _ hp1⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v : V, bitmask v = p.2.2 := ⟨vecOfNat p.2.2, bitmask_vecOfNat _ hp2⟩
  have hT₁ : SpinFixes tA v₁ := (fixesT_iff v₁).2 (by rw [hv₁]; exact hfT1)
  have hT₂ : SpinFixes tA v₂ := (fixesT_iff v₂).2 (by rw [hv₂]; exact hfT2)
  have hg₁ : SpinFixes g v₁ :=
    hfix v₁ hT₁ ((b_eq_zero_iff v₁ w).2 (by rw [hv₁, ← hpw]; exact hb1))
  have hg₂ : SpinFixes g v₂ :=
    hfix v₂ hT₂ ((b_eq_zero_iff v₂ w).2 (by rw [hv₂, ← hpw]; exact hb2))
  have h01 : (1 : A45) ≠ tA := tA_ne_one.symm
  have h02 : (1 : A45) ≠ g := hg1.symm
  have h03 : (1 : A45) ≠ tA * g := by
    intro h
    exact hgt' (mul_left_cancel (a := tA) (h.symm.trans tA_mul_self.symm))
  have h12 : tA ≠ g := hgt'.symm
  have h13 : tA ≠ tA * g := fun h => hg1 (left_eq_mul.1 h)
  have h23 : g ≠ tA * g := fun h => tA_ne_one (mul_eq_right.1 h.symm)
  let Kset : Finset A45 := {1, tA, g, tA * g}
  have hKcard : Kset.card = 4 := by
    have e1 : (1 : A45) ∉ ({tA, g, tA * g} : Finset A45) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01, h02, h03⟩
    have e2 : tA ∉ ({g, tA * g} : Finset A45) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h12, h13⟩
    have e3 : g ∉ ({tA * g} : Finset A45) := by
      simp only [Finset.mem_singleton]
      exact h23
    simp only [Kset]
    rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
      Finset.card_insert_of_notMem e3, Finset.card_singleton]
  have htC : tA ∈ C := hmemC tA rfl
  have hgC : g ∈ C := hmemC g hgt
  have hKC : ∀ k ∈ Kset, k ∈ C := by
    intro k hk
    simp only [Kset, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact C.one_mem
    · exact htC
    · exact hgC
    · exact C.mul_mem htC hgC
  have hKfix : ∀ k ∈ Kset, SpinFixes k v₁ ∧ SpinFixes k v₂ := by
    intro k hk
    simp only [Kset, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨spinFixes_one _, spinFixes_one _⟩
    · exact ⟨hT₁, hT₂⟩
    · exact ⟨hg₁, hg₂⟩
    · exact ⟨spinFixes_mul hT₁ hg₁, spinFixes_mul hT₂ hg₂⟩
  let hW : List ℕ → A45 := fun l => evalSpinWord spinGenA (toW l)
  have hWC : ∀ l ∈ zWords, hW l ∈ C := fun l hl =>
    hmemC _ (comm_of_tab permTab_tA (zWords_comm l hl))
  have himg : ∀ (l : List ℕ) (k : A45) (v : V), SpinFixes k v →
      bapply (evalB b3 (toW l)) (bitmask v) =
        bitmask (((rhoA (hW l * k) : GL8) : Mat8) *ᵥ v) := by
    intro l k v hk
    have hk' : ((rhoA k : GL8) : Mat8) *ᵥ v = v := hk
    rw [rhoA_mulVec_mul, hk']
    exact (bitmask_rhoA_mulVec_word (toW l) v).symm
  have hnd' : (zWords.map fun l =>
      (bapply (evalB b3 (toW l)) p.2.1, bapply (evalB b3 (toW l)) p.2.2)).Nodup := by
    have h1 : zMats.map (fun A => (bapply A p.2.1, bapply A p.2.2)) =
        zWords.map fun l => (bapply (evalB b3 (toW l)) p.2.1, bapply (evalB b3 (toW l)) p.2.2) := by
      simp only [zMats, List.map_map, Function.comp_def]
    rw [← h1]
    exact hnd
  have hzNodup : zWords.Nodup := List.Nodup.of_map _ hnd'
  let S : Finset (List ℕ × A45) := zWords.toFinset ×ˢ Kset
  let f : List ℕ × A45 → A45 := fun q => hW q.1 * q.2
  have hf_inj : Set.InjOn f (S : Set (List ℕ × A45)) := by
    rintro ⟨l, k⟩ hq ⟨l', k'⟩ hq' hfq
    simp only [S, Finset.coe_product, Set.mem_prod, Finset.mem_coe, List.mem_toFinset] at hq hq'
    have hfq' : hW l * k = hW l' * k' := hfq
    have hll : l = l' := by
      refine List.inj_on_of_nodup_map hnd' hq.1 hq'.1 ?_
      have e1 := himg l k v₁ (hKfix k hq.2).1
      have e2 := himg l' k' v₁ (hKfix k' hq'.2).1
      have e3 := himg l k v₂ (hKfix k hq.2).2
      have e4 := himg l' k' v₂ (hKfix k' hq'.2).2
      rw [hfq'] at e1 e3
      rw [hv₁] at e1 e2
      rw [hv₂] at e3 e4
      exact Prod.ext (e1.trans e2.symm) (e3.trans e4.symm)
    subst hll
    rw [mul_left_cancel hfq']
  have hsub : ∀ q ∈ (S : Set (List ℕ × A45)), f q ∈ (C : Set A45) := by
    rintro ⟨l, k⟩ hq
    simp only [S, Finset.coe_product, Set.mem_prod, Finset.mem_coe, List.mem_toFinset] at hq
    exact C.mul_mem (hWC l hq.1) (hKC k hq.2)
  have hScard : S.card = 289 * 4 := by
    have hcn : zWords.toFinset.card = 289 := by
      rw [List.toFinset_card_of_nodup hzNodup, zWords_length]
    simp only [S, Finset.card_product, hcn, hKcard]
  have hle := Set.ncard_le_ncard_of_injOn f hsub hf_inj (Set.toFinite _)
  rw [Set.ncard_coe_finset, hScard] at hle
  have hnc : (C : Set A45).ncard = Nat.card C := (Nat.card_coe_set_eq _).symm
  omega

end Facts

end CFSG.RankThree.GF2n.Parrott
