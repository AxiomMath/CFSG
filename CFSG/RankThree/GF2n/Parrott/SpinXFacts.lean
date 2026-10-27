module

public import CFSG.RankThree.GF2n.Parrott.SpinXChecks
public import CFSG.RankThree.GF2n.Parrott.SpinTFacts
public import CFSG.RankThree.GF2n.Parrott.QA45SigmaCentralizers
public import CFSG.RankThree.GF2n.Parrott.Section2Products
public import CFSG.RankThree.GF2n.Parrott.QA45InvolutionClasses
public import CFSG.GroupTheory.ConjTransport
public import CFSG.GroupTheory.ConjClassCover
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.GF2n.Parrott.CentralizerOrders
public import CFSG.RankThree.GF2n.Parrott.CommutatorExtraspecial

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
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
local notation "P45" => Equiv.Perm (Fin 45)

section Facts

@[expose] def xabRho : A45 := ⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩

@[expose] def xabX : A45 := tA * (uA * vA)

theorem xabRho_eq : xabRho = evalSpinWord spinGenA (toW lRho) :=
  eq_evalSpinWord_of (by
    show permTab (sigma1 * sigma2⁻¹) = evalT t3 (toW lRho)
    decide +kernel)

theorem xabX_eq : xabX = evalSpinWord spinGenA (toW lXa) :=
  eq_evalSpinWord_of (by
    show permTab (t * (u * v)) = evalT t3 (toW lXa)
    decide +kernel)

theorem cols_xabRho : colsOf (spinMat xabRho) = bRho := by
  rw [xabRho_eq]
  exact colsOf_spinMat_word _

theorem cols_xabX : colsOf (spinMat xabX) = bX := by
  rw [xabX_eq]
  exact colsOf_spinMat_word _

theorem mem_wZero_iff (v : V) : bitmask v ∈ wZero ↔ SpinFixes xabRho v := by
  rw [spinFixes_iff, cols_xabRho]
  simp only [wZero, List.mem_filter, List.mem_range, beq_iff_eq]
  exact ⟨fun h => h.2, fun h => ⟨bitmask_lt v, h⟩⟩

theorem mem_fixX_iff (v : V) : bitmask v ∈ fixX ↔ SpinFixes xabX v := by
  rw [spinFixes_iff, cols_xabX]
  simp only [fixX, List.mem_filter, List.mem_range, beq_iff_eq]
  exact ⟨fun h => h.2, fun h => ⟨bitmask_lt v, h⟩⟩

theorem xabX_fixedCount : fixedCount ((rhoA xabX : GL8) : Mat8) = 16 := by
  rw [fixedCount_eq_count, ← spinMat_apply, cols_xabX]
  decide +kernel

theorem xabX_isotropic : ∀ w w' : V, SpinFixes xabX w → SpinFixes xabX w' → b w w' = 0 := by
  intro w w' hw hw'
  rw [b_eq_zero_iff]
  exact fixX_iso _ ((mem_fixX_iff w).2 hw) _ ((mem_fixX_iff w').2 hw')

theorem xab_fixes_t : ∀ w : V, SpinFixes xabRho w → SpinFixes xabX w → q w = 0 →
    SpinFixes tA w := by
  intro w hr hx hq
  rw [fixesT_iff]
  have h1 := fixT_of_fixX _ ((mem_wZero_iff w).2 hr) ((mem_fixX_iff w).2 hx)
    ((q_eq_zero_iff w).1 hq)
  simpa [fixesT, bT] using h1

theorem xab_pair : ∀ w₁ wk w : V, SpinFixes xabRho w₁ → SpinFixes xabRho wk →
    SpinFixes xabRho w → SpinFixes xabX w → q w = 0 →
    wk + ((rhoA xabX : GL8) : Mat8) *ᵥ wk = w₁ + ((rhoA tA : GL8) : Mat8) *ᵥ w₁ → b wk w = 0 := by
  intro w₁ wk w h₁ hk hw hxw hq heq
  rw [b_eq_zero_iff]
  have h2 := congrArg bitmask heq
  rw [bitmask_add, bitmask_add, ← spinMat_apply xabX, ← bapply_colsOf, cols_xabX,
    ← spinMat_apply tA, ← bapply_colsOf, cols_tA] at h2
  exact pair_check _ ((mem_wZero_iff w₁).2 h₁) _ ((mem_wZero_iff wk).2 hk) _
    ((mem_wZero_iff w).2 hw) ((mem_fixX_iff w).2 hxw) ((q_eq_zero_iff w).1 hq) h2

theorem xabX_mul_self : xabX * xabX = 1 := by
  apply Subtype.ext
  show (t * (u * v)) * (t * (u * v)) = 1
  decide +kernel

theorem tA_mul_xabX : tA * xabX = uA * vA := by
  apply Subtype.ext
  show t * (t * (u * v)) = u * v
  decide +kernel

theorem uAvA_mul_xabX : (uA * vA) * xabX = tA := by
  apply Subtype.ext
  show (u * v) * (t * (u * v)) = t
  decide +kernel

theorem xabX_comm_t : xabX * tA = tA * xabX := by
  apply Subtype.ext
  show (t * (u * v)) * t = t * (t * (u * v))
  decide +kernel

theorem xabX_inv_spinR0 : xabX * spinR0 = spinR0⁻¹ * xabX := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_spinR0]
  show (t * (u * v)) * (sigma1 * sigma2) = (sigma1 * sigma2)⁻¹ * (t * (u * v))
  decide +kernel

theorem spinR0_comm_rho : spinR0 * xabRho = xabRho * spinR0 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_spinR0]
  show (sigma1 * sigma2) * (sigma1 * sigma2⁻¹) = (sigma1 * sigma2⁻¹) * (sigma1 * sigma2)
  decide +kernel

theorem xabX_conj_spinR0_inv : xabX * spinR0⁻¹ * xabX⁻¹ = spinR0 := by
  rw [inv_eq_of_mul_eq_one_right xabX_mul_self]
  calc xabX * spinR0⁻¹ * xabX = xabX * (spinR0⁻¹ * xabX) := by group
    _ = xabX * (xabX * spinR0) := by rw [xabX_inv_spinR0]
    _ = (xabX * xabX) * spinR0 := by group
    _ = spinR0 := by rw [xabX_mul_self, one_mul]

theorem xabX_conj_tA : xabX * tA * xabX⁻¹ = tA := by
  rw [xabX_comm_t]
  group

theorem mem_closure_pair_four {M : Type*} [Group M] {a b : M} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {g : M} (hg : g ∈ Subgroup.closure ({a, b} : Set M)) :
    g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
    · exact Or.inl (one_mul _)
    · exact Or.inr (Or.inl (one_mul _))
    · exact Or.inr (Or.inr (Or.inl (one_mul _)))
    · exact Or.inr (Or.inr (Or.inr (one_mul _)))
    · exact Or.inr (Or.inl (mul_one _))
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, ha, one_mul])))
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inr (Or.inr (Or.inr hab.symm))
    · exact Or.inl hb
    · exact Or.inr (Or.inl (by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]))
    · exact Or.inr (Or.inr (Or.inr (mul_one _)))
    · exact Or.inr (Or.inr (Or.inl (by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul])))
    · exact Or.inr (Or.inl (by rw [mul_assoc, hb, mul_one]))
    · exact Or.inl (by rw [mul_assoc, ← mul_assoc b a b, ← hab, mul_assoc, hb, mul_one, ha])
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl (inv_one)
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
    · refine Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right ?_)))
      rw [mul_assoc, ← mul_assoc b a b, ← hab, mul_assoc, hb, mul_one, ha]

section Normalize

theorem card_centralizer_xabRho : Nat.card (Subgroup.centralizer ({xabRho} : Set A45)) = 108 := by
  have hm : sigma1 * sigma2⁻¹ ∈ QA45.originalSubgroup := sigma1_mul_sigma2_inv_mem_A
  exact (card_centralizer_QA45_eq_filter (sigma1 * sigma2⁻¹) hm).trans
    Certificates.certificate946005.centralizer_sigma1sigma2inv

theorem xab_normalize (S : Subgroup A45) (hS : S ≤ Subgroup.centralizer ({xabRho} : Set A45))
    (hSp : IsPGroup 2 S) {y : A45} (hy : y ∈ S) (hyv : IsConj y vA) :
    ∃ c ∈ Subgroup.centralizer ({xabRho} : Set A45), c * y * c⁻¹ = xabX ∧
      ∀ g ∈ S, c * g * c⁻¹ = 1 ∨ c * g * c⁻¹ = tA ∨ c * g * c⁻¹ = uA * vA ∨
        c * g * c⁻¹ = xabX := by
  obtain ⟨-, ⟨hE4le, -, hE4card⟩, -⟩ := qa45_sigma_centralizer_sylow
  obtain ⟨hC1, -, hC3, hC4⟩ := qa45_involution_centralizers
  set E4 : Subgroup A45 := Subgroup.closure ({tA, uA * vA} : Set A45) with hE4
  set B0 : Subgroup A45 := Subgroup.centralizer ({xabRho} : Set A45) with hB0
  have hE4B : E4 ≤ B0 := hE4le
  have hB0card : Nat.card B0 = 108 := card_centralizer_xabRho
  have hE4p : IsPGroup 2 E4 := IsPGroup.of_card (n := 2) (by rw [hE4card]; norm_num)
  have hE'p : IsPGroup 2 (E4.subgroupOf B0) := hE4p.comap_subtype
  have hE'card : Nat.card (E4.subgroupOf B0) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE4B).toEquiv, hE4card]
  have hE'idx : ¬ 2 ∣ (E4.subgroupOf B0).index := by
    have h1 := Subgroup.card_mul_index (E4.subgroupOf B0)
    have h2 : Nat.card ↥B0 = 108 := hB0card
    rw [hE'card, h2] at h1
    omega
  let P0 : Sylow 2 ↥B0 := hE'p.toSylow hE'idx
  have hSp' : IsPGroup 2 (S.subgroupOf B0) := hSp.comap_subtype
  obtain ⟨g, hg⟩ := CFSG.GroupTheory.exists_map_conj_le_sylow P0 hSp'
  have hP0 : (P0 : Subgroup ↥B0) = E4.subgroupOf B0 := IsPGroup.toSylow_coe hE'p hE'idx
  have hgE4 : ∀ g' ∈ S, (g : A45) * g' * (g : A45)⁻¹ ∈ E4 := by
    intro g' hg'
    have h1 : (⟨g', hS hg'⟩ : ↥B0) ∈ S.subgroupOf B0 := hg'
    have h2 := hg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom h1)
    rw [hP0] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hE4cases : ∀ e ∈ E4, e = 1 ∨ e = tA ∨ e = uA * vA ∨ e = xabX := by
    have hcomm : tA * (uA * vA) = (uA * vA) * tA := by
      apply Subtype.ext
      show t * (u * v) = (u * v) * t
      decide +kernel
    have hb : (uA * vA) * (uA * vA) = 1 := by
      apply Subtype.ext
      show (u * v) * (u * v) = 1
      decide +kernel
    intro e he
    exact mem_closure_pair_four tA_mul_self hb hcomm he
  have hcy := hE4cases _ (hgE4 y hy)
  have hconj : IsConj ((g : A45) * y * (g : A45)⁻¹) vA :=
    (isConj_iff.mpr ⟨(g : A45), rfl⟩ : IsConj y ((g : A45) * y * (g : A45)⁻¹)).symm.trans hyv
  refine ⟨(g : A45), g.2, ?_, fun g' hg' => hE4cases _ (hgE4 g' hg')⟩
  rcases hcy with h1 | h1 | h1 | h1
  · exfalso
    rw [h1] at hconj
    have h2 : vA = 1 := isConj_one_right.mp hconj
    exact v_ne_one (by simpa using congrArg Subtype.val h2)
  · exfalso
    rw [h1] at hconj
    have h2 := CFSG.GroupTheory.card_centralizer_eq_of_isConj hconj
    rw [hC1, hC3] at h2
    omega
  · exfalso
    rw [h1] at hconj
    have h2 := CFSG.GroupTheory.card_centralizer_eq_of_isConj hconj
    rw [hC4, hC3] at h2
    omega
  · exact h1

end Normalize

end Facts

end CFSG.RankThree.GF2n.Parrott
