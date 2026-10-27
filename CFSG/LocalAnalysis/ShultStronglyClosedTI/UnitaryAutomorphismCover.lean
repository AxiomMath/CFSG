module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryPerfectFamily
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_13

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.BenderSuzuki.MatrixGroups

variable {p f : ℕ} {K : Type} [Field K]

theorem isPerfect_hypSU (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) :
    Group.IsPerfect (hypSU h 1 1) := by
  have hfin : Module.finrank K (HypIndex 1 1 → K) = 3 := by
    rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]
  have hP := unitary_perfect h (hypForm_isSymm h (r := 1) (ε := 1)) (hypForm_separatingLeft h)
    (by rw [hfin]) (by rw [hfin]; intro h'; simp only [Prod.mk.injEq, true_and] at h'; omega)
  have hmap : (gramSU h (hypGram 1 1 K)).map
      (Matrix.GeneralLinearGroup.toLin : GL (HypIndex 1 1) K ≃* _).toMonoidHom =
      sesqSpecialUnitaryGroup (gramForm h (hypGram 1 1 K)) := by
    ext g
    rw [Subgroup.mem_map_equiv, ← toLin_mem_sesqSpecialUnitaryGroup_iff h (hypGram 1 1 K),
      MulEquiv.apply_symm_apply]
  let e : gramSU h (hypGram 1 1 K) ≃* sesqSpecialUnitaryGroup (gramForm h (hypGram 1 1 K)) :=
    (Matrix.GeneralLinearGroup.toLin.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

variable {J : HermitianForm 3 K}

theorem isPerfect_specialSubgroup [Finite K] {p f : ℕ} (hp : p.Prime) (hq : 2 < p ^ f)
    (hcard : Nat.card K = (p ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = p ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) : Group.IsPerfect J.specialSubgroup := by
  have h := unitaryFieldData_of_card (K := K) hp hq hcard
  have hconj : ∀ c, J.conj c = h.bar c := fun c => by
    rw [CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J (p ^ f) hcard hfixed,
      UnitaryFieldData.bar_apply]
  have := isPerfect_hypSU h hq
  exact Group.IsPerfect.ofSurjective (f := (hypSUEquiv h hconj hJ).toMonoidHom)
    (hypSUEquiv h hconj hJ).surjective

section CharTwo

variable [CharP K 2]

theorem psuMk_upper_lower_ne (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    psuMk J (sublineHom J hJ (upperSL _ (Multiplicative.ofAdd 1))) *
        psuMk J (sublineHom J hJ (lowerSL _ (Multiplicative.ofAdd 1))) ≠
      psuMk J (sublineHom J hJ (lowerSL _ (Multiplicative.ofAdd 1))) *
        psuMk J (sublineHom J hJ (upperSL _ (Multiplicative.ofAdd 1))) := by
  intro h
  rw [← map_mul (psuMk J), ← map_mul (psuMk J), psuMk_eq_psuMk_iff] at h
  obtain ⟨u, hu⟩ := h
  have h00 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hu
  simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at h00
  rw [coe_sublineHom_upperSL, coe_sublineHom_lowerSL] at h00
  simp [Matrix.mul_apply, Fin.sum_univ_three, scalar_apply, diagonal_apply] at h00
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [one_add_one_eq_two, h2, zero_mul] at h00
  exact zero_ne_one h00

theorem center_psu_eq_bot [Finite K] (q : ℕ) (hq : 2 < q) (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  have hs := CFSG.BenderSuzuki.External.huppert_II_10_13 J q hq hcard hfixed
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J)) with h | h
  · exact h
  · exfalso
    apply psuMk_upper_lower_ne hJ
    have hmem : psuMk J (sublineHom J hJ (upperSL _ (Multiplicative.ofAdd 1))) ∈
        Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) := h ▸ Subgroup.mem_top _
    exact (Subgroup.mem_center_iff.mp hmem _).symm

end CharTwo

variable {C : Subgroup J.specialSubgroup} [C.Normal]

theorem map_mem_center_of_surjective {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Surjective φ) {x : G} (hx : x ∈ Subgroup.center G) :
    φ x ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨z, rfl⟩ := hφ y
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx z)]

theorem center_eq_ker_coverToPSU (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J)
    (hP : Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥) :
    Subgroup.center (J.specialSubgroup ⧸ C) = (coverToPSU J C hJ hC).ker := by
  apply le_antisymm
  · intro x hx
    have := map_mem_center_of_surjective (coverToPSU_surjective hJ hC) hx
    rw [hP] at this
    exact this
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
    have hg : g ∈ scalarCenter J := by
      rw [scalarCenter_eq_ker J hJ]
      exact hx
    exact map_mem_center_of_surjective (QuotientGroup.mk'_surjective C)
      (scalarCenter_le_center J hg)

theorem map_ker_coverToPSU (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J)
    (hcen : Subgroup.center (J.specialSubgroup ⧸ C) = (coverToPSU J C hJ hC).ker)
    (β : MulAut (J.specialSubgroup ⧸ C)) :
    (coverToPSU J C hJ hC).ker.map (β : J.specialSubgroup ⧸ C →* J.specialSubgroup ⧸ C) =
      (coverToPSU J C hJ hC).ker := by
  rw [← hcen]
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance β

@[expose] def coverAutPSU (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J)
    (hcen : Subgroup.center (J.specialSubgroup ⧸ C) = (coverToPSU J C hJ hC).ker)
    (β : MulAut (J.specialSubgroup ⧸ C)) : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
  let Φ := QuotientGroup.quotientKerEquivOfSurjective _ (coverToPSU_surjective hJ hC)
  (Φ.symm.trans (QuotientGroup.congr _ _ β (map_ker_coverToPSU hJ hC hcen β))).trans Φ

theorem coverAutPSU_apply (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J)
    (hcen : Subgroup.center (J.specialSubgroup ⧸ C) = (coverToPSU J C hJ hC).ker)
    (β : MulAut (J.specialSubgroup ⧸ C)) (x : J.specialSubgroup ⧸ C) :
    coverAutPSU hJ hC hcen β (coverToPSU J C hJ hC x) = coverToPSU J C hJ hC (β x) := by
  set Φ := QuotientGroup.quotientKerEquivOfSurjective _ (coverToPSU_surjective hJ hC)
  have hΦ : ∀ y : J.specialSubgroup ⧸ C,
      Φ (QuotientGroup.mk y) = coverToPSU J C hJ hC y := fun _ => rfl
  change Φ (QuotientGroup.congr _ _ β (map_ker_coverToPSU hJ hC hcen β)
    (Φ.symm (coverToPSU J C hJ hC x))) = _
  rw [← hΦ x, MulEquiv.symm_apply_apply, QuotientGroup.congr_mk, hΦ]

theorem eq_of_coverToPSU_comp_eq [Group.IsPerfect (J.specialSubgroup ⧸ C)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    (hcen : Subgroup.center (J.specialSubgroup ⧸ C) = (coverToPSU J C hJ hC).ker)
    {β₁ β₂ : MulAut (J.specialSubgroup ⧸ C)}
    (h : ∀ x, coverToPSU J C hJ hC (β₁ x) = coverToPSU J C hJ hC (β₂ x)) : β₁ = β₂ := by
  set ν := coverToPSU J C hJ hC
  have hmem : ∀ x, β₁ x * (β₂ x)⁻¹ ∈ Subgroup.center (J.specialSubgroup ⧸ C) := fun x => by
    rw [hcen, MonoidHom.mem_ker, map_mul, map_inv, h x, mul_inv_cancel]
  let c : J.specialSubgroup ⧸ C →* Subgroup.center (J.specialSubgroup ⧸ C) :=
    { toFun := fun x => ⟨β₁ x * (β₂ x)⁻¹, hmem x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [map_mul, _root_.mul_inv_rev, Subgroup.coe_mul]
        have hy := Subgroup.mem_center_iff.mp (hmem y) (β₁ x)
        calc β₁ x * β₁ y * ((β₂ y)⁻¹ * (β₂ x)⁻¹)
            = β₁ x * (β₁ y * (β₂ y)⁻¹) * (β₂ x)⁻¹ := by group
          _ = β₁ y * (β₂ y)⁻¹ * β₁ x * (β₂ x)⁻¹ := by rw [hy]
          _ = β₁ x * (β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹) := by
            have hx := Subgroup.mem_center_iff.mp (hmem x) (β₁ y * (β₂ y)⁻¹)
            rw [mul_assoc (β₁ y * (β₂ y)⁻¹), ← hx] }
  have hker : c.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top]
    exact Abelianization.commutator_subset_ker c
  ext x
  have hx : c x = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_top x
  have hx' := congrArg Subtype.val hx
  change β₁ x * (β₂ x)⁻¹ = 1 at hx'
  exact mul_inv_eq_one.mp hx'

end CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
