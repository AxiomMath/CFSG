module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Residual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Torus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par KTabC KTabD

variable {K : Type} [Field K]

private theorem sigma_mulVec_e1_S07 (hK : UnitaryFieldData 2 2 K)
    (x : Fin 2 → rootsOfUnity 3 K) :
    (((hypSU hK 2 0).subtype (splitTorusHom hK 2 0 (rootsOfUnity 3 K)
        (splitInv_rootsOfUnity_three hK) x) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ Pi.single ie1 (1 : K) =
      ((x 0 : Kˣ) : K) • Pi.single ie1 (1 : K) := by
  change ((((splitTorusHom hK 2 0 (rootsOfUnity 3 K) (splitInv_rootsOfUnity_three hK) x :
      hypSU hK 2 0) : GL (HypIndex 2 0) K)) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ Pi.single ie1 (1 : K) =
    ((x 0 : Kˣ) : K) • Pi.single ie1 (1 : K)
  rw [coe_splitTorusHom, Matrix.diagonal_mulVec_single]
  ext j
  by_cases hj : j = ie1
  · rw [hj]
    simp [torusEntries, ie1]
  · simp [hj]

private theorem sigma_mem_vecStab_iff_S07 (hK : UnitaryFieldData 2 2 K)
    (x : Fin 2 → rootsOfUnity 3 K) :
    splitTorusHom hK 2 0 (rootsOfUnity 3 K) (splitInv_rootsOfUnity_three hK) x ∈
        vecStab (hypSU hK 2 0).subtype (Pi.single ie1 (1 : K)) ↔ x 0 = 1 := by
  rw [mem_vecStab, sigma_mulVec_e1_S07 hK x]
  constructor
  · intro h
    have h1 : ((x 0 : Kˣ) : K) = ((1 : Kˣ) : K) := by
      have := congrFun h ie1
      simpa using this
    refine Subtype.ext ?_
    exact Units.ext h1
  · intro h
    rw [h]
    simp

private theorem sigma_mem_levHom_S07 (hK : UnitaryFieldData 2 2 K)
    (x : Fin 2 → rootsOfUnity 3 K) (hx : x 0 = 1) :
    splitTorusHom hK 2 0 (rootsOfUnity 3 K) (splitInv_rootsOfUnity_three hK) x ∈
      (levHom hK).range := by
  have hb : hK.bar ((x 1 : Kˣ) : K) = ((x 1 : Kˣ) : K) :=
    splitInv_rootsOfUnity_three hK (x 1)
  let A : Matrix.SpecialLinearGroup (Fin 2) hK.fixedField :=
    ⟨!![⟨((x 1 : Kˣ) : K), hb⟩, 0; 0, ⟨((x 1 : Kˣ) : K), hb⟩⁻¹], by
      rw [Matrix.det_fin_two_of]
      apply Subtype.ext
      simp [Subfield.coe_mul, Subfield.coe_inv, Subfield.coe_one, Subfield.coe_zero,
        mul_inv_cancel₀ (Units.ne_zero (x 1 : Kˣ))]⟩
  refine ⟨A, ?_⟩
  apply hypSU_ext hK
  rw [coe_levHom, coe_splitTorusHom]
  ext i j
  rcases ix_cases i with rfl | rfl | rfl | rfl <;>
    rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [levMat_apply, slMat, A, torusEntries, ie1, ie2, if1, if2, hx, hb]

theorem torusE_inf_vecStab_le_levHom (hK : UnitaryFieldData 2 2 K) :
    torusE hK ⊓ vecStab (hypSU hK 2 0).subtype (Pi.single ie1 1) ≤ (levHom hK).range := by
  rintro g ⟨hgE, hgF⟩
  rw [torusE] at hgE
  obtain ⟨x, rfl⟩ := hgE
  exact sigma_mem_levHom_S07 hK x ((sigma_mem_vecStab_iff_S07 hK x).mp hgF)

theorem card_torusE_inf_vecStab (hK : UnitaryFieldData 2 2 K) :
    Nat.card ↥(torusE hK ⊓ vecStab (hypSU hK 2 0).subtype (Pi.single ie1 1)) = 3 := by
  let f : rootsOfUnity 3 K →
      ↥(torusE hK ⊓ vecStab (hypSU hK 2 0).subtype (Pi.single ie1 1)) := fun c =>
    ⟨splitTorusHom hK 2 0 (rootsOfUnity 3 K) (splitInv_rootsOfUnity_three hK)
        (Pi.mulSingle 1 c),
      ⟨⟨Pi.mulSingle 1 c, rfl⟩,
        (sigma_mem_vecStab_iff_S07 hK (Pi.mulSingle 1 c)).mpr (by simp)⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · have h := congrArg Subtype.val hab
      have h' := splitTorusHom_injective (splitInv_rootsOfUnity_three hK) h
      have h2 := congrFun h' 1
      simpa using h2
    · obtain ⟨g, hg⟩ := y
      obtain ⟨hgE, hgF⟩ := hg
      rw [torusE] at hgE
      obtain ⟨x, hx⟩ := hgE
      have hx0 : x 0 = 1 := by
        rw [← hx] at hgF
        exact (sigma_mem_vecStab_iff_S07 hK x).mp hgF
      refine ⟨x 1, Subtype.ext ?_⟩
      change (splitTorusHom hK 2 0 (rootsOfUnity 3 K) (splitInv_rootsOfUnity_three hK))
        (Pi.mulSingle 1 (x 1)) = g
      have hmul : Pi.mulSingle 1 (x 1) = x := by
        funext i
        fin_cases i <;> simp [hx0]
      rw [hmul, hx]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), card_rootsOfUnity_three hK]

theorem torusE_inf_vecStab_eq (hK : UnitaryFieldData 2 2 K) :
    torusE hK ⊓ vecStab (hypSU hK 2 0).subtype (Pi.single ie1 1) =
      torusE hK ⊓ Hinf (lineStab (hypSU hK 2 0) (Pi.single ie1 1)) := by
  apply le_antisymm
  · rintro g ⟨hgE, hgF⟩
    exact ⟨hgE, levHom_range_le_hinf_lineStab hK le_rfl
      (torusE_inf_vecStab_le_levHom hK ⟨hgE, hgF⟩)⟩
  · rintro g ⟨hgE, hgH⟩
    exact ⟨hgE, hinf_lineStab_le_vecStab hK hgH⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE
