module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Residual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Torus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.TorusFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par KTabC KTabD

private lemma levMat_ie2_if2_S08 {K : Type} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) : levMat A ie2 if2 = A 0 1 := by
  rw [levMat_apply]
  simp [ie1, ie2, if1, if2]

private noncomputable def rootSL2_S08 {K : Type} [Field K] (hK : UnitaryFieldData 2 2 K) :
    Matrix.SpecialLinearGroup (Fin 2) hK.fixedField :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private lemma slMat_root_apply_S08 {K : Type} [Field K] (hK : UnitaryFieldData 2 2 K) :
    (slMat hK (rootSL2_S08 hK)) 0 1 = 1 := by
  simp [slMat, rootSL2_S08]

private lemma eq_one_of_eq_inv_of_cube_eq_one_S08 {K : Type} [Field K] {b : K}
    (hb : b = b⁻¹) (h3 : b ^ 3 = 1) : b = 1 := by
  have hb0 : b ≠ 0 := by
    intro h0
    have hz : (0 : K) ^ 3 = 0 := zero_pow (by norm_num)
    rw [h0, hz] at h3
    exact zero_ne_one h3
  have h2 : b ^ 2 = 1 := by
    rw [pow_two]
    have h := congrArg (fun z : K => z * b) hb
    rwa [inv_mul_cancel₀ hb0] at h
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, h2, one_mul, pow_one] at h3
  exact h3

private lemma splitTorusHom_fix_x0_S08 {K : Type} [Field K] (hK : UnitaryFieldData 2 2 K)
    (x : Fin 2 → rootsOfUnity 3 K)
    (hv : Matrix.mulVec (((splitTorusHom hK 2 0 (rootsOfUnity 3 K)
        (splitInv_rootsOfUnity_three hK) x : hypSU hK 2 0) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) (Pi.single ie1 1) = Pi.single ie1 1) :
    x 0 = 1 := by
  rw [coe_splitTorusHom (splitInv_rootsOfUnity_three hK) x,
    Matrix.diagonal_mulVec_single] at hv
  have h0 := congrFun hv ie1
  simp [torusEntries, ie1] at h0
  apply Subtype.ext
  apply Units.ext
  simpa using h0

private lemma commute_root_entry_S08 {K : Type} [Field K] (hK : UnitaryFieldData 2 2 K)
    (e k : hypSU hK 2 0) (t : HypIndex 2 0 → K)
    (he : ((e : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      Matrix.diagonal t)
    (hk : ((k : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      levMat (slMat hK (rootSL2_S08 hK)))
    (hc : e * k = k * e) : t ie2 = t if2 := by
  have hcomm' : (((e * k : hypSU hK 2 0) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      (((k * e : hypSU hK 2 0) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by rw [hc]
  rw [coe_mul_hypSU hK e k, coe_mul_hypSU hK k e] at hcomm'
  have hentry := congrFun (congrFun hcomm' ie2) if2
  rw [he, hk, Matrix.diagonal_mul, Matrix.mul_diagonal,
    levMat_ie2_if2_S08 (slMat hK (rootSL2_S08 hK)), slMat_root_apply_S08 hK] at hentry
  simpa only [mul_one, one_mul] using hentry

private lemma eq_one_of_commute_root_S08 {K : Type} [Field K] (hK : UnitaryFieldData 2 2 K)
    (e k : hypSU hK 2 0) (x : Fin 2 → rootsOfUnity 3 K)
    (hk : k = levHom hK (rootSL2_S08 hK))
    (hσ : splitTorusHom hK 2 0 (rootsOfUnity 3 K) (splitInv_rootsOfUnity_three hK) x = e)
    (hx0 : x 0 = 1) (hcomm : e * k = k * e) : x = 1 := by
  let t : HypIndex 2 0 → K := torusEntries hK (fun i => (x i : Kˣ)) (1 : Fin 0 → Kˣ)
  let b : K := ((x 1 : Kˣ) : K)
  have hmat : ((e : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      Matrix.diagonal t := by
    rw [← hσ]
    exact coe_splitTorusHom (splitInv_rootsOfUnity_three hK) x
  have hmatk : ((k : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      levMat (slMat hK (rootSL2_S08 hK)) := by
    rw [hk]
    exact coe_levHom hK (rootSL2_S08 hK)
  have hbar_b : hK.bar b = b := by
    simpa [b] using splitInv_rootsOfUnity_three hK (x 1)
  have hb3 : b ^ 3 = 1 := by
    have h := (mem_rootsOfUnity' 3 (x 1 : Kˣ)).mp (x 1).2
    simpa [b] using h
  have hti : t ie2 = b := by simp [t, b, torusEntries, ie2]
  have htf : t if2 = b⁻¹ := by
    have h1 : t if2 = (hK.bar b)⁻¹ := by simp [t, b, torusEntries, if2]
    rwa [hbar_b] at h1
  have hentry : t ie2 = t if2 := commute_root_entry_S08 hK e k t hmat hmatk hcomm
  have hb_eq : b = b⁻¹ := hti.symm.trans (hentry.trans htf)
  have hb1 : b = 1 := eq_one_of_eq_inv_of_cube_eq_one_S08 hb_eq hb3
  have hx1 : x 1 = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa [b] using hb1
  funext i
  fin_cases i
  · exact hx0
  · exact hx1

theorem torusE_noncentral {K : Type} [Field K] (hK : UnitaryFieldData 2 2 K) :
    ∃ k ∈ Hinf (lineStab (hypSU hK 2 0) (Pi.single ie1 1)),
      ∃ e ∈ torusE hK ⊓ Hinf (lineStab (hypSU hK 2 0) (Pi.single ie1 1)), e * k ≠ k * e := by
  let P : Subgroup (hypSU hK 2 0) := lineStab (hypSU hK 2 0) (Pi.single ie1 1)
  haveI : Finite K := hK.finite
  have hcard : Nat.card ↥(torusE hK ⊓ Hinf P) = 3 := by
    rw [← torusE_inf_vecStab_eq hK]
    exact card_torusE_inf_vecStab hK
  haveI : Nontrivial ↥(torusE hK ⊓ Hinf P) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  obtain ⟨e, he, hne⟩ := Subgroup.exists_ne_one_of_nontrivial (torusE hK ⊓ Hinf P)
  let k : hypSU hK 2 0 := levHom hK (rootSL2_S08 hK)
  have hkHinf : k ∈ Hinf P := levHom_range_le_hinf_lineStab hK le_rfl ⟨rootSL2_S08 hK, rfl⟩
  refine ⟨k, hkHinf, e, he, ?_⟩
  intro hcomm
  have he_torus : e ∈ torusE hK := he.1
  have he_hinf : e ∈ Hinf P := he.2
  change e ∈ (splitTorusHom hK 2 0 (rootsOfUnity 3 K)
    (splitInv_rootsOfUnity_three hK)).range at he_torus
  rw [MonoidHom.mem_range] at he_torus
  obtain ⟨x, hxσ⟩ := he_torus
  have hev : e ∈ vecStab (hypSU hK 2 0).subtype (Pi.single ie1 1) :=
    hinf_lineStab_le_vecStab hK he_hinf
  rw [KTabC.mem_vecStab] at hev
  change Matrix.mulVec (((e : GL (HypIndex 2 0) K) :
    Matrix (HypIndex 2 0) (HypIndex 2 0) K)) (Pi.single ie1 1) = Pi.single ie1 1 at hev
  have hx0 : x 0 = 1 := by
    apply splitTorusHom_fix_x0_S08 hK x
    rw [hxσ]
    exact hev
  have hx : x = 1 := eq_one_of_commute_root_S08 hK e k x rfl hxσ hx0 hcomm
  have he1 : e = 1 := by rw [← hxσ, hx, map_one]
  exact hne he1

end CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE
