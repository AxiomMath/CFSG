module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootSylow
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix Projectivization
open scoped LinearAlgebra.Projectivization MatrixGroups

universe u

public theorem no_involution_centralizes_psl2UpperUnipotent
    {K : Type u} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (v : PSL2 K) (hv : IsInvolution v) :
    v * psl2QuotientMap K (sl2UpperUnipotent (1 : K)) * v⁻¹ ≠
      psl2QuotientMap K (sl2UpperUnipotent (1 : K)) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  intro hconj
  let uSL : Matrix.SpecialLinearGroup (Fin 2) K := sl2UpperUnipotent (1 : K)
  let uPSL : PSL2 K := psl2QuotientMap K uSL
  have hcomm : uPSL * v = v * uPSL := by
    calc
      uPSL * v = (v * uPSL * v⁻¹) * v := by rw [hconj]
      _ = v * uPSL := by group
  have hfix1 : uPSL • psl2ProjectiveInfinity K = psl2ProjectiveInfinity K := by
    exact (psl2UpperUnipotent_one_fixed_iff K (psl2ProjectiveInfinity K)).2 rfl
  have hfix : uPSL • (v • psl2ProjectiveInfinity K) =
      v • psl2ProjectiveInfinity K := by
    calc
      uPSL • (v • psl2ProjectiveInfinity K) =
          (uPSL * v) • psl2ProjectiveInfinity K := by rw [← mul_smul]
      _ = (v * uPSL) • psl2ProjectiveInfinity K := by rw [hcomm]
      _ = v • (uPSL • psl2ProjectiveInfinity K) := by rw [mul_smul]
      _ = v • psl2ProjectiveInfinity K := by rw [hfix1]
  have hvfix : v • psl2ProjectiveInfinity K = psl2ProjectiveInfinity K := by
    exact (psl2UpperUnipotent_one_fixed_iff K
      (v • psl2ProjectiveInfinity K)).mp hfix
  have hvBorel : v ∈ psl2Borel K := by
    rw [psl2Borel]
    exact MulAction.mem_stabilizer_iff.mpr hvfix
  have hvBorel' : v ∈ (sl2Borel K).map (psl2QuotientMap K) := by
    rwa [← psl2Borel_eq_map]
  rcases Subgroup.mem_map.mp hvBorel' with ⟨A, hA, hAv⟩
  have hAconj : A * uSL * A⁻¹ = sl2UpperUnipotent (A.val 0 0 ^ 2 * (1 : K)) :=
    sl2Borel_conj_upperUnipotent hA (1 : K)
  have hqconj : psl2QuotientMap K (A * uSL * A⁻¹) = uPSL := by
    calc
      psl2QuotientMap K (A * uSL * A⁻¹)
          = psl2QuotientMap K A * psl2QuotientMap K uSL *
              (psl2QuotientMap K A)⁻¹ := by simp
      _ = v * uPSL * v⁻¹ := by rw [hAv]
      _ = uPSL := hconj
  have hqeq : psl2QuotientMap K (sl2UpperUnipotent (A.val 0 0 ^ 2 * (1 : K))) =
      psl2QuotientMap K uSL := by
    rw [hAconj] at hqconj
    exact hqconj
  let x : K := A.val 0 0 ^ 2 * (1 : K)
  have hqdiff : psl2QuotientMap K (sl2UpperUnipotent (x - 1)) = 1 := by
    have hmul : psl2QuotientMap K (sl2UpperUnipotent (x - 1)) *
        psl2QuotientMap K (sl2UpperUnipotent (1 : K)) =
        psl2QuotientMap K (sl2UpperUnipotent (1 : K)) := by
      calc
        psl2QuotientMap K (sl2UpperUnipotent (x - 1)) *
            psl2QuotientMap K (sl2UpperUnipotent (1 : K))
            = psl2QuotientMap K (sl2UpperUnipotent (x - 1) *
                sl2UpperUnipotent (1 : K)) := by rw [← (psl2QuotientMap K).map_mul]
        _ = psl2QuotientMap K (sl2UpperUnipotent ((x - 1) + 1)) := by rw [sl2UpperUnipotent_mul]
        _ = psl2QuotientMap K (sl2UpperUnipotent x) := by
          congr 1
          ring
        _ = psl2QuotientMap K (sl2UpperUnipotent (1 : K)) := by
          simpa [x] using hqeq
    have hcancel : psl2QuotientMap K (sl2UpperUnipotent (x - 1)) *
        psl2QuotientMap K (sl2UpperUnipotent (1 : K)) =
        1 * psl2QuotientMap K (sl2UpperUnipotent (1 : K)) := by
      rw [hmul]
      simp
    exact mul_right_cancel hcancel
  have hcenter : sl2UpperUnipotent (x - 1) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (QuotientGroup.eq_one_iff
      (N := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
      (sl2UpperUnipotent (x - 1))).mp hqdiff
  rcases (Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter) with ⟨r, _hr, hr_eq⟩
  have h01 : (0 : K) = x - 1 := by
    have hcoord := congrFun (congrFun hr_eq (0 : Fin 2)) (1 : Fin 2)
    simpa [Matrix.scalar, sl2UpperUnipotent] using hcoord
  have hx1 : x = 1 := sub_eq_zero.mp (by simpa using h01.symm)
  have hA00sq : A.val 0 0 ^ 2 = 1 := by
    simpa [x] using hx1
  have hA10 : A.val 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff A).mp hA
  have hdet : A.val 0 0 * A.val 1 1 = 1 := by
    have h := A.property
    rw [Matrix.det_fin_two, hA10] at h
    simpa using h
  have hA11 : A.val 1 1 = (A.val 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hdet)
  have hchar : ringChar K ≠ 2 := by
    intro hc
    have heven := FiniteField.even_card_of_char_two hc
    have hodd' : Odd (Fintype.card K) := by
      rw [Nat.card_eq_fintype_card] at hodd
      exact hodd
    rcases hodd' with ⟨k, hk⟩
    rw [hk] at heven
    omega
  have hAcenter : A * A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    have hq : psl2QuotientMap K (A * A) = 1 := by
      calc
        psl2QuotientMap K (A * A) = psl2QuotientMap K A * psl2QuotientMap K A := by
          rw [← (psl2QuotientMap K).map_mul]
        _ = v * v := by rw [hAv]
        _ = 1 := by simpa [pow_two] using hv.2
    exact (QuotientGroup.eq_one_iff
      (N := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
      (A * A)).mp hq
  rcases (Matrix.SpecialLinearGroup.mem_center_iff.mp hAcenter) with ⟨r, _hr, hr_eq⟩
  have hAA01_zero : (A * A).val 0 1 = 0 := by
    have hcoord := congrFun (congrFun hr_eq (0 : Fin 2)) (1 : Fin 2)
    simpa [Matrix.scalar] using hcoord.symm
  have hsum : A.val 0 0 * A.val 0 1 + A.val 0 1 * A.val 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA10] using hAA01_zero
  have hfactor : A.val 0 1 * (A.val 0 0 + A.val 1 1) = 0 := by
    rw [mul_add]
    rw [← hsum]
    ring
  have hchar2 : (2 : K) ≠ 0 := by
    intro hzero
    have hc : ringChar K = 2 := by
      apply (ringChar.eq_iff).mpr
      exact (CharP.charP_iff_prime_eq_zero (R := K) (p := 2)
        Nat.prime_two).mpr hzero
    exact hchar hc
  have hsum_ne : A.val 0 0 + A.val 1 1 ≠ 0 := by
    rcases (sq_eq_one_iff.mp hA00sq) with ha1 | ha_neg
    · have hval : A.val 0 0 + A.val 1 1 = (2 : K) := by
        rw [hA11, ha1]
        simp
        ring
      rw [hval]
      exact hchar2
    · have hval : A.val 0 0 + A.val 1 1 = -(2 : K) := by
        rw [hA11, ha_neg]
        have hinv : (-1 : K)⁻¹ = -1 := by simp
        rw [hinv]
        ring
      rw [hval]
      exact neg_ne_zero.mpr hchar2
  have hb0 : A.val 0 1 = 0 := (mul_eq_zero.mp hfactor).resolve_right hsum_ne
  have hA11_eq : A.val 1 1 = A.val 0 0 := by
    rw [hA11]
    rcases (sq_eq_one_iff.mp hA00sq) with ha1 | ha_neg
    · rw [ha1]
      simp
    · rw [ha_neg]
      simp
  have hAcenter' : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨A.val 0 0, by simpa using hA00sq, ?_⟩
    have hM : (Matrix.scalar (Fin 2) (A.val 0 0) : Matrix (Fin 2) (Fin 2) K) =
        (A : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, hA10, hb0, hA11_eq]
    exact hM
  have hqA : psl2QuotientMap K A = 1 :=
    (QuotientGroup.eq_one_iff
      (N := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) A).mpr hAcenter'
  have hv_one : v = 1 := by
    rw [← hAv, hqA]
  exact hv.1 hv_one

public theorem no_kleinFour_centralizes_psl2UpperUnipotentSubgroup
    {K : Type u} [Field K] [Finite K]
    (hodd : Odd (Nat.card K))
    (V : Subgroup (PSL2 K)) (hVK : IsKleinFour V)
    (hVleC : V ≤ Subgroup.centralizer
      (psl2UpperUnipotentSubgroup K : Set (PSL2 K))) :
    False := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hlt : 1 < Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, hVK.card_four]
    norm_num
  obtain ⟨w, hwne⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : V)
  let v : PSL2 K := (w : V)
  have hvmem : v ∈ V := w.property
  have hvne : v ≠ 1 := by
    intro h
    apply hwne
    ext
    exact h
  have hvtwo : v * v = 1 :=
    congrArg Subtype.val (IsKleinFour.mul_self w)
  have hv : IsInvolution v := ⟨hvne, by simpa [pow_two] using hvtwo⟩
  let u : PSL2 K := psl2QuotientMap K (sl2UpperUnipotent (1 : K))
  have hu : u ∈ psl2UpperUnipotentSubgroup K :=
    (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨1, rfl⟩
  have hcomm : u * v = v * u :=
    (Subgroup.mem_centralizer_iff.mp (hVleC hvmem)) u hu
  have hcent : v * u * v⁻¹ = u := by
    calc
      v * u * v⁻¹ = (u * v) * v⁻¹ := by rw [hcomm]
      _ = u := by group
  exact no_involution_centralizes_psl2UpperUnipotent hodd v hv hcent

end CFSG.GorensteinWalter
