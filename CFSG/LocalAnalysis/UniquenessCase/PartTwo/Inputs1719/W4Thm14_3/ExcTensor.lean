module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityPairUnitary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups
open Polynomial

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable {E : Type*} [Field E] [CharP E 2] [Algebra F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma aexp_single (e : ι → ℕ) (j : ι) :
    aexp e (Pi.single j (1 : Fin 2)) = 2 ^ e j := by
  unfold aexp
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi]
    simp
  · simp

private lemma tmatE_uElt_eq_zero (e : ι → ℕ) (t : F) (z y : ι → Fin 2) (h : ¬ z ≤ y) :
    tmatE E e (uElt t) z y = 0 := by
  classical
  rw [tmatE]
  simp only [Pi.le_def] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  have hz : z i = 1 := by
    have hlt : (y i : ℕ) < (z i : ℕ) := by simpa using hi
    exact Fin.ext (by have := (z i).isLt; omega)
  have hy : y i = 0 := by
    have hlt : (y i : ℕ) < (z i : ℕ) := by simpa using hi
    exact Fin.ext (by have := (z i).isLt; omega)
  rw [twistMat_apply, hz, hy]
  simp [uElt]

private lemma tmatE_uElt_diag (e : ι → ℕ) (t : F) (j : ι) :
    tmatE E e (uElt t) (Pi.single j (1 : Fin 2)) (Pi.single j (1 : Fin 2)) = 1 := by
  classical
  rw [tmatE]
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases hi : i = j
  · subst hi
    rw [Pi.single_eq_same, twistMat_uElt]
    simp
  · rw [Pi.single_eq_of_ne hi, twistMat_uElt]
    simp

private lemma eq_zero_or_eq_single_of_le_single (j : ι) (z : ι → Fin 2)
    (hz : z ≤ Pi.single j (1 : Fin 2)) :
    z = 0 ∨ z = Pi.single j (1 : Fin 2) := by
  classical
  by_cases h0 : z = 0
  · exact Or.inl h0
  · right
    have hex : ∃ i, z i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h0 (funext hcon)
    obtain ⟨i, hi⟩ := hex
    have hzi : z i = 1 := by
      rcases fin2_cases (z i) with h | h
      · exact absurd h hi
      · exact h
    have hd : (Pi.single j (1 : Fin 2) : ι → Fin 2) i = 1 := by
      have hle := hz i
      rw [hzi] at hle
      rcases fin2_cases ((Pi.single j (1 : Fin 2) : ι → Fin 2) i) with h | h
      · rw [h] at hle; simp at hle
      · exact h
    have hij : i = j := by
      by_contra hne
      rw [Pi.single_eq_of_ne hne] at hd
      simp at hd
    subst hij
    funext k
    by_cases hk : k = i
    · subst hk
      rw [Pi.single_eq_same]
      exact hzi
    · rw [Pi.single_eq_of_ne hk]
      have hle := hz k
      rcases fin2_cases (z k) with h | h
      · exact h
      · rw [h, Pi.single_eq_of_ne hk] at hle
        simp at hle

private lemma tmatE_uElt_single (e : ι → ℕ) (t : F) (j : ι) (z : ι → Fin 2) :
    tmatE E e (uElt t) z (Pi.single j (1 : Fin 2)) =
      (if z = Pi.single j (1 : Fin 2) then (1 : E) else 0) +
        (if z = 0 then (algebraMap F E t) ^ (2 ^ e j) else 0) := by
  classical
  by_cases h1 : z = Pi.single j (1 : Fin 2)
  · subst h1
    rw [tmatE_uElt_diag]
    have hne : (Pi.single j (1 : Fin 2) : ι → Fin 2) ≠ 0 := by
      intro h
      have := congrFun h j
      rw [Pi.single_eq_same] at this
      simp at this
    simp [hne]
  · by_cases h0 : z = 0
    · subst h0
      have hrow : tmatE E e (uElt t) (0 : ι → Fin 2) (Pi.single j (1 : Fin 2)) =
          (algebraMap F E t) ^ (2 ^ e j) := by
        rw [show (0 : ι → Fin 2) = (fun _ => 0) from rfl]
        rw [tmatE_uElt_base_row, aexp_single]
      rw [hrow]
      simp [h1]
    · have hle : ¬ z ≤ Pi.single j (1 : Fin 2) := fun hz => by
        rcases eq_zero_or_eq_single_of_le_single j z hz with h | h
        · exact h0 h
        · exact h1 h
      have hzero := tmatE_uElt_eq_zero (E := E) (e := e) (t := t) (z := z)
        (y := Pi.single j (1 : Fin 2)) hle
      rw [hzero]
      simp [h1, h0]

section Model

private lemma tensorRep_uElt_pi_single (e : ι → ℕ) (t : F) (j : ι) :
    tensorRep F E e (uElt t) (Pi.single (Pi.single j (1 : Fin 2)) (1 : E)) =
      (Pi.single (Pi.single j (1 : Fin 2)) (1 : E) : (ι → Fin 2) → E) +
        (algebraMap F E t) ^ (2 ^ e j) • baseVec := by
  funext z
  rw [tensorRep_apply, Finset.sum_eq_single (Pi.single j (1 : Fin 2))]
  · rw [Pi.single_eq_same, mul_one, tmatE_uElt_single]
    have hz : (Pi.single (Pi.single j (1 : Fin 2)) (1 : E) : (ι → Fin 2) → E) z =
        (if z = Pi.single j (1 : Fin 2) then 1 else 0) := by
      rw [Pi.single_apply]
    have hb : (baseVec : (ι → Fin 2) → E) z = if z = 0 then 1 else 0 := baseVec_apply z
    rw [Pi.add_apply, Pi.smul_apply, hz, hb]
    by_cases h : z = Pi.single j (1 : Fin 2)
    · simp [h]
    · by_cases h0 : z = 0 <;> simp [h, h0]
  · intro x _ hx
    rw [Pi.single_eq_of_ne hx, mul_zero]
  · simp

private lemma frobTensor_uElt_combine (J : Finset ℕ) (t : F) (j0 j1 : J) (a0 a1 : E) :
    frobTensor F E J (uElt t)
        (a0 • (Pi.single (Pi.single j0 (1 : Fin 2)) (1 : E) : (J → Fin 2) → E) +
          a1 • Pi.single (Pi.single j1 (1 : Fin 2)) (1 : E)) =
      (a0 • (Pi.single (Pi.single j0 (1 : Fin 2)) (1 : E) : (J → Fin 2) → E) +
          a1 • Pi.single (Pi.single j1 (1 : Fin 2)) (1 : E)) +
        (a0 * (algebraMap F E t) ^ (2 ^ (j0 : ℕ)) +
          a1 * (algebraMap F E t) ^ (2 ^ (j1 : ℕ))) • baseVec := by
  rw [frobTensor, map_add, map_smul, map_smul, tensorRep_uElt_pi_single,
    tensorRep_uElt_pi_single]
  simp only [smul_add, smul_smul, add_smul]
  abel

end Model

section ModelClaim

private lemma model_024 (x y : F) (hx : x ≠ 0) (hxy : x * y ^ 4 ≠ y * x ^ 4) :
    ∃ v : (({0, 2, 4} : Finset ℕ) → Fin 2) → E,
      (∀ l : F, l ^ 4 = l → frobTensor F E ({0, 2, 4} : Finset ℕ) (uElt (l * x)) v = v) ∧
      frobTensor F E ({0, 2, 4} : Finset ℕ) (uElt y) v ≠ v := by
  classical
  let X : E := algebraMap F E x
  let j0 : ({0, 2, 4} : Finset ℕ) := ⟨0, by simp⟩
  let j1 : ({0, 2, 4} : Finset ℕ) := ⟨2, by simp⟩
  let v : (({0, 2, 4} : Finset ℕ) → Fin 2) → E :=
    X ^ 4 • (Pi.single (Pi.single j0 (1 : Fin 2) :
        ({0, 2, 4} : Finset ℕ) → Fin 2) (1 : E)) +
      X • (Pi.single (Pi.single j1 (1 : Fin 2) :
        ({0, 2, 4} : Finset ℕ) → Fin 2) (1 : E))
  refine ⟨v, ?_, ?_⟩
  · intro l hl
    have hcomb := frobTensor_uElt_combine ({0, 2, 4} : Finset ℕ) (l * x) j0 j1 (X ^ 4) X
    rw [hcomb]
    have hL : (algebraMap F E l) ^ 4 = algebraMap F E l := by rw [← map_pow, hl]
    have hzero : X ^ 4 * (algebraMap F E (l * x)) ^ (2 ^ (j0 : ℕ)) +
        X * (algebraMap F E (l * x)) ^ (2 ^ (j1 : ℕ)) = 0 := by
      simp only [j0, j1]
      norm_num
      change (algebraMap F E x) ^ 4 * ((algebraMap F E l) * (algebraMap F E x)) +
        (algebraMap F E x) * ((algebraMap F E l) * (algebraMap F E x)) ^ 4 = 0
      rw [mul_pow, hL]
      have hcomm : (algebraMap F E x) ^ 4 * ((algebraMap F E l) * (algebraMap F E x)) =
          (algebraMap F E x) * ((algebraMap F E l) * (algebraMap F E x) ^ 4) := by ring
      rw [hcomm]
      exact add_self_eq_zero_of_charTwo E _
    rw [hzero, zero_smul, add_zero]
  · intro hbad
    have hcomb := frobTensor_uElt_combine ({0, 2, 4} : Finset ℕ) y j0 j1 (X ^ 4) X
    have hy : X ^ 4 * (algebraMap F E y) ^ (2 ^ (j0 : ℕ)) +
        X * (algebraMap F E y) ^ (2 ^ (j1 : ℕ)) ≠ 0 := by
      simp only [j0, j1]
      norm_num
      intro hzero
      have hXY : algebraMap F E (x ^ 4 * y) = algebraMap F E (x * y ^ 4) := by
        rw [map_mul, map_mul, map_pow, map_pow]
        change (algebraMap F E x) ^ 4 * (algebraMap F E y) =
          (algebraMap F E x) * (algebraMap F E y) ^ 4
        rw [← sub_eq_zero, sub_eq_add_neg, neg_eq_self_of_charTwo E, hzero]
      have hEq : x ^ 4 * y = x * y ^ 4 := (algebraMap F E).injective hXY
      rw [mul_comm (x ^ 4) y] at hEq
      exact hxy hEq.symm
    have h2 : v + (X ^ 4 * (algebraMap F E y) ^ (2 ^ (j0 : ℕ)) +
        X * (algebraMap F E y) ^ (2 ^ (j1 : ℕ))) • baseVec = v + 0 := by
      rw [add_zero]
      exact hcomb.symm.trans hbad
    have h3 : (X ^ 4 * (algebraMap F E y) ^ (2 ^ (j0 : ℕ)) +
        X * (algebraMap F E y) ^ (2 ^ (j1 : ℕ))) • baseVec = 0 := add_left_cancel h2
    have hbase : (baseVec : (({0, 2, 4} : Finset ℕ) → Fin 2) → E) ≠ 0 := by
      intro h
      have h1 := congrFun h (0 : ({0, 2, 4} : Finset ℕ) → Fin 2)
      rw [baseVec_apply] at h1
      simp at h1
      exact h1 rfl
    have hc : X ^ 4 * (algebraMap F E y) ^ (2 ^ (j0 : ℕ)) +
        X * (algebraMap F E y) ^ (2 ^ (j1 : ℕ)) = 0 := by
      rcases smul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h hbase
    exact hy hc

end ModelClaim

section ModelClaim135

private lemma model_135 (x y : F) (hx : x ≠ 0) (hxy : x * y ^ 4 ≠ y * x ^ 4) :
    ∃ v : (({1, 3, 5} : Finset ℕ) → Fin 2) → E,
      (∀ l : F, l ^ 4 = l → frobTensor F E ({1, 3, 5} : Finset ℕ) (uElt (l * x)) v = v) ∧
      frobTensor F E ({1, 3, 5} : Finset ℕ) (uElt y) v ≠ v := by
  classical
  let X : E := algebraMap F E x
  let j0 : ({1, 3, 5} : Finset ℕ) := ⟨1, by simp⟩
  let j1 : ({1, 3, 5} : Finset ℕ) := ⟨3, by simp⟩
  let v : (({1, 3, 5} : Finset ℕ) → Fin 2) → E :=
    X ^ 8 • (Pi.single (Pi.single j0 (1 : Fin 2) :
        ({1, 3, 5} : Finset ℕ) → Fin 2) (1 : E)) +
      X ^ 2 • (Pi.single (Pi.single j1 (1 : Fin 2) :
        ({1, 3, 5} : Finset ℕ) → Fin 2) (1 : E))
  refine ⟨v, ?_, ?_⟩
  · intro l hl
    have hcomb := frobTensor_uElt_combine ({1, 3, 5} : Finset ℕ) (l * x) j0 j1 (X ^ 8) (X ^ 2)
    rw [hcomb]
    have hL : (algebraMap F E l) ^ 8 = (algebraMap F E l) ^ 2 := by
      have hlE : (algebraMap F E l) ^ 4 = algebraMap F E l := by rw [← map_pow, hl]
      rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, hlE]
    have hzero : X ^ 8 * (algebraMap F E (l * x)) ^ (2 ^ ((j0 : ℕ))) +
        X ^ 2 * (algebraMap F E (l * x)) ^ (2 ^ ((j1 : ℕ))) = 0 := by
      simp only [j0, j1]
      norm_num
      change (algebraMap F E x) ^ 8 * ((algebraMap F E l) * (algebraMap F E x)) ^ 2 +
        (algebraMap F E x) ^ 2 * ((algebraMap F E l) * (algebraMap F E x)) ^ 8 = 0
      rw [mul_pow, mul_pow, hL]
      have hcomm : (algebraMap F E x) ^ 8 * ((algebraMap F E l) ^ 2 * (algebraMap F E x) ^ 2) =
          (algebraMap F E x) ^ 2 * ((algebraMap F E l) ^ 2 * (algebraMap F E x) ^ 8) := by
        ring
      rw [hcomm]
      exact add_self_eq_zero_of_charTwo E _
    rw [hzero, zero_smul, add_zero]
  · intro hbad
    have hcomb := frobTensor_uElt_combine ({1, 3, 5} : Finset ℕ) y j0 j1 (X ^ 8) (X ^ 2)
    have hy : X ^ 8 * (algebraMap F E y) ^ (2 ^ ((j0 : ℕ))) +
        X ^ 2 * (algebraMap F E y) ^ (2 ^ ((j1 : ℕ))) ≠ 0 := by
      simp only [j0, j1]
      norm_num
      change (algebraMap F E x) ^ 8 * (algebraMap F E y) ^ 2 +
        (algebraMap F E x) ^ 2 * (algebraMap F E y) ^ 8 ≠ 0
      intro hzero
      have hfac : (algebraMap F E x) ^ 8 * (algebraMap F E y) ^ 2 +
          (algebraMap F E x) ^ 2 * (algebraMap F E y) ^ 8 =
          (algebraMap F E x) ^ 2 * (algebraMap F E y) ^ 2 *
            ((algebraMap F E x) ^ 3 + (algebraMap F E y) ^ 3) ^ 2 := by
        have h2 : (2 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 2
        ring_nf
        rw [h2]
        ring
      rw [hfac] at hzero
      have hXY2 : (algebraMap F E x) ^ 2 * (algebraMap F E y) ^ 2 ≠ 0 := by
        apply mul_ne_zero
        · exact pow_ne_zero _ (by simpa using (algebraMap F E).injective.ne hx)
        · intro hy0
          have hy : y = 0 := by
            apply (algebraMap F E).injective
            simpa using hy0
          exfalso
          apply hxy
          rw [hy]
          ring
      have hsq : ((algebraMap F E x) ^ 3 + (algebraMap F E y) ^ 3) ^ 2 = 0 := by
        by_contra h
        exact (mul_ne_zero hXY2 h) hzero
      have hsum : (algebraMap F E x) ^ 3 + (algebraMap F E y) ^ 3 = 0 := by
        have hAA : ((algebraMap F E x) ^ 3 + (algebraMap F E y) ^ 3) *
            ((algebraMap F E x) ^ 3 + (algebraMap F E y) ^ 3) = 0 := by
          rw [← pow_two]; exact hsq
        rcases mul_eq_zero.mp hAA with h | h
        · exact h
        · exact h
      apply hxy
      have hmap : algebraMap F E (x ^ 3 + y ^ 3) = 0 := by
        rw [map_add, map_pow, map_pow]
        exact hsum
      have h3 : x ^ 3 + y ^ 3 = 0 := by
        apply (algebraMap F E).injective
        simpa using hmap
      have hzero2 : x * y ^ 4 + y * x ^ 4 = 0 := by
        have hfac' : x * y ^ 4 + y * x ^ 4 = x * y * (y ^ 3 + x ^ 3) := by ring
        rw [hfac', add_comm (y ^ 3) (x ^ 3), h3, mul_zero]
      have hneg : x * y ^ 4 = -(y * x ^ 4) := eq_neg_of_add_eq_zero_left hzero2
      rwa [CharTwo.neg_eq] at hneg
    have h2 : v + (X ^ 8 * (algebraMap F E y) ^ (2 ^ ((j0 : ℕ))) +
        X ^ 2 * (algebraMap F E y) ^ (2 ^ ((j1 : ℕ)))) • baseVec = v + 0 := by
      rw [add_zero]
      exact hcomb.symm.trans hbad
    have h3 : (X ^ 8 * (algebraMap F E y) ^ (2 ^ ((j0 : ℕ))) +
        X ^ 2 * (algebraMap F E y) ^ (2 ^ ((j1 : ℕ)))) • baseVec = 0 := add_left_cancel h2
    have hbase : (baseVec : (({1, 3, 5} : Finset ℕ) → Fin 2) → E) ≠ 0 := by
      intro h
      have h1 := congrFun h (0 : ({1, 3, 5} : Finset ℕ) → Fin 2)
      rw [baseVec_apply] at h1
      simp at h1
      exact h1 rfl
    rcases smul_eq_zero.mp h3 with h | h
    · exact hy h
    · exact absurd h hbase

end ModelClaim135

section PlaneModel

variable [Finite E]

private lemma frobTensor_uElt_combine3 (J : Finset ℕ) (t : F) (j0 j1 j2 : J) (a0 a1 a2 : E) :
    frobTensor F E J (uElt t)
        (a0 • (Pi.single (Pi.single j0 (1 : Fin 2)) (1 : E) : (J → Fin 2) → E) +
          a1 • Pi.single (Pi.single j1 (1 : Fin 2)) (1 : E) +
          a2 • Pi.single (Pi.single j2 (1 : Fin 2)) (1 : E)) =
      (a0 • (Pi.single (Pi.single j0 (1 : Fin 2)) (1 : E) : (J → Fin 2) → E) +
          a1 • Pi.single (Pi.single j1 (1 : Fin 2)) (1 : E) +
          a2 • Pi.single (Pi.single j2 (1 : Fin 2)) (1 : E)) +
        (a0 * (algebraMap F E t) ^ (2 ^ (j0 : ℕ)) +
          a1 * (algebraMap F E t) ^ (2 ^ (j1 : ℕ)) +
          a2 * (algebraMap F E t) ^ (2 ^ (j2 : ℕ))) • baseVec := by
  rw [frobTensor, map_add, map_add, map_smul, map_smul, map_smul, tensorRep_uElt_pi_single,
    tensorRep_uElt_pi_single, tensorRep_uElt_pi_single]
  simp only [smul_add, smul_smul, add_smul]
  abel

private lemma plane_P_eq_zero (x y l l' : F) (hl : l ^ 4 = l) (hl' : l' ^ 4 = l') :
    let X : E := algebraMap F E x
    let Y : E := algebraMap F E y
    let Z : E := algebraMap F E (l * x + l' * y)
    let a0 : E := X ^ 4 * Y ^ 16 + X ^ 16 * Y ^ 4
    let a1 : E := X ^ 16 * Y + X * Y ^ 16
    let a2 : E := X * Y ^ 4 + X ^ 4 * Y
    a0 * Z + a1 * Z ^ 4 + a2 * Z ^ 16 = 0 := by
  classical
  dsimp only
  have hL : (algebraMap F E l) ^ 4 = algebraMap F E l := by rw [← map_pow, hl]
  have hL' : (algebraMap F E l') ^ 4 = algebraMap F E l' := by rw [← map_pow, hl']
  have hL16 : (algebraMap F E l) ^ 16 = algebraMap F E l := by
    rw [show (16 : ℕ) = 4 * 4 by norm_num, pow_mul, hL, hL]
  have hL16' : (algebraMap F E l') ^ 16 = algebraMap F E l' := by
    rw [show (16 : ℕ) = 4 * 4 by norm_num, pow_mul, hL', hL']
  have hX : ((algebraMap F E x) ^ 4 * (algebraMap F E y) ^ 16 +
      (algebraMap F E x) ^ 16 * (algebraMap F E y) ^ 4) * (algebraMap F E x) +
      ((algebraMap F E x) ^ 16 * (algebraMap F E y) +
      (algebraMap F E x) * (algebraMap F E y) ^ 16) * (algebraMap F E x) ^ 4 +
      ((algebraMap F E x) * (algebraMap F E y) ^ 4 +
      (algebraMap F E x) ^ 4 * (algebraMap F E y)) * (algebraMap F E x) ^ 16 = 0 := by
    ring_nf
    rw [show (2 : E) = 0 from CharP.cast_eq_zero E 2]
    ring
  have hY : ((algebraMap F E x) ^ 4 * (algebraMap F E y) ^ 16 +
      (algebraMap F E x) ^ 16 * (algebraMap F E y) ^ 4) * (algebraMap F E y) +
      ((algebraMap F E x) ^ 16 * (algebraMap F E y) +
      (algebraMap F E x) * (algebraMap F E y) ^ 16) * (algebraMap F E y) ^ 4 +
      ((algebraMap F E x) * (algebraMap F E y) ^ 4 +
      (algebraMap F E x) ^ 4 * (algebraMap F E y)) * (algebraMap F E y) ^ 16 = 0 := by
    ring_nf
    rw [show (2 : E) = 0 from CharP.cast_eq_zero E 2]
    ring
  have hZ4eq : (algebraMap F E (l * x + l' * y)) ^ 4 =
      algebraMap F E l * (algebraMap F E x) ^ 4 +
      algebraMap F E l' * (algebraMap F E y) ^ 4 := by
    rw [map_add, map_mul, map_mul]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, add_pow_char_pow]
    norm_num
    rw [mul_pow, mul_pow, hL, hL']
  have hZ16eq : (algebraMap F E (l * x + l' * y)) ^ 16 =
      algebraMap F E l * (algebraMap F E x) ^ 16 +
      algebraMap F E l' * (algebraMap F E y) ^ 16 := by
    rw [map_add, map_mul, map_mul]
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, add_pow_char_pow]
    norm_num
    rw [mul_pow, mul_pow, hL16, hL16']
  rw [hZ4eq, hZ16eq]
  rw [map_add, map_mul, map_mul]
  calc ((algebraMap F E x) ^ 4 * (algebraMap F E y) ^ 16 +
        (algebraMap F E x) ^ 16 * (algebraMap F E y) ^ 4) *
        (algebraMap F E l * (algebraMap F E x) + algebraMap F E l' * (algebraMap F E y)) +
      ((algebraMap F E x) ^ 16 * (algebraMap F E y) +
        (algebraMap F E x) * (algebraMap F E y) ^ 16) *
        (algebraMap F E l * (algebraMap F E x) ^ 4 + algebraMap F E l' * (algebraMap F E y) ^ 4) +
      ((algebraMap F E x) * (algebraMap F E y) ^ 4 +
        (algebraMap F E x) ^ 4 * (algebraMap F E y)) *
        (algebraMap F E l * (algebraMap F E x) ^ 16 + algebraMap F E l' * (algebraMap F E y) ^ 16)
    = algebraMap F E l * (((algebraMap F E x) ^ 4 * (algebraMap F E y) ^ 16 +
        (algebraMap F E x) ^ 16 * (algebraMap F E y) ^ 4) * (algebraMap F E x) +
        ((algebraMap F E x) ^ 16 * (algebraMap F E y) +
        (algebraMap F E x) * (algebraMap F E y) ^ 16) * (algebraMap F E x) ^ 4 +
        ((algebraMap F E x) * (algebraMap F E y) ^ 4 +
        (algebraMap F E x) ^ 4 * (algebraMap F E y)) * (algebraMap F E x) ^ 16) +
      algebraMap F E l' * (((algebraMap F E x) ^ 4 * (algebraMap F E y) ^ 16 +
        (algebraMap F E x) ^ 16 * (algebraMap F E y) ^ 4) * (algebraMap F E y) +
        ((algebraMap F E x) ^ 16 * (algebraMap F E y) +
        (algebraMap F E x) * (algebraMap F E y) ^ 16) * (algebraMap F E y) ^ 4 +
        ((algebraMap F E x) * (algebraMap F E y) ^ 4 +
        (algebraMap F E x) ^ 4 * (algebraMap F E y)) * (algebraMap F E y) ^ 16) := by ring
    _ = algebraMap F E l * 0 + algebraMap F E l' * 0 := by rw [hX, hY]
    _ = 0 := by simp

private lemma plane_param_injective (x y p1 p2 q1 q2 : F) (hx : x ≠ 0)
    (hxy : x * y ^ 4 ≠ y * x ^ 4)
    (hp1 : p1 ^ 4 = p1) (hp2 : p2 ^ 4 = p2)
    (hq1 : q1 ^ 4 = q1) (hq2 : q2 ^ 4 = q2)
    (heq : p1 * x + p2 * y = q1 * x + q2 * y) : p1 = q1 ∧ p2 = q2 := by
  have h2 : p1 * x + p2 * y + (q1 * x + q2 * y) = 0 := by
    have h := congrArg (fun t => t + (q1 * x + q2 * y)) heq
    rw [CharTwo.add_self_eq_zero] at h
    exact h
  have h3 : p1 * x + q1 * x + (p2 * y + q2 * y) = 0 := by
    calc p1 * x + q1 * x + (p2 * y + q2 * y)
        = p1 * x + p2 * y + (q1 * x + q2 * y) := by ring
      _ = 0 := h2
  have h4 : (p1 + q1) * x + (p2 + q2) * y = 0 := by
    rw [add_mul, add_mul]
    exact h3
  have hlin : (p1 + q1) * x = (q2 + p2) * y := by
    have h5 : (p2 + q2) * y = -((p1 + q1) * x) := eq_neg_of_add_eq_zero_right h4
    rw [CharTwo.neg_eq] at h5
    rw [add_comm p2 q2] at h5
    exact h5.symm
  by_cases hden : q2 + p2 = 0
  · have hsum : p1 + q1 = 0 := by
      have := hlin
      rw [hden, zero_mul] at this
      exact (mul_eq_zero.mp this).resolve_right hx
    have hp1_eq : p1 = q1 := by
      have h : p1 = -q1 := eq_neg_of_add_eq_zero_left hsum
      rwa [CharTwo.neg_eq q1] at h
    have hp2_eq : p2 = q2 := by
      have h : p2 = -q2 := eq_neg_of_add_eq_zero_right hden
      rwa [CharTwo.neg_eq q2] at h
    exact ⟨hp1_eq, hp2_eq⟩
  · have hden' : q2 + p2 ≠ 0 := hden
    let m : F := (p1 + q1) / (q2 + p2)
    have hm : y = m * x := by
      dsimp [m]
      field_simp [hden']
      rw [hlin]
      ring
    have hm4 : m ^ 4 = m := by
      dsimp [m]
      rw [div_pow]
      have num : (p1 + q1) ^ 4 = p1 ^ 4 + q1 ^ 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        rw [add_pow_char_pow]
      have den : (q2 + p2) ^ 4 = q2 ^ 4 + p2 ^ 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        rw [add_pow_char_pow]
      rw [num, den, hp1, hq1, hq2, hp2]
    have hcontra : x * y ^ 4 = y * x ^ 4 := by
      rw [hm]
      rw [mul_pow, hm4]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    exact absurd hcontra hxy

private lemma plane_P_ne_zero (E : Type*) [Field E] [CharP E 2] [Algebra F E] [Finite E]
    (hF : Fintype.card F = 2 ^ 6) (x y z : F)
    (hx : x ≠ 0) (hxy : x * y ^ 4 ≠ y * x ^ 4)
    (hz : ∀ l l' : F, l ^ 4 = l → l' ^ 4 = l' → z ≠ l * x + l' * y) :
    (x ^ 4 * y ^ 16 + x ^ 16 * y ^ 4) * z +
    (x ^ 16 * y + x * y ^ 16) * z ^ 4 +
    (x * y ^ 4 + x ^ 4 * y) * z ^ 16 ≠ 0 := by
  classical
  let c0 : F := x ^ 4 * y ^ 16 + x ^ 16 * y ^ 4
  let c1 : F := x ^ 16 * y + x * y ^ 16
  let c2 : F := x * y ^ 4 + x ^ 4 * y
  change c0 * z + c1 * z ^ 4 + c2 * z ^ 16 ≠ 0
  have hc2 : c2 ≠ 0 := by
    intro h
    apply hxy
    have h' : x * y ^ 4 = x ^ 4 * y := by
      have := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at this
    simpa [mul_comm] using h'
  let q : F[X] := Polynomial.C c2 * Polynomial.X ^ 16 +
    Polynomial.C c1 * Polynomial.X ^ 4 + Polynomial.C c0 * Polynomial.X
  have hq_deg : q.natDegree = 16 := by
    have h16 : (Polynomial.C c2 * Polynomial.X ^ 16).natDegree = 16 := by
      rw [Polynomial.natDegree_C_mul_X_pow 16 c2 hc2]
    have hlow : (Polynomial.C c1 * Polynomial.X ^ 4 +
        Polynomial.C c0 * Polynomial.X).natDegree <
        (Polynomial.C c2 * Polynomial.X ^ 16).natDegree := by
      rw [h16]
      have h1 : (Polynomial.C c1 * Polynomial.X ^ 4).natDegree ≤ 4 := by
        by_cases hc1 : c1 = 0
        · simp [hc1]
        · rw [Polynomial.natDegree_C_mul_X_pow 4 c1 hc1]
      have h0 : (Polynomial.C c0 * Polynomial.X).natDegree ≤ 1 := by
        by_cases hc0 : c0 = 0
        · simp [hc0]
        · rw [Polynomial.natDegree_C_mul_X c0 hc0]
      calc (Polynomial.C c1 * Polynomial.X ^ 4 +
            Polynomial.C c0 * Polynomial.X).natDegree
          ≤ max (Polynomial.C c1 * Polynomial.X ^ 4).natDegree
              (Polynomial.C c0 * Polynomial.X).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ max 4 1 := max_le_max h1 h0
        _ < 16 := by norm_num
    dsimp [q]
    rw [add_assoc]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlow]
    exact h16
  have hq_ne_zero : q ≠ 0 := by
    intro h
    rw [h] at hq_deg
    norm_num at hq_deg
  let S : Finset F := Finset.univ.filter (fun l : F => l ^ 4 = l)
  have hS_card : S.card = 4 := by
    let p : F[X] := Polynomial.X ^ 4 - Polynomial.X
    have hp_deg : p.natDegree = 4 := by
      dsimp [p]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · simpa using Polynomial.natDegree_X_pow (R := F) 4
      · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
        norm_num
    have hp_ne : p ≠ 0 := by
      intro h
      rw [h] at hp_deg
      norm_num at hp_deg
    have hS_sub_roots : S.val ⊆ p.roots := by
      intro a ha
      have ha' : a ^ 4 = a := by simpa [S] using ha
      rw [Polynomial.mem_roots hp_ne, Polynomial.IsRoot.def, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, ha', sub_self]
    have hS_card_le : S.card ≤ 4 := by
      have h := Polynomial.card_le_degree_of_subset_roots hS_sub_roots
      rw [hp_deg] at h
      exact h
    obtain ⟨ω, hω⟩ := CFSG.RankThree.PartTwo.Sec19.NF5Pair.exists_omega (F := F)
      (by rw [Nat.card_eq_fintype_card, hF]; norm_num)
    have hsq : ω ^ 2 = ω + 1 := by
      have h1 : ω ^ 2 + ω = 1 := by
        have := eq_neg_of_add_eq_zero_left hω
        rwa [CharTwo.neg_eq] at this
      have h2 := congrArg (fun x : F => x + ω) h1
      have h3 : ω ^ 2 + ω + ω = ω ^ 2 := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [h3, add_comm] at h2
      exact h2
    have hω0 : ω ≠ 0 := by
      intro h
      rw [h] at hsq
      have h1 : (0 : F) = 1 := by simpa using hsq
      exact zero_ne_one h1
    have hω1 : ω ≠ 1 := by
      intro h
      rw [h] at hsq
      have h1 : (1 : F) = 0 := by
        have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
        simpa [h2] using hsq
      exact one_ne_zero h1
    have hω2 : ω ^ 2 ≠ 1 := by
      intro h
      rw [h] at hsq
      apply hω0
      have h2 : ω + 1 = 0 + 1 := by rw [zero_add]; exact hsq.symm
      exact add_right_cancel h2
    have hω20 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
    have hne : ω ^ 2 ≠ ω := by
      intro h
      rw [h] at hsq
      have h2 : ω + 0 = ω + 1 := by rw [add_zero]; exact hsq
      exact zero_ne_one (add_left_cancel h2)
    have hω3 : ω ^ 3 = 1 := by
      calc ω ^ 3 = ω * ω ^ 2 := by ring
        _ = ω * (ω + 1) := by rw [hsq]
        _ = ω ^ 2 + ω := by ring
        _ = (ω + 1) + ω := by rw [hsq]
        _ = 1 := by
          rw [add_comm (ω + 1) ω, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have h4 : ω ^ 4 = ω := by
      calc ω ^ 4 = ω ^ 3 * ω := by ring
        _ = 1 * ω := by rw [hω3]
        _ = ω := by ring
    have h4sq : (ω ^ 2) ^ 4 = ω ^ 2 := by
      calc (ω ^ 2) ^ 4 = (ω ^ 4) ^ 2 := by ring
        _ = ω ^ 2 := by rw [h4]
    let T_F : Finset F := {0, 1, ω, ω ^ 2}
    have hT_F_sub : T_F ⊆ S := by
      intro a ha
      simp only [T_F, Finset.mem_insert, Finset.mem_singleton] at ha
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases ha with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact h4
      · exact h4sq
    have hT_F_card : T_F.card = 4 := by
      simp only [T_F]
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · simpa using hne.symm
        · simp [hω1.symm, hω2.symm]
      · simp [zero_ne_one, hω0.symm, hω20.symm]
    have hT_F_card_le : T_F.card ≤ S.card := Finset.card_le_card hT_F_sub
    rw [hT_F_card] at hT_F_card_le
    exact le_antisymm hS_card_le hT_F_card_le
  let R : Finset F := S.product S |>.image (fun p => p.1 * x + p.2 * y)
  have hR_card : R.card = 16 := by
    have hinj : Set.InjOn (fun p : F × F => p.1 * x + p.2 * y) (↑(S ×ˢ S) : Set (F × F)) := by
      intro p hp q hq h_eq
      have hp' : p.1 ∈ S ∧ p.2 ∈ S := by
        simpa only [Finset.mem_coe, Finset.mem_product] using hp
      have hq' : q.1 ∈ S ∧ q.2 ∈ S := by
        simpa only [Finset.mem_coe, Finset.mem_product] using hq
      have hp1 : p.1 ^ 4 = p.1 := by simpa [S] using hp'.1
      have hp2 : p.2 ^ 4 = p.2 := by simpa [S] using hp'.2
      have hq1 : q.1 ^ 4 = q.1 := by simpa [S] using hq'.1
      have hq2 : q.2 ^ 4 = q.2 := by simpa [S] using hq'.2
      have := plane_param_injective x y p.1 p.2 q.1 q.2 hx hxy hp1 hp2 hq1 hq2 h_eq
      exact Prod.ext this.1 this.2
    dsimp [R]
    rw [Finset.card_image_of_injOn hinj]
    simp [Finset.card_product, hS_card]
  have hR_roots : ∀ r ∈ R, q.eval r = 0 := by
    intro r hr
    simp only [R] at hr
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    have hp' : p.1 ∈ S ∧ p.2 ∈ S := Finset.mem_product.mp hp
    have hp1' : p.1 ^ 4 = p.1 := by simpa [S] using hp'.1
    have hp2' : p.2 ^ 4 = p.2 := by simpa [S] using hp'.2
    have hzero := plane_P_eq_zero (E := E) x y p.1 p.2 hp1' hp2'
    have hq_eval_zero : algebraMap F E (q.eval (p.1 * x + p.2 * y)) = 0 := by
      simpa [q, c0, c1, c2, map_add, map_mul, map_pow, add_comm, add_left_comm, add_assoc]
        using hzero
    exact (algebraMap F E).injective (by simpa using hq_eval_zero)
  intro hz0
  have hz_root : q.eval z = 0 := by
    simp [q, c0, c1, c2, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X]
    simp only [c0, c1, c2] at hz0
    ring_nf at hz0 ⊢
    exact hz0
  have hz_not_mem : z ∉ R := by
    intro h
    simp only [R] at h
    rcases Finset.mem_image.mp h with ⟨p, hp, h_eq⟩
    have hp' : p.1 ∈ S ∧ p.2 ∈ S := Finset.mem_product.mp hp
    have hp1' : p.1 ^ 4 = p.1 := by simpa [S] using hp'.1
    have hp2' : p.2 ^ 4 = p.2 := by simpa [S] using hp'.2
    exact hz p.1 p.2 hp1' hp2' h_eq.symm
  have h_union_card : (insert z R).card = 17 := by
    simp [Finset.card_insert_of_notMem hz_not_mem, hR_card]
  have h_union_roots : (insert z R).val ⊆ q.roots := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rw [Polynomial.mem_roots hq_ne_zero, Polynomial.IsRoot.def]
      exact hz_root
    · rw [Polynomial.mem_roots hq_ne_zero, Polynomial.IsRoot.def]
      exact hR_roots a ha
  have h_contra : 17 ≤ q.natDegree := by
    have h := Polynomial.card_le_degree_of_subset_roots h_union_roots
    rw [h_union_card] at h
    exact h
  rw [hq_deg] at h_contra
  norm_num at h_contra

private lemma model_024_plane (hF : Fintype.card F = 2 ^ 6) (x y z : F) (hx : x ≠ 0)
    (hxy : x * y ^ 4 ≠ y * x ^ 4)
    (hz : ∀ l l' : F, l ^ 4 = l → l' ^ 4 = l' → z ≠ l * x + l' * y) :
    ∃ v : (({0, 2, 4} : Finset ℕ) → Fin 2) → E,
      (∀ l l' : F, l ^ 4 = l → l' ^ 4 = l' →
        frobTensor F E ({0, 2, 4} : Finset ℕ) (uElt (l * x + l' * y)) v = v) ∧
      frobTensor F E ({0, 2, 4} : Finset ℕ) (uElt z) v ≠ v := by
  classical
  let X : E := algebraMap F E x
  let Y : E := algebraMap F E y
  let j0 : ({0, 2, 4} : Finset ℕ) := ⟨0, by simp⟩
  let j1 : ({0, 2, 4} : Finset ℕ) := ⟨2, by simp⟩
  let j2 : ({0, 2, 4} : Finset ℕ) := ⟨4, by simp⟩
  let a0 : E := X ^ 4 * Y ^ 16 + X ^ 16 * Y ^ 4
  let a1 : E := X ^ 16 * Y + X * Y ^ 16
  let a2 : E := X * Y ^ 4 + X ^ 4 * Y
  let v : (({0, 2, 4} : Finset ℕ) → Fin 2) → E :=
    a0 • (Pi.single (Pi.single j0 (1 : Fin 2) :
        ({0, 2, 4} : Finset ℕ) → Fin 2) (1 : E)) +
      a1 • (Pi.single (Pi.single j1 (1 : Fin 2) :
        ({0, 2, 4} : Finset ℕ) → Fin 2) (1 : E)) +
      a2 • (Pi.single (Pi.single j2 (1 : Fin 2) :
        ({0, 2, 4} : Finset ℕ) → Fin 2) (1 : E))
  refine ⟨v, ?_, ?_⟩
  · intro l l' hl hl'
    have hcomb := frobTensor_uElt_combine3 ({0, 2, 4} : Finset ℕ) (l * x + l' * y) j0 j1 j2 a0 a1 a2
    rw [hcomb]
    have hL : (algebraMap F E l) ^ 4 = algebraMap F E l := by rw [← map_pow, hl]
    have hL' : (algebraMap F E l') ^ 4 = algebraMap F E l' := by rw [← map_pow, hl']
    have hL16 : (algebraMap F E l) ^ 16 = algebraMap F E l := by
      rw [show (16 : ℕ) = 4 * 4 by norm_num, pow_mul, hL, hL]
    have hL16' : (algebraMap F E l') ^ 16 = algebraMap F E l' := by
      rw [show (16 : ℕ) = 4 * 4 by norm_num, pow_mul, hL', hL']
    have hzero : a0 * (algebraMap F E (l * x + l' * y)) ^ (2 ^ (j0 : ℕ)) +
        a1 * (algebraMap F E (l * x + l' * y)) ^ (2 ^ (j1 : ℕ)) +
        a2 * (algebraMap F E (l * x + l' * y)) ^ (2 ^ (j2 : ℕ)) = 0 := by
      simp only [j0, j1, j2]
      norm_num
      let Z : E := algebraMap F E l * X + algebraMap F E l' * Y
      change a0 * Z + a1 * Z ^ 4 + a2 * Z ^ 16 = 0
      have hX : a0 * X + a1 * X ^ 4 + a2 * X ^ 16 = 0 := by
        simp only [a0, a1, a2]
        ring_nf
        rw [show (2 : E) = 0 from CharP.cast_eq_zero E 2]
        ring
      have hY : a0 * Y + a1 * Y ^ 4 + a2 * Y ^ 16 = 0 := by
        simp only [a0, a1, a2]
        ring_nf
        rw [show (2 : E) = 0 from CharP.cast_eq_zero E 2]
        ring
      have hZ4eq : Z ^ 4 = algebraMap F E l * X ^ 4 + algebraMap F E l' * Y ^ 4 := by
        dsimp [Z]
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, add_pow_char_pow]
        norm_num
        rw [mul_pow, mul_pow, hL, hL']
      have hZ16eq : Z ^ 16 = algebraMap F E l * X ^ 16 + algebraMap F E l' * Y ^ 16 := by
        dsimp [Z]
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, add_pow_char_pow]
        norm_num
        rw [mul_pow, mul_pow, hL16, hL16']
      rw [hZ4eq, hZ16eq]
      dsimp [Z]
      calc a0 * ((algebraMap F E l) * X + (algebraMap F E l') * Y) +
            a1 * ((algebraMap F E l) * X ^ 4 + (algebraMap F E l') * Y ^ 4) +
            a2 * ((algebraMap F E l) * X ^ 16 + (algebraMap F E l') * Y ^ 16)
          = algebraMap F E l * (a0 * X + a1 * X ^ 4 + a2 * X ^ 16) +
            algebraMap F E l' * (a0 * Y + a1 * Y ^ 4 + a2 * Y ^ 16) := by ring
        _ = algebraMap F E l * 0 + algebraMap F E l' * 0 := by rw [hX, hY]
        _ = 0 := by simp
    rw [hzero, zero_smul, add_zero]
  · intro hbad
    let Z : E := algebraMap F E z
    have hcomb := frobTensor_uElt_combine3 ({0, 2, 4} : Finset ℕ) z j0 j1 j2 a0 a1 a2
    rw [hcomb] at hbad
    have hbase : (baseVec : (({0, 2, 4} : Finset ℕ) → Fin 2) → E) ≠ 0 := by
      intro h
      have h1 := congrFun h (0 : ({0, 2, 4} : Finset ℕ) → Fin 2)
      rw [baseVec_apply] at h1
      simp at h1
      exact h1 rfl
    have h3 : (a0 * Z ^ (2 ^ (j0 : ℕ)) + a1 * Z ^ (2 ^ (j1 : ℕ)) +
        a2 * Z ^ (2 ^ (j2 : ℕ))) • (baseVec : (({0, 2, 4} : Finset ℕ) → Fin 2) → E) = 0 := by
      have h2 : v + (a0 * Z ^ (2 ^ (j0 : ℕ)) + a1 * Z ^ (2 ^ (j1 : ℕ)) +
          a2 * Z ^ (2 ^ (j2 : ℕ))) • (baseVec : (({0, 2, 4} : Finset ℕ) → Fin 2) → E) = v + 0 := by
        rw [add_zero]
        exact hbad
      exact add_left_cancel h2
    have hZ : a0 * Z + a1 * Z ^ 4 + a2 * Z ^ 16 = 0 := by
      have hc := (smul_eq_zero.mp h3).resolve_right hbase
      simpa [j0, j1, j2] using hc
    have hmap : algebraMap F E ((x ^ 4 * y ^ 16 + x ^ 16 * y ^ 4) * z +
        (x ^ 16 * y + x * y ^ 16) * z ^ 4 +
        (x * y ^ 4 + x ^ 4 * y) * z ^ 16) = 0 := by
      simpa [a0, a1, a2, Z, map_add, map_mul, map_pow] using hZ
    have hq : (x ^ 4 * y ^ 16 + x ^ 16 * y ^ 4) * z +
        (x ^ 16 * y + x * y ^ 16) * z ^ 4 +
        (x * y ^ 4 + x ^ 4 * y) * z ^ 16 = 0 := by
      exact (algebraMap F E).injective (by simpa using hmap)
    exact plane_P_ne_zero E hF x y z hx hxy hz hq

private lemma plane_P_sq (a0 a1 a2 T : E) :
    a0 ^ 2 * T ^ 2 + a1 ^ 2 * T ^ 8 + a2 ^ 2 * T ^ 32 =
      (a0 * T + a1 * T ^ 4 + a2 * T ^ 16) ^ 2 := by
  ring_nf
  rw [show (2 : E) = 0 from CharP.cast_eq_zero E 2]
  ring

private lemma model_135_plane (hF : Fintype.card F = 2 ^ 6) (x y z : F) (hx : x ≠ 0)
    (hxy : x * y ^ 4 ≠ y * x ^ 4)
    (hz : ∀ l l' : F, l ^ 4 = l → l' ^ 4 = l' → z ≠ l * x + l' * y) :
    ∃ v : (({1, 3, 5} : Finset ℕ) → Fin 2) → E,
      (∀ l l' : F, l ^ 4 = l → l' ^ 4 = l' →
        frobTensor F E ({1, 3, 5} : Finset ℕ) (uElt (l * x + l' * y)) v = v) ∧
      frobTensor F E ({1, 3, 5} : Finset ℕ) (uElt z) v ≠ v := by
  classical
  let X : E := algebraMap F E x
  let Y : E := algebraMap F E y
  let j0 : ({1, 3, 5} : Finset ℕ) := ⟨1, by simp⟩
  let j1 : ({1, 3, 5} : Finset ℕ) := ⟨3, by simp⟩
  let j2 : ({1, 3, 5} : Finset ℕ) := ⟨5, by simp⟩
  let a0 : E := X ^ 4 * Y ^ 16 + X ^ 16 * Y ^ 4
  let a1 : E := X ^ 16 * Y + X * Y ^ 16
  let a2 : E := X * Y ^ 4 + X ^ 4 * Y
  let b0 : E := a0 ^ 2
  let b1 : E := a1 ^ 2
  let b2 : E := a2 ^ 2
  let v : (({1, 3, 5} : Finset ℕ) → Fin 2) → E :=
    b0 • (Pi.single (Pi.single j0 (1 : Fin 2) :
        ({1, 3, 5} : Finset ℕ) → Fin 2) (1 : E)) +
      b1 • (Pi.single (Pi.single j1 (1 : Fin 2) :
        ({1, 3, 5} : Finset ℕ) → Fin 2) (1 : E)) +
      b2 • (Pi.single (Pi.single j2 (1 : Fin 2) :
        ({1, 3, 5} : Finset ℕ) → Fin 2) (1 : E))
  refine ⟨v, ?_, ?_⟩
  · intro l l' hl hl'
    have hcomb := frobTensor_uElt_combine3 ({1, 3, 5} : Finset ℕ) (l * x + l' * y) j0 j1 j2 b0 b1 b2
    rw [hcomb]
    have hzero : b0 * (algebraMap F E (l * x + l' * y)) ^ (2 ^ (j0 : ℕ)) +
        b1 * (algebraMap F E (l * x + l' * y)) ^ (2 ^ (j1 : ℕ)) +
        b2 * (algebraMap F E (l * x + l' * y)) ^ (2 ^ (j2 : ℕ)) = 0 := by
      simp only [j0, j1, j2]
      norm_num
      let Z : E := algebraMap F E l * X + algebraMap F E l' * Y
      change b0 * Z ^ 2 + b1 * Z ^ 8 + b2 * Z ^ 32 = 0
      have h024 : a0 * Z + a1 * Z ^ 4 + a2 * Z ^ 16 = 0 := by
        simpa only [X, Y, Z, a0, a1, a2, map_add, map_mul]
          using plane_P_eq_zero (E := E) x y l l' hl hl'
      simpa [b0, b1, b2, plane_P_sq, h024]
    rw [hzero, zero_smul, add_zero]
  · intro hbad
    let Z : E := algebraMap F E z
    have hcomb := frobTensor_uElt_combine3 ({1, 3, 5} : Finset ℕ) z j0 j1 j2 b0 b1 b2
    rw [hcomb] at hbad
    have hbase : (baseVec : (({1, 3, 5} : Finset ℕ) → Fin 2) → E) ≠ 0 := by
      intro h
      have h1 := congrFun h (0 : ({1, 3, 5} : Finset ℕ) → Fin 2)
      rw [baseVec_apply] at h1
      simp at h1
      exact h1 rfl
    have h3 : (b0 * Z ^ (2 ^ (j0 : ℕ)) + b1 * Z ^ (2 ^ (j1 : ℕ)) +
        b2 * Z ^ (2 ^ (j2 : ℕ))) •
        (baseVec : (({1, 3, 5} : Finset ℕ) → Fin 2) → E) = 0 := by
      have h2 : v + (b0 * Z ^ (2 ^ (j0 : ℕ)) + b1 * Z ^ (2 ^ (j1 : ℕ)) +
          b2 * Z ^ (2 ^ (j2 : ℕ))) •
          (baseVec : (({1, 3, 5} : Finset ℕ) → Fin 2) → E) = v + 0 := by
        rw [add_zero]
        exact hbad
      exact add_left_cancel h2
    have hZsq : b0 * Z ^ 2 + b1 * Z ^ 8 + b2 * Z ^ 32 = 0 := by
      have hc := (smul_eq_zero.mp h3).resolve_right hbase
      simpa [j0, j1, j2] using hc
    have hZ : a0 * Z + a1 * Z ^ 4 + a2 * Z ^ 16 = 0 := by
      have hsq : (a0 * Z + a1 * Z ^ 4 + a2 * Z ^ 16) ^ 2 = 0 := by
        simpa [b0, b1, b2, plane_P_sq] using hZsq
      exact sq_eq_zero_iff.mp hsq
    have hmap : algebraMap F E ((x ^ 4 * y ^ 16 + x ^ 16 * y ^ 4) * z +
        (x ^ 16 * y + x * y ^ 16) * z ^ 4 +
        (x * y ^ 4 + x ^ 4 * y) * z ^ 16) = 0 := by
      simpa [a0, a1, a2, Z, map_add, map_mul, map_pow] using hZ
    have hq : (x ^ 4 * y ^ 16 + x ^ 16 * y ^ 4) * z +
        (x ^ 16 * y + x * y ^ 16) * z ^ 4 +
        (x * y ^ 4 + x ^ 4 * y) * z ^ 16 = 0 := by
      exact (algebraMap F E).injective (by simpa using hmap)
    exact plane_P_ne_zero E hF x y z hx hxy hz hq

end PlaneModel

section Tensor

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]

theorem exists_fixW_line_moved (hF : Fintype.card F = 2 ^ 6) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E] [Finite E] [CharP E 2]
    (ιF : F →+* E) (ιD : EndRing ρ →+* E) (J : Finset ℕ) (hJ : J = {0, 2, 4} ∨ J = {1, 3, 5})
    (Φ : (letI := ιF.toAlgebra; (matRepE b ιD).Equiv (frobTensor F E J))) {x y : F}
    (hx : x ≠ 0) (hxy : x * y ^ 4 ≠ y * x ^ 4) :
    ∃ w : W, (∀ l : F, l ^ 4 = l → ρ (uElt (l * x)) w = w) ∧ ρ (uElt y) w ≠ w := by
  classical
  letI : Algebra F E := ιF.toAlgebra
  have hmodel : ∃ v : (J → Fin 2) → E,
      (∀ l : F, l ^ 4 = l → frobTensor F E J (uElt (l * x)) v = v) ∧
      frobTensor F E J (uElt y) v ≠ v := by
    rcases hJ with rfl | rfl
    · exact model_024 x y hx hxy
    · exact model_135 x y hx hxy
  obtain ⟨v, hvfix, hvmove⟩ := hmodel
  by_contra hcon
  push Not at hcon
  let κ := {l : F // l ^ 4 = l}
  let s1 : κ → SL(2, F) := fun l => uElt (l.1 * x)
  let s2 : Option κ → SL(2, F) := fun o => match o with
    | none => uElt y
    | some l => s1 l
  have hcard1 := natCard_fixW_pow ρ b s1 ιF ιD J Φ
  have hcard2 := natCard_fixW_pow ρ b s2 ιF ιD J Φ
  have hKD : Nat.card {w : W // ∀ a : κ, ρ (s1 a) w = w} =
      Nat.card {w : W // ∀ a : Option κ, ρ (s2 a) w = w} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro w
    constructor
    · intro hw a
      cases a with
      | none => exact hcon w (fun l hl => hw ⟨l, hl⟩)
      | some l => exact hw l
    · intro hw l
      exact hw (some l)
  have hlt : Nat.card {y : (J → Fin 2) → E // ∀ a : Option κ,
        frobTensor F E J (s2 a) y = y} <
      Nat.card {y : (J → Fin 2) → E // ∀ a : κ, frobTensor F E J (s1 a) y = y} := by
    change ({y : (J → Fin 2) → E | ∀ a : Option κ,
      frobTensor F E J (s2 a) y = y} : Set ((J → Fin 2) → E)).ncard <
      ({y : (J → Fin 2) → E | ∀ a : κ, frobTensor F E J (s1 a) y = y} :
        Set ((J → Fin 2) → E)).ncard
    refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
    refine ⟨?_, ?_⟩
    · intro y hy l
      exact hy (some l)
    · intro hsub
      have hv1 : v ∈ {y : (J → Fin 2) → E | ∀ a : κ, frobTensor F E J (s1 a) y = y} :=
        fun l => hvfix l l.2
      exact hvmove ((hsub hv1) none)
  rw [hKD] at hcard1
  omega

theorem exists_fixW_plane_moved (hF : Fintype.card F = 2 ^ 6) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E] [Finite E] [CharP E 2]
    (ιF : F →+* E) (ιD : EndRing ρ →+* E) (J : Finset ℕ) (hJ : J = {0, 2, 4} ∨ J = {1, 3, 5})
    (Φ : (letI := ιF.toAlgebra; (matRepE b ιD).Equiv (frobTensor F E J))) {x y z : F}
    (hx : x ≠ 0) (hxy : x * y ^ 4 ≠ y * x ^ 4)
    (hz : ∀ l l' : F, l ^ 4 = l → l' ^ 4 = l' → z ≠ l * x + l' * y) :
    ∃ w : W, (∀ l l' : F, l ^ 4 = l → l' ^ 4 = l' → ρ (uElt (l * x + l' * y)) w = w) ∧
      ρ (uElt z) w ≠ w := by
  classical
  letI : Algebra F E := ιF.toAlgebra
  have hmodel : ∃ v : (J → Fin 2) → E,
      (∀ l l' : F, l ^ 4 = l → l' ^ 4 = l' →
        frobTensor F E J (uElt (l * x + l' * y)) v = v) ∧
      frobTensor F E J (uElt z) v ≠ v := by
    rcases hJ with rfl | rfl
    · exact model_024_plane hF x y z hx hxy hz
    · exact model_135_plane hF x y z hx hxy hz
  obtain ⟨v, hvfix, hvmove⟩ := hmodel
  by_contra hcon
  push Not at hcon
  let κ := {l : F // l ^ 4 = l} × {l : F // l ^ 4 = l}
  let s1 : κ → SL(2, F) := fun p => uElt (p.1.1 * x + p.2.1 * y)
  let s2 : Option κ → SL(2, F) := fun o => match o with
    | none => uElt z
    | some p => s1 p
  have hcard1 := natCard_fixW_pow ρ b s1 ιF ιD J Φ
  have hcard2 := natCard_fixW_pow ρ b s2 ιF ιD J Φ
  have hKD : Nat.card {w : W // ∀ a : κ, ρ (s1 a) w = w} =
      Nat.card {w : W // ∀ a : Option κ, ρ (s2 a) w = w} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro w
    constructor
    · intro hw a
      cases a with
      | none => exact hcon w (fun l l' hl hl' => hw ⟨⟨l, hl⟩, ⟨l', hl'⟩⟩)
      | some p => exact hw p
    · intro hw p
      exact hw (some p)
  have hlt : Nat.card {y : (J → Fin 2) → E // ∀ a : Option κ,
        frobTensor F E J (s2 a) y = y} <
      Nat.card {y : (J → Fin 2) → E // ∀ a : κ, frobTensor F E J (s1 a) y = y} := by
    change ({y : (J → Fin 2) → E | ∀ a : Option κ,
      frobTensor F E J (s2 a) y = y} : Set ((J → Fin 2) → E)).ncard <
      ({y : (J → Fin 2) → E | ∀ a : κ, frobTensor F E J (s1 a) y = y} :
        Set ((J → Fin 2) → E)).ncard
    refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
    refine ⟨?_, ?_⟩
    · intro y hy p
      exact hy (some p)
    · intro hsub
      have hv1 : v ∈ {y : (J → Fin 2) → E | ∀ a : κ, frobTensor F E J (s1 a) y = y} :=
        fun p => hvfix p.1.1 p.2.1 p.1.2 p.2.2
      exact hvmove ((hsub hv1) none)
  rw [hKD] at hcard1
  omega

end Tensor

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
