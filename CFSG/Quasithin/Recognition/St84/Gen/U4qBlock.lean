module

public import CFSG.Quasithin.H13.U4ParOuterO2
public import CFSG.Quasithin.Vol2.Ch6OrthIrred
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.JonesParshall
open scoped commutatorElement

variable {m : ℕ} {K : Type} [Field K]

private def q2Nil (C : Matrix (Fin 2) (Fin 2) K) : Matrix Ix Ix K :=
  single ie1 if1 (C 0 0) + single ie1 if2 (C 0 1) + single ie2 if1 (C 1 0) +
    single ie2 if2 (C 1 1)

private def q2Mat (C : Matrix (Fin 2) (Fin 2) K) : Matrix Ix Ix K := 1 + q2Nil C

private theorem q2Mat_apply (C : Matrix (Fin 2) (Fin 2) K) (i j : Ix) :
    q2Mat C i j = (1 : Matrix Ix Ix K) i j + (if ie1 = i ∧ if1 = j then C 0 0 else 0) +
      (if ie1 = i ∧ if2 = j then C 0 1 else 0) +
      (if ie2 = i ∧ if1 = j then C 1 0 else 0) +
      (if ie2 = i ∧ if2 = j then C 1 1 else 0) := by
  simp only [q2Mat, q2Nil, Matrix.add_apply, Matrix.single_apply]
  ring_nf

private theorem q2Nil_add (C C' : Matrix (Fin 2) (Fin 2) K) :
    q2Nil (C + C') = q2Nil C + q2Nil C' := by
  ext i j
  simp only [q2Nil, Matrix.add_apply, Matrix.single_add]
  abel

private theorem q2Nil_mul (C C' : Matrix (Fin 2) (Fin 2) K) : q2Nil C * q2Nil C' = 0 := by
  ext i j
  rw [Matrix.mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;>
    rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [q2Nil, Matrix.single_apply]

private theorem q2Mat_mul (C C' : Matrix (Fin 2) (Fin 2) K) :
    q2Mat C * q2Mat C' = q2Mat (C + C') := by
  have h : q2Mat C * q2Mat C' = 1 + (q2Nil C + q2Nil C') := by
    rw [q2Mat, q2Mat, add_mul, one_mul, mul_add, mul_one, q2Nil_mul, add_zero]
    abel
  rw [h, q2Mat, q2Nil_add]

private theorem q2Mat_zero : q2Mat (0 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [q2Mat, q2Nil]
  simp

private theorem q2Mat_self_mul [CharP K 2] (C : Matrix (Fin 2) (Fin 2) K) :
    q2Mat C * q2Mat C = 1 := by
  rw [q2Mat_mul, CharTwo.add_self_eq_zero, q2Mat_zero]

private theorem det_q2Mat [CharP K 2] (C : Matrix (Fin 2) (Fin 2) K) :
    (q2Mat C).det = 1 := by
  have hN : IsNilpotent (q2Nil C) := ⟨2, by rw [pow_two]; exact q2Nil_mul C C⟩
  have h : q2Mat C = 1 + q2Nil C := rfl
  rw [h]
  exact CFSG.LieType.BorelTits.det_one_add_of_isNilpotent 2 hN

private theorem q2Mat_gram [CharP K 2] (h : UnitaryFieldData 2 m K)
    (C : Matrix (Fin 2) (Fin 2) K) (hC : C ∈ hermA m K) :
    ((q2Mat C).map h.bar)ᵀ * hypGram 2 0 K * q2Mat C = hypGram 2 0 K := by
  have hCc : ∀ i j : Fin 2, h.bar (C j i) = C i j := by
    intro i j
    have h := mem_hermA.mp hC
    have := congrFun (congrFun h i) j
    simpa [frobPow, transpose_apply, UnitaryFieldData.bar_apply] using this
  ext i j
  rw [Matrix.mul_apply, sum_ix]
  simp only [mul_hypGram_apply, transpose_apply, map_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;>
    rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [q2Mat_apply, one_apply, hypGram_apply, hCc] <;> grind

private noncomputable def q2Elt [CharP K 2] (h : UnitaryFieldData 2 m K)
    (C : Matrix (Fin 2) (Fin 2) K) (hC : C ∈ hermA m K) : hypSU h 2 0 :=
  ⟨⟨q2Mat C, q2Mat C, q2Mat_self_mul C, q2Mat_self_mul C⟩,
    mem_gramSU.mpr ⟨q2Mat_gram h C hC, det_q2Mat C⟩⟩

private theorem coe_q2Elt [CharP K 2] (h : UnitaryFieldData 2 m K)
    (C : Matrix (Fin 2) (Fin 2) K)
    (hC : C ∈ hermA m K) :
    (((q2Elt h C hC : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = q2Mat C := rfl

private theorem q2Elt_mem_radQ [CharP K 2] (h : UnitaryFieldData 2 m K)
    (C : Matrix (Fin 2) (Fin 2) K)
    (hC : C ∈ hermA m K) : q2Elt h C hC ∈ radQ2 h := by
  change IsQ2Mat (q2Mat C)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [q2Mat_apply, one_apply]

private theorem sq_eq_one_of_mem_radQ2 (h : UnitaryFieldData 2 m K) {g : hypSU h 2 0}
    (hg : g ∈ radQ2 h) : g ^ 2 = 1 := by
  have := h.charP
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hg
  apply Subtype.ext
  apply Units.ext
  change ((((g : hypSU h 2 0) ^ 2 : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = 1
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, sq]
  ext i j
  rw [Matrix.mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;>
    rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, CharTwo.add_self_eq_zero]

noncomputable def q2Blk (h : UnitaryFieldData 2 m K) (g : hypSU h 2 0) :
    Matrix (Fin 2) (Fin 2) K :=
  of fun i j => ((g : GL Ix K) : Matrix Ix Ix K)
    (if i = 0 then ie1 else ie2) (if j = 0 then if1 else if2)

private theorem q2Blk_q2Elt [CharP K 2] (h : UnitaryFieldData 2 m K)
    (C : Matrix (Fin 2) (Fin 2) K) (hC : C ∈ hermA m K) :
    q2Blk h (q2Elt h C hC) = C := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [q2Blk, coe_q2Elt, q2Mat_apply, one_apply]

private theorem q2Blk_one (h : UnitaryFieldData 2 m K) :
    q2Blk h (1 : hypSU h 2 0) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [q2Blk, ie1, ie2, if1, if2]

private theorem coe_eq_q2Mat_of_mem_radQ2 (h : UnitaryFieldData 2 m K)
    {q : hypSU h 2 0} (hq : q ∈ radQ2 h) :
    ((q : GL Ix K) : Matrix Ix Ix K) = q2Mat (q2Blk h q) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hq
  ext i j
  rcases ix_cases i with rfl | rfl | rfl | rfl <;>
    rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [q2Blk, q2Mat_apply, one_apply, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]

theorem q2Blk_mem_herm [CharP K 2] (h : UnitaryFieldData 2 m K)
    {q : hypSU h 2 0} (hq : q ∈ radQ2 h) : q2Blk h q ∈ hermA m K := by
  rw [mem_hermA]
  have hgram := (mem_hypSU.mp q.2).1
  rw [coe_eq_q2Mat_of_mem_radQ2 h hq] at hgram
  ext i j
  change h.bar (q2Blk h q j i) = q2Blk h q i j
  fin_cases i <;> fin_cases j
  · have e := congrFun (congrFun hgram if1) if1
    rw [Matrix.mul_apply, sum_ix] at e
    simp only [mul_hypGram_apply, transpose_apply, map_apply] at e
    simp [q2Mat_apply, one_apply, hypGram_apply, frobPow, ie1, ie2, if1, if2] at e
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at e
    exact e.symm
  · have e := congrFun (congrFun hgram if1) if2
    rw [Matrix.mul_apply, sum_ix] at e
    simp only [mul_hypGram_apply, transpose_apply, map_apply] at e
    simp [q2Mat_apply, one_apply, hypGram_apply, frobPow, ie1, ie2, if1, if2] at e
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at e
    exact e.symm
  · have e := congrFun (congrFun hgram if2) if1
    rw [Matrix.mul_apply, sum_ix] at e
    simp only [mul_hypGram_apply, transpose_apply, map_apply] at e
    simp [q2Mat_apply, one_apply, hypGram_apply, frobPow, ie1, ie2, if1, if2] at e
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at e
    exact e.symm
  · have e := congrFun (congrFun hgram if2) if2
    rw [Matrix.mul_apply, sum_ix] at e
    simp only [mul_hypGram_apply, transpose_apply, map_apply] at e
    simp [q2Mat_apply, one_apply, hypGram_apply, frobPow, ie1, ie2, if1, if2] at e
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at e
    exact e.symm

theorem q2Blk_inj (h : UnitaryFieldData 2 m K) {q q' : hypSU h 2 0}
    (hq : q ∈ radQ2 h) (hq' : q' ∈ radQ2 h) (he : q2Blk h q = q2Blk h q') : q = q' := by
  apply hypSU_ext
  rw [coe_eq_q2Mat_of_mem_radQ2 h hq, coe_eq_q2Mat_of_mem_radQ2 h hq', he]

private theorem q2Blk_add (h : UnitaryFieldData 2 m K) {q q' : hypSU h 2 0}
    (hq : q ∈ radQ2 h) (hq' : q' ∈ radQ2 h) :
    q2Blk h (q * q') = q2Blk h q + q2Blk h q' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hq
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := hq'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [q2Blk, Matrix.of_apply, coe_mul_hypSU, Matrix.mul_apply, sum_ix,
      Matrix.add_apply] <;>
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, one_apply] <;> ring

private noncomputable def slInvMat (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

private abbrev eIdx (i : Fin 2) : Ix := if i = 0 then ie1 else ie2

private abbrev fIdx (j : Fin 2) : Ix := if j = 0 then if1 else if2

private theorem q2Nil_eq_sum (C : Matrix (Fin 2) (Fin 2) K) :
    q2Nil C = ∑ a : Fin 2, ∑ b : Fin 2, single (eIdx a) (fIdx b) (C a b) := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [q2Nil, eIdx, fIdx]
  abel

private theorem lev2Mat_e (h : UnitaryFieldData 2 m K) (A : Matrix (Fin 2) (Fin 2) K)
    (i a : Fin 2) : lev2Mat h A (eIdx i) (eIdx a) = A i a := by
  fin_cases i <;> fin_cases a <;> simp [eIdx, lev2Mat_apply]

private theorem slInvMat_def (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    slInvMat A = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

private theorem coe_inv_sl2 [CharP K 2] (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    slInvMat A = !![A.1 1 1, A.1 0 1; A.1 1 0, A.1 0 0] := by
  unfold slInvMat
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]

private theorem lev2Mat_inv_f [CharP K 2] (h : UnitaryFieldData 2 m K)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (b j : Fin 2) :
    lev2Mat h (slInvMat A) (fIdx b) (fIdx j) = h.bar (A.1 j b) := by
  rw [coe_inv_sl2 A]
  fin_cases b <;> fin_cases j <;>
    simp [fIdx, lev2Mat_apply, UnitaryFieldData.bar_apply]

private theorem lev2Mat_conj_single [CharP K 2] (h : UnitaryFieldData 2 m K)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (x : K) (a b i j : Fin 2) :
    (lev2Mat h A * single (eIdx a) (fIdx b) x * lev2Mat h (slInvMat A))
      (eIdx i) (fIdx j) = A i a * x * h.bar (A.1 j b) := by
  have h1 : ∀ k : Ix, (lev2Mat h A * single (eIdx a) (fIdx b) x) (eIdx i) k =
      if k = fIdx b then lev2Mat h A (eIdx i) (eIdx a) * x else 0 := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single (eIdx a)]
    · simp [Matrix.single_apply, eq_comm]
    · intro c _ hc
      have hc' : eIdx a ≠ c := fun h => hc h.symm
      simp [Matrix.single_apply, hc, hc']
    · intro h
      exact absurd (Finset.mem_univ (eIdx a)) h
  rw [Matrix.mul_apply]
  simp only [h1]
  rw [Finset.sum_eq_single (fIdx b)]
  · rw [lev2Mat_e, lev2Mat_inv_f]
    simp
  · intro c _ hc
    simp [hc]
  · intro h
    exact absurd (Finset.mem_univ (fIdx b)) h

private theorem lev2Mat_conj_q2Mat [CharP K 2] (h : UnitaryFieldData 2 m K)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K)
    (i j : Fin 2) :
    (lev2Mat h A * q2Mat C * lev2Mat h (slInvMat A)) (eIdx i) (fIdx j) =
      (A.1 * C * (A.1.map h.bar)ᵀ) i j := by
  have hmul : A.1 * slInvMat A = 1 := by
    have h : A * A⁻¹ = 1 := mul_inv_cancel A
    have hc := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) K =>
      (B : Matrix (Fin 2) (Fin 2) K)) h
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at hc
    simpa [slInvMat, Matrix.SpecialLinearGroup.coe_inv] using hc
  have hAinv : lev2Mat h A * lev2Mat h (slInvMat A) = 1 := by
    rw [lev2Mat_mul, hmul, lev2Mat_one]
  have h1 : (lev2Mat h A * q2Mat C * lev2Mat h (slInvMat A)) (eIdx i) (fIdx j) =
      (lev2Mat h A * q2Nil C * lev2Mat h (slInvMat A)) (eIdx i) (fIdx j) := by
    rw [show q2Mat C = 1 + q2Nil C from rfl, mul_add, mul_one, add_mul, Matrix.add_apply,
      hAinv]
    fin_cases i <;> fin_cases j <;> simp [eIdx, fIdx]
  rw [h1, q2Nil_eq_sum]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  rw [Matrix.sum_apply]
  simp only [Matrix.sum_apply, lev2Mat_conj_single]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  ring

private theorem q2Blk_conj_lev2 [CharP K 2] (h : UnitaryFieldData 2 m K)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) {q : hypSU h 2 0} (hq : q ∈ radQ2 h) :
    q2Blk h (lev2Hom h A * q * (lev2Hom h A)⁻¹) = twistActCh6 m A (q2Blk h q) := by
  have hmat : (((lev2Hom h A * q * (lev2Hom h A)⁻¹ : hypSU h 2 0) : GL Ix K) :
      Matrix Ix Ix K) = lev2Mat h A * q2Mat (q2Blk h q) * lev2Mat h (slInvMat A) := by
    rw [coe_mul_hypSU, coe_mul_hypSU,
      show (lev2Hom h A)⁻¹ = lev2Hom h (A⁻¹) from (map_inv (lev2Hom h) A).symm]
    rw [coe_lev2Hom, coe_lev2Hom, ← slInvMat_def]
    rw [coe_eq_q2Mat_of_mem_radQ2 h hq]
  ext i j
  simp only [q2Blk, Matrix.of_apply]
  rw [hmat]
  change (lev2Mat h A * q2Mat (q2Blk h q) * lev2Mat h (slInvMat A)) (eIdx i) (fIdx j) =
    twistActCh6 m A (q2Blk h q) i j
  rw [twistActCh6]
  have hfrob : frobPow m A.1 = A.1.map h.bar := by
    ext i j
    rfl
  rw [hfrob]
  exact lev2Mat_conj_q2Mat h A (q2Blk h q) i j

private theorem exists_radQ2_mul_rho2F (h : UnitaryFieldData 2 m K) {g : hypSU h 2 0}
    (hg : g ∈ parH2 h) :
    ∃ q ∈ radQ2 h, g = q * lev2Hom h (rho2F h ⟨g, hg⟩) := by
  let g' : hypSU h 2 0 := g * (lev2Hom h (rho2F h ⟨g, hg⟩))⁻¹
  have hg' : g' ∈ parH2 h :=
    (parH2 h).mul_mem hg ((parH2 h).inv_mem (lev2Hom_le_parH2 h ⟨_, rfl⟩))
  have hρ : rho2F h ⟨g', hg'⟩ = 1 := by
    have h1 : (⟨g', hg'⟩ : parH2 h) = ⟨g, hg⟩ *
        (⟨lev2Hom h (rho2F h ⟨g, hg⟩),
          lev2Hom_le_parH2 h ⟨_, rfl⟩⟩ : parH2 h)⁻¹ := by
      apply Subtype.ext
      rfl
    rw [h1, map_mul, map_inv, rho2F_lev2Hom, mul_inv_cancel]
  have hmat : rho2 h g' = 1 := by
    have h2 := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) K =>
      (B : Matrix (Fin 2) (Fin 2) K)) hρ
    change ((⟨rho2 h g', hg'.2⟩ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = ((1 : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) at h2
    simpa using h2
  refine ⟨g', mem_radQ2_of_rho2 h (parH2_le_parP2 h hg') hmat, ?_⟩
  show g = g * (lev2Hom h (rho2F h ⟨g, hg⟩))⁻¹ * lev2Hom h (rho2F h ⟨g, hg⟩)
  group

theorem q2Blk_conj_mem [CharP K 2] (h : UnitaryFieldData 2 m K)
    {ℓ : hypSU h 2 0} (hℓ : ℓ ∈ perfectCore (parP2 h)) {q : hypSU h 2 0}
    (hq : q ∈ radQ2 h) :
    q2Blk h (ℓ * q * ℓ⁻¹) =
      twistActCh6 m (rho2F h ⟨ℓ, perfectCore_parP2_le_parH2 h hℓ⟩) (q2Blk h q) := by
  set A : Matrix.SpecialLinearGroup (Fin 2) K :=
    rho2F h ⟨ℓ, perfectCore_parP2_le_parH2 h hℓ⟩ with hA
  obtain ⟨q₀, hq₀, hℓeq⟩ := exists_radQ2_mul_rho2F h (perfectCore_parP2_le_parH2 h hℓ)
  rw [← hA] at hℓeq
  rw [hℓeq]
  have hxq : lev2Hom h A * q * (lev2Hom h A)⁻¹ ∈ radQ2 h :=
    (Subgroup.mem_normalizer_iff.mp
      (parP2_le_normalizer_radQ2 h (lev2Hom_le_parP2 h ⟨A, rfl⟩)) q).mp hq
  have hq₀x : q₀ * (lev2Hom h A * q * (lev2Hom h A)⁻¹) * q₀⁻¹ =
      lev2Hom h A * q * (lev2Hom h A)⁻¹ := by
    have hc := radQ2_comm h hq₀ hxq
    calc q₀ * (lev2Hom h A * q * (lev2Hom h A)⁻¹) * q₀⁻¹
        = (lev2Hom h A * q * (lev2Hom h A)⁻¹) * q₀ * q₀⁻¹ := by
          rw [hc]
      _ = lev2Hom h A * q * (lev2Hom h A)⁻¹ := by rw [mul_inv_cancel_right]
  have hassoc : q₀ * lev2Hom h A * q * (q₀ * lev2Hom h A)⁻¹ =
      q₀ * (lev2Hom h A * q * (lev2Hom h A)⁻¹) * q₀⁻¹ := by group
  rw [hassoc, hq₀x, q2Blk_conj_lev2 h A hq]

private theorem mem_hermA_one [CharP K 2] : (1 : Matrix (Fin 2) (Fin 2) K) ∈ hermA m K := by
  rw [mem_hermA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow]

private theorem mem_hermA_E11 [CharP K 2] :
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) ∈ hermA m K := by
  rw [mem_hermA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow]

private theorem mem_hermA_E22 [CharP K 2] :
    (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) ∈ hermA m K := by
  rw [mem_hermA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow]

private theorem mem_hermA_off [CharP K 2] :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) ∈ hermA m K := by
  rw [mem_hermA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow]

private theorem eq_one_of_forall_twistAct [CharP K 2] (h : UnitaryFieldData 2 m K)
    (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (hA : ∀ C ∈ hermA m K, twistActCh6 m A C = C) : A = 1 := by
  have hA' : ∀ C ∈ hermA m K, A.1 * C * (A.1.map (fun x => x ^ 2 ^ m))ᵀ = C := by
    intro C hC
    have := hA C hC
    simpa [twistActCh6, frobPow] using this
  have h1mem : (1 : Matrix (Fin 2) (Fin 2) K) ∈ hermA m K := by
    rw [mem_hermA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frobPow]
  have hE11 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) ∈ hermA m K := by
    rw [mem_hermA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frobPow]
  have hoff : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) ∈ hermA m K := by
    rw [mem_hermA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frobPow]
  have hX : A.1 * (A.1.map (fun x => x ^ 2 ^ m))ᵀ = 1 := by
    simpa using hA' 1 h1mem
  have hXA : (A.1.map (fun x => x ^ 2 ^ m))ᵀ * A.1 = 1 := by
    have hu : IsUnit A.1.det := Matrix.isUnit_det_of_right_inverse hX
    have h1 : A.1⁻¹ = (A.1.map (fun x => x ^ 2 ^ m))ᵀ := Matrix.inv_eq_right_inv hX
    rw [← h1]
    exact Matrix.nonsing_inv_mul A.1 hu
  have hcomm : ∀ C ∈ hermA m K, A.1 * C = C * A.1 := by
    intro C hC
    have hAC := hA' C hC
    calc A.1 * C = A.1 * C * 1 := by rw [mul_one]
      _ = A.1 * C * ((A.1.map (fun x => x ^ 2 ^ m))ᵀ * A.1) := by rw [hXA]
      _ = (A.1 * C * (A.1.map (fun x => x ^ 2 ^ m))ᵀ) * A.1 := by noncomm_ring
      _ = C * A.1 := by rw [hAC]
  have h01 : A.1 0 1 = 0 := by
    have h := hcomm !![1, 0; 0, 0] hE11
    have e := congrFun (congrFun h 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] using e.symm
  have h10 : A.1 1 0 = 0 := by
    have h := hcomm !![1, 0; 0, 0] hE11
    have e := congrFun (congrFun h 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] using e
  have hdiag : A.1 0 0 = A.1 1 1 := by
    have h := hcomm !![0, 1; 1, 0] hoff
    have e := congrFun (congrFun h 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, h01, h10] using e
  have hsq : A.1 0 0 ^ 2 = 1 := by
    have hdet := A.2
    rw [Matrix.det_fin_two, h01, h10, hdiag] at hdet
    rw [pow_two, hdiag]
    simpa [sub_eq_add_neg, CharTwo.neg_eq] using hdet
  have h00 : A.1 0 0 = 1 := by
    rcases sq_eq_one_iff.mp hsq with h1 | h1
    · exact h1
    · rw [h1, CharTwo.neg_eq]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, hdiag, h01, h10, ← hdiag]

theorem radQ2_irreducible (h : UnitaryFieldData 2 m K)
    (W : Subgroup (hypSU h 2 0)) (hW : W ≤ radQ2 h)
    (hWN : (lev2Hom h).range ≤ Subgroup.normalizer (W : Set (hypSU h 2 0))) :
    W = ⊥ ∨ W = radQ2 h := by
  haveI := h.charP
  haveI := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hwQ : (w : hypSU h 2 0) ∈ radQ2 h := hW w.2
  have hwC : q2Blk h (w : hypSU h 2 0) ≠ 0 := by
    intro h0
    apply hw
    have hinj := q2Blk_inj h hwQ (hW (Subgroup.one_mem W)) (by rw [h0, q2Blk_one])
    exact Subtype.ext hinj
  let S : AddSubgroup (Matrix (Fin 2) (Fin 2) K) :=
    { carrier := {C | ∃ v : W, q2Blk h (v : hypSU h 2 0) = C}
      zero_mem' := ⟨1, q2Blk_one h⟩
      add_mem' := by
        rintro C C' ⟨v, rfl⟩ ⟨v', rfl⟩
        refine ⟨v * v', ?_⟩
        show q2Blk h ((v : hypSU h 2 0) * (v' : hypSU h 2 0)) =
          q2Blk h v + q2Blk h v'
        exact q2Blk_add h (hW v.2) (hW v'.2)
      neg_mem' := by
        rintro C ⟨v, rfl⟩
        refine ⟨v⁻¹, ?_⟩
        have hvq : ((v⁻¹ : W) : hypSU h 2 0) = ((v : W) : hypSU h 2 0)⁻¹ :=
          Subgroup.coe_inv W v
        have hsum : q2Blk h (((v : W) : hypSU h 2 0)⁻¹) +
            q2Blk h ((v : W) : hypSU h 2 0) = 0 := by
          rw [← q2Blk_add h (hW (W.inv_mem v.2)) (hW v.2), inv_mul_cancel, q2Blk_one]
        rw [hvq, CharTwo.neg_eq]
        exact CharTwo.add_eq_zero.1 hsum }
  have hS_le : S ≤ hermA m K := by
    rintro C ⟨v, rfl⟩
    exact q2Blk_mem_herm h (hW v.2)
  have hS_inv : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K, ∀ C ∈ S,
      twistActCh6 m A C ∈ S := by
    rintro A C ⟨v, rfl⟩
    refine ⟨⟨lev2Hom h A * (v : hypSU h 2 0) * (lev2Hom h A)⁻¹, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hWN ⟨A, rfl⟩) (v : hypSU h 2 0)).mp v.2
    · have hρ : rho2F h ⟨lev2Hom h A, perfectCore_parP2_le_parH2 h
          (lev2Hom_range_le_perfectCore h ⟨A, rfl⟩)⟩ = A := rho2F_lev2Hom h A
      have h1 := q2Blk_conj_mem h (lev2Hom_range_le_perfectCore h ⟨A, rfl⟩) (hW v.2)
      rw [hρ] at h1
      exact h1
  have hS_ne : S ≠ ⊥ := by
    intro hSb
    apply hwC
    have hmem : q2Blk h (w : hypSU h 2 0) ∈ S := ⟨w, rfl⟩
    rw [hSb, AddSubgroup.mem_bot] at hmem
    exact hmem
  have hcard : Fintype.card K = 2 ^ (2 * m) := by
    rw [Fintype.card_eq_nat_card, h.card]
  have hle := hermA_le_of_invariant_ch6 hcard (by have := h.one_le; omega) S hS_le hS_inv
    (X₀ := q2Blk h (w : hypSU h 2 0)) ⟨w, rfl⟩ hwC
  refine le_antisymm hW ?_
  intro q hq
  obtain ⟨v, hv⟩ := hle (q2Blk_mem_herm h hq)
  have hinj := q2Blk_inj h hq (hW v.2) hv.symm
  rw [hinj]
  exact v.2

private theorem inf_centralizer_radQ2_le (h : UnitaryFieldData 2 m K) :
    perfectCore (parP2 h) ⊓ Subgroup.centralizer (radQ2 h : Set (hypSU h 2 0)) ≤ radQ2 h := by
  haveI := h.charP
  rintro x ⟨hxL, hxC⟩
  have hxH : x ∈ parH2 h := perfectCore_parP2_le_parH2 h hxL
  set A : Matrix.SpecialLinearGroup (Fin 2) K := rho2F h ⟨x, hxH⟩ with hA
  have hAc : ∀ C ∈ hermA m K, twistActCh6 m A C = C := by
    intro C hC
    have hqQ : q2Elt h C hC ∈ radQ2 h := q2Elt_mem_radQ h C hC
    have hcomm : x * q2Elt h C hC = q2Elt h C hC * x := (hxC _ hqQ).symm
    have hconj : x * q2Elt h C hC * x⁻¹ = q2Elt h C hC := by
      rw [hcomm, mul_inv_cancel_right]
    have h1 := q2Blk_conj_mem h hxL hqQ
    rw [hconj, q2Blk_q2Elt h C hC] at h1
    exact h1.symm
  have hA1 : A = 1 := eq_one_of_forall_twistAct h A hAc
  refine mem_radQ2_of_rho2 h (parH2_le_parP2 h hxH) ?_
  have hAval : (A : Matrix (Fin 2) (Fin 2) K) = rho2 h x := rfl
  rw [← hAval, hA1]
  rfl

private theorem exists_radQ2_commutator_ne_one (h : UnitaryFieldData 2 m K) :
    ∃ q ∈ radQ2 h, ∃ A : Matrix.SpecialLinearGroup (Fin 2) K, ⁅q, lev2Hom h A⁆ ≠ 1 := by
  haveI := h.charP
  let C0 : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, 0]
  have hC0 : C0 ∈ hermA m K := by
    rw [mem_hermA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [C0, frobPow]
  let A : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [det_fin_two_of]⟩
  refine ⟨q2Elt h C0 hC0, q2Elt_mem_radQ h C0 hC0, A, ?_⟩
  intro hcomm
  have hcomm' : q2Elt h C0 hC0 * lev2Hom h A = lev2Hom h A * q2Elt h C0 hC0 :=
    commutatorElement_eq_one_iff_mul_comm.mp hcomm
  have hconj : lev2Hom h A * q2Elt h C0 hC0 * (lev2Hom h A)⁻¹ = q2Elt h C0 hC0 := by
    rw [← hcomm', mul_inv_cancel_right]
  have h1 := q2Blk_conj_lev2 h A (q2Elt_mem_radQ h C0 hC0)
  rw [hconj, q2Blk_q2Elt h C0 hC0] at h1
  have hA : ((A : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, 0; 1, 1] := rfl
  have htw : twistActCh6 m A C0 = !![1, 1; 1, 1] := by
    rw [twistActCh6]
    have hf : frobPow m (A : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [frobPow, hA]
    rw [hf, hA]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C0, Matrix.mul_apply, Fin.sum_univ_two]
  rw [htw] at h1
  have e : (0 : K) = 1 := by simpa [C0] using congrFun (congrFun h1 1) 1
  exact zero_ne_one e

theorem commutator_radQ2_lev2_eq (h : UnitaryFieldData 2 m K) :
    ⁅radQ2 h, (lev2Hom h).range⁆ = radQ2 h := by
  haveI := h.charP
  have hLN : perfectCore (parP2 h) ≤ Subgroup.normalizer (radQ2 h : Set (hypSU h 2 0)) :=
    (perfectCore_le (parP2 h)).trans (parP2_le_normalizer_radQ2 h)
  have hle : ⁅radQ2 h, (lev2Hom h).range⁆ ≤ radQ2 h :=
    (Subgroup.commutator_mono le_rfl (lev2Hom_range_le_perfectCore h)).trans
      ((Subgroup.le_normalizer_iff_commutator_le_left
        (H := perfectCore (parP2 h)) (K := radQ2 h)).1 hLN)
  rcases radQ2_irreducible h (⁅radQ2 h, (lev2Hom h).range⁆) hle
    (Subgroup.normalizer_commutator_ge_right (H₁ := radQ2 h) (H₂ := (lev2Hom h).range)) with
    hbot | htop
  · exfalso
    obtain ⟨q, hq, A, hA⟩ := exists_radQ2_commutator_ne_one h
    have hmem : ⁅q, lev2Hom h A⁆ ∈ ⁅radQ2 h, (lev2Hom h).range⁆ :=
      Subgroup.commutator_mem_commutator hq ⟨A, rfl⟩
    rw [hbot] at hmem
    exact hA (Subgroup.mem_bot.mp hmem)
  · exact htop

theorem radQ2_le_perfectCore_parP2' (h : UnitaryFieldData 2 m K) :
    radQ2 h ≤ perfectCore (parP2 h) := by
  have hLnorm : parP2 h ≤ Subgroup.normalizer (perfectCore (parP2 h) : Set (hypSU h 2 0)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le (parP2 h))).mp
      (perfectCore_normal (parP2 h))
  calc radQ2 h = ⁅radQ2 h, (lev2Hom h).range⁆ := (commutator_radQ2_lev2_eq h).symm
    _ ≤ ⁅parP2 h, perfectCore (parP2 h)⁆ :=
      Subgroup.commutator_mono (radQ2_le_parP2 h) (lev2Hom_range_le_perfectCore h)
    _ ≤ perfectCore (parP2 h) :=
      (Subgroup.le_normalizer_iff_commutator_le_right (H := parP2 h)
        (K := perfectCore (parP2 h))).1 hLnorm

theorem pCoreOf_perfectCore_parP2_eq' (h : UnitaryFieldData 2 m K) :
    CFSG.Open.pCoreOf 2 (perfectCore (parP2 h)) = radQ2 h := by
  refine le_antisymm (pCoreOf_perfectCore_parP2_le_radQ2 h) ?_
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 (radQ2_le_perfectCore_parP2' h)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (radQ2_le_perfectCore_parP2' h)).mpr
      ((perfectCore_le _).trans (parP2_le_normalizer_radQ2 h)))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (parP2 h)).to_le
      (radQ2_le_pCoreOf_parP2 h))

private theorem eq_one_of_mem_radQ2_centralizer (h : UnitaryFieldData 2 m K)
    {q : hypSU h 2 0} (hq : q ∈ radQ2 h)
    (hcent : ∀ ℓ ∈ perfectCore (parP2 h), q * ℓ = ℓ * q) : q = 1 := by
  haveI := h.charP
  let W : Subgroup (hypSU h 2 0) :=
    radQ2 h ⊓ Subgroup.centralizer (perfectCore (parP2 h) : Set (hypSU h 2 0))
  have hLN : perfectCore (parP2 h) ≤ Subgroup.normalizer (radQ2 h : Set (hypSU h 2 0)) :=
    (perfectCore_le (parP2 h)).trans (parP2_le_normalizer_radQ2 h)
  have hcent_conj : ∀ y : hypSU h 2 0,
      y ∈ Subgroup.normalizer (perfectCore (parP2 h) : Set (hypSU h 2 0)) →
      ∀ c ∈ Subgroup.centralizer (perfectCore (parP2 h) : Set (hypSU h 2 0)),
        y * c * y⁻¹ ∈ Subgroup.centralizer (perfectCore (parP2 h) : Set (hypSU h 2 0)) := by
    intro y hy c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro l hl
    rw [eq_comm]
    have hyl : y⁻¹ * l * y ∈ perfectCore (parP2 h) :=
      (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (perfectCore (parP2 h) : Set (hypSU h 2 0))).inv_mem hy) l).mp hl
    calc y * c * y⁻¹ * l = y * c * (y⁻¹ * l * y) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * l * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * l * y) * c) * y⁻¹ := by rw [← hc _ hyl]
      _ = l * (y * c * y⁻¹) := by group
  have hWnorm : (lev2Hom h).range ≤ Subgroup.normalizer (W : Set (hypSU h 2 0)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨hwQ, hwC⟩ := Subgroup.mem_inf.mp hw
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (hLN (lev2Hom_range_le_perfectCore h hx)) w).mp hwQ,
          hcent_conj x (Subgroup.le_normalizer (lev2Hom_range_le_perfectCore h hx)) w hwC⟩
    · intro hw
      obtain ⟨hwQ, hwC⟩ := Subgroup.mem_inf.mp hw
      have hxL : x⁻¹ ∈ perfectCore (parP2 h) :=
        (perfectCore (parP2 h)).inv_mem (lev2Hom_range_le_perfectCore h hx)
      have hQ : x⁻¹ * (x * w * x⁻¹) * x ∈ radQ2 h := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hLN hxL) (x * w * x⁻¹)).mp hwQ
      have hC : x⁻¹ * (x * w * x⁻¹) * x ∈
          Subgroup.centralizer (perfectCore (parP2 h) : Set (hypSU h 2 0)) := by
        simpa using hcent_conj x⁻¹ (Subgroup.le_normalizer hxL) (x * w * x⁻¹) hwC
      have h1 : x⁻¹ * (x * w * x⁻¹) * x ∈ W := Subgroup.mem_inf.mpr ⟨hQ, hC⟩
      have e : x⁻¹ * (x * w * x⁻¹) * x = w := by group
      rwa [e] at h1
  have hqW : q ∈ W :=
    Subgroup.mem_inf.mpr
      ⟨hq, Subgroup.mem_centralizer_iff.mpr fun ℓ hℓ => (hcent ℓ hℓ).symm⟩
  have hne : W ≠ radQ2 h := by
    obtain ⟨q₀, hq₀, A, hA⟩ := exists_radQ2_commutator_ne_one h
    have hq₀C : q₀ ∉ Subgroup.centralizer (perfectCore (parP2 h) : Set (hypSU h 2 0)) := by
      intro hc
      have hcomm : lev2Hom h A * q₀ = q₀ * lev2Hom h A :=
        Subgroup.mem_centralizer_iff.mp hc _ (lev2Hom_range_le_perfectCore h ⟨A, rfl⟩)
      exact hA (commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm)
    intro hEq
    exact hq₀C (Subgroup.mem_inf.mp (hEq.symm ▸ hq₀)).2
  have hWle : W ≤ radQ2 h := fun x hx => (Subgroup.mem_inf.mp hx).1
  rcases radQ2_irreducible h W hWle hWnorm with hbot | htop
  · rw [hbot] at hqW
    exact Subgroup.mem_bot.mp hqW
  · exact absurd htop hne

theorem blockU_perfectCore_parP2 (h : UnitaryFieldData 2 m K) :
    blockU (perfectCore (parP2 h)) = radQ2 h := by
  have hQ : blockQ (perfectCore (parP2 h)) = radQ2 h := pCoreOf_perfectCore_parP2_eq' h
  rw [blockU, hQ]
  refine le_antisymm ?_ ?_
  · exact (Subgroup.le_normalizer_iff_commutator_le_left (H := perfectCore (parP2 h))
      (K := radQ2 h)).1 ((perfectCore_le (parP2 h)).trans (parP2_le_normalizer_radQ2 h))
  · calc radQ2 h = ⁅radQ2 h, (lev2Hom h).range⁆ := (commutator_radQ2_lev2_eq h).symm
      _ ≤ ⁅radQ2 h, perfectCore (parP2 h)⁆ :=
        Subgroup.commutator_mono le_rfl (lev2Hom_range_le_perfectCore h)

private noncomputable def alphaU4 (h : UnitaryFieldData 2 m K) :
    ↥(perfectCore (parP2 h)) →* Matrix.SpecialLinearGroup (Fin 2) K :=
  (rho2F h).comp (Subgroup.inclusion (perfectCore_parP2_le_parH2 h))

private theorem alphaU4_surjective (h : UnitaryFieldData 2 m K) :
    Function.Surjective (alphaU4 h) := by
  intro A
  refine ⟨⟨lev2Hom h A, lev2Hom_range_le_perfectCore h ⟨A, rfl⟩⟩, ?_⟩
  show rho2F h ⟨lev2Hom h A, perfectCore_parP2_le_parH2 h (lev2Hom_range_le_perfectCore h
    ⟨A, rfl⟩)⟩ = A
  exact rho2F_lev2Hom h A

private theorem alphaU4_ker (h : UnitaryFieldData 2 m K) :
    (alphaU4 h).ker = CFSG.pCore 2 (perfectCore (parP2 h)) := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hxP : (x : hypSU h 2 0) ∈ parP2 h :=
      parH2_le_parP2 h (perfectCore_parP2_le_parH2 h x.2)
    have hxrho : rho2 h x = 1 := by
      have hh := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) K =>
        (B : Matrix (Fin 2) (Fin 2) K)) hx
      change rho2 h (x : hypSU h 2 0) = 1 at hh
      exact hh
    have hxQ := mem_radQ2_of_rho2 h hxP hxrho
    rw [← pCoreOf_perfectCore_parP2_eq' h] at hxQ
    exact (CFSG.mem_openPCoreOf_iff x).mp hxQ
  · intro hx
    have hxQ : (x : hypSU h 2 0) ∈ radQ2 h := by
      rw [← pCoreOf_perfectCore_parP2_eq' h]
      exact (CFSG.mem_openPCoreOf_iff x).mpr hx
    have hrho : rho2 h x = 1 := rho2_eq_one_of_mem_radQ2 h hxQ
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change rho2 h x i j = (1 : Matrix (Fin 2) (Fin 2) K) i j
    rw [hrho]

private noncomputable def quotEquivSL2 (h : UnitaryFieldData 2 m K) :
    (↥(perfectCore (parP2 h)) ⧸ CFSG.pCore 2 (perfectCore (parP2 h))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.quotientMulEquivOfEq (alphaU4_ker h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (alphaU4 h) (alphaU4_surjective h))

private theorem isQuasisimple_quot (h : UnitaryFieldData 2 m K) :
    CFSG.IsQuasisimple
      (↥(perfectCore (parP2 h)) ⧸ CFSG.pCore 2 (perfectCore (parP2 h))) := by
  haveI := h.charP
  have h4 : 4 ≤ Nat.card K := four_le_card h
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Group.isPerfect_def, commutator_def]
    exact commutator_sl2_eq_top_of_charTwo K h4
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
    center_sl2_eq_bot_of_charTwo K
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    isSimpleGroup_sl2_of_charTwo K h4
  have hquasi : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) := by
    refine ⟨hperf, ?_, ?_⟩
    · have e : (Matrix.SpecialLinearGroup (Fin 2) K ⧸
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) ≃*
          Matrix.SpecialLinearGroup (Fin 2) K :=
        (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
      exact e.isSimpleGroup
    · obtain ⟨A, B, hAB⟩ := exists_sl2_ne_comm K
      refine ⟨QuotientGroup.mk (s := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) A,
        QuotientGroup.mk (s := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) B,
        fun hcon => hAB ?_⟩
      have h' : QuotientGroup.mk A * QuotientGroup.mk B =
          QuotientGroup.mk B * QuotientGroup.mk A := hcon
      have h'' : QuotientGroup.mk (s := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
          (A * B) = QuotientGroup.mk (s := Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)) (B * A) := by
        simpa [map_mul] using h'
      rw [QuotientGroup.eq, hcenter, Subgroup.mem_bot, inv_mul_eq_one] at h''
      exact h''
  exact CFSG.IsQuasisimple.of_mulEquiv (quotEquivSL2 h) hquasi

private noncomputable def q2BlkHom (h : UnitaryFieldData 2 m K) :
    ↥(radQ2 h) →* Multiplicative (Matrix (Fin 2) (Fin 2) K) where
  toFun q := Multiplicative.ofAdd (q2Blk h q)
  map_one' := by
    rw [Subgroup.coe_one, q2Blk_one]
    rfl
  map_mul' q q' := by
    rw [Subgroup.coe_mul, q2Blk_add h q.2 q'.2]
    rfl

private theorem q2BlkHom_ker (h : UnitaryFieldData 2 m K) : (q2BlkHom h).ker = ⊥ := by
  ext q
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hq
    have h0 : q2Blk h (q : hypSU h 2 0) = 0 := by
      have h := congrArg Multiplicative.toAdd hq
      simpa [q2BlkHom] using h
    have hinj := q2Blk_inj h q.2 (Subgroup.one_mem _) (by rw [h0, q2Blk_one])
    exact Subtype.ext hinj
  · intro hq
    rw [hq]
    exact map_one _

theorem blockZ_perfectCore_parP2 (h : UnitaryFieldData 2 m K) :
    blockZ (perfectCore (parP2 h)) = ⊥ := by
  haveI := h.charP
  have hU : blockU (perfectCore (parP2 h)) = radQ2 h := blockU_perfectCore_parP2 h
  rw [blockZ, hU]
  refine le_bot_iff.mp ?_
  intro q hq
  obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.mp hq
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_radQ2_centralizer h hqQ fun ℓ hℓ =>
    (Subgroup.mem_centralizer_iff.mp hqC ℓ hℓ).symm

theorem _root_.CFSG.Quasithin.F112R.isShort2_perfectCore_parP2 {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) :
    IsShort2 (perfectCore (parP2 h)) := by
  haveI := h.charP
  haveI := finite_hypSU h
  set L := perfectCore (parP2 h) with hLdef
  have hQ : blockQ L = radQ2 h := pCoreOf_perfectCore_parP2_eq' h
  have hU : blockU L = radQ2 h := blockU_perfectCore_parP2 h
  have hZ : blockZ L = ⊥ := blockZ_perfectCore_parP2 h
  have hQne : radQ2 h ≠ ⊥ :=
    fun e => zRad_ne_bot h (le_bot_iff.mp ((zRad_le_radQ2 h).trans (le_of_eq e)))
  have hperf : ⁅L, L⁆ = L := perfectCore_perfect (parP2 h)
  have hperfTop : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hperf)
  refine ⟨?_, ?_, ⟨?_, ?_⟩, Or.inl (isQuasisimple_quot h), ?_, ?_⟩
  · intro N hN hN2
    haveI : N.Normal := hN
    by_contra hNtop
    haveI : Nontrivial (↥L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
    haveI : Group.IsNilpotent (↥L ⧸ N) := hN2.isNilpotent
    haveI : Group.IsSolvable (↥L ⧸ N) := inferInstance
    have hle : (⊤ : Subgroup ↥L) ≤ N :=
      Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient (M := N) (H := ⊤) hperfTop
    exact hNtop (top_le_iff.mp hle)
  · change L ⊓ Subgroup.centralizer (blockQ L : Set (hypSU h 2 0)) ≤ blockQ L
    rw [hQ]
    exact inf_centralizer_radQ2_le h
  · rw [hU, hQ]
    refine le_inf le_rfl fun x hx => ?_
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => radQ2_comm h hy hx
  · intro x hx
    rw [hU] at hx
    exact sq_eq_one_of_mem_radQ2 h hx
  · rw [hZ, hU]
    exact bot_lt_iff_ne_bot.mpr hQne
  · rw [hZ, hU]
    intro W _ hWU hWN
    rcases radQ2_irreducible h W hWU ((lev2Hom_range_le_perfectCore h).trans hWN) with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem _root_.CFSG.Quasithin.F112R.isOmega4MinusType_perfectCore_parP2 {m : ℕ} {K : Type}
    [Field K]
    (h : UnitaryFieldData 2 m K) :
    IsOmega4MinusType (perfectCore (parP2 h)) m := by
  haveI := h.charP
  haveI := h.finite
  letI : Fintype K := Fintype.ofFinite K
  have hU : blockU (perfectCore (parP2 h)) = radQ2 h := blockU_perfectCore_parP2 h
  let eU : ↥(blockU (perfectCore (parP2 h))) ≃* ↥(radQ2 h) := MulEquiv.subgroupCongr hU
  let β : ↥(blockU (perfectCore (parP2 h))) →* Multiplicative (Matrix (Fin 2) (Fin 2) K) :=
    (q2BlkHom h).comp eU.toMonoidHom
  have hcard : Fintype.card K = 2 ^ (2 * m) := by
    rw [Fintype.card_eq_nat_card, h.card]
  have hβim : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (∃ u : ↥(blockU (perfectCore (parP2 h))), Multiplicative.toAdd (β u) = X) ↔
        X.map (· ^ 2 ^ m) = X.transpose := by
    intro X
    have him : (∃ u : ↥(blockU (perfectCore (parP2 h))),
        Multiplicative.toAdd (β u) = X) ↔ X ∈ hermA m K := by
      constructor
      · rintro ⟨u, rfl⟩
        exact q2Blk_mem_herm h (eU u).2
      · intro hX
        refine ⟨eU.symm ⟨q2Elt h X hX, q2Elt_mem_radQ h X hX⟩, ?_⟩
        show Multiplicative.toAdd (Multiplicative.ofAdd (q2Blk h (q2Elt h X hX))) = X
        rw [q2Blk_q2Elt]
        rfl
    rw [him, mem_hermA]
    constructor
    · intro hh
      have := congrArg Matrix.transpose hh
      simpa [frobPow, Matrix.transpose_transpose] using this
    · intro hh
      have := congrArg Matrix.transpose hh
      simpa [frobPow, Matrix.transpose_transpose] using this
  have hβker : β.ker = (blockZ (perfectCore (parP2 h))).subgroupOf
      (blockU (perfectCore (parP2 h))) := by
    rw [blockZ_perfectCore_parP2 h, Subgroup.bot_subgroupOf]
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hu
      have h0 : q2Blk h ((eU u : ↥(radQ2 h)) : hypSU h 2 0) = 0 := by
        have hh := congrArg Multiplicative.toAdd hu
        change Multiplicative.toAdd (Multiplicative.ofAdd
          (q2Blk h ((eU u : ↥(radQ2 h)) : hypSU h 2 0))) = 0 at hh
        simpa using hh
      have hinj := q2Blk_inj h (eU u).2 (Subgroup.one_mem _) (by rw [h0, q2Blk_one])
      apply eU.injective
      exact Subtype.ext hinj
    · intro hu
      rw [hu]
      exact map_one β
  have hβeq : ∀ (ℓ : ↥(perfectCore (parP2 h)))
      (u v : ↥(blockU (perfectCore (parP2 h)))),
      (v : hypSU h 2 0) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (alphaU4 h ℓ : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd (β u) *
          ((alphaU4 h ℓ : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ m)).transpose := by
    intro ℓ u v huv
    have hconj : ((eU v : ↥(radQ2 h)) : hypSU h 2 0) =
        (ℓ : hypSU h 2 0) * ((eU u : ↥(radQ2 h)) : hypSU h 2 0) *
          (ℓ : hypSU h 2 0)⁻¹ := by
      change (v : hypSU h 2 0) = (ℓ : hypSU h 2 0) * (u : hypSU h 2 0) *
        (ℓ : hypSU h 2 0)⁻¹
      rw [← Subgroup.coe_inv]
      exact huv
    have h1 := q2Blk_conj_mem h ℓ.2 (eU u).2
    rw [← hconj] at h1
    have halpha : rho2F h ⟨ℓ, perfectCore_parP2_le_parH2 h ℓ.2⟩ = alphaU4 h ℓ := rfl
    rw [halpha] at h1
    show q2Blk h (eU v : ↥(radQ2 h)) = (alphaU4 h ℓ : Matrix (Fin 2) (Fin 2) K) *
      q2Blk h (eU u : ↥(radQ2 h)) *
        ((alphaU4 h ℓ : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ m)).transpose
    simpa [twistActCh6, frobPow] using h1
  exact ⟨K, inferInstance, Fintype.ofFinite K, hcard, alphaU4 h, alphaU4_surjective h,
    alphaU4_ker h, β, hβim, hβker, hβeq⟩

end CFSG.Quasithin.H13.U4Par
