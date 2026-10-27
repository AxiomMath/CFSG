module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructPSUBlock
import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeRadical
import CFSG.Timmesfeld.LieEmbed.UnitaryWitt
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTransvectionCoreGroup
import CFSG.LocalAnalysis.StandardType.GGRootDetectSU
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUCore
import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.StandardType.KGPSU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
open CFSG.Timmesfeld.LieEmbed
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

private def suA {k : ℕ} (a : Fin k → K) : Fin (k + 2) → K := midExt a

private noncomputable def suW (f : ℕ) {k : ℕ} (a : Fin k → K) : Fin (k + 2) → K :=
  fun i => unitaryInvolution K 2 f (suA a (Fin.rev i))

private noncomputable def suN (f : ℕ) {k : ℕ} (a : Fin k → K) (s : K) :
    Matrix (Fin (k + 2)) (Fin (k + 2)) K :=
  vecMulVec (suA a) e0 + vecMulVec eL (suW f a) + s • vecMulVec eL e0

private noncomputable def suMat (f : ℕ) {k : ℕ} (a : Fin k → K) (s : K) :
    Matrix (Fin (k + 2)) (Fin (k + 2)) K :=
  1 + suN f a s

private noncomputable def SuAdm (f : ℕ) {k : ℕ} (a : Fin k → K) (s : K) : Prop :=
  s + unitaryInvolution K 2 f s = aform (unitaryInvolution K 2 f) a a

private theorem antidiag_mulVec_midExt_comp_rev {k : ℕ} (a : Fin k → K) :
    (antidiag (k + 2) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) *ᵥ
        midExt (a ∘ Fin.rev) = midExt a := by
  rw [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.antidiag_mulVec]
  funext i
  by_cases hi : i ∈ Set.range (mid (m := k))
  · obtain ⟨l, rfl⟩ := hi
    rw [rev_mid, midExt_mid, midExt_mid, Function.comp_apply, Fin.rev_rev]
  · rcases RCSTSU.eq_zero_or_eq_last_of_not_mem hi with rfl | rfl
    · rw [midExt_zero_apply, Fin.rev_zero, midExt_last]
    · rw [midExt_last, Fin.rev_last, midExt_zero_apply]

private theorem suW_eq_sigma_midExt_comp_rev {k : ℕ} (a : Fin k → K) :
    (fun j => unitaryInvolution K 2 f (midExt (a ∘ Fin.rev) j)) = suW f a := by
  funext j
  by_cases hj : j ∈ Set.range (mid (m := k))
  · obtain ⟨l, rfl⟩ := hj
    rw [midExt_mid, Function.comp_apply, suW, suA, rev_mid, midExt_mid]
  · rcases RCSTSU.eq_zero_or_eq_last_of_not_mem hj with rfl | rfl
    · simp [suW, suA, midExt_zero_apply, midExt_last, Fin.rev_zero]
    · simp [suW, suA, midExt_zero_apply, midExt_last, Fin.rev_last]

private theorem antidiag_eMat_antidiag {k : ℕ} (a : Fin k → K) (s : K) :
    (antidiag (k + 2) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) *
        eMat (unitaryInvolution K 2 f) (midExt (a ∘ Fin.rev)) s *
        (antidiag (k + 2) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) = suMat f a s := by
  let J : Matrix (Fin (k + 2)) (Fin (k + 2)) K := antidiag (k + 2)
  let y : Fin (k + 2) → K := midExt (a ∘ Fin.rev)
  let w : Fin (k + 2) → K := fun i => unitaryInvolution K 2 f (y i)
  have hJJ : J * J = 1 := antidiag_mul_self (k + 2)
  have hJy : J *ᵥ y = suA a := antidiag_mulVec_midExt_comp_rev a
  have hJe0 : J *ᵥ (e0 : Fin (k + 2) → K) = eL := by
    rw [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.antidiag_mulVec]
    funext i
    rw [e0, eL, Pi.single_apply, Pi.single_apply]
    by_cases hi : i = Fin.last (k + 1)
    · subst hi
      simp [Fin.rev_last]
    · have hri : Fin.rev i ≠ 0 := fun h => hi (by rw [← Fin.rev_rev i, h, Fin.rev_zero])
      simp [hi, hri]
  have heLJ : (eL : Fin (k + 2) → K) ᵥ* J = e0 := by
    rw [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.vecMul_antidiag]
    funext i
    rw [eL, e0, Pi.single_apply, Pi.single_apply]
    by_cases hi : i = 0
    · subst hi
      simp [Fin.rev_zero]
    · have hri : Fin.rev i ≠ Fin.last (k + 1) := fun h =>
        hi (by rw [← Fin.rev_rev i, h, Fin.rev_last])
      simp [hi, hri]
  have hrow : (s • (eL : Fin (k + 2) → K) - w ᵥ* J) ᵥ* J =
      s • (e0 : Fin (k + 2) → K) - suW f a := by
    rw [sub_vecMul, smul_vecMul, vecMul_vecMul, hJJ, vecMul_one, heLJ]
    exact congrArg (fun u => s • (e0 : Fin (k + 2) → K) - u)
      (suW_eq_sigma_midExt_comp_rev a)
  calc
    J * eMat (unitaryInvolution K 2 f) y s * J
        = J * (1 + vecMulVec y eL +
            vecMulVec e0 (s • eL - (fun a => unitaryInvolution K 2 f (y a)) ᵥ* J)) * J := by
          rw [eMat]
    _ = J * J + vecMulVec (J *ᵥ y) (eL ᵥ* J) +
          vecMulVec (J *ᵥ e0) ((s • eL - w ᵥ* J) ᵥ* J) := by
          dsimp only [w]
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
            mul_vecMulVec, vecMulVec_mul]
    _ = 1 + vecMulVec (suA a) e0 + vecMulVec eL (s • e0 - suW f a) := by
          rw [hJJ, hJy, hJe0, heLJ, hrow]
    _ = suMat f a s := by
          rw [suMat, suN, vecMulVec_sub, vecMulVec_smul, sub_eq_add_neg, CharTwo.neg_eq]
          abel

private theorem midExt_eq_zero_of_not_mem {k : ℕ} {w : Fin k → K} {p : Fin (k + 2)}
    (hp : p ∉ Set.range (mid (m := k))) : midExt w p = 0 := by
  rw [midExt, dite_eq_right]
  intro h
  exact absurd (mem_range_mid.2 h) hp

private theorem aform_midExt_eq_sum {k : ℕ} (w : Fin k → K) :
    aform (unitaryInvolution K 2 f) (midExt w) (midExt w) =
      ∑ l : Fin k, unitaryInvolution K 2 f (w l) * w (Fin.rev l) := by
  rw [aform_apply]
  symm
  refine Fintype.sum_of_injective mid mid_injective
    (fun l : Fin k => unitaryInvolution K 2 f (w l) * w (Fin.rev l))
    (fun p : Fin (k + 2) => unitaryInvolution K 2 f (midExt w p) * midExt w (Fin.rev p))
    ?_ ?_
  · intro p hp
    have hp' : Fin.rev p ∉ Set.range (mid (m := k)) := fun h => hp (rev_mem_range_mid_iff.1 h)
    rw [midExt_eq_zero_of_not_mem hp, midExt_eq_zero_of_not_mem hp', map_zero, zero_mul]
  · intro l
    rw [rev_mid, midExt_mid, midExt_mid]

private theorem aform_midExt_comp_rev {k : ℕ} (a : Fin k → K) :
    aform (unitaryInvolution K 2 f) (midExt (a ∘ Fin.rev)) (midExt (a ∘ Fin.rev)) =
      aform (unitaryInvolution K 2 f) (midExt a) (midExt a) := by
  rw [aform_midExt_eq_sum, aform_midExt_eq_sum]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun l => ?_
  simp only [Fin.revPerm_apply, Function.comp_apply, Fin.rev_rev]

private theorem aform_midExt_self {k : ℕ} (a : Fin k → K) :
    aform (unitaryInvolution K 2 f) (midExt a) (midExt a) =
      aform (unitaryInvolution K 2 f) a a := by
  rw [aform_midExt_eq_sum, aform_apply]

private theorem aform_mat_SU {k : ℕ} (B : SU (unitaryInvolution K 2 f) k) (a : Fin k → K) :
    aform (unitaryInvolution K 2 f) (mat (unitaryInvolution K 2 f) k B *ᵥ a)
        (mat (unitaryInvolution K 2 f) k B *ᵥ a) =
      aform (unitaryInvolution K 2 f) a a :=
  aform_mat B a a

private theorem SuAdm.mulVec (h : UnitaryFieldData 2 f K) {k : ℕ} {a : Fin k → K} {s : K}
    (B : SU (unitaryInvolution K 2 f) k) (hAdm : SuAdm (f := f) a s) :
    SuAdm (f := f) (mat (unitaryInvolution K 2 f) k B *ᵥ a) s := by
  unfold SuAdm at *
  rw [aform_mat_SU B a]
  exact hAdm

private theorem exists_suAdm (h : UnitaryFieldData 2 f K) {k : ℕ} (a : Fin k → K) :
    ∃ s : K, SuAdm (f := f) a s := by
  have hσ : ∀ c, unitaryInvolution K 2 f (unitaryInvolution K 2 f c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive h.card_eq_sq
  have ht : h.bar (aform (unitaryInvolution K 2 f) a a) =
      aform (unitaryInvolution K 2 f) a a := by
    rw [RootDetectSU.bar_eq h, map_aform (unitaryInvolution K 2 f) hσ]
  obtain ⟨s, hs⟩ := CFSG.SeitzReduction.UnitaryPilot.exists_add_bar_eq h ht
  refine ⟨s, ?_⟩
  unfold SuAdm
  rw [← RootDetectSU.bar_eq h]
  exact hs

private theorem det_antidiag_eq_one (n : ℕ) :
    (antidiag n : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h : (antidiag n : Matrix (Fin n) (Fin n) K).det *
      (antidiag n : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [← det_mul, antidiag_mul_self, det_one]
  have h2 : (antidiag n : Matrix (Fin n) (Fin n) K).det ^ 2 = (1 : K) ^ 2 := by
    rw [pow_two, h, one_pow]
  exact CharTwo.sq_inj.1 h2

private theorem antidiag_transpose (n : ℕ) :
    (antidiag n : Matrix (Fin n) (Fin n) K)ᵀ = antidiag n := by
  ext i j
  simp only [transpose_apply, antidiag, of_apply]
  by_cases h : i = Fin.rev j
  · have h' : j = Fin.rev i := by rw [h, Fin.rev_rev]
    rw [if_pos h', if_pos h]
  · have h' : j ≠ Fin.rev i := fun hh => h (by rw [hh, Fin.rev_rev])
    rw [if_neg h', if_neg h]

private theorem antidiag_map (n : ℕ) :
    (antidiag n : Matrix (Fin n) (Fin n) K).map (unitaryInvolution K 2 f) = antidiag n := by
  ext i j
  rw [Matrix.map_apply]
  change unitaryInvolution K 2 f (if j = Fin.rev i then (1 : K) else 0) =
    (if j = Fin.rev i then (1 : K) else 0)
  by_cases h : j = Fin.rev i
  · rw [if_pos h]
    exact map_one _
  · rw [if_neg h]
    exact map_zero _

private noncomputable def suJ {k : ℕ} : SU (unitaryInvolution K 2 f) (k + 2) :=
  ⟨⟨antidiag (k + 2), antidiag (k + 2), antidiag_mul_self (k + 2),
      antidiag_mul_self (k + 2)⟩,
    mem_SU.2 ⟨det_antidiag_eq_one (k + 2), by
      rw [conjTr, antidiag_map, antidiag_transpose]
      change (antidiag (k + 2) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) *
          antidiag (k + 2) * antidiag (k + 2) = antidiag (k + 2)
      rw [Matrix.mul_assoc, antidiag_mul_self, Matrix.mul_one]⟩⟩

private noncomputable def suHeis (h : UnitaryFieldData 2 f K) {k : ℕ} (i j : Fin k)
    (hi : i ≠ Fin.rev i) (hij : i ≠ j) (hj : Fin.rev j = j) (b : K) (hb : b + b = 0)
    (hb1 : b + unitaryInvolution K 2 f b = 1) :
    SU (unitaryInvolution K 2 f) k :=
  let M := heisenbergMatrix (unitaryInvolution K 2 f) i j 1 b
  let M' := heisenbergMatrix (unitaryInvolution K 2 f) i j (-1) (-b - 1 * unitaryInvolution K 2 f 1)
  have hMM' : M * M' = 1 := by
    rw [heisenbergMatrix_mul (unitaryInvolution K 2 f) hi hij hj]
    have h1 : (1 : K) + -1 = 0 := by ring
    have h2 : b + (-b - 1 * unitaryInvolution K 2 f 1) -
        1 * unitaryInvolution K 2 f (-1) = 0 := by
      rw [map_neg, map_one]
      ring
    rw [h1, h2, heisenbergMatrix_zero]
  have hM'M : M' * M = 1 := by
    rw [heisenbergMatrix_mul (unitaryInvolution K 2 f) hi hij hj]
    have h1 : (-1 : K) + 1 = 0 := by ring
    have h2 : (-b - 1 * unitaryInvolution K 2 f 1) + b -
        (-1) * unitaryInvolution K 2 f 1 = 0 := by
      rw [map_one]
      ring
    rw [h1, h2, heisenbergMatrix_zero]
  let gl : GL (Fin k) K := ⟨M, M', hMM', hM'M⟩
  ⟨gl, mem_SU.2 ⟨by rw [Units.val_mk, det_heisenbergMatrix (unitaryInvolution K 2 f) hi hij hj], by
    rw [Units.val_mk]
    refine heisenbergMatrix_isometry (unitaryInvolution K 2 f)
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive h.card_eq_sq) hi hij hj ?_
    rw [hb1, map_one, one_mul, CharTwo.add_self_eq_zero]⟩⟩

private theorem mat_suHeis (h : UnitaryFieldData 2 f K) {k : ℕ} (i j : Fin k)
    (hi : i ≠ Fin.rev i) (hij : i ≠ j) (hj : Fin.rev j = j) (b : K) (hb : b + b = 0)
    (hb1 : b + unitaryInvolution K 2 f b = 1) :
    mat (unitaryInvolution K 2 f) k (suHeis h i j hi hij hj b hb hb1) =
      heisenbergMatrix (unitaryInvolution K 2 f) i j 1 b :=
  rfl

private noncomputable def suJn (n : ℕ) : SU (unitaryInvolution K 2 f) n :=
  ⟨⟨antidiag n, antidiag n, antidiag_mul_self n, antidiag_mul_self n⟩,
    mem_SU.2 ⟨det_antidiag_eq_one n, by
      rw [conjTr, antidiag_map, antidiag_transpose]
      change (antidiag n : Matrix (Fin n) (Fin n) K) * antidiag n * antidiag n =
        antidiag n
      rw [Matrix.mul_assoc, antidiag_mul_self, Matrix.mul_one]⟩⟩

private theorem mat_suJn (n : ℕ) :
    mat (unitaryInvolution K 2 f) n (suJn (f := f) n) = antidiag n :=
  rfl

private theorem suJn_mul_self (n : ℕ) :
    suJn (K := K) (f := f) n * suJn (K := K) (f := f) n = 1 := by
  apply mat_injective
  simp only [map_mul, map_one, mat_suJn, antidiag_mul_self]

private theorem inv_suJn (n : ℕ) :
    (suJn (K := K) (f := f) n)⁻¹ = suJn (K := K) (f := f) n := by
  rw [inv_eq_iff_mul_eq_one]
  exact suJn_mul_self n

private noncomputable def suB' {k : ℕ} (B : SU (unitaryInvolution K 2 f) k) :
    SU (unitaryInvolution K 2 f) k :=
  suJn (K := K) (f := f) k * B * (suJn (K := K) (f := f) k)⁻¹

private theorem mat_suB' {k : ℕ} (B : SU (unitaryInvolution K 2 f) k) :
    mat (unitaryInvolution K 2 f) k (suB' B) =
      (antidiag k : Matrix (Fin k) (Fin k) K) * mat (unitaryInvolution K 2 f) k B *
        antidiag k := by
  simp only [suB', map_mul, inv_suJn, mat_suJn]

private theorem mul_antidiag_apply {n : ℕ} (C : Matrix (Fin n) (Fin n) K) (a b : Fin n) :
    (C * (antidiag n : Matrix (Fin n) (Fin n) K)) a b = C a (Fin.rev b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev b)]
  · simp [antidiag]
  · intro k _ hk
    have hkb : ¬ b = Fin.rev k := fun h => hk (by rw [h, Fin.rev_rev])
    simp [antidiag, hkb]
  · simp

private theorem antidiag_mul_mul_antidiag {n : ℕ} (C : Matrix (Fin n) (Fin n) K) (a b : Fin n) :
    ((antidiag n : Matrix (Fin n) (Fin n) K) * C *
      (antidiag n : Matrix (Fin n) (Fin n) K)) a b = C (Fin.rev a) (Fin.rev b) := by
  rw [Matrix.mul_assoc, antidiag_mul_apply,
    mul_antidiag_apply]

private theorem antidiag_iotaMat_suB' {k : ℕ} (B : SU (unitaryInvolution K 2 f) k) :
    (antidiag (k + 2) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) *
        iotaMat (mat (unitaryInvolution K 2 f) k (suB' B)) *
        (antidiag (k + 2) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) =
      iotaMat (mat (unitaryInvolution K 2 f) k B) := by
  refine isBlkOn_ext ?_ (iotaMat_isBlkOn _) ?_
  · intro a b hab
    have hab' : Fin.rev a ∉ Set.range (mid (m := k)) ∨
        Fin.rev b ∉ Set.range (mid (m := k)) := by
      rcases hab with ha | hb
      · exact Or.inl (fun h => ha (rev_mem_range_mid_iff.1 h))
      · exact Or.inr (fun h => hb (rev_mem_range_mid_iff.1 h))
    have h := iotaMat_isBlkOn (A := mat (unitaryInvolution K 2 f) k (suB' B))
      (Fin.rev a) (Fin.rev b) hab'
    rw [antidiag_mul_mul_antidiag, h]
    simp [Matrix.one_apply]
  · ext i j
    have hR : (iotaMat (mat (unitaryInvolution K 2 f) k B)).submatrix mid mid i j =
        mat (unitaryInvolution K 2 f) k B i j := by
      rw [Matrix.submatrix_apply, iotaMat_mid]
    rw [hR, Matrix.submatrix_apply, antidiag_mul_mul_antidiag, rev_mid, rev_mid,
      mat_suB', iotaMat_mid, antidiag_mul_mul_antidiag]
    simp only [Fin.rev_rev]

private theorem mat_suJ {k : ℕ} :
    mat (unitaryInvolution K 2 f) (k + 2) (suJ (K := K) (f := f) (k := k)) =
      antidiag (k + 2) :=
  rfl

private theorem suJ_mul_self {k : ℕ} :
    suJ (K := K) (f := f) (k := k) * suJ (K := K) (f := f) (k := k) = 1 := by
  apply mat_injective
  simp only [map_mul, map_one, mat_suJ, antidiag_mul_self]

private theorem inv_suJ {k : ℕ} :
    (suJ (K := K) (f := f) (k := k))⁻¹ = suJ (K := K) (f := f) (k := k) := by
  rw [inv_eq_iff_mul_eq_one]
  exact suJ_mul_self

private theorem iotaHom_eq_suJ_mul {k : ℕ} (B : SU (unitaryInvolution K 2 f) k) :
    iotaHom B = suJ (K := K) (f := f) (k := k) * iotaHom (suB' B) *
      suJ (K := K) (f := f) (k := k) := by
  apply mat_injective
  simp only [map_mul, mat_suJ, mat_iotaHom]
  exact (antidiag_iotaMat_suB' B).symm

private theorem suB'_mulVec_midExt {k : ℕ} (B : SU (unitaryInvolution K 2 f) k)
    (a : Fin k → K) :
    mat (unitaryInvolution K 2 f) k (suB' B) *ᵥ (a ∘ Fin.rev) =
      (mat (unitaryInvolution K 2 f) k B *ᵥ a) ∘ Fin.rev := by
  rw [mat_suB', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.antidiag_mulVec]
  simp only [Function.comp_apply, Fin.rev_rev,
    CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.antidiag_mulVec]
  rfl

private theorem iotaMat_mulVec_midExt {k : ℕ} (A : Matrix (Fin k) (Fin k) K)
    (v : Fin k → K) : iotaMat A *ᵥ midExt v = midExt (A *ᵥ v) := by
  funext p
  by_cases hp : p ∈ Set.range (mid (m := k))
  · obtain ⟨i, rfl⟩ := hp
    rw [midExt_mid]
    change (∑ t : Fin (k + 2), iotaMat A (mid i) t * midExt v t) =
      ∑ j : Fin k, A i j * v j
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (mid (m := k))))]
    · rw [Finset.sum_image]
      · simp [iotaMat_mid, midExt_mid]
      · intro a _ b _ hab
        exact mid_injective hab
    · intro t _ ht
      rw [midExt_eq_zero_of_not_mem (by simpa [Finset.mem_image] using ht), mul_zero]
  · rcases RCSTSU.eq_zero_or_eq_last_of_not_mem hp with rfl | rfl
    · rw [midExt_zero_apply]
      change (∑ t : Fin (k + 2), iotaMat A 0 t * midExt v t) = 0
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases ht : t ∈ Set.range (mid (m := k))
      · obtain ⟨j, rfl⟩ := ht
        rw [iotaMat_isBlkOn A 0 (mid j) (Or.inl hp), Matrix.one_apply]
        simp [Ne.symm (mid_ne_zero j)]
      · rw [midExt_eq_zero_of_not_mem ht, mul_zero]
    · rw [midExt_last]
      change (∑ t : Fin (k + 2), iotaMat A (Fin.last (k + 1)) t * midExt v t) = 0
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases ht : t ∈ Set.range (mid (m := k))
      · obtain ⟨j, rfl⟩ := ht
        rw [iotaMat_isBlkOn A (Fin.last (k + 1)) (mid j) (Or.inl hp), Matrix.one_apply]
        simp [mid_ne_last j, Ne.symm (mid_ne_last j)]
      · rw [midExt_eq_zero_of_not_mem ht, mul_zero]

private theorem suMat_apply {k : ℕ} (a : Fin k → K) (s : K) (i j : Fin (k + 2)) :
    suMat f a s i j =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) K) i j +
        (if j = 0 then suA a i else 0) +
        (if i = Fin.last (k + 1) then suW f a j else 0) +
        (if i = Fin.last (k + 1) then if j = 0 then s else 0 else 0) := by
  by_cases hj : j = 0
  · subst hj
    by_cases hi : i = Fin.last (k + 1)
    · subst hi
      simp [suMat, suN, vecMulVec, e0, eL, Pi.single_apply]
    · simp [suMat, suN, vecMulVec, e0, eL, Pi.single_apply, hi]
  · by_cases hi : i = Fin.last (k + 1)
    · subst hi
      simp [suMat, suN, vecMulVec, e0, eL, Pi.single_apply, hj]
    · simp [suMat, suN, vecMulVec, e0, eL, Pi.single_apply, hj, hi]

private def suE {k : ℕ} : Matrix (Fin (k + 2)) (Fin (k + 2)) K := vecMulVec eL e0

private theorem suE_eq_single {k : ℕ} :
    suE (K := K) (k := k) = Matrix.single (Fin.last (k + 1)) 0 1 := by
  ext i j
  by_cases hi : i = Fin.last (k + 1)
  · subst hi
    by_cases hj : j = 0
    · subst hj
      simp [suE, vecMulVec, e0, eL, Pi.single_apply, Matrix.single_apply]
    · simp [suE, vecMulVec, e0, eL, Pi.single_apply, Matrix.single_apply, hj,
        Ne.symm hj]
  · by_cases hj : j = 0
    · subst hj
      simp [suE, vecMulVec, e0, eL, Pi.single_apply, Matrix.single_apply, hi,
        Ne.symm hi]
    · simp [suE, vecMulVec, e0, eL, Pi.single_apply, Matrix.single_apply, hi, hj,
        Ne.symm hi, Ne.symm hj]

private theorem e0_dot_eL {k : ℕ} : (e0 : Fin (k + 2) → K) ⬝ᵥ eL = 0 := by
  rw [dotProduct, Finset.sum_eq_single 0]
  · simp [e0, eL, zero_ne_last]
  · intro i _ hi
    simp [e0, Pi.single_eq_of_ne hi]
  · simp

private theorem e0_dot_suA {k : ℕ} (a : Fin k → K) :
    (e0 : Fin (k + 2) → K) ⬝ᵥ suA a = 0 := by
  rw [dotProduct, Finset.sum_eq_single 0]
  · simp [e0, suA, midExt_zero_apply]
  · intro i _ hi
    simp [e0, Pi.single_eq_of_ne hi]
  · simp

private theorem suW_dot_eL {k : ℕ} (a : Fin k → K) :
    suW f a ⬝ᵥ (eL : Fin (k + 2) → K) = 0 := by
  rw [dotProduct, Finset.sum_eq_single (Fin.last (k + 1))]
  · simp [suW, suA, eL, midExt_zero_apply, Fin.rev_last]
  · intro i _ hi
    simp [eL, Pi.single_eq_of_ne hi]
  · simp

private theorem suN_mul_suE {k : ℕ} (a : Fin k → K) (s : K) :
    suN f a s * suE (K := K) (k := k) = 0 := by
  rw [suN, suE, add_mul, add_mul, smul_mul, vecMulVec_mul_vecMulVec,
    vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec]
  simp [e0_dot_eL, suW_dot_eL, suW, suA, Fin.rev_last, midExt_zero_apply]

private theorem suE_mul_suN {k : ℕ} (a : Fin k → K) (s : K) :
    suE (K := K) (k := k) * suN f a s = 0 := by
  rw [suN, suE, mul_add, mul_add, Matrix.mul_smul, vecMulVec_mul_vecMulVec,
    vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec]
  simp [e0_dot_suA, e0_dot_eL, suA, midExt_zero_apply]

private theorem suMat_mid_mid {k : ℕ} (a : Fin k → K) (s : K) (i j : Fin k) :
    suMat f a s (mid i) (mid j) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) K) (mid i) (mid j) := by
  rw [suMat_apply, if_neg (mid_ne_zero j), if_neg (mid_ne_last i),
    if_neg (mid_ne_last i)]
  simp

private theorem suMat_last_last {k : ℕ} (a : Fin k → K) (s : K) :
    suMat f a s (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 := by
  rw [suMat_apply]
  simp [Fin.last_ne_zero, suW, suA, Fin.rev_last, midExt_zero_apply]

private theorem suMat_mid_zero {k : ℕ} (a : Fin k → K) (s : K) (i : Fin k) :
    suMat f a s (mid i) 0 = a i := by
  rw [suMat_apply]
  simp [Matrix.one_apply, mid_ne_zero i, mid_ne_last i, suA, midExt_mid]

private theorem suMat_last_zero {k : ℕ} (a : Fin k → K) (s : K) :
    suMat f a s (Fin.last (k + 1)) 0 = s := by
  rw [suMat_apply]
  simp [Matrix.one_apply, zero_ne_last, suA, midExt_last, suW, midExt_zero, map_zero]

private theorem suMat_last_mid {k : ℕ} (a : Fin k → K) (s : K) (j : Fin k) :
    suMat f a s (Fin.last (k + 1)) (mid j) = suW f a (mid j) := by
  rw [suMat_apply]
  simp [Matrix.one_apply, mid_ne_zero j, mid_ne_last j, Ne.symm (mid_ne_last j), suA, midExt_last]

private theorem suMat_row_zero {k : ℕ} (a : Fin k → K) (s : K) (j : Fin (k + 2)) :
    suMat f a s 0 j = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) K) 0 j := by
  rw [suMat_apply]
  by_cases hj : j = 0
  · subst hj
    simp [suA, midExt_zero_apply]
  · simp [hj]

private theorem suMat_col_last {k : ℕ} (a : Fin k → K) (s : K) (i : Fin (k + 2)) :
    suMat f a s i (Fin.last (k + 1)) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) K) i (Fin.last (k + 1)) := by
  rw [suMat_apply]
  by_cases hi : i = Fin.last (k + 1)
  · subst hi
    simp [suW, suA, Fin.rev_last, midExt_zero_apply]
  · simp [hi]

private noncomputable def suElt (h : UnitaryFieldData 2 f K) {k : ℕ} (a : Fin k → K) (s : K)
    (hAdm : SuAdm (f := f) a s) : SU (unitaryInvolution K 2 f) (k + 2) :=
  let hσ : ∀ c, unitaryInvolution K 2 f (unitaryInvolution K 2 f c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive h.card_eq_sq
  eSU (unitaryInvolution K 2 f) hσ (midExt_last (a ∘ Fin.rev)) (c := s)
    (by
      rw [aform_midExt_comp_rev, aform_midExt_self, ← hAdm,
        CharTwo.add_self_eq_zero])

private noncomputable def suM (h : UnitaryFieldData 2 f K) {k : ℕ} (a : Fin k → K) (s : K)
    (hAdm : SuAdm (f := f) a s) : SU (unitaryInvolution K 2 f) (k + 2) :=
  suJ (f := f) (k := k) * suElt h a s hAdm * suJ (f := f) (k := k)

private theorem mat_suM (h : UnitaryFieldData 2 f K) {k : ℕ} (a : Fin k → K) (s : K)
    (hAdm : SuAdm (f := f) a s) :
    mat (unitaryInvolution K 2 f) (k + 2) (suM h a s hAdm) = suMat f a s := by
  rw [suM]
  simp only [map_mul, mat_suJ]
  change (antidiag (k + 2) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) *
      eMat (unitaryInvolution K 2 f) (midExt (a ∘ Fin.rev)) s *
      (antidiag (k + 2) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) = suMat f a s
  exact antidiag_eMat_antidiag a s

private theorem sum_univ_eq_zero_add_last_add_mid {M : Type*} [AddCommMonoid M] {k : ℕ}
    (F : Fin (k + 2) → M) :
    ∑ t, F t = F 0 + F (Fin.last (k + 1)) + ∑ i : Fin k, F (mid i) := by
  have hlast : Fin.last (k + 1) ∈ Finset.univ.erase (0 : Fin (k + 2)) := by
    rw [Finset.mem_erase]
    exact ⟨Ne.symm (zero_ne_last (m := k)), Finset.mem_univ _⟩
  rw [← Finset.sum_erase_add (Finset.univ) F (Finset.mem_univ 0)]
  rw [← Finset.sum_erase_add (Finset.univ.erase 0) F hlast]
  have hmid : ∑ x ∈ (Finset.univ.erase (0 : Fin (k + 2))).erase (Fin.last (k + 1)), F x =
      ∑ i : Fin k, F (mid i) := by
    have h1 : (∑ x ∈ Finset.univ.image (mid (m := k)), F x) =
        ∑ x ∈ (Finset.univ.erase (0 : Fin (k + 2))).erase (Fin.last (k + 1)), F x := by
      refine Finset.sum_subset ?_ ?_
      · intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        simp [mid_ne_zero, mid_ne_last]
      · intro x hx hxnot
        exfalso
        have hx' : x ∉ Set.range (mid (m := k)) := by
          simpa [Finset.mem_image] using hxnot
        rcases RCSTSU.eq_zero_or_eq_last_of_not_mem hx' with rfl | rfl <;> simp at hx
    rw [← h1, Finset.sum_image]
    intro a _ b _ hab
    exact mid_injective hab
  rw [hmid]
  abel

private theorem suA_add {k : ℕ} (a a' : Fin k → K) : suA (a + a') = suA a + suA a' := by
  funext p
  exact congrFun (midExt_add a a') p

private theorem suW_add {k : ℕ} (a a' : Fin k → K) :
    suW f (a + a') = suW f a + suW f a' := by
  funext p
  simp only [suW, suA_add, Pi.add_apply, map_add]

private theorem suW_dot_suA {k : ℕ} (a a' : Fin k → K) :
    suW f a ⬝ᵥ suA a' = aform (unitaryInvolution K 2 f) a a' := by
  rw [aform_apply, dotProduct]
  trans ∑ l : Fin k,
      unitaryInvolution K 2 f (a (Fin.rev l)) * a' l
  · symm
    refine Fintype.sum_of_injective mid mid_injective _ _ ?_ ?_
    · intro p hp
      have hp' : Fin.rev p ∉ Set.range (mid (m := k)) := fun h =>
        hp (rev_mem_range_mid_iff.1 h)
      simp [suW, suA, midExt_eq_zero_of_not_mem hp, midExt_eq_zero_of_not_mem hp']
    · intro l
      simp [suW, suA, midExt_mid, rev_mid]
  · refine Fintype.sum_equiv Fin.revPerm
      (fun l : Fin k => unitaryInvolution K 2 f (a (Fin.rev l)) * a' l)
      (fun l : Fin k => unitaryInvolution K 2 f (a l) * a' (Fin.rev l)) ?_
    intro l
    simp only [Fin.revPerm_apply, Fin.rev_rev]

private theorem suA_zero {k : ℕ} (a : Fin k → K) : suA a 0 = 0 := midExt_zero_apply a

private theorem suW_zero {k : ℕ} : suW f (0 : Fin k → K) = 0 := by
  funext i
  simp [suW, suA, midExt_zero, map_zero]

private theorem suW_last {k : ℕ} (a : Fin k → K) :
    suW f a (Fin.last (k + 1)) = 0 := by
  simp [suW, suA, Fin.rev_last, midExt_zero_apply]

private theorem suN_mul {k : ℕ} (a a' : Fin k → K) (s s' : K) :
    suN f a s * suN f a' s' =
      (aform (unitaryInvolution K 2 f) a a') • suE (K := K) (k := k) := by
  simp only [suN, suE, add_mul, mul_add, smul_mul, Matrix.mul_smul,
    vecMulVec_mul_vecMulVec]
  simp [e0_dot_suA, e0_dot_eL, suW_dot_eL, suW_dot_suA, suA_zero, suW_last]

private theorem SuAdm.add (h : UnitaryFieldData 2 f K) {k : ℕ} {a a' : Fin k → K} {s s' : K}
    (ha : SuAdm (f := f) a s) (ha' : SuAdm (f := f) a' s') :
    SuAdm (f := f) (a + a') (s + s' +
      aform (unitaryInvolution K 2 f) a a') := by
  have hσ : ∀ c, unitaryInvolution K 2 f (unitaryInvolution K 2 f c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive h.card_eq_sq
  unfold SuAdm at *
  rw [aform_add_left, aform_add_right, aform_add_right,
    map_add, map_add, map_aform (unitaryInvolution K 2 f) hσ]
  linear_combination ha + ha'

private theorem suMat_mul {k : ℕ} (a a' : Fin k → K) (s s' : K) :
    suMat f a s * suMat f a' s' =
      suMat f (a + a') (s + s' +
        aform (unitaryInvolution K 2 f) a a') := by
  calc
    suMat f a s * suMat f a' s'
        = (1 + suN f a s) * (1 + suN f a' s') := by rw [suMat, suMat]
    _ = 1 + suN f a s + suN f a' s' + suN f a s * suN f a' s' := by
          rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul,
            Matrix.mul_one, Matrix.one_mul]
          abel
    _ = 1 + suN f a s + suN f a' s' +
          (aform (unitaryInvolution K 2 f) a a') •
            suE (K := K) (k := k) := by
          rw [suN_mul]
    _ = suMat f (a + a') (s + s' +
          aform (unitaryInvolution K 2 f) a a') := by
          rw [suMat, suE, suN, suN, suN, suA_add, suW_add, add_vecMulVec,
            vecMulVec_add, add_smul, add_smul]
          abel

private theorem mul_suM (h : UnitaryFieldData 2 f K) {k : ℕ} (a a' : Fin k → K) (s s' : K)
    (hAdm : SuAdm (f := f) a s) (hAdm' : SuAdm (f := f) a' s') :
    suM h a s hAdm * suM h a' s' hAdm' =
      suM h (a + a') (s + s' + aform (unitaryInvolution K 2 f) a a')
        (hAdm.add h hAdm') := by
  apply mat_injective
  rw [map_mul, mat_suM, mat_suM, mat_suM, suMat_mul]

private theorem SuAdm.bar (h : UnitaryFieldData 2 f K) {k : ℕ} {a : Fin k → K} {s : K}
    (hAdm : SuAdm (f := f) a s) :
    SuAdm (f := f) a (unitaryInvolution K 2 f s) := by
  have hσ : ∀ c, unitaryInvolution K 2 f (unitaryInvolution K 2 f c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive h.card_eq_sq
  unfold SuAdm at *
  rw [hσ s, add_comm]
  exact hAdm

private theorem suAdm_zero {k : ℕ} : SuAdm (f := f) (0 : Fin k → K) 0 := by
  unfold SuAdm
  simp [aform_zero_left]

private noncomputable def suLongRoot {k : ℕ} (i : Fin k) (hi : i ≠ Fin.rev i) :
    SU (unitaryInvolution K 2 f) k :=
  longRootHom (unitaryInvolution K 2 f) hi
    (Multiplicative.ofAdd ⟨1, by rw [mem_traceZero, map_one,
      CharTwo.add_self_eq_zero]⟩)

private theorem mat_suLongRoot {k : ℕ} (i : Fin k) (hi : i ≠ Fin.rev i) :
    mat (unitaryInvolution K 2 f) k (suLongRoot (f := f) i hi) =
      longRootMatrix (F := K) i 1 := by
  rw [suLongRoot]
  exact coe_longRootHom (unitaryInvolution K 2 f) hi _

private theorem suLongRoot_mulVec {k : ℕ} (i : Fin k) (hi : i ≠ Fin.rev i) (c : K) :
    mat (unitaryInvolution K 2 f) k (suLongRoot (f := f) i hi) *ᵥ
        (c • (Pi.single (Fin.rev i) 1 : Fin k → K)) =
      c • (Pi.single (Fin.rev i) 1 : Fin k → K) + c • (Pi.single i 1 : Fin k → K) := by
  rw [mat_suLongRoot]
  funext p
  simp only [longRootMatrix, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.single_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.update_apply,
    Pi.single_apply, Pi.zero_apply]
  by_cases h1 : p = i <;> by_cases h2 : p = Fin.rev i <;>
    simp [h1, h2, hi, Ne.symm hi] <;> ring

private theorem suHeis_mulVec (h : UnitaryFieldData 2 f K) {k : ℕ} (i j : Fin k)
    (hi : i ≠ Fin.rev i) (hij : i ≠ j) (hj : Fin.rev j = j) (b : K) (hb : b + b = 0)
    (hb1 : b + unitaryInvolution K 2 f b = 1) (c : K) :
    mat (unitaryInvolution K 2 f) k (suHeis h i j hi hij hj b hb hb1) *ᵥ
        (c • (Pi.single (Fin.rev i) 1 : Fin k → K)) =
      c • (Pi.single (Fin.rev i) 1 : Fin k → K) + c • (Pi.single j 1 : Fin k → K) +
        (b * c) • (Pi.single i 1 : Fin k → K) := by
  rw [mat_suHeis]
  funext p
  simp only [heisenbergMatrix, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.single_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Function.update_apply, Pi.single_apply, Pi.zero_apply]
  have hrij : Fin.rev i ≠ j := fun hh => hij (by rw [← hj, ← hh, Fin.rev_rev])
  by_cases hp : p = i <;> by_cases hpj : p = j <;> by_cases hpr : p = Fin.rev i <;>
    simp [hp, hpj, hpr, hij, Ne.symm hij, hrij, Ne.symm hrij, hi, Ne.symm hi, hj,
      hb1, map_one, mul_comm, CharTwo.neg_eq] <;> ring

private theorem mat_suElt (h : UnitaryFieldData 2 f K) {k : ℕ} (a : Fin k → K) (s : K)
    (hAdm : SuAdm (f := f) a s) :
    mat (unitaryInvolution K 2 f) (k + 2) (suElt h a s hAdm) =
      eMat (unitaryInvolution K 2 f) (midExt (a ∘ Fin.rev)) s := by
  rw [suElt, mat_eSU]

private theorem conj_suM (h : UnitaryFieldData 2 f K) {k : ℕ}
    (B : SU (unitaryInvolution K 2 f) k) (a : Fin k → K) (s : K)
    (hAdm : SuAdm (f := f) a s) :
    iotaHom B * suM h a s hAdm * (iotaHom B)⁻¹ =
      suM h (mat (unitaryInvolution K 2 f) k B *ᵥ a) s (hAdm.mulVec h B) := by
  have hσ : ∀ c, unitaryInvolution K 2 f (unitaryInvolution K 2 f c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive h.card_eq_sq
  have hE : iotaHom (suB' B) * suElt h a s hAdm * (iotaHom (suB' B))⁻¹ =
      suElt h (mat (unitaryInvolution K 2 f) k B *ᵥ a) s (hAdm.mulVec h B) := by
    apply mat_injective
    have hg : mat (unitaryInvolution K 2 f) (k + 2) (iotaHom (suB' B)) *ᵥ e0 =
        (1 : K) • e0 := by
      rw [mat_iotaHom, iotaMat_mulVec_e0, one_smul]
    have hx : mat (unitaryInvolution K 2 f) (k + 2) (suElt h a s hAdm) =
        eMat (unitaryInvolution K 2 f) (midExt (a ∘ Fin.rev)) s :=
      mat_suElt h a s hAdm
    have hconj := mat_conj_eMat (σ := unitaryInvolution K 2 f) hσ hg hx
    have harg : unitaryInvolution K 2 f 1 •
        (mat (unitaryInvolution K 2 f) (k + 2) (iotaHom (suB' B)) *ᵥ
          midExt (a ∘ Fin.rev)) =
        midExt ((mat (unitaryInvolution K 2 f) k B *ᵥ a) ∘ Fin.rev) := by
      rw [map_one, one_smul, mat_iotaHom, iotaMat_mulVec_midExt, suB'_mulVec_midExt]
    have hc : unitaryInvolution K 2 f 1 * 1 * s = s := by simp
    rw [harg, hc] at hconj
    rw [hconj, mat_suElt]
  have hinv : (iotaHom B)⁻¹ = suJ (K := K) (f := f) (k := k) *
      (iotaHom (suB' B))⁻¹ * suJ (K := K) (f := f) (k := k) := by
    rw [iotaHom_eq_suJ_mul B]
    simp only [_root_.mul_inv_rev, inv_suJ]
    group
  calc
    iotaHom B * suM h a s hAdm * (iotaHom B)⁻¹
        = suJ (K := K) (f := f) (k := k) *
            (iotaHom (suB' B) * suElt h a s hAdm * (iotaHom (suB' B))⁻¹) *
            suJ (K := K) (f := f) (k := k) := by
          rw [hinv, iotaHom_eq_suJ_mul B]
          simp only [suM, inv_suJ]
          group
          have hAssoc : suJ (K := K) (f := f) (k := k) * iotaHom (suB' B) *
              suJ (K := K) (f := f) (k := k) * suJ (K := K) (f := f) (k := k) *
              suElt h a s hAdm * suJ (K := K) (f := f) (k := k) *
              suJ (K := K) (f := f) (k := k) =
              suJ (K := K) (f := f) (k := k) * iotaHom (suB' B) *
              (suJ (K := K) (f := f) (k := k) * suJ (K := K) (f := f) (k := k)) *
              suElt h a s hAdm *
              (suJ (K := K) (f := f) (k := k) * suJ (K := K) (f := f) (k := k)) := by
            group
          rw [hAssoc, suJ_mul_self, mul_one, mul_one]
    _ = suJ (K := K) (f := f) (k := k) *
          suElt h (mat (unitaryInvolution K 2 f) k B *ᵥ a) s (hAdm.mulVec h B) *
          suJ (K := K) (f := f) (k := k) := by rw [hE]
    _ = suM h (mat (unitaryInvolution K 2 f) k B *ᵥ a) s (hAdm.mulVec h B) := by
          rw [suM]

private theorem suM_congr (h : UnitaryFieldData 2 f K) {k : ℕ} {a : Fin k → K} {s : K}
    (h₁ h₂ : SuAdm (f := f) a s) : suM h a s h₁ = suM h a s h₂ := by
  apply mat_injective
  simp only [mat_suM]

private theorem suM_zero (h : UnitaryFieldData 2 f K) {k : ℕ} :
    suM h (0 : Fin k → K) 0 (suAdm_zero (f := f) (k := k)) = 1 := by
  apply mat_injective
  rw [mat_suM, map_one, suMat, suN]
  simp [suA, suW, suW_zero, midExt_zero, map_zero, vecMulVec_zero]

private theorem suM_mul_inv (h : UnitaryFieldData 2 f K) {k : ℕ} (a : Fin k → K) (s : K)
    (hAdm : SuAdm (f := f) a s) :
    suM h a s hAdm * suM h a (unitaryInvolution K 2 f s) (hAdm.bar h) = 1 := by
  apply mat_injective
  rw [map_mul, mat_suM, mat_suM, map_one, suMat_mul]
  have ha : a + a = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  have hs : s + unitaryInvolution K 2 f s +
      aform (unitaryInvolution K 2 f) a a = 0 := by
    rw [hAdm, CharTwo.add_self_eq_zero]
  rw [ha, hs, suMat, suN]
  simp [suA, suW, suW_zero, midExt_zero, map_zero, vecMulVec_zero]

private theorem suM_inv (h : UnitaryFieldData 2 f K) {k : ℕ} (a : Fin k → K) (s : K)
    (hAdm : SuAdm (f := f) a s) :
    (suM h a s hAdm)⁻¹ = suM h a (unitaryInvolution K 2 f s) (hAdm.bar h) := by
  rw [inv_eq_iff_mul_eq_one]
  exact suM_mul_inv h a s hAdm

private theorem suMat_mul_one_add_suE {k : ℕ} (a : Fin k → K) (s : K) :
    suMat f a s * (1 + suE (K := K) (k := k)) =
      (1 + suE (K := K) (k := k)) * suMat f a s := by
  simp only [suMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    suN_mul_suE, suE_mul_suN, add_zero]
  abel

private theorem suM_mem_suRad (h : UnitaryFieldData 2 f K) {k : ℕ} (a : Fin k → K) (s : K)
    (hAdm : SuAdm (f := f) a s) :
    suM h a s hAdm ∈ RCSTSU.suRad (unitaryInvolution K 2 f) k := by
  refine RCSTSU.mem_suRad.mpr ⟨?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply mat_injective
    rw [map_mul, map_mul, mat_suM, RCSTSU.mat_ggInvSU_one, RootCentSU.ggInvUMatrix_one_eq,
      ← suE_eq_single]
    exact suMat_mul_one_add_suE a s
  · rw [mat_suM, suMat_last_last]
  · ext i j
    rw [Matrix.submatrix_apply, mat_suM, suMat_mid_mid]
    simp [Matrix.one_apply, mid_injective.eq_iff]

private theorem suRad_exists_suM (h : UnitaryFieldData 2 f K) {k : ℕ}
    {x : SU (unitaryInvolution K 2 f) (k + 2)}
    (hx : x ∈ RCSTSU.suRad (unitaryInvolution K 2 f) k) :
    ∃ (a : Fin k → K) (s : K) (hAdm : SuAdm (f := f) a s), x = suM h a s hAdm := by
  obtain ⟨hC, hcorner, hmid⟩ := RCSTSU.mem_suRad.mp hx
  have hA := RCSTSU.commute_of_mem hC
  have hrow : ∀ b, mat (unitaryInvolution K 2 f) (k + 2) x 0 b =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) K) 0 b := by
    intro b
    rw [RootCentSU.row_zero_of_commute hA b, hcorner, Matrix.one_apply]
    by_cases hb : b = 0 <;> simp [hb, eq_comm]
  have hcol : ∀ a, mat (unitaryInvolution K 2 f) (k + 2) x a (Fin.last (k + 1)) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) K) a (Fin.last (k + 1)) := by
    intro a
    have h00 : mat (unitaryInvolution K 2 f) (k + 2) x 0 0 = 1 := by
      rw [← RootCentSU.corner_eq_of_commute hA, hcorner]
    rw [RootCentSU.col_last_of_commute hA a, h00, Matrix.one_apply]
  have hmid' : ∀ i j : Fin k,
      mat (unitaryInvolution K 2 f) (k + 2) x (mid i) (mid j) =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) K) (mid i) (mid j) := by
    intro i j
    have := congrFun (congrFun hmid i) j
    simpa [Matrix.submatrix_apply, Matrix.one_apply, mid_injective.eq_iff] using this
  let a : Fin k → K := fun i => mat (unitaryInvolution K 2 f) (k + 2) x (mid i) 0
  let s : K := mat (unitaryInvolution K 2 f) (k + 2) x (Fin.last (k + 1)) 0
  have hAdm : SuAdm (f := f) a s := by
    unfold SuAdm
    rw [aform_apply]
    have hsum := CFSG.LieType.Universal.Unitary.SUExtras.sum_mat_mul_mat x 0 0
    rw [sum_univ_eq_zero_add_last_add_mid
      (fun t => unitaryInvolution K 2 f (mat (unitaryInvolution K 2 f) (k + 2) x t 0) *
        mat (unitaryInvolution K 2 f) (k + 2) x (Fin.rev t) 0)] at hsum
    have h0 : unitaryInvolution K 2 f (mat (unitaryInvolution K 2 f) (k + 2) x 0 0) *
        mat (unitaryInvolution K 2 f) (k + 2) x (Fin.rev 0) 0 = s := by
      rw [hrow 0, Fin.rev_zero]
      simp [s]
    have hl : unitaryInvolution K 2 f
        (mat (unitaryInvolution K 2 f) (k + 2) x (Fin.last (k + 1)) 0) *
        mat (unitaryInvolution K 2 f) (k + 2) x (Fin.rev (Fin.last (k + 1))) 0 =
          unitaryInvolution K 2 f s := by
      rw [Fin.rev_last, hrow 0]
      simp [s]
    have hm : ∀ i : Fin k, unitaryInvolution K 2 f
        (mat (unitaryInvolution K 2 f) (k + 2) x (mid i) 0) *
        mat (unitaryInvolution K 2 f) (k + 2) x (Fin.rev (mid i)) 0 =
          unitaryInvolution K 2 f (a i) * a (Fin.rev i) := by
      intro i
      rw [rev_mid]
    rw [h0, hl, Finset.sum_congr rfl (fun i _ => hm i)] at hsum
    simp [Fin.rev_zero, zero_ne_last] at hsum
    exact CharTwo.add_eq_zero.mp hsum
  have hlastmid : ∀ j : Fin k,
      mat (unitaryInvolution K 2 f) (k + 2) x (Fin.last (k + 1)) (mid j) =
        suW f a (mid j) := by
    intro j
    have hsum := CFSG.LieType.Universal.Unitary.SUExtras.sum_mat_mul_mat x 0 (mid j)
    rw [sum_univ_eq_zero_add_last_add_mid
      (fun t => unitaryInvolution K 2 f (mat (unitaryInvolution K 2 f) (k + 2) x t 0) *
        mat (unitaryInvolution K 2 f) (k + 2) x (Fin.rev t) (mid j))] at hsum
    have h0 : unitaryInvolution K 2 f (mat (unitaryInvolution K 2 f) (k + 2) x 0 0) *
        mat (unitaryInvolution K 2 f) (k + 2) x (Fin.rev 0) (mid j) =
          mat (unitaryInvolution K 2 f) (k + 2) x (Fin.last (k + 1)) (mid j) := by
      rw [hrow 0, Fin.rev_zero]
      simp
    have hl : unitaryInvolution K 2 f
        (mat (unitaryInvolution K 2 f) (k + 2) x (Fin.last (k + 1)) 0) *
        mat (unitaryInvolution K 2 f) (k + 2) x (Fin.rev (Fin.last (k + 1))) (mid j) = 0 := by
      rw [Fin.rev_last, hrow (mid j)]
      simp [Matrix.one_apply, mid_ne_zero j, Ne.symm (mid_ne_zero j)]
    have hm : ∑ i : Fin k, unitaryInvolution K 2 f
        (mat (unitaryInvolution K 2 f) (k + 2) x (mid i) 0) *
        mat (unitaryInvolution K 2 f) (k + 2) x (Fin.rev (mid i)) (mid j) =
          unitaryInvolution K 2 f (a (Fin.rev j)) := by
      rw [Finset.sum_eq_single (Fin.rev j)]
      · rw [rev_mid, hmid']
        simp [Fin.rev_rev, Matrix.one_apply, mid_injective.eq_iff]
        rfl
      · intro i _ hi
        rw [rev_mid, hmid']
        have hne : ¬ mid (Fin.rev i) = mid j := fun h => hi (by
          rw [← Fin.rev_rev i, mid_injective h])
        simp [Matrix.one_apply, hne]
      · simp
    rw [h0, hl, hm, Fin.rev_zero, if_neg (mid_ne_last j), add_zero] at hsum
    have hxlast := CharTwo.add_eq_zero.mp hsum
    rw [hxlast]
    rw [suW, suA, rev_mid, midExt_mid]
  have hmat : mat (unitaryInvolution K 2 f) (k + 2) x = suMat f a s := by
    ext i j
    by_cases hi0 : i = 0
    · subst hi0
      rw [hrow, suMat_row_zero]
    · by_cases hil : i = Fin.last (k + 1)
      · subst hil
        by_cases hj0 : j = 0
        · subst hj0
          rw [show mat (unitaryInvolution K 2 f) (k + 2) x (Fin.last (k + 1)) 0 = s from rfl,
            suMat_last_zero]
        · by_cases hjl : j = Fin.last (k + 1)
          · subst hjl
            rw [hcorner, suMat_last_last]
          · have hj_mid : j ∈ Set.range (mid (m := k)) := by
              by_contra hj
              rcases RCSTSU.eq_zero_or_eq_last_of_not_mem hj with h0 | hl
              · exact hj0 h0
              · exact hjl hl
            obtain ⟨l, rfl⟩ := hj_mid
            rw [hlastmid l, suMat_last_mid]
      · have hi_mid : i ∈ Set.range (mid (m := k)) := by
          by_contra hi
          rcases RCSTSU.eq_zero_or_eq_last_of_not_mem hi with h0 | hl
          · exact hi0 h0
          · exact hil hl
        obtain ⟨m, rfl⟩ := hi_mid
        by_cases hj0 : j = 0
        · subst hj0
          rw [show mat (unitaryInvolution K 2 f) (k + 2) x (mid m) 0 = a m from rfl,
            suMat_mid_zero]
        · by_cases hjl : j = Fin.last (k + 1)
          · subst hjl
            rw [hcol, suMat_col_last]
          · have hj_mid : j ∈ Set.range (mid (m := k)) := by
              by_contra hj
              rcases RCSTSU.eq_zero_or_eq_last_of_not_mem hj with h0 | hl
              · exact hj0 h0
              · exact hjl hl
            obtain ⟨l, rfl⟩ := hj_mid
            rw [hmid', suMat_mid_mid]
  refine ⟨a, s, hAdm, ?_⟩
  apply mat_injective
  rw [hmat, mat_suM]

private noncomputable def suVec {k : ℕ} (x : RCSTSU.suRad (unitaryInvolution K 2 f) k) :
    Fin k → K :=
  fun i => mat (unitaryInvolution K 2 f) (k + 2)
    (x : SU (unitaryInvolution K 2 f) (k + 2)) (mid i) 0

private theorem suVec_suM (h : UnitaryFieldData 2 f K) {k : ℕ} (a : Fin k → K) (s : K)
    (hAdm : SuAdm (f := f) a s) :
    suVec ⟨suM h a s hAdm, suM_mem_suRad h a s hAdm⟩ = a := by
  funext i
  rw [suVec, mat_suM, suMat_mid_zero]

private theorem suVec_mul (h : UnitaryFieldData 2 f K) {k : ℕ}
    (x y : RCSTSU.suRad (unitaryInvolution K 2 f) k) :
    suVec (x * y) = suVec x + suVec y := by
  obtain ⟨a, s, hAdm, hx⟩ := suRad_exists_suM h x.2
  obtain ⟨a', s', hAdm', hy⟩ := suRad_exists_suM h y.2
  have hxsub : x = ⟨suM h a s hAdm, suM_mem_suRad h a s hAdm⟩ := Subtype.ext hx
  have hysub : y = ⟨suM h a' s' hAdm', suM_mem_suRad h a' s' hAdm'⟩ :=
    Subtype.ext hy
  have hEq : ((⟨suM h a s hAdm, suM_mem_suRad h a s hAdm⟩ *
      ⟨suM h a' s' hAdm', suM_mem_suRad h a' s' hAdm'⟩ :
        RCSTSU.suRad (unitaryInvolution K 2 f) k) :
        SU (unitaryInvolution K 2 f) (k + 2)) =
      suM h (a + a') (s + s' + aform (unitaryInvolution K 2 f) a a')
        (hAdm.add h hAdm') := by
    rw [Subgroup.coe_mul, mul_suM]
  have hEqsub : (⟨suM h a s hAdm, suM_mem_suRad h a s hAdm⟩ *
      ⟨suM h a' s' hAdm', suM_mem_suRad h a' s' hAdm'⟩ :
        RCSTSU.suRad (unitaryInvolution K 2 f) k) =
      ⟨suM h (a + a') (s + s' + aform (unitaryInvolution K 2 f) a a')
        (hAdm.add h hAdm'), suM_mem_suRad h (a + a')
        (s + s' + aform (unitaryInvolution K 2 f) a a') (hAdm.add h hAdm')⟩ :=
    Subtype.ext hEq
  rw [hxsub, hysub, hEqsub, suVec_suM, suVec_suM, suVec_suM]

private theorem suCommutator_mem (h : UnitaryFieldData 2 f K) {k : ℕ}
    (B : SU (unitaryInvolution K 2 f) k) (a : Fin k → K) (s : K)
    (hAdm : SuAdm (f := f) a s) :
    ⁅iotaHom B, suM h a s hAdm⁆ ∈ RCSTSU.suRad (unitaryInvolution K 2 f) k := by
  have hu : iotaHom B ∈ Subgroup.normalizer
      ((RCSTSU.suRad (unitaryInvolution K 2 f) k : Subgroup
        (SU (unitaryInvolution K 2 f) (k + 2))) : Set _) :=
    RCSTSU.centralizer_le_normalizer_suRad (σ := unitaryInvolution K 2 f) (k := k)
      (RCSTSU.range_iotaHom_le_centralizer ⟨B, rfl⟩)
  have hr : suM h a s hAdm ∈ RCSTSU.suRad (unitaryInvolution K 2 f) k :=
    suM_mem_suRad h a s hAdm
  have hc : iotaHom B * suM h a s hAdm * (iotaHom B)⁻¹ ∈
      RCSTSU.suRad (unitaryInvolution K 2 f) k :=
    (Subgroup.mem_normalizer_iff.mp hu (suM h a s hAdm)).1 hr
  rw [commutatorElement_def]
  exact mul_mem hc (inv_mem hr)

private noncomputable def suCommutator (h : UnitaryFieldData 2 f K) {k : ℕ}
    (B : SU (unitaryInvolution K 2 f) k) (a : Fin k → K) (s : K)
    (hAdm : SuAdm (f := f) a s) :
    RCSTSU.suRad (unitaryInvolution K 2 f) k :=
  ⟨⁅iotaHom B, suM h a s hAdm⁆, suCommutator_mem h B a s hAdm⟩

private theorem suVec_suCommutator (h : UnitaryFieldData 2 f K) {k : ℕ}
    (B : SU (unitaryInvolution K 2 f) k) (a : Fin k → K) (s : K)
    (hAdm : SuAdm (f := f) a s) :
    suVec (suCommutator h B a s hAdm) =
      mat (unitaryInvolution K 2 f) k B *ᵥ a + a := by
  have hEq : (suCommutator h B a s hAdm : SU (unitaryInvolution K 2 f) (k + 2)) =
      suM h (mat (unitaryInvolution K 2 f) k B *ᵥ a + a)
        (s + unitaryInvolution K 2 f s +
          aform (unitaryInvolution K 2 f) (mat (unitaryInvolution K 2 f) k B *ᵥ a) a)
        ((hAdm.mulVec h B).add h (hAdm.bar h)) := by
    change ⁅iotaHom B, suM h a s hAdm⁆ = _
    rw [commutatorElement_def, conj_suM h B a s hAdm, suM_inv h a s hAdm, mul_suM]
  have hEqsub : suCommutator h B a s hAdm =
      ⟨suM h (mat (unitaryInvolution K 2 f) k B *ᵥ a + a)
        (s + unitaryInvolution K 2 f s +
          aform (unitaryInvolution K 2 f) (mat (unitaryInvolution K 2 f) k B *ᵥ a) a)
        ((hAdm.mulVec h B).add h (hAdm.bar h)),
        suM_mem_suRad h (mat (unitaryInvolution K 2 f) k B *ᵥ a + a)
          (s + unitaryInvolution K 2 f s +
            aform (unitaryInvolution K 2 f) (mat (unitaryInvolution K 2 f) k B *ᵥ a) a)
          ((hAdm.mulVec h B).add h (hAdm.bar h))⟩ :=
    Subtype.ext hEq
  rw [hEqsub, suVec_suM]

private theorem suVec_inv (h : UnitaryFieldData 2 f K) {k : ℕ}
    (x : RCSTSU.suRad (unitaryInvolution K 2 f) k) :
    suVec x⁻¹ = suVec x := by
  obtain ⟨a, s, hAdm, hx⟩ := suRad_exists_suM h x.2
  have hxsub : x = ⟨suM h a s hAdm, suM_mem_suRad h a s hAdm⟩ := Subtype.ext hx
  have hEq : (⟨suM h a s hAdm, suM_mem_suRad h a s hAdm⟩ :
        RCSTSU.suRad (unitaryInvolution K 2 f) k)⁻¹ =
      ⟨suM h a (unitaryInvolution K 2 f s) (hAdm.bar h),
        suM_mem_suRad h a (unitaryInvolution K 2 f s) (hAdm.bar h)⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_inv, suM_inv]
  rw [hxsub, hEq, suVec_suM, suVec_suM]

private noncomputable abbrev suRadP {k : ℕ} : Subgroup (SU (unitaryInvolution K 2 f) (k + 2)) :=
  RCSTSU.suRad (unitaryInvolution K 2 f) k

private noncomputable abbrev suUP {k : ℕ} : Subgroup (SU (unitaryInvolution K 2 f) (k + 2)) :=
  (iotaHom (σ := unitaryInvolution K 2 f) (m := k)).range

private noncomputable abbrev suHP {k : ℕ} : Subgroup (SU (unitaryInvolution K 2 f) (k + 2)) :=
  (⁅suRadP (K := K) (f := f) (k := k) ⊔ suUP (K := K) (f := f) (k := k),
    suRadP (K := K) (f := f) (k := k) ⊔ suUP (K := K) (f := f) (k := k)⁆ :
    Subgroup (SU (unitaryInvolution K 2 f) (k + 2)))

private theorem exists_commutator_suVec_nonself (h : UnitaryFieldData 2 f K) {k : ℕ}
    (j : Fin k) (hj : j ≠ Fin.rev j) (c : K) :
    ∃ y : suRadP (K := K) (f := f) (k := k),
      (y : SU (unitaryInvolution K 2 f) (k + 2)) ∈
        suHP (K := K) (f := f) (k := k) ∧
      suVec y = c • (Pi.single j 1 : Fin k → K) := by
  obtain ⟨s, hAdm⟩ := exists_suAdm h (c • (Pi.single (Fin.rev j) 1 : Fin k → K))
  refine ⟨suCommutator h (suLongRoot (f := f) j hj)
    (c • (Pi.single (Fin.rev j) 1 : Fin k → K)) s hAdm, ?_, ?_⟩
  · change ⁅iotaHom (suLongRoot (f := f) j hj),
      suM h (c • (Pi.single (Fin.rev j) 1 : Fin k → K)) s hAdm⁆ ∈
        suHP (K := K) (f := f) (k := k)
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_sup_right ⟨suLongRoot (f := f) j hj, rfl⟩)
      (Subgroup.mem_sup_left
        (suM_mem_suRad h (c • (Pi.single (Fin.rev j) 1 : Fin k → K)) s hAdm))
  · rw [suVec_suCommutator, suLongRoot_mulVec]
    funext p
    simp [Pi.add_apply, Pi.smul_apply, CharTwo.add_self_eq_zero, add_assoc, add_comm,
      add_left_comm]

private theorem exists_commutator_suVec_self (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k)
    (j : Fin k) (hj : Fin.rev j = j) (c : K) :
    ∃ y : suRadP (K := K) (f := f) (k := k),
      (y : SU (unitaryInvolution K 2 f) (k + 2)) ∈
        suHP (K := K) (f := f) (k := k) ∧
      suVec y = c • (Pi.single j 1 : Fin k → K) := by
  haveI : NeZero k := ⟨by omega⟩
  have hi : (0 : Fin k) ≠ Fin.rev 0 := by
    intro h0
    have hv := congrArg Fin.val h0
    rw [Fin.val_rev, Fin.val_zero] at hv
    omega
  have hij : (0 : Fin k) ≠ j := by
    intro h0
    apply hi
    rw [h0]
    exact hj.symm
  obtain ⟨b, hb'⟩ := CFSG.SeitzReduction.UnitaryPilot.exists_add_bar_eq h (by rw [map_one])
  have hb1 : b + unitaryInvolution K 2 f b = 1 := by
    rwa [RootDetectSU.bar_eq h] at hb'
  have hb : b + b = 0 := CharTwo.add_self_eq_zero b
  let B : SU (unitaryInvolution K 2 f) k := suHeis h 0 j hi hij hj b hb hb1
  let a0 : Fin k → K := c • (Pi.single (Fin.rev (0 : Fin k)) 1 : Fin k → K)
  obtain ⟨s0, hAdm0⟩ := exists_suAdm h a0
  let y1 : suRadP (K := K) (f := f) (k := k) := suCommutator h B a0 s0 hAdm0
  have hy1mem : (y1 : SU (unitaryInvolution K 2 f) (k + 2)) ∈
      suHP (K := K) (f := f) (k := k) := by
    change ⁅iotaHom B, suM h a0 s0 hAdm0⁆ ∈ suHP (K := K) (f := f) (k := k)
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_sup_right ⟨B, rfl⟩)
      (Subgroup.mem_sup_left (suM_mem_suRad h a0 s0 hAdm0))
  have hy1vec : suVec y1 = c • (Pi.single j 1 : Fin k → K) +
      (b * c) • (Pi.single (0 : Fin k) 1 : Fin k → K) := by
    dsimp only [B, a0, y1]
    rw [suVec_suCommutator]
    have h := suHeis_mulVec h 0 j hi hij hj b hb hb1 c
    rw [h]
    funext p
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, CharTwo.add_self_eq_zero, add_assoc,
      add_comm, add_left_comm, mul_comm]
  obtain ⟨y2, hy2mem, hy2vec⟩ := exists_commutator_suVec_nonself h (0 : Fin k) hi (b * c)
  refine ⟨y1 * y2⁻¹, ?_, ?_⟩
  · exact Subgroup.mul_mem (H := suHP (K := K) (f := f) (k := k)) hy1mem
      (Subgroup.inv_mem (H := suHP (K := K) (f := f) (k := k)) hy2mem)
  · rw [suVec_mul h, suVec_inv h, hy1vec, hy2vec]
    funext p
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, CharTwo.add_self_eq_zero, add_assoc,
      add_comm, add_left_comm, mul_comm]

private theorem exists_commutator_suM_zero (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k)
    (t : K) (ht : t + unitaryInvolution K 2 f t = 0) :
    ∃ y : suRadP (K := K) (f := f) (k := k),
      (y : SU (unitaryInvolution K 2 f) (k + 2)) ∈
        suHP (K := K) (f := f) (k := k) ∧
      (y : SU (unitaryInvolution K 2 f) (k + 2)) =
        suM h 0 t (by
          unfold SuAdm
          rw [aform_zero_left]
          exact ht) := by
  haveI : NeZero k := ⟨by omega⟩
  have ht' : h.bar t = t := by
    rw [RootDetectSU.bar_eq h]
    exact (CharTwo.add_eq_zero.mp ht).symm
  obtain ⟨α, hα⟩ := CFSG.SeitzReduction.UnitaryPilot.exists_add_bar_eq h ht'
  have hα' : α + unitaryInvolution K 2 f α = t := by
    rwa [RootDetectSU.bar_eq h] at hα
  let a : Fin k → K := α • (Pi.single (0 : Fin k) 1 : Fin k → K)
  let b : Fin k → K := (Pi.single (Fin.rev (0 : Fin k)) 1 : Fin k → K)
  obtain ⟨s1, hAdm1⟩ := exists_suAdm h a
  obtain ⟨s2, hAdm2⟩ := exists_suAdm h b
  let x : suRadP (K := K) (f := f) (k := k) :=
    ⟨suM h a s1 hAdm1, suM_mem_suRad h a s1 hAdm1⟩
  let z : suRadP (K := K) (f := f) (k := k) :=
    ⟨suM h b s2 hAdm2, suM_mem_suRad h b s2 hAdm2⟩
  have hRcomm : ⁅suRadP (K := K) (f := f) (k := k),
      suRadP (K := K) (f := f) (k := k)⁆ ≤
      suRadP (K := K) (f := f) (k := k) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (suRadP (K := K) (f := f) (k := k)).mul_mem
      ((suRadP (K := K) (f := f) (k := k)).mul_mem
        ((suRadP (K := K) (f := f) (k := k)).mul_mem ha hb)
        ((suRadP (K := K) (f := f) (k := k)).inv_mem ha))
      ((suRadP (K := K) (f := f) (k := k)).inv_mem hb)
  let y : suRadP (K := K) (f := f) (k := k) :=
    ⟨⁅(x : SU (unitaryInvolution K 2 f) (k + 2)),
        (z : SU (unitaryInvolution K 2 f) (k + 2))⁆,
      hRcomm (Subgroup.commutator_mem_commutator x.2 z.2)⟩
  refine ⟨y, ?_, ?_⟩
  · change ⁅(x : SU (unitaryInvolution K 2 f) (k + 2)),
        (z : SU (unitaryInvolution K 2 f) (k + 2))⁆ ∈
      suHP (K := K) (f := f) (k := k)
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_left z.2)
  · change ⁅(x : SU (unitaryInvolution K 2 f) (k + 2)),
        (z : SU (unitaryInvolution K 2 f) (k + 2))⁆ =
      suM h 0 t (by unfold SuAdm; rw [aform_zero_left]; exact ht)
    rw [commutatorElement_def]
    change ((suM h a s1 hAdm1 * suM h b s2 hAdm2) * (suM h a s1 hAdm1)⁻¹) *
        (suM h b s2 hAdm2)⁻¹ = _
    rw [suM_inv h b s2 hAdm2, suM_inv h a s1 hAdm1,
      mul_suM, mul_suM, mul_suM]
    have hav : a + b + a + b = 0 := by
      funext p
      simp [a, b, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        CharTwo.add_self_eq_zero, add_assoc, add_comm, add_left_comm]
    have hab : aform (unitaryInvolution K 2 f) a b =
        unitaryInvolution K 2 f α := by
      rw [aform_apply, Finset.sum_eq_single 0]
      · simp [a, b, Pi.single_apply, Fin.rev_zero]
      · intro x _ hx
        simp [a, Pi.smul_apply, Pi.single_apply, hx]
      · simp
    have hba : aform (unitaryInvolution K 2 f) b a = α := by
      rw [aform_apply, Finset.sum_eq_single (Fin.rev (0 : Fin k))]
      · simp [a, b, Pi.single_apply, Fin.rev_zero]
      · intro x _ hx
        simp [b, Pi.single_apply, hx]
      · simp
    have h1 := hAdm1
    have h2 := hAdm2
    unfold SuAdm at h1 h2
    have hsv : s1 + s2 + aform (unitaryInvolution K 2 f) a b +
        unitaryInvolution K 2 f s1 +
        aform (unitaryInvolution K 2 f) (a + b) a +
        unitaryInvolution K 2 f s2 +
        aform (unitaryInvolution K 2 f) (a + b + a) b = t := by
      rw [aform_add_left, aform_add_left, aform_add_left, hab, hba]
      have hgroup : s1 + s2 + unitaryInvolution K 2 f α +
          unitaryInvolution K 2 f s1 +
          (aform (unitaryInvolution K 2 f) a a + α) +
          unitaryInvolution K 2 f s2 +
          (unitaryInvolution K 2 f α + aform (unitaryInvolution K 2 f) b b +
            unitaryInvolution K 2 f α) =
          (s1 + unitaryInvolution K 2 f s1) +
          (s2 + unitaryInvolution K 2 f s2) +
          aform (unitaryInvolution K 2 f) a a +
          aform (unitaryInvolution K 2 f) b b +
          (α + unitaryInvolution K 2 f α) +
          (unitaryInvolution K 2 f α + unitaryInvolution K 2 f α) := by
        abel
      rw [hgroup, h1, h2, hα']
      simp [CharTwo.add_self_eq_zero, add_assoc, add_comm, add_left_comm]
    apply mat_injective
    rw [mat_suM, mat_suM, hav, hsv]

private theorem suAdm_zero_of_trace (h : UnitaryFieldData 2 f K) {k : ℕ} {t : K}
    (ht : t + unitaryInvolution K 2 f t = 0) :
    SuAdm (f := f) (0 : Fin k → K) t := by
  unfold SuAdm
  rw [aform_zero_left]
  exact ht

private theorem suVec_one (h : UnitaryFieldData 2 f K) {k : ℕ} :
    suVec (1 : suRadP (K := K) (f := f) (k := k)) = 0 := by
  have h1 : (1 : suRadP (K := K) (f := f) (k := k)) =
      ⟨suM h 0 0 (suAdm_zero (f := f) (k := k)),
        suM_mem_suRad h 0 0 (suAdm_zero (f := f) (k := k))⟩ :=
    Subtype.ext (suM_zero h).symm
  rw [h1, suVec_suM]

private theorem exists_mem_suHP_suVec_eq (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k)
    (a : Fin k → K) :
    ∃ y : suRadP (K := K) (f := f) (k := k),
      (y : SU (unitaryInvolution K 2 f) (k + 2)) ∈
        suHP (K := K) (f := f) (k := k) ∧ suVec y = a := by
  classical
  let P : Finset (Fin k) → Prop := fun s =>
    ∃ y : suRadP (K := K) (f := f) (k := k),
      (y : SU (unitaryInvolution K 2 f) (k + 2)) ∈
        suHP (K := K) (f := f) (k := k) ∧
      suVec y = ∑ j ∈ s, a j • (Pi.single j 1 : Fin k → K)
  have hP : ∀ s : Finset (Fin k), P s := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [suVec_one h]
        simp
    | insert j s hj ih =>
        obtain ⟨y, hy, hyvec⟩ := ih
        by_cases hjm : j = Fin.rev j
        · obtain ⟨w, hw, hwvec⟩ := exists_commutator_suVec_self h hk j hjm.symm (a j)
          refine ⟨y * w, ?_, ?_⟩
          · exact Subgroup.mul_mem (H := suHP (K := K) (f := f) (k := k)) hy hw
          · rw [suVec_mul h, hyvec, hwvec, Finset.sum_insert hj]
            abel
        · obtain ⟨w, hw, hwvec⟩ := exists_commutator_suVec_nonself h j hjm (a j)
          refine ⟨y * w, ?_, ?_⟩
          · exact Subgroup.mul_mem (H := suHP (K := K) (f := f) (k := k)) hy hw
          · rw [suVec_mul h, hyvec, hwvec, Finset.sum_insert hj]
            abel
  obtain ⟨y, hy, hyvec⟩ := hP Finset.univ
  refine ⟨y, hy, ?_⟩
  rw [hyvec]
  funext p
  simp [Finset.sum_apply, Pi.single_apply]

theorem commutator_suRad_sup_range_iotaHom (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k)
    (hL : ⁅(iotaHom (σ := unitaryInvolution K 2 f) (m := k)).range,
      (iotaHom (σ := unitaryInvolution K 2 f) (m := k)).range⁆ =
      (iotaHom (σ := unitaryInvolution K 2 f) (m := k)).range) :
    ⁅RCSTSU.suRad (unitaryInvolution K 2 f) k ⊔
        (iotaHom (σ := unitaryInvolution K 2 f) (m := k)).range,
      RCSTSU.suRad (unitaryInvolution K 2 f) k ⊔
        (iotaHom (σ := unitaryInvolution K 2 f) (m := k)).range⁆ =
      RCSTSU.suRad (unitaryInvolution K 2 f) k ⊔
        (iotaHom (σ := unitaryInvolution K 2 f) (m := k)).range := by
  change ⁅suRadP (K := K) (f := f) (k := k) ⊔ suUP (K := K) (f := f) (k := k),
      suRadP (K := K) (f := f) (k := k) ⊔ suUP (K := K) (f := f) (k := k)⁆ =
    suRadP (K := K) (f := f) (k := k) ⊔ suUP (K := K) (f := f) (k := k)
  have hUle : suUP (K := K) (f := f) (k := k) ≤ suHP (K := K) (f := f) (k := k) := by
    have hmono : ⁅suUP (K := K) (f := f) (k := k),
        suUP (K := K) (f := f) (k := k)⁆ ≤
        suHP (K := K) (f := f) (k := k) :=
      Subgroup.commutator_mono (le_sup_right) (le_sup_right)
    rwa [hL] at hmono
  have hRle : suRadP (K := K) (f := f) (k := k) ≤
      suHP (K := K) (f := f) (k := k) := by
    intro x hx
    obtain ⟨y, hyH, hyv⟩ := exists_mem_suHP_suVec_eq h hk (suVec ⟨x, hx⟩)
    let z : suRadP (K := K) (f := f) (k := k) :=
      ⟨x * (y : SU (unitaryInvolution K 2 f) (k + 2))⁻¹,
        (suRadP (K := K) (f := f) (k := k)).mul_mem hx
          ((suRadP (K := K) (f := f) (k := k)).inv_mem y.2)⟩
    have hzvec : suVec z = 0 := by
      change suVec (⟨x, hx⟩ * y⁻¹) = 0
      rw [suVec_mul h, suVec_inv h, hyv]
      funext p
      simp [Pi.add_apply, CharTwo.add_self_eq_zero]
    obtain ⟨a', s', hAdm', hz⟩ := suRad_exists_suM h z.2
    have hzsub : z = ⟨suM h a' s' hAdm', suM_mem_suRad h a' s' hAdm'⟩ :=
      Subtype.ext hz
    have ha' : a' = 0 := by
      rw [hzsub, suVec_suM] at hzvec
      exact hzvec
    subst ha'
    have ht : s' + unitaryInvolution K 2 f s' = 0 := by
      have hh := hAdm'
      unfold SuAdm at hh
      rw [aform_zero_left] at hh
      exact hh
    obtain ⟨y0, hy0H, hy0eq⟩ := exists_commutator_suM_zero h hk s' ht
    have hzy0 : z = y0 := by
      apply Subtype.ext
      rw [hz, hy0eq, suM_congr h hAdm' (suAdm_zero_of_trace h ht)]
    have hxeq : x = z * y := by
      apply Subtype.ext
      dsimp only [z]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hxeq]
    refine (suHP (K := K) (f := f) (k := k)).mul_mem ?_ hyH
    show (z : SU (unitaryInvolution K 2 f) (k + 2)) ∈ suHP (K := K) (f := f) (k := k)
    rw [hzy0]
    exact hy0H
  have hAll : suRadP (K := K) (f := f) (k := k) ⊔
      suUP (K := K) (f := f) (k := k) ≤ suHP (K := K) (f := f) (k := k) :=
    sup_le hRle hUle
  have hHle : suHP (K := K) (f := f) (k := k) ≤
      suRadP (K := K) (f := f) (k := k) ⊔ suUP (K := K) (f := f) (k := k) := by
    rw [suHP, Subgroup.commutator_le]
    intro g hg h hh
    exact (suRadP (K := K) (f := f) (k := k) ⊔
      suUP (K := K) (f := f) (k := k)).mul_mem
      ((suRadP (K := K) (f := f) (k := k) ⊔
        suUP (K := K) (f := f) (k := k)).mul_mem
        ((suRadP (K := K) (f := f) (k := k) ⊔
          suUP (K := K) (f := f) (k := k)).mul_mem hg hh)
        ((suRadP (K := K) (f := f) (k := k) ⊔
          suUP (K := K) (f := f) (k := k)).inv_mem hg))
      ((suRadP (K := K) (f := f) (k := k) ⊔
        suUP (K := K) (f := f) (k := k)).inv_mem hh)
  exact le_antisymm hHle hAll

private theorem map_suRad_sup_suUP (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k) :
    (suRadP (K := K) (f := f) (k := k) ⊔ suUP (K := K) (f := f) (k := k)).map
        (AutPSU.projU h) = radical h (k + 1) ⊔ suBlock h k := by
  rw [Subgroup.map_sup, radical_of_le, suBlock, blockHom, MonoidHom.range_comp]
  congr 1
  exact congrArg (Subgroup.map (AutPSU.projU h)) (suRad_eq_suR h hk)

theorem commutator_radical_sup_suBlock (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k)
    (hkq : 4 ≤ k ∨ 2 ≤ f) :
    ⁅radical h (k + 1) ⊔ suBlock h k, radical h (k + 1) ⊔ suBlock h k⁆ =
      radical h (k + 1) ⊔ suBlock h k := by
  have hdisj : (3 ≤ k ∧ (k, 2 ^ f) ≠ (3, 2)) ∨ (k = 2 ∧ 4 ≤ 2 ^ f) := by
    rcases hkq with hk4 | hf2
    · left
      refine ⟨by omega, ?_⟩
      intro hpair
      have hk3 : k = 3 := congrArg Prod.fst hpair
      omega
    · by_cases hk2 : k = 2
      · right
        refine ⟨hk2, ?_⟩
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      · left
        refine ⟨by omega, ?_⟩
        intro hpair
        have hk3 : k = 3 := congrArg Prod.fst hpair
        have hq2 : 2 ^ f = 2 := congrArg Prod.snd hpair
        have h4 : 4 ≤ 2 ^ f := by
          calc
            4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
        omega
  have hq := RCSTSU.isQuasisimple_su h.card_eq_sq hdisj
  have hcomm : commutator (SU (unitaryInvolution K 2 f) k) = ⊤ :=
    hq.1.commutator_eq_top
  have hUcomm : ⁅suUP (K := K) (f := f) (k := k),
      suUP (K := K) (f := f) (k := k)⁆ = suUP (K := K) (f := f) (k := k) := by
    have hmap := Subgroup.map_commutator (H₁ := (⊤ : Subgroup
      (SU (unitaryInvolution K 2 f) k))) (H₂ := ⊤)
      (f := iotaHom (σ := unitaryInvolution K 2 f) (m := k))
    rw [show (⁅(⊤ : Subgroup (SU (unitaryInvolution K 2 f) k)), ⊤⁆ :
        Subgroup (SU (unitaryInvolution K 2 f) k)) = ⊤ from hcomm,
      Subgroup.map_top] at hmap
    exact hmap.symm
  have hperf := commutator_suRad_sup_range_iotaHom h hk hUcomm
  calc
    ⁅radical h (k + 1) ⊔ suBlock h k, radical h (k + 1) ⊔ suBlock h k⁆
        = (⁅suRadP (K := K) (f := f) (k := k) ⊔ suUP (K := K) (f := f) (k := k),
            suRadP (K := K) (f := f) (k := k) ⊔
              suUP (K := K) (f := f) (k := k)⁆).map (AutPSU.projU h) := by
          rw [Subgroup.map_commutator, map_suRad_sup_suUP h hk]
    _ = (suRadP (K := K) (f := f) (k := k) ⊔
          suUP (K := K) (f := f) (k := k)).map (AutPSU.projU h) := by rw [hperf]
    _ = radical h (k + 1) ⊔ suBlock h k := map_suRad_sup_suUP h hk

end CFSG.StandardType.KGPSU

end
