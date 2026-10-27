module

public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectA6
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.Open.PGLModelStated
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.HardMathSupport.Solomon.Coordinator.T112TRank
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KThirty2ACore
import CFSG.RankThree.SubgroupLists2.SpectralBounds
import CFSG.RankThree.PartTwo.Sec6.Item65Two
import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
import CFSG.Quasithin.EmptyFaithful.S1565L1

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG CFSG.Open Module
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU StatedSp StatedProj StatedScalars)

section Central

theorem false_of_central_scalar {K : Type} [Field K] [Finite K] (ωu : Kˣ) (hωu : orderOf ωu = 3)
    (M : Subgroup (GL (Fin 3) K)) (hdet : ∀ A ∈ M, ((A : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1)
    (hz : Matrix.GeneralLinearGroup.scalar (Fin 3) ωu ∈ M) {X : Type} [Group X] [Finite X]
    (φ : X ≃* M) {P : Subgroup X} (hP : IsA6Sub P) : False := by
  have hω3 : ωu ^ 3 = 1 := by rw [← hωu]; exact pow_orderOf_eq_one ωu
  have hω1 : ωu ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hωu
    omega
  have h3K : (3 : K) ≠ 0 :=
    HardMathSupport.Solomon.UniquenessMaximal.K32A.three_ne_zero_of_cube_root (τ := (ωu : K))
      (by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]) (fun h => hω1 (Units.ext h))
  obtain ⟨R, -, hR, hR9, hRc⟩ := hP.exists_elemAbelian_nine
  let ι : X →* GL (Fin 3) K := M.subtype.comp φ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp φ.injective
  set g : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) ωu with hg
  have hg3 : g ^ 3 = 1 := by rw [hg, ← map_pow, hω3, map_one]
  have hgcomm : ∀ k : GL (Fin 3) K, k * g = g * k := by
    intro k
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hg, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (ωu : K) (fun r => Commute.all (ωu : K) r) _).symm
  have hg1 : g ≠ 1 := by
    intro h
    have h' := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp only [hg, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h'
    exact hω1 (Units.ext h')
  have hgE : g ∉ R.map ι := by
    rintro ⟨r, hr, hrg⟩
    apply hg1
    have hrc : r ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply hι
      rw [map_mul, map_mul, hrg]
      exact hgcomm _
    rw [hRc r hr hrc, map_one] at hrg
    exact hrg.symm
  obtain ⟨hF, hFcard⟩ := Sec6.isElemAbelian_sup_zpowers_three (Sec4.isElemAbelian_map ι hR) hgE
    hg3 (fun k _ => hgcomm k)
  have hker : R.map ι ⊔ Subgroup.zpowers g ≤
      (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
    refine sup_le ?_ ?_
    · rintro _ ⟨r, -, rfl⟩
      rw [MonoidHom.mem_ker, Units.ext_iff]
      have h := hdet ((φ r : M) : GL (Fin 3) K) (φ r).2
      simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact h
    · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, Units.ext_iff, hg]
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_diagonal, ← pow_three',
        ← Units.val_pow_eq_pow_val, hω3]
  have hdetF : ∀ A ∈ R.map ι ⊔ Subgroup.zpowers g,
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    intro A hA
    have := hker hA
    rw [MonoidHom.mem_ker, Units.ext_iff] at this
    simpa using this
  have hle := HardMathSupport.Solomon.Coordinator.card_le_nine h3K hdetF
    (fun x hx y hy => congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx => hF.2 x hx)
  rw [hFcard, Subgroup.card_map_of_injective hι, hR9] at hle
  omega

section Instances

open CFSG.Open.StatedAPI

variable {X : Type} [Group X] [Finite X] {P : Subgroup X}

theorem false_of_statedSL_of_dvd {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    (φ : X ≃* StatedSL 3 K) (hP : IsA6Sub P) : False := by
  obtain ⟨ωu, hωu⟩ := Quasithin.exists_unit_orderOf_three h3
  have hω3 : ωu ^ 3 = 1 := by rw [← hωu]; exact pow_orderOf_eq_one ωu
  refine false_of_central_scalar ωu hωu (StatedSL 3 K) (fun A hA => det_of_mem_statedSL hA) ?_ φ hP
  apply mem_statedSL_of_det
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have := congrArg Units.val hω3
  simpa using this

theorem false_of_statedSU_of_two {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hq : q % 3 = 2) (φ : X ≃* StatedSU 3 q K) (hP : IsA6Sub P) : False := by
  have h3 : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨ωu, hωu⟩ := Quasithin.exists_unit_orderOf_three h3
  have hω3 : ωu ^ 3 = 1 := by rw [← hωu]; exact pow_orderOf_eq_one ωu
  have hωq : ωu ^ (q + 1) = 1 := by
    obtain ⟨k, hk⟩ : 3 ∣ q + 1 := by omega
    rw [hk, pow_mul, hω3, one_pow]
  refine false_of_central_scalar ωu hωu (StatedSU 3 q K)
    (fun A hA => det_of_mem_statedSU hA) ?_ φ hP
  rw [PGLModel.statedSU_eq_closure_det]
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [Units.ext_iff]
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have := congrArg Units.val hω3
    simpa using this
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply,
      Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ]
      have := congrArg Units.val hωq
      simpa [pow_succ, mul_comm] using this
    · have hq0 : q ≠ 0 := by omega
      simp [hij, Ne.symm hij, hq0]

theorem false_of_statedSL_two {m : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * m)) (φ : X ≃* StatedSL 3 K) (hP : IsA6Sub P) : False := by
  refine false_of_statedSL_of_dvd ?_ φ hP
  rw [hK, pow_mul]
  have : (2 ^ 2) ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h1 : 1 ≤ (2 ^ 2) ^ m := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem false_of_isSLThreePiAt {q : ℕ} (h : Sec4.IsSLThreePiAt X q) (hP : IsA6Sub P) : False := by
  obtain ⟨K, _, _, ⟨hK, hq, ⟨φ⟩⟩ | ⟨hK, hq, ⟨φ⟩⟩⟩ := h
  · refine false_of_statedSL_of_dvd ?_ φ hP
    rw [hK]
    omega
  · exact false_of_statedSU_of_two hK hq φ hP

theorem false_of_statedSU_even {m : ℕ} (hm : Even m) (hm1 : 1 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 2) (φ : X ≃* StatedSU 3 (2 ^ m) K) (hP : IsA6Sub P) :
    False := by
  have hq : 2 ^ m % 3 = 1 := by
    obtain ⟨k, hk⟩ := hm
    rw [← two_mul] at hk
    rw [hk, pow_mul, Nat.pow_mod]
    norm_num
  have h3K : (3 : K) ≠ 0 :=
    Sec4.three_ne_zero_of_card (f := 2 * m) Nat.prime_two (by norm_num)
      (by rw [hK, ← pow_mul, mul_comm])
  obtain ⟨R, -, hR, hR9, -⟩ := hP.exists_elemAbelian_nine
  let ι : X →* GL (Fin 3) K := (StatedSU 3 (2 ^ m) K).subtype.comp φ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp φ.injective
  have hE := Sec4.isElemAbelian_map ι hR
  have hEcard : Nat.card (R.map ι) = 9 := by rw [Subgroup.card_map_of_injective hι, hR9]
  have hdet : ∀ e ∈ R.map ι, ((e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rintro _ ⟨r, -, rfl⟩
    exact det_of_mem_statedSL (statedSU_le_statedSL 3 (2 ^ m) K (φ r).2)
  obtain ⟨a, ha, ha1, c, hac⟩ := RankThree.SubgroupLists.exists_scalar_of_card_eq_nine h3K
    (R.map ι) (fun x hx y hy => congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx => hE.2 x hx) hdet hEcard
  have hdeta := hdet a ha
  rw [hac, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdeta
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hdeta
  have hc3 : c ^ 3 = 1 := hdeta
  obtain ⟨r, -, rfl⟩ := ha
  have hscal : (ι r) = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) := by
    apply Units.ext
    rw [hac, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) ∈
      StatedSU 3 (2 ^ m) K := by
    rw [← hscal]
    exact (φ r).2
  rw [(LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num : 1 ≤ 3)).2.1] at hmem
  obtain ⟨-, hu2⟩ := hmem
  have h2 : 2 ^ m + 1 = 3 * (2 ^ m / 3) + 2 := by omega
  have hu3 : (Units.mk0 c hc0) ^ 3 = 1 := Units.ext (by simpa using hc3)
  rw [h2, pow_add, pow_mul, hu3, one_pow, one_mul] at hu2
  have hu1 : Units.mk0 c hc0 = 1 := by
    have h1 : (Units.mk0 c hc0) ^ 3 = (Units.mk0 c hc0) ^ 2 * Units.mk0 c hc0 := pow_succ _ 2
    rw [hu3, hu2, one_mul] at h1
    exact h1.symm
  apply ha1
  rw [hscal, hu1, map_one]

end Instances

end Central

end CFSG.RankThree.PartTwo.Sec8.Hering611R
