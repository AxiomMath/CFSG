module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

namespace CFSG
end CFSG
open CFSG

/-!
# Cardinalities of `SL₂` and `PSL₂` over finite fields

This module records the order calculations used by the odd-characteristic
`PSL₂` Sylow analysis.  The `SL₂` formula is obtained from the determinant
kernel in `GL₂`; in odd characteristic the scalar center has the two roots
of unity `±1`, so quotienting gives the usual `PSL₂` formula.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace CFSG.GorensteinWalter

private lemma specialLinearGroup_fin_two_card_eq_det_ker
    (K : Type*) [Field K] [Fintype K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card ((Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ).ker) := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K →*
      (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ).ker :=
    Matrix.SpecialLinearGroup.toGL.codRestrict _ (by
      intro A
      exact MonoidHom.mem_ker.mpr
        (Matrix.SpecialLinearGroup.coeToGL_det A))
  have hf_inj : Function.Injective f := by
    intro A B h
    apply Matrix.SpecialLinearGroup.toGL_injective
    exact congrArg Subtype.val h
  have hf_surj : Function.Surjective f := by
    intro A
    refine ⟨⟨(A : Matrix.GeneralLinearGroup (Fin 2) K).1, ?_⟩, ?_⟩
    · have hdet := MonoidHom.mem_ker.mp A.property
      change ((A : Matrix.GeneralLinearGroup (Fin 2) K).1).det = 1
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using
        congrArg Units.val hdet
    · apply Subtype.ext
      apply Units.ext
      rfl
  exact Nat.card_congr (MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).toEquiv

/-- The order formula `|SL₂(K)| = q(q² - 1)` for a finite field of order
`q = Nat.card K`. -/
public theorem sl2_card_formula (K : Type*) [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let d : Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ :=
    Matrix.GeneralLinearGroup.det
  have hdet_surj : Function.Surjective d :=
    Matrix.GeneralLinearGroup.det_surjective
  have hidx : d.ker.index = Nat.card Kˣ := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hdet_surj,
      Subgroup.card_top]
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) K) =
      (Fintype.card K ^ 2 - 1) *
        (Fintype.card K ^ 2 - Fintype.card K) := by
    rw [Matrix.card_GL_field]
    norm_num [Fintype.card_fin]
  have hker : Nat.card d.ker * d.ker.index =
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) K) :=
    Subgroup.card_mul_index d.ker
  have hunit : Fintype.card Kˣ = Fintype.card K - 1 :=
    Fintype.card_units K
  have hGL' : Fintype.card (Matrix.GeneralLinearGroup (Fin 2) K) =
      (Fintype.card K ^ 2 - 1) *
        (Fintype.card K ^ 2 - Fintype.card K) := by
    simpa only [Nat.card_eq_fintype_card] using hGL
  have hker' : Nat.card d.ker * (Fintype.card K - 1) =
      (Fintype.card K ^ 2 - 1) *
        (Fintype.card K ^ 2 - Fintype.card K) := by
    simpa [hidx, hunit, hGL'] using hker
  have hq : 1 < Fintype.card K :=
    Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hqsub : 0 < Fintype.card K - 1 := Nat.sub_pos_of_lt hq
  have hfactor : Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib]
    simp
  have hker'' : Nat.card d.ker * (Fintype.card K - 1) =
      (Fintype.card K * (Fintype.card K ^ 2 - 1)) *
        (Fintype.card K - 1) := by
    calc
      Nat.card d.ker * (Fintype.card K - 1) =
          (Fintype.card K ^ 2 - 1) *
            (Fintype.card K ^ 2 - Fintype.card K) := hker'
      _ = (Fintype.card K * (Fintype.card K ^ 2 - 1)) *
          (Fintype.card K - 1) := by rw [hfactor]; ac_rfl
  have hcardker : Nat.card d.ker =
      Fintype.card K * (Fintype.card K ^ 2 - 1) :=
    Nat.eq_of_mul_eq_mul_right hqsub hker''
  rw [specialLinearGroup_fin_two_card_eq_det_ker, hcardker]
  simp only [Nat.card_eq_fintype_card]

/-- Over a field of characteristic different from two, the two square roots
of one are exactly `1` and `-1`. -/
public theorem rootsOfUnity_two_of_char_ne_two
    (K : Type*) [Field K] [Finite K] (hchar : (2 : K) ≠ 0) :
    Nat.card (rootsOfUnity 2 K) = 2 := by
  let : Fintype K := Fintype.ofFinite K
  let z : rootsOfUnity 2 K :=
    ⟨(-1 : Kˣ), by
      rw [mem_rootsOfUnity]
      apply Units.ext
      simp [pow_two]⟩
  have hz : z ≠ (1 : rootsOfUnity 2 K) := by
    intro hz
    have hvU : (-1 : Kˣ) = 1 := by
      simpa [z] using
        congrArg (fun x : rootsOfUnity 2 K ↦ (x : Kˣ)) hz
    have hv' : (-1 : K) = 1 := congrArg Units.val hvU
    apply hchar
    calc
      (2 : K) = 1 - (-1) := by ring
      _ = 1 - 1 := by rw [hv']
      _ = 0 := by ring
  apply (Nat.card_eq_two_iff' (1 : rootsOfUnity 2 K)).2
  refine ⟨z, hz, ?_⟩
  intro y hy
  have hyPow : (y : Kˣ) ^ 2 = 1 :=
    (mem_rootsOfUnity 2 (y : Kˣ)).mp y.property
  let a : K := ((y : Kˣ) : K)
  have hyPow' : a ^ 2 = 1 := by
    simpa [a] using congrArg Units.val hyPow
  have hfactor : (a - 1) * (a + 1) = 0 := by
    calc
      (a - 1) * (a + 1) = a ^ 2 - 1 := by ring
      _ = 0 := by rw [hyPow']; ring
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · exfalso
    apply hy
    apply Subtype.ext
    apply Units.ext
    change a = 1
    exact sub_eq_zero.mp hminus
  · apply Subtype.ext
    apply Units.ext
    change a = -1
    exact eq_neg_of_add_eq_zero_left hplus

/-- The order formula `|PSL₂(K)| = q(q² - 1) / 2` when the finite field
order `q = Nat.card K` is an odd prime power. -/
public theorem psl2_card_formula
    (K : Type*) [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) :
    Nat.card (PSL2 K) = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
  let : Fintype K := Fintype.ofFinite K
  rcases hodd with ⟨p, n, hp, hpOdd, _hn, hcard⟩
  have hcardF : Fintype.card K = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := charP_of_card_eq_prime_pow hcardF
  have hchar : (2 : K) ≠ 0 := by
    intro h2
    have hpdiv : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp h2
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv
    subst p
    rcases hpOdd with ⟨k, hk⟩
    omega
  have hc : Nat.card (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) K)) = 2 := by
    let e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
      (i := (0 : Fin 2)) (R := K)
    rw [Nat.card_congr e.toEquiv]
    exact rootsOfUnity_two_of_char_ne_two K hchar
  change Nat.card (Matrix.SpecialLinearGroup (Fin 2) K ⧸
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) = _
  rw [← Subgroup.index_eq_card]
  have hi := Subgroup.index_mul_card
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
  rw [hc, sl2_card_formula] at hi
  have heq : Nat.card K * (Nat.card K ^ 2 - 1) =
      2 * (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)).index := by
    calc
      Nat.card K * (Nat.card K ^ 2 - 1) =
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)).index * 2 := hi.symm
      _ = 2 * (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) K)).index := Nat.mul_comm _ _
  have hdvd : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) := ⟨_, heq⟩
  exact ((Nat.div_eq_iff_eq_mul_right (by norm_num) hdvd).2 heq).symm

end CFSG.GorensteinWalter
