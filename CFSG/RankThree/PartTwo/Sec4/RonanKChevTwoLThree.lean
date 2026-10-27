module

public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoBasic
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoLinAlg
public import CFSG.RankThree.PartTwo.KFacts.K72L3Fix

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open CFSG CFSG.RankThree.PartTwo.Sec4.Item462AltProof
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (proj proj_surjective scalars_eq_center)
open Matrix

section Linear

variable {K : Type} [Field K]

theorem center_sl_three_eq_bot (hK : Nat.card K % 3 = 2) :
    Subgroup.center (SpecialLinearGroup (Fin 3) K) = ⊥ := by
  rw [← scalars_eq_center, KFacts.scalars_three_eq_bot_of_mod_three hK]

theorem nonempty_sl_three_mulEquiv_projSL (hK : Nat.card K % 3 = 2) :
    Nonempty (SpecialLinearGroup (Fin 3) K ≃* projSL 3 K) :=
  ⟨(MulEquiv.ofBijective (proj 3 K)
    ⟨KFacts.proj_three_injective hK, proj_surjective 3 K⟩).trans
      (KFacts.nonempty_projSL_mulEquiv 3 K).some.symm⟩

theorem sl_three_eq_one_of_commute [CharP K 2] (hK : Nat.card K % 3 = 2)
    {x c : SpecialLinearGroup (Fin 3) K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxc : x * c = c * x)
    (hc2 : c ^ 2 = 1) : c = 1 := by
  have hA3 : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hx3, Matrix.SpecialLinearGroup.coe_one]
  have hAs : ∀ a : K, (x : Matrix (Fin 3) (Fin 3) K) ≠ a • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro a ha
    have hdet : a ^ 3 = 1 := by
      have h := x.2
      rw [ha, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h
      exact h
    have ha0 : a ≠ 0 := by
      rintro rfl
      norm_num at hdet
    have hu := KFacts.units_eq_one_of_pow_three_eq_one hK (c := Units.mk0 a ha0)
      (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet, Units.val_one]))
    have ha1 : a = 1 := by
      have := congrArg Units.val hu
      rwa [Units.val_mk0, Units.val_one] at this
    apply hx1
    ext i j
    rw [ha, ha1, one_smul, Matrix.SpecialLinearGroup.coe_one]
  have hAB : (x : Matrix (Fin 3) (Fin 3) K) * c = c * x := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hxc, Matrix.SpecialLinearGroup.coe_mul]
  have hB : (c : Matrix (Fin 3) (Fin 3) K) * c = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← sq, hc2, Matrix.SpecialLinearGroup.coe_one]
  exact Subtype.ext (eq_one_of_commute_of_pow_three_eq_one hA3 x.2 hAs hAB hB)

theorem sl_three_not_pullDatum [Finite K] [CharP K 2] (hK : Nat.card K % 3 = 2)
    (β : MulAut (SpecialLinearGroup (Fin 3) K)) (hβ : orderOf β = 3) : ¬ PullDatum β := by
  intro hD
  have hinj := conj_injective_of_center_eq_bot (center_sl_three_eq_bot hK)
  by_cases hin : KFacts.IsInnerAut β
  · obtain ⟨x, rfl, hx3, hx1⟩ := exists_conj_of_isInnerAut hinj hβ hin
    refine hD.false_of_no_involution fun c hc hc2 => ?_
    rw [conj_apply_eq_iff] at hc
    exact sl_three_eq_one_of_commute hK hx3 hx1 hc hc2
  · have hβ3 : β ^ 3 = 1 := by
      have h := pow_orderOf_eq_one β
      rwa [hβ] at h
    obtain ⟨hZ, hq⟩ := KFacts.fixedPoints_facts_of_mulEquiv_projSL hK
      (nonempty_sl_three_mulEquiv_projSL hK).some hβ3 hin
    refine hD.false_of_quasisimple_fixed _ (fun _ => Iff.rfl) hq ?_
    rw [hZ, Subgroup.card_bot]
    exact odd_one

end Linear

private theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem kChevTwo_projSL_three (n : ℕ) (hn : Odd n) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
      Nonempty (X ≃* projSL 3 (GaloisField 2 n)) →
      ∀ β : MulAut X, orderOf β = 3 → ¬ InnThetaNoncyclic β := by
  intro X _ _ _ ⟨e⟩ β hβ
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (Nat.not_odd_zero hn).elim
  have hK : Nat.card (GaloisField 2 n) % 3 = 2 := by
    rw [GaloisField.card 2 n hn0]
    exact two_pow_mod_three_of_odd hn
  let e' : X ≃* SpecialLinearGroup (Fin 3) (GaloisField 2 n) :=
    e.trans (nonempty_sl_three_mulEquiv_projSL hK).some.symm
  exact not_innThetaNoncyclic_of_mulEquiv e'
    (KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e' (center_sl_three_eq_bot hK))
    (sl_three_not_pullDatum hK) β hβ

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

end
