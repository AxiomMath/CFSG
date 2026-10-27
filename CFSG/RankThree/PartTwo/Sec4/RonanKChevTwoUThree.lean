module

public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoBasic
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoLinAlg
public import CFSG.RankThree.PartTwo.KFacts.K72L3Fix

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open CFSG CFSG.RankThree.PartTwo.Sec4.Item462AltProof
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open Matrix

private theorem two_lt_two_pow_of_mod_three {m : ℕ} (hm : 1 ≤ m) (hq : 2 ^ m % 3 = 1) :
    2 < 2 ^ m := by
  have h2 : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h2' : 2 ^ m ≠ 2 := fun h => by rw [h] at hq; norm_num at hq
  omega

section Unitary

variable {m : ℕ} {K : Type} [Field K]

theorem center_su_three_eq_bot (h : UnitaryFieldData 2 m K) (hq : 2 ^ m % 3 = 1) :
    Subgroup.center (unitarySU 2 m K 3) = ⊥ := by
  rw [KFacts.center_unitarySU_three (h := h) (two_lt_two_pow_of_mod_three h.one_le hq),
    KFacts.unitaryScalars_three_eq_bot_of_mod_three h hq]

theorem su_three_eq_one_of_commute (h : UnitaryFieldData 2 m K) (hq : 2 ^ m % 3 = 1)
    {x c : unitarySU 2 m K 3} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxc : x * c = c * x)
    (hc2 : c ^ 2 = 1) : c = 1 := by
  have : CharP K 2 := h.charP
  have hmem := (mem_unitarySU_iff h).mp x.2
  have hA3 : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    have e := congrArg
      (fun y : unitarySU 2 m K 3 => ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hx3
    simpa using e
  have hAs : ∀ a : K,
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ a • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro a ha
    have hdet : a ^ 3 = 1 := by
      have h1 := hmem.1
      rw [ha, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
      exact h1
    have hnorm : a ^ 2 ^ m * a = 1 := by
      have h1 := congrFun (congrFun hmem.2 0) 0
      rw [ha] at h1
      simpa [Matrix.mul_apply, Fin.sum_univ_three, UnitaryFieldData.bar_apply] using h1
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ m + 1 = 3 * t + 2 := ⟨(2 ^ m + 1) / 3, by omega⟩
    have ha2 : a ^ 2 = 1 := by
      have e : a ^ (2 ^ m + 1) = 1 := by rw [pow_succ]; exact hnorm
      rwa [ht, pow_add, pow_mul, hdet, one_pow, one_mul] at e
    have ha1 : a = 1 := by linear_combination hdet - a * ha2
    apply hx1
    apply Subtype.ext
    apply Units.ext
    rw [ha, ha1, one_smul]
    rfl
  have hAB : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((c : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = ((c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have e := congrArg
      (fun y : unitarySU 2 m K 3 => ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hxc
    simpa using e
  have hBB : ((c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have e := congrArg
      (fun y : unitarySU 2 m K 3 => ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hc2
    simpa [sq] using e
  exact Subtype.ext (Units.ext (eq_one_of_commute_of_pow_three_eq_one hA3 hmem.1 hAs hAB hBB))

theorem su_three_not_pullDatum (h : UnitaryFieldData 2 m K) (hq : 2 ^ m % 3 = 1)
    (β : MulAut (unitarySU 2 m K 3)) (hβ : orderOf β = 3) : ¬ PullDatum β := by
  intro hD
  have := h.finite
  have hinj := conj_injective_of_center_eq_bot (center_su_three_eq_bot h hq)
  by_cases hin : KFacts.IsInnerAut β
  · obtain ⟨x, rfl, hx3, hx1⟩ := exists_conj_of_isInnerAut hinj hβ hin
    refine hD.false_of_no_involution fun c hc hc2 => ?_
    rw [conj_apply_eq_iff] at hc
    exact su_three_eq_one_of_commute h hq hx3 hx1 hc hc2
  · have hβ3 : β ^ 3 = 1 := by
      have h' := pow_orderOf_eq_one β
      rwa [hβ] at h'
    obtain ⟨hZ, hqs⟩ := KFacts.fixedPoints_facts_of_mulEquiv_unitaryPSU h hq
      (two_lt_two_pow_of_mod_three h.one_le hq)
      (MulEquiv.ofBijective (unitaryProj h 3)
        ⟨KFacts.unitaryProj_three_injective h hq, unitaryProj_surjective h 3⟩) hβ3 hin
    refine hD.false_of_quasisimple_fixed _ (fun _ => Iff.rfl) hqs ?_
    rw [hZ, Subgroup.card_bot]
    exact odd_one

end Unitary

theorem kChevTwo_statedSU_three (m : ℕ) (hm : 1 ≤ m) (hq : 2 ^ m % 3 = 1) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ m) ^ 2 ∧
        Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K)) →
      ∀ β : MulAut X, orderOf β = 3 → ¬ InnThetaNoncyclic β := by
  intro X _ _ _ ⟨K, _, _, hK, ⟨e⟩⟩ β hβ
  have h : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  exact not_innThetaNoncyclic_of_mulEquiv e
    (KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e (center_su_three_eq_bot h hq))
    (su_three_not_pullDatum h hq) β hβ

theorem kChevTwo_projSU_three (m : ℕ) (hm : 1 ≤ m) (hq : 2 ^ m % 3 = 1) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Nonempty (X ≃* projSU 3 2 m) →
      ∀ β : MulAut X, orderOf β = 3 → ¬ InnThetaNoncyclic β := by
  intro X _ _ hX ⟨e⟩
  have hcard : Nat.card (GaloisField 2 (2 * m)) = 2 ^ (2 * m) :=
    GaloisField.card 2 (2 * m) (by omega)
  have h : UnitaryFieldData 2 m (GaloisField 2 (2 * m)) := ⟨Nat.prime_two, hm, hcard⟩
  obtain ⟨φ⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU h
  let ψ : unitarySU 2 m (GaloisField 2 (2 * m)) 3 ≃* unitaryPSU h 3 :=
    MulEquiv.ofBijective (unitaryProj h 3)
      ⟨KFacts.unitaryProj_three_injective h hq, unitaryProj_surjective h 3⟩
  exact kChevTwo_statedSU_three m hm hq X hX ⟨GaloisField 2 (2 * m), inferInstance, inferInstance,
    by rw [hcard, pow_mul'], ⟨e.trans (φ.symm.trans ψ.symm)⟩⟩

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

end
