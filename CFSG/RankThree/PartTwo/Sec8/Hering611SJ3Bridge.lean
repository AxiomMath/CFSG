module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFJ3Aut
import CFSG.Sporadic.J3
import CFSG.Sporadic.SmallOddCore.J3Aut
import CFSG.Sporadic.Schreier.PairJ3Faithful
import CFSG.RankThree.Asc83Table.J3
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem card_le_27_of_isElemAbelian
    {M : Type} [Group M] (e : M ≃* Blueprint.NativeSporadic.J3) (W : Subgroup M)
    (hW : CFSG.Assembly.IsElemAbelian 3 W) : Nat.card W ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite Blueprint.NativeSporadic.J3 := (CFSG.Sporadic.J3.fam_j3_simplicity).1
  have : Finite M := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hW).exists_card_eq
  have hkr : k ≤ CFSG.pRank 3 M := by
    refine le_csSup ⟨Nat.card M, ?_⟩ ⟨W, hW.isElementaryAbelian, hk⟩
    rintro r ⟨B, -, hB⟩
    calc r ≤ 3 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card M := Subgroup.card_le_card_group B
  have hrank : CFSG.pRank 3 M = 3 :=
    (CFSG.RankThree.Asc83Table.J3.table (L := M) ⟨e⟩).1
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (hkr.trans hrank.le)
    _ = 27 := by norm_num

private theorem center_eq_bot_of_certificate3169 {M : Type}
    [Group M] (e : M ≃* Blueprint.NativeSporadic.J3) : Subgroup.center M = ⊥ := by
  have : IsSimpleGroup M := @MulEquiv.isSimpleGroup M _ _ _ CFSG.Sporadic.J3.isSimpleGroup_J3 e
  refine CFSG.RankThree.PartTwo.Sec4.center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J3.card_J3]
  norm_num

theorem center_eq_bot_of_mulEquiv_J3 {M : Type} [Group M]
    (e : M ≃* Blueprint.NativeSporadic.J3) : Subgroup.center M = ⊥ :=
  center_eq_bot_of_certificate3169 e


theorem exists_conj_of_pow_three_J3 {M : Type} [Group M] (e : M ≃* Blueprint.NativeSporadic.J3)
    (σ : MulAut M) (hσ : σ ^ 3 = 1) : ∃ g : M, MulAut.conj g = σ := by
  have hfin : Finite Blueprint.NativeSporadic.J3 := (CFSG.Sporadic.J3.fam_j3_simplicity).1
  have : Finite M := Finite.of_equiv _ e.symm.toEquiv
  have hOut : Nat.card (Outer M) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (e.trans CFSG.Sporadic.Schreier.j3PermEquiv)).toEquiv]
    exact CFSG.Sporadic.SmallOddCore.j3_outer_card_le
  have h3' : (QuotientGroup.mk σ : Outer M) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one]
  have hord : orderOf (QuotientGroup.mk σ : Outer M) ∣ 3 := orderOf_dvd_of_pow_eq_one h3'
  have hord2 : orderOf (QuotientGroup.mk σ : Outer M) ∣ Nat.card (Outer M) :=
    orderOf_dvd_natCard _
  have hle : orderOf (QuotientGroup.mk σ : Outer M) ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos hord2).trans hOut
  have h1 : orderOf (QuotientGroup.mk σ : Outer M) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
    · exact h
    · omega
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  obtain ⟨g, hg⟩ := h1
  exact ⟨g, hg⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611
