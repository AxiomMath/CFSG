module

public import CFSG.RankThree.PartOne.FOCD.G2EvenOuter
public import CFSG.RankThree.PartOne.FOCD.G2EvenSplit
public import CFSG.RankThree.PartOne.FOCD.G2EvenQPlus
public import CFSG.RankThree.PartOne.FOCD.G2EvenCyc
public import CFSG.RankThree.PartOne.FOCD.PRank
public import CFSG.RankThree.PartOne.FOCD.ExcFinite
import CFSG.RankThree.PartOne.K128.G2Syl
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.QuasithinUnique.Id2519 (isSimpleGroup_adjointGroup_g2)

open TauCeti (PrimePower)


section G2

variable {K : Type} [Field K] [Finite K] {p m : ℕ}

theorem compGoodAt_G2_even (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = 2 ^ m) (hm : 1 ≤ m)
    (b : adjointGroup .G2 K) (hb1 : b ≠ 1) (hbp : b ^ p = 1) : CompGoodAt p b := by
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hm hK
  have hq : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hpq : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  by_cases hd : p ∣ Nat.card K ^ 2 - 1
  · rcases K128.dvd_pred_or_succ_of_dvd_sq_sub_one hp (by omega) (by omega) hd with
      ⟨h, -⟩ | ⟨h, -⟩
    · exact compGoodAt_G2_split hp (by omega) h b hb1 hbp
    · exact compGoodAt_G2_qplus hp (by omega) h b hb1 hbp
  · exact compGoodAt_G2_cyc hp (by omega) hq hpq hd b hb1 hbp

theorem pRankLeTwo_G2_even (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = 2 ^ m) (hm : 1 ≤ m) :
    PRankLeTwo p (adjointGroup .G2 K) := by
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hm hK
  by_cases hdvd : p ∣ Nat.card (adjointGroup .G2 K)
  · by_cases hd : p ∣ Nat.card K ^ 2 - 1
    · exact pRankLeTwo_of_sylowShape hp (K128.sylowShape_G2 K hp hp5 hK hm hd)
    · exact pRankLeTwo_of_pRank_le_one hp (K128.pRank_le_one_G2 K hp hp5 hK hm hdvd hd)
  · exact pRankLeTwo_of_not_dvd hp hdvd


theorem innerCompN_G2_even (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = 2 ^ m) (hm : 2 ≤ m) :
    InnerCompN p (adjointGroup .G2 K) := by
  have hk3 : 3 ≤ Nat.card K := by
    rw [hK]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have := isSimpleGroup_adjointGroup_g2 hk3
  exact innerCompN_of_rank hp (pRankLeTwo_G2_even hp hp5 hK (by omega))
    fun b hb1 hbp E hE => compGoodAt_G2_even hp hp5 hK (by omega) b hb1 hbp E hE


theorem fieldInnerT_G2_even {T : Type} [Group T] [Finite T] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m) (e : T ≃* adjointGroup .G2 K) : FieldInnerT p T :=
  FieldInnerT.of_mulEquiv e hp
    (fieldInnerT_of_compN center_adjointGroup_eq_bot (innerCompN_G2_even hp hp5 hK hm)
      (outerComp_G2_even hp hp5 hm hK))

end G2

section Index


theorem fieldInnerIdx_G2_even (q : PrimePower) (hq2 : q.p = 2) : FieldInnerIdx (.G2 q) := by
  intro T _ _ p hp hp5 _ _ hiso
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq2 e0
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := K128.exists_equiv_adjoint_G2 hmodel
  rw [hq2] at hK
  have hm : 2 ≤ q.exponent := by
    have h3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    rw [PrimePower.card_def, hq2] at h3
    by_contra hlt
    have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [h1] at h3
    norm_num at h3
  exact fieldInnerT_G2_even hp hp5 hm hK e

end Index

end CFSG.RankThree.PartOne.FOCD
