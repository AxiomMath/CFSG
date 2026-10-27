module

public import CFSG.RankThree.PartOne.FOCD.G2OddSplit
public import CFSG.RankThree.PartOne.FOCD.G2OddQPlus
public import CFSG.RankThree.PartOne.FOCD.G2OddCyc
public import CFSG.RankThree.PartOne.FOCD.Final
public import CFSG.RankThree.PartOne.FOCD.ExcFinite
import CFSG.RankThree.PartOne.K128.G2Syl
import CFSG.RankThree.PartOne.S11c.OddG2Plane
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.RankThree.PartOne.FOCD.PRank

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.RankThree.PartOne.Sec66T (innerAut)

open CFSG.QuasithinUnique.Id2519 (isSimpleGroup_adjointGroup_g2)

open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

open TauCeti (PrimePower)


section G2

variable {K : Type} [Field K] [Finite K] {p : ℕ}

theorem compGoodZAt_G2_odd (hK : Odd (Nat.card K)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : 2 ≤ Nat.card K) (hpq : ¬ p ∣ Nat.card K) (b : adjointGroup .G2 K) (hb1 : b ≠ 1)
    (hbp : b ^ p = 1) : CompGoodZAt p b := by
  by_cases hd : p ∣ Nat.card K ^ 2 - 1
  · rcases K128.dvd_pred_or_succ_of_dvd_sq_sub_one hp (by omega) (by omega) hd with
      ⟨h, -⟩ | ⟨h, -⟩
    · exact compGoodZAt_G2_oddsplit hK hp (by omega) h b hb1 hbp
    · exact compGoodZAt_G2_oddqplus hK hp (by omega) h b hb1 hbp
  · exact compGoodZAt_G2_oddcyc hK hp (by omega) hq hpq hd b hb1 hbp

theorem pRankLeTwo_G2_odd (hK : Odd (Nat.card K)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : 2 ≤ Nat.card K) (hpq : ¬ p ∣ Nat.card K) : PRankLeTwo p (adjointGroup .G2 K) := by
  by_cases hdvd : p ∣ Nat.card (adjointGroup .G2 K)
  · by_cases hd : p ∣ Nat.card K ^ 2 - 1
    · rcases K128.dvd_pred_or_succ_of_dvd_sq_sub_one hp (by omega) (by omega) hd with
        ⟨h, -⟩ | ⟨h, -⟩
      · exact pRankLeTwo_G2_oddsplit hK hp (by omega) h
      · exact pRankLeTwo_G2_oddqplus hK hp (by omega) h
    · exact pRankLeTwo_G2_oddcyc hK hp (by omega) hq hpq hd hdvd
  · exact pRankLeTwo_of_not_dvd hp hdvd


theorem innerCompN_G2_odd (hK : Odd (Nat.card K)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : 3 ≤ Nat.card K) (hpq : ¬ p ∣ Nat.card K) : InnerCompN p (adjointGroup .G2 K) := by
  have := isSimpleGroup_adjointGroup_g2 hq
  exact innerCompN_of_rank' hp (pRankLeTwo_G2_odd hK hp hp5 (by omega) hpq)
    fun b hb1 hbp E hE => compGoodZAt_G2_odd hK hp hp5 (by omega) hpq b hb1 hbp E hE

end G2

theorem outerComp_G2_odd {T : Type} [Group T] [Finite T] {ℓ p : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hmod : ChevalleyExceptionalModel T .G2 ℓ 1) (hp : p.Prime) (hp5 : 5 ≤ p) :
    OuterComp p T := by
  have : Fact p.Prime := ⟨hp⟩
  intro _ β hβp hβout _
  exfalso
  have hβ1 : β ≠ 1 := fun h => hβout (h ▸ (innerAut T).one_mem)
  have hord : orderOf β = p := orderOf_eq_prime hβp hβ1
  exact hβout (g2_prime_order_automorphism_inner hℓ hℓ2 hmod
    ⟨fun _ => rfl, fun _ => by norm_num⟩ hp (by omega) β hord)

section Cross


theorem fieldInnerT_G2_odd {T : Type} [Group T] [Finite T] {ℓ p : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hmod : ChevalleyExceptionalModel T .G2 ℓ 1) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : p ≠ ℓ) : FieldInnerT p T := by
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmod.2
  have hK' : Nat.card K = ℓ := by simpa using hK
  have hℓ3 : 3 ≤ ℓ := by
    have := hℓ.two_le
    omega
  refine FieldInnerT.of_mulEquiv e hp ?_
  have hmodC : ChevalleyExceptionalModel (adjointGroup .G2 K) .G2 ℓ 1 :=
    ⟨hmod.1, K, hKf, hKfin, hK, ⟨(CFSG.RankThree.Chevalley.adjointQuotientEquiv .G2 K).symm⟩⟩
  have hodd : Odd (Nat.card K) := by
    rw [hK']
    exact hℓ.odd_of_ne_two hℓ2
  have hpq : ¬ p ∣ Nat.card K := by
    rw [hK']
    intro h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 h)
  exact fieldInnerT_of_compN center_adjointGroup_eq_bot
    (innerCompN_G2_odd hodd hp hp5 (by omega) hpq) (outerComp_G2_odd hℓ hℓ2 hmodC hp hp5)

end Cross

section Index


theorem fieldInnerIdx_G2_odd (q : PrimePower) (hq2 : q.p ≠ 2) (hq1 : q.exponent = 1) :
    FieldInnerIdx (.G2 q) := by
  intro T _ _ p hp hp5 hs hnab hiso
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hmodel := CFSG.TauCetiBridge.untwistedModel_of_bridge
    CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hq2 e0
  have hge3 : 3 ≤ q.p ^ q.exponent := by
    have h := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa only [PrimePower.card_def] using h
  have hadm : StatedLieAdmissible .G2 0 q.p q.exponent :=
    ⟨q.prime_p, q.exponent_pos, rfl, hge3⟩
  have hmod : ChevalleyExceptionalModel T .G2 q.p q.exponent := ⟨hadm, hmodel⟩
  by_cases hpq : p = q.p
  ·
    subst hpq
    have hLie : LieModel T .G2 0 q.p q.exponent := Or.inr (Or.inl ⟨rfl, by decide, hmod⟩)
    exact fieldInnerT_of_comp (center_eq_bot_of_nonab hs hnab)
      (defInnerComponent_of_certs T .G2 0 q.exponent q.p hp hp5 hadm hs hLie)
      (defOuterComponent_of_certs T .G2 0 q.exponent q.p hp hp5 hadm hs hLie)
  · rw [hq1] at hmod
    exact fieldInnerT_G2_odd q.prime_p hq2 hmod hp hp5 hpq

end Index

end CFSG.RankThree.PartOne.FOCD
