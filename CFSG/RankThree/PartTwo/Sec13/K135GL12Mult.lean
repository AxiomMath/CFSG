module

public import CFSG.RankThree.PartTwo.Sec13.K135SFGL12Defs
public import CFSG.RankThree.PartTwo.Sec13.K135GL12Census
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.RankThree.PartOne.N143.SectionListLieC
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I66At
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.OutThreeCore

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135GL12

open CFSG CFSG.RankThree.PartTwo.Sec13.K135SF TauCeti CFSG.RankThree.PartOne.N143

theorem not_primeCover_of_surv {d : LieTypeIndex} {p : ℕ} (hp7 : 7 ≤ p) (hs : GL12Surv d)
    (h : PrimeCoverLieIndex p d) : False := by
  cases d with
  | A n q =>
    have hmem : (n, q.p, q.exponent) ∈ survA := hs
    obtain ⟨h1, h2⟩ := h
    have hn : n ≤ 11 := by
      have key : ∀ x ∈ survA, x.1 ≤ 11 := by decide
      exact key _ hmem
    have hp12 : p ≤ 12 := (Nat.le_of_dvd (by omega) h1).trans (by omega)
    have key : ∀ x ∈ survA, ∀ p ∈ List.range 13, 7 ≤ p → p ∣ x.1 + 1 →
        ¬ p ∣ x.2.1 ^ x.2.2 - 1 := by decide
    exact key _ hmem p (List.mem_range.2 (by omega)) hp7 h1 (by rwa [PrimePower.card_def] at h2)
  | twistedA n q =>
    have hmem : (n, q.p, q.exponent) ∈ survTA := hs
    obtain ⟨h1, h2⟩ := h
    have hn : n ≤ 11 := by
      have key : ∀ x ∈ survTA, x.1 ≤ 11 := by decide
      exact key _ hmem
    have hp12 : p ≤ 12 := (Nat.le_of_dvd (by omega) h1).trans (by omega)
    have key : ∀ x ∈ survTA, ∀ p ∈ List.range 13, 7 ≤ p → p ∣ x.1 + 1 →
        ¬ p ∣ x.2.1 ^ x.2.2 + 1 := by decide
    exact key _ hmem p (List.mem_range.2 (by omega)) hp7 h1 (by rwa [PrimePower.card_def] at h2)
  | _ => exact h.elim

theorem kFactMultPrimeGL12_of_inputs
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hB : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    KFactMultPrimeGL12 := by
  intro Q _ _ hQ hK hGL p hp hp7 hdvd
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.1
  obtain ⟨i, ⟨e⟩⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.isCatalogGroup_of_isKGroup_simple hK
  cases i with
  | cyclic q hq =>
    obtain ⟨a, b, hab⟩ := hQ.2.2
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    haveI : Group.IsPerfect Q := hQ.1
    exact CFSG.RankThree.PartOne.Mult.alternating_center_small_primes hn e hp (by omega) hdvd
  | sporadic s =>
    have h1 := CFSG.LocalAnalysis.GLTheoremA.i66_card_center_dvd hSpor hQ.1 s e
    have h2 := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultiplierOrder_dvd_twelve s
    have h3 : p ∣ 12 := hdvd.trans (h1.trans h2)
    have hle := Nat.le_of_dvd (by norm_num) h3
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  | lie d =>
    have hPC := primeCoverLie_of_griess hGA hp hp7 d hQ e hdvd
    have hord : Nat.card (Q ⧸ Subgroup.center Q) = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d.1 :=
      hB d (Q ⧸ Subgroup.center Q) ⟨e⟩
    have hdiv : Nat.card (Q ⧸ Subgroup.center Q) ∣ gl12Order :=
      gl12Data_card_dvd hGL
    rw [hord] at hdiv
    exact not_primeCover_of_surv hp7 (lie_census d.2 hdiv) hPC

theorem kFactMultPrimeGL12_holds :
    KFactMultPrimeGL12 :=
  kFactMultPrimeGL12_of_inputs CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds

end CFSG.RankThree.PartTwo.Sec13.K135GL12
