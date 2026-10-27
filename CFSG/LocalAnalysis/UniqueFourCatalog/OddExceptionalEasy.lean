module

public import CFSG.LocalAnalysis.UniqueFourCatalog.Standing4Basic
public import CFSG.Blueprint.Catalog
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate8150
import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOddBasic
import CFSG.RankThree.PartTwo.Census.Carrier.ReeG2One
import CFSG.RankThree.PartTwo.Census.Carrier.G2Prime
import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
import CFSG.Adapters.TauCetiExceptional.BridgeTransport
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

private theorem oddExc_cube_free_4245696 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({3} : Finset ℕ) → ¬ p ^ 3 ∣ 4245696 := by
  refine CFSG.LocalAnalysis.RankThreeUC.not_pow_three_dvd_of_primeFactors (by norm_num)
    {2, 3, 7, 13} _ (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

theorem false_of_reeG2
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) {p f : ℕ}
    (h : CFSG.Blueprint.ReeTitsModel G .twistedG2 p f) : False := by
  obtain ⟨⟨-, -, -, rfl, -, hf3⟩, a, rfl, K, hKF, hKfin, hKf, ⟨e⟩⟩ := h
  have ha : 1 ≤ a := by omega
  haveI : CharP K 3 := CFSG.SectionRank.ClassicalOdd.charP_of_card hKf
  exact hS.false_of_not_isCharTwoType e
    (CFSG.RankThree.PartTwo.Census.not_isCharTwoType_derivedCentralQuotient_reeG2 a ha K hKf)

theorem false_of_G2_odd
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) {p f : ℕ} (hp : p ≠ 2)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel G .G2 p f) : False := by
  obtain ⟨⟨hpp, -, -, h3q⟩, K, hKF, hKfin, hK, ⟨e⟩⟩ := h
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hpp.odd_of_ne_two hp).pow
  by_cases hq : Nat.card K = 3
  · letI : Fintype K := Fintype.ofFinite K
    have hKcard : Fintype.card K = 3 := by
      rwa [Nat.card_eq_fintype_card] at hq
    have eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hKcard
    have e' : G ≃* CFSG.Blueprint.AdjointQuotient .G2 (ZMod 3) :=
      e.trans (CFSG.TauCetiBridge.adjointQuotientCongr eK.symm)
    refine hS.false_of_card e' (N := 4245696) {3} ?_ ?_ oddExc_cube_free_4245696
    · rw [Nat.card_congr
        CFSG.RankThree.PartTwo.Census.Carrier.G2Three.adjointQuotientEquivR3.toEquiv]
      exact CFSG.RankThree.PartTwo.Census.Carrier.G2Three.card_R3
    · intro _ r hr _ _
      obtain rfl : r = 3 := by simpa using hr
      exact CFSG.RankThree.PartTwo.Census.Carrier.G2Three.localRank_three_adjointQuotient
  · have h3K : 3 ≤ Nat.card K := by
      rw [hK]
      exact h3q
    have h4 : 4 ≤ Nat.card K := by
      have hodd' := Nat.odd_iff.mp hodd
      omega
    exact hS.false_of_not_isCharTwoType e
      (CFSG.RankThree.PartTwo.Census.Carrier.not_isCharTwoType_adjointQuotient_G2 hodd h4)

end CFSG.LocalAnalysis.UniqueFourCatalog
