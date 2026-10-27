module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6ThreeDvd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6FourDvd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6SixDvd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Cyclic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Arith
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Cover
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitCyclicCore
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Hyp
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KF4.KernelTools

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open scoped Matrix

namespace E6Nonsplit

theorem exists_card_eq_two_pow {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  exact ⟨f, f.pos, by rw [Nat.card_eq_fintype_card, hf]⟩

section Rows


theorem dvd_card_of_isComponentOf_E6_ad_of_phiThree {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 3).eval (Nat.card K : ℤ)) {x : ↥(adjointGroup .E6 K)}
    (hx : orderOf x = p) {X : Subgroup ↥(adjointGroup .E6 K)}
    (hX : IsComponentOf X (Subgroup.centralizer ({x} : Set ↥(adjointGroup .E6 K)))) :
    p ∣ Nat.card X := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow (K := K)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1 := by
    simpa [exhaustionPhi] using hpf
  exact CFSG.RankThree.PartOne.KE6.NonsplitLayers.e6_three_components_dvd K hf hK hp hp3 hpq
    (AlgebraicClosure K) x hx X hX

theorem dvd_card_of_isComponentOf_E6_ad_of_phiSix {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 6).eval (Nat.card K : ℤ)) {x : ↥(adjointGroup .E6 K)}
    (hx : orderOf x = p) {X : Subgroup ↥(adjointGroup .E6 K)}
    (hX : IsComponentOf X (Subgroup.centralizer ({x} : Set ↥(adjointGroup .E6 K)))) :
    p ∣ Nat.card X := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow (K := K)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1 := by
    simpa [exhaustionPhi] using hpf
  exact CFSG.RankThree.PartOne.KE6.NonsplitLayers.e6_six_components_dvd K hf hK hp hp3 hpq
    (AlgebraicClosure K) x hx X hX

theorem dvd_card_of_isComponentOf_E6_ad_of_phiFour {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 4).eval (Nat.card K : ℤ)) {x : ↥(adjointGroup .E6 K)}
    (hx : orderOf x = p) {X : Subgroup ↥(adjointGroup .E6 K)}
    (hX : IsComponentOf X (Subgroup.centralizer ({x} : Set ↥(adjointGroup .E6 K)))) :
    p ∣ Nat.card X := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow (K := K)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by
    simpa [exhaustionPhi] using hpf
  have hcm := canonicalRep_mem_monomialSubgroup (τ := Tag.E6) (AlgebraicClosure K) e6F4U
  have hπ : weylQuotientHom .E6 (AlgebraicClosure K)
      ⟨canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) e6F4U, hcm⟩ = e6F4U :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep e6F4U)
  have hnW : ∀ u, weylQuotientHom .E6 (AlgebraicClosure K)
      ⟨canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) e6F4U, hcm⟩ • u =
        (weylMatrix e6F4U) *ᵥ u := fun u => by
    rw [hπ, weylMatrix_mulVec]
  exact CFSG.RankThree.PartOne.KE.NonsplitLayers.e6_four_components_dvd K hf hK hp hp3 hpq
    (AlgebraicClosure K) _ hcm hnW x hx X hX

end Rows

section Dvd


theorem ggNonsplitDvdAt_E6_ad_of_row {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpC : p ∣ Nat.card ↥(adjointGroup .E6 K)) {m : ℕ}
    (hm : m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 8 ∨ m = 9 ∨ m = 12)
    (hpf : (p : ℤ) ∣ (exhaustionPhi m).eval (Nat.card K : ℤ)) :
    ExcNonsplit.GGNonsplitDvdAt ↥(adjointGroup .E6 K) p := by
  intro a ha X hX
  by_cases ha1 : a = 1
  · subst ha1
    rw [ExcNonsplit.centralizer_one_eq_top] at hX
    obtain rfl := ExcNonsplit.eq_top_of_isComponentOf_top
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K) hX
    rwa [Subgroup.card_top]
  · have : Fact p.Prime := ⟨hp⟩
    have hao : orderOf a = p := orderOf_eq_prime ha ha1
    rcases hm with rfl | rfl | rfl | hm'
    · exact dvd_card_of_isComponentOf_E6_ad_of_phiThree hp hp3 hpf hao hX
    · exact dvd_card_of_isComponentOf_E6_ad_of_phiFour hp hp3 hpf hao hX
    · exact dvd_card_of_isComponentOf_E6_ad_of_phiSix hp hp3 hpf hao hX
    · exact absurd hX (not_isComponentOf_centralizer_of_dvd_phi_regular hp hp3 hm' hpf hao)

end Dvd

end E6Nonsplit

end CFSG.StandardType
