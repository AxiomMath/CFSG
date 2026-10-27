module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcHeis
public import CFSG.LieType.Steinberg.RankTwo.G2ExtrasRankTwo
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
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint


theorem isSpecialGood_xPar_G2 {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (c : K) :
    IsSpecialGood p (xPar (rootOperatorFamily .G2) ![1, 0] c) ∧
      IsSpecialGood p (xPar (rootOperatorFamily .G2) ![2, 3] c) := by
  have h0 : RootCertificate.root (Tag.rootCertificate Tag.G2) 0 = ![1, 0] := by
    ext i; fin_cases i <;> rfl
  have h7 : RootCertificate.root (Tag.rootCertificate Tag.G2) 7 = ![2, 3] :=
    CFSG.LieType.Steinberg.RankTwo.G2Extras.g2Root_seven
  obtain ⟨ha, -, hz⟩ :=
    isSpecialGood_of_comm (K := K) hp hp2 hK h3
      (xa := fun s => xPar (rootOperatorFamily Tag.G2)
        (RootCertificate.root (Tag.rootCertificate Tag.G2) 7) s)
      (xb := fun s => xPar (rootOperatorFamily Tag.G2)
        (RootCertificate.root (Tag.rootCertificate Tag.G2) 6) s)
      (z := fun s => xPar (rootOperatorFamily Tag.G2)
        (RootCertificate.root (Tag.rootCertificate Tag.G2) 0) s)
      (fun s t => xPar_add (F := rootOperatorFamily Tag.G2) _ s t)
      (fun s t => xPar_add (F := rootOperatorFamily Tag.G2) _ s t)
      (fun s t => xPar_add (F := rootOperatorFamily Tag.G2) _ s t)
      (xPar_injective (F := rootOperatorFamily Tag.G2)
        (γ := RootCertificate.root (Tag.rootCertificate Tag.G2) 0)
        (CFSG.LieType.Steinberg.RankTwo.G2Extras.isRoot_g2Root (n := 0) (by norm_num)))
      (fun s t => CFSG.LieType.Steinberg.RankTwo.G2Extras.commutator_seven_six (k := K) s t)
      (fun s t => CFSG.LieType.Steinberg.RankTwo.G2Extras.commute_of_repCheck_nil
        (k := K) (a := 0) (b := 7) (by decide +kernel) s t)
      (fun s t => CFSG.LieType.Steinberg.RankTwo.G2Extras.commute_of_repCheck_nil
        (k := K) (a := 0) (b := 6) (by decide +kernel) s t) c
  refine ⟨?_, ?_⟩
  · rw [← h0]
    exact hz
  · rw [← h7]
    exact ha

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
