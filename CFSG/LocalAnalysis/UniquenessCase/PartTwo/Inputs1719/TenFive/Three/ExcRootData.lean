module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcRootPair
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.IrrationalRoot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.SeitzGeneration.ExcOuterLeOne (exists_adjData_valid_E)

private def singleCheck (τ : Tag) (t : List (List ℤ × List ℤ × List ℤ)) (i : Fin τ.rank) :
    Bool :=
  let d := t.getD i ([], [], [])
  rootPairsCheck τ (fun j => d.1.getD j 0) (Pi.single i 1) (fun j => d.2.1.getD j 0)
    (fun j => d.2.2.getD j 0)

private def f4Pairs : List (List ℤ × List ℤ × List ℤ) :=
  [([0, 1, 0, 0], [0, 0, -1, 0], [1, 1, 1, 0]),
    ([1, 0, 0, 0], [0, 0, -1, 0], [1, 1, 1, 0]),
    ([0, -1, -1, 0], [-1, -1, 0, 0], [1, 0, 0, 0]),
    ([0, -1, -2, -1], [0, -1, -1, 0], [0, 0, -1, 0])]

private def e6Pairs : List (List ℤ × List ℤ × List ℤ) :=
  [([0, 0, 1, 0, 0, 0], [0, 0, 0, -1, 0, 0], [1, 0, 1, 1, 0, 0]),
    ([0, 0, 0, 1, 0, 0], [0, 0, -1, 0, 0, 0], [0, 1, 1, 1, 0, 0]),
    ([0, 0, 0, 1, 0, 0], [-1, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0]),
    ([0, 0, 0, 0, 1, 0], [0, -1, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0]),
    ([0, 0, 0, 0, 0, 1], [0, 0, 0, -1, 0, 0], [0, 0, 0, 1, 1, 1]),
    ([0, 0, 0, 0, 1, 0], [0, 0, 0, -1, 0, 0], [0, 0, 0, 1, 1, 1])]

private def e7Pairs : List (List ℤ × List ℤ × List ℤ) :=
  [([0, 0, 1, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0]),
    ([0, 0, 0, 1, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0]),
    ([0, 0, 0, 1, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0]),
    ([0, 0, 0, 0, 1, 0, 0], [0, -1, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0]),
    ([0, 0, 0, 0, 0, 1, 0], [0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 1, 1, 1, 0]),
    ([0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 1, 1, 1]),
    ([0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 1, 1, 1])]

private def e8Pairs : List (List ℤ × List ℤ × List ℤ) :=
  [([0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0]),
    ([0, 0, 0, 1, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0]),
    ([0, 0, 0, 1, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0]),
    ([0, 0, 0, 0, 1, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0]),
    ([0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 1, 1, 1, 0, 0]),
    ([0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 1, 0]),
    ([0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 1]),
    ([0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 1])]

private theorem f4_singleCheck : ∀ i, singleCheck .F4 f4Pairs i = true := by decide +kernel

private theorem e6_singleCheck : ∀ i, singleCheck .E6 e6Pairs i = true := by decide +kernel

private theorem e7_singleCheck : ∀ i, singleCheck .E7 e7Pairs i = true := by decide +kernel

private theorem e8_singleCheck : ∀ i, singleCheck .E8 e8Pairs i = true := by decide +kernel

private theorem e6_zero_five_check :
    rootPairsCheck .E6 ![-1, 0, -1, -1, -1, 0] (Pi.single ⟨0, by decide⟩ 1)
      ![0, 0, -1, -1, -1, -1] (Pi.single ⟨5, by decide⟩ 1) = true := by
  decide +kernel

theorem exists_rootPairs_single {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) :
    ∃ γ₁ γ₃ γ₄ : Fin τ.rank → ℤ, RootPairs τ γ₁ (Pi.single i 1) γ₃ γ₄ := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact ⟨_, _, _, RootPairs.of_check (f4_singleCheck i)⟩
  · exact ⟨_, _, _, RootPairs.of_check (e6_singleCheck i)⟩
  · exact ⟨_, _, _, RootPairs.of_check (e7_singleCheck i)⟩
  · exact ⟨_, _, _, RootPairs.of_check (e8_singleCheck i)⟩


private theorem exists_adjData_valid {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ D : AdjData τ, D.Valid ∧ NoG2 τ := by
  rcases hτ with rfl | hE
  · exact ⟨_, f4Data_valid, noG2_F4⟩
  · exact exists_adjData_valid_E hE

theorem isExtraGood_xPar_single {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) (i : Fin τ.rank) (c : K) :
    IsExtraGood (xPar (rootOperatorFamily τ) (Pi.single i 1) c) := by
  obtain ⟨D, hD, hτ'⟩ := exists_adjData_valid hτ
  obtain ⟨γ₁, γ₃, γ₄, h⟩ := exists_rootPairs_single hτ i
  exact isExtraGood_xPar_of_rootPairs _ hτ' hD hK h c

theorem isExtraGood_xPar_single_mul_E6 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (s t : K) :
    IsExtraGood (xPar (rootOperatorFamily .E6) (Pi.single ⟨0, by decide⟩ 1) s *
      xPar (rootOperatorFamily .E6) (Pi.single ⟨5, by decide⟩ 1) t) := by
  obtain ⟨D, hD, hτ'⟩ := exists_adjData_valid (τ := .E6) (Or.inr (Or.inl rfl))
  exact isExtraGood_xPar_mul_of_rootPairs _ hτ' hD hK (RootPairs.of_check e6_zero_five_check) s t

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
