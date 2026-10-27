module

public import CFSG.RankThree.PartOne.KE.E7FourFinal
public import CFSG.RankThree.PartOne.KE.E7FourStab

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.RankThree.PartOne
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem planeLocalCoreOdd_E7_four (hD4 : D4TranspositionLayer Tag.E7) (K : Type) [Field K]
    [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 4).eval (Nat.card K : ℤ)) :
    PlaneLocalCoreOdd p (adjointGroup .E7 K) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by simpa [exhaustionPhi] using hpf
  obtain ⟨F⟩ := exists_e7FourFrame K hf hK hp hp3 hpq L
  exact planeLocalCoreOdd_E7_four_of_frame hD4 F hf hK hp hp3 hpq (e7_stabHyp F hK hp hp3 hpq)

theorem oddEndpoint_E7_phi4 (hD4 : D4TranspositionLayer Tag.E7) :
    OddEndpoint .E7 fun p ℓ f => (p : ℤ) ∣ cycloVal 4 ℓ f := by
  refine oddEndpoint_E7_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_E7_four hD4 K hℓ hf hK hp hp3 (by simpa [cycloVal, hK] using hc)

end CFSG.RankThree.PartOne.KE
