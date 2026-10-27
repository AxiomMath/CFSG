module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsCube
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsModelOmega

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TableBSymp

variable {K : Type} [Field K] {m : ℕ}

theorem exists_omegaPlusNsTorus [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (hK : 4 ≤ Nat.card K) (hm : 4 ≤ m) :
    ∃ (τ : (Fin 3 → Multiplicative (ZMod p)) →* GL (Fin m ⊕ Fin m) K)
      (X : Multiplicative K →* GL (Fin m ⊕ Fin m) K),
      (∀ f, τ f ∈ LargeEvenOmega (LargeEvenQPlus K m)) ∧
      (∀ f, τ f ∈ LargeEvenScalars (Fin m ⊕ Fin m) K → f = 1) ∧
      (∀ i j : Fin 3, ∃ w ∈ LargeEvenOmega (LargeEvenQPlus K m),
        w * torusBasis τ i * w⁻¹ = (torusBasis τ i)⁻¹ ∧
          (j ≠ i → w * torusBasis τ j * w⁻¹ = torusBasis τ j)) ∧
      (∀ c, X c ∈ LargeEvenOmega (LargeEvenQPlus K m)) ∧
      X (Multiplicative.ofAdd 1) ∉ LargeEvenScalars (Fin m ⊕ Fin m) K ∧
      (∀ c, X c ^ 2 = 1) ∧ (∀ f c, ∃ c', τ f * X c * (τ f)⁻¹ = X c') := by
  obtain ⟨Φ, Y, hΦ, hΦH, hYH, hY1, hY2, hΦY⟩ := exists_nsDetModel (K := K) hK hm
  exact exists_matrixTorus_of_sl2Cube hp hp2 hpq (H := LargeEvenOmega (LargeEvenQPlus K m)) Φ Y hΦ
    hΦH hYH hY1 hY2 hΦY

end TableBSymp

end CFSG.StandardType

end
