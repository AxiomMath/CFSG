module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsCube
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsModelSp

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBSymp

variable {K : Type} [Field K] {m : ℕ}

theorem ggTorusLift_symplecticNs [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (hm : 4 ≤ m) :
    GGTorusLift p 3 (LargeEvenProj (LargeEvenSpGroup K m)) := by
  obtain ⟨Φ, Y, hΦ, hΦH, hYH, hY1, hY2, hΦY⟩ := exists_nsSpModel (K := K) hm
  obtain ⟨τ, X, hτH, hτs, hinv, hXH, hX1, hX2, hτX⟩ :=
    exists_matrixTorus_of_sl2Cube hp hp2 hpq (H := LargeEvenSpGroup K m) Φ Y hΦ hΦH hYH hY1 hY2
      hΦY
  exact ggTorusLift_of_matrixTorus hp hp2 τ hτH hτs hinv X hXH hX1 hX2 hτX

end TableBSymp

end CFSG.StandardType

end
