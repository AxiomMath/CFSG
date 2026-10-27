module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

@[expose] def GGSecFiveBSpCoordFrameInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (r f : ℕ), 2 ≤ r → 2 ≤ f → p ∣ 2 ^ f - 1 →
    ∀ (B Bs X : Subgroup G), GGBstar p B Bs → GGInnerDiagOn Bs X →
      Nonempty (↥X ≃* StatedSp (r + 1) (GaloisField 2 f)) →
    ∀ (eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))) (i0 : Fin (r + 2)),
      (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (r + 2) p i0 →
      ∃ (π : Fin (r + 2) ≃ Fin (r + 2)) (κ : StatedSp (r + 1) (GaloisField 2 f) →* G)
        (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ), π 0 = i0 ∧
        GGSecFiveBPermSpKFrame Bs X eta π κ χ

end CFSG.StandardType

end
