module

public import CFSG.LocalAnalysis.StandardType.FS81.Pieces

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly Matrix

@[expose] def OrbitLine {k : ℕ} (X : Subgroup (GL (Fin k) (ZMod 3))) (e₀ e : Coords k) : Prop :=
  ∃ g ∈ X, (g : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ e₀ = e ∨
    (g : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ e₀ = -e

end CFSG.StandardType.FrameRoute.FS81
