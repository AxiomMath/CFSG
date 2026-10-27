module

public import CFSG.Sporadic.Recognition.LyonsModel

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open Equiv Subgroup

@[expose] def Cp3Fact : Prop :=
  Nat.card B0 = 5388768000 →
    Nat.card ↥(B0 ⊓ normalizer (zpowers y0G : Set (Perm (Fin deg)))) = 349920 →
    ∀ g ∈ B0, ∀ w : Perm (Fin deg), w = g * y0G * g⁻¹ → w * y0G = y0G * w → w ≠ y0G →
      w ≠ y0G⁻¹ → ∃ u ∈ closure (Set.range fun j : Fin 4 => uG j.val),
        u * w * u⁻¹ = w0G ∨ u * w * u⁻¹ = w0G⁻¹

end CFSG.Sporadic.Recognition.LyonsSims.Ly0

end
