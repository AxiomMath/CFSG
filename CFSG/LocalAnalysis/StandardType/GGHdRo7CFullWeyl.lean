module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem c2_fullWeyl_holds :
    ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
      [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
      (F : Subgroup (V ≃ₗ[ZMod p] V)), (∀ a, a ∈ F ↔ C2Full p b a) → ZS.LinWeyl p F :=
  fun p _ hp n hn V _ _ b F hF => ggRC_linWeyl_of_signed (by omega) (by omega) b F hF

end CFSG.StandardType.HdRo7C
