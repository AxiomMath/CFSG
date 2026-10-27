module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQTwoXInLDatum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → x ∈ L → ∀ [Fact p.Prime] (y : G) (K : Subgroup G),
      GGNbr p B x D J y K → ∀ M : GGQTwoModel p Bs x y D L J K,
        LinearIndependent (ZMod p) (fun i : {k // k ≠ M.a} => M.coroot i) ∧
        M.xV ∈ Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ M.a} => M.coroot i) ∧
        Module.finrank (ZMod p) M.V ≤ Fintype.card {k // k ≠ M.a} + 1

end CFSG.StandardType

end
