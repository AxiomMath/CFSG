module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSecFivePermNbrLabelOfJInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
    ∀ (n : ℕ), 4 ≤ n → ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (K : Subgroup G),
      K ∈ 𝒦 → (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
      ∀ (t : LargeEvenLieTag) (e : ℕ), (t = .A ∨ t = .twA) →
        LargeEvenInLambda2 ⟨t, n - 2, e⟩ → GGHasLabel ⟨t, n - 2, e⟩ (↥J ⧸ Subgroup.center ↥J) →
        GGHasLabel ⟨t, n - 1, e⟩ (↥K ⧸ Subgroup.center ↥K)

end CFSG.StandardType

end
