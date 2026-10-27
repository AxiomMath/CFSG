module

public import CFSG.Quasithin.EmptyFaithful.Vocabulary
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def OrthoFixedParabolic : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ q : W → ZMod 2, IsQuadraticFormOn q → IsNondegQuadratic q →
      ∀ E : Subgroup W, Nat.card E = 2 ^ 3 → (∀ e ∈ E, q e = 0) → Nat.card W = 2 ^ 6 →
        ∀ S₀ L₀ : Subgroup (MulAut W), IsSylowTwoOf S₀ (orthogonalGroupOf q) →
          L₀ ≤ orthogonalGroupOf q → (L₀.subgroupOf (orthogonalGroupOf q)).Normal →
            ⁅L₀, L₀⁆ = L₀ → L₀ ≠ ⊥ → ∀ a : W, a ≠ 1 → (∀ g ∈ S₀, g a = a) →
              IsMaxParabolic2 L₀ (L₀ ⊓ MulAction.stabilizer (MulAut W) a)

end CFSG.Quasithin
