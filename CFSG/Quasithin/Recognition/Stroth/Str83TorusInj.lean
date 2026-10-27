module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.EmptyFaithful.F112HypW
public import CFSG.Quasithin.Recognition.GoldschmidtF112RLeaves
public import CFSG.Quasithin.Recognition.Stroth.SliceSplit

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender

@[expose] def Str83TorusInj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      (∀ d ∈ borelOf L2 S, Odd (orderOf d) →
          (∀ l ∈ L1, d * l * d⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) → d = 1) ∧
      (∀ d ∈ borelOf L1 S, Odd (orderOf d) →
          (∀ l ∈ L2, d * l * d⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → d = 1)

end CFSG.Quasithin.Stroth

end
