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

@[expose] def Str83SevenPath : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      ∃ x₁ ∈ L1 ⊔ bigB L1 L2 S, x₁ ∉ bigB L1 L2 S ∧
        ∃ x₂ ∈ L2 ⊔ bigB L1 L2 S, x₂ ∉ bigB L1 L2 S ∧
          (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓ pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) ⊓
            (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓ pCoreOf 2 (L2 ⊔ bigB L1 L2 S)).map
              (MulAut.conj (x₂ * x₁)).toMonoidHom ⊓
            (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓ pCoreOf 2 (L2 ⊔ bigB L1 L2 S)).map
              (MulAut.conj ((x₂ * x₁) ^ 2)).toMonoidHom ⊓
            (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓ pCoreOf 2 (L2 ⊔ bigB L1 L2 S)).map
              (MulAut.conj ((x₂ * x₁) ^ 3)).toMonoidHom = ⊥

end CFSG.Quasithin.Stroth

end
