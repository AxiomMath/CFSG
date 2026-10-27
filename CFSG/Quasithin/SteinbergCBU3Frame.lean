module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.SteinbergCB

open Subgroup

@[expose] def QTU3InternalFrame {G : Type*} [Group G] (T L V : Subgroup G) (z : G) : Prop :=
  T ≤ normalizer (L : Set G) ∧ V ≤ T ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 64 ∧
    V ≤ CFSG.Open.pCoreOf 2 (L ⊔ T) ∧
    V ≤ centralizer (CFSG.Open.pCoreOf 2 (L ⊔ T) : Set G) ∧
    L ≤ normalizer (V : Set G) ∧ T ≤ normalizer (V : Set G) ∧
    (∀ W : Subgroup G, W ≤ V → (∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) → W = ⊥ ∨ W = V) ∧
    (∃ l ∈ L, ∃ v ∈ V, l * v * l⁻¹ ≠ v) ∧
    T ⊓ centralizer (V : Set G) = CFSG.Open.pCoreOf 2 (L ⊔ T) ∧
    V ⊓ centralizer (T : Set G) = zpowers z ∧ orderOf z = 2

end CFSG.Quasithin.SteinbergCB
