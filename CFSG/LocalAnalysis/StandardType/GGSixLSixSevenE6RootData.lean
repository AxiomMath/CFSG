module

public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.Blueprint.Catalog
public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType

open CFSG.Open

@[expose] def GGSixE6A24RootData : Prop :=
  ∀ (E : Type) [Group E] [Finite E], commutator E = ⊤ →
    CFSG.Blueprint.LieModel (E ⧸ Subgroup.center E) .E6 0 2 1 →
    Subgroup.center E = ⊥ ∧
    ∀ (x₀ : E) (L' J' : Subgroup E), x₀ ^ 3 = 1 →
      CFSG.Assembly.IsComponentOf L' (Subgroup.centralizer {x₀}) →
      CFSG.Blueprint.LieModel (↥L' ⧸ Subgroup.center ↥L') .PSL 6 2 1 →
      J' ≤ L' → CFSG.Assembly.IsQuasisimple ↥J' →
      CFSG.Blueprint.LieModel (↥J' ⧸ Subgroup.center ↥J') .PSL 3 2 2 →
      ∃ R' J₀' : Subgroup E, R' ≤ J' ∧ R' ≠ ⊥ ∧ IsPGroup 2 R' ∧ J₀' ≤ J' ∧
        pCoreOf 2 (Subgroup.normalizer (R' : Set E)) ⊔ J₀' = ⊤ ∧
        (∀ Q' : Subgroup E, Q' = pCoreOf 2 (Subgroup.normalizer (R' : Set E)) →
          ∀ U : Subgroup E, (Subgroup.center ↥Q').map Q'.subtype ≤ U → U ≤ Q' →
            U ≠ (Subgroup.center ↥Q').map Q'.subtype → U ≠ Q' →
            Subgroup.normalizer (R' : Set E) ≤ Subgroup.normalizer (U : Set E) →
            J' ⊔ U = ⊤) ∧
        GGRootNormInner R' ∧
        ∀ g : E, g ^ 3 = 1 → g ≠ 1 → g ∈ Subgroup.centralizer {x₀} →
          g ∈ Subgroup.centralizer (J' : Set E) →
          ∀ K' : Subgroup E, J' ≤ K' →
            CFSG.Assembly.IsComponentOf K' (Subgroup.centralizer {g}) →
            GGRootNormNoCentral (R'.subgroupOf K') ∧
              (GGRootNormInner (R'.subgroupOf K') ∨
                ∃ δ : ↥(Subgroup.normalizer (K' : Set E)),
                  (δ : E) ∈ Subgroup.centralizer {g} ∧
                    (δ : E) ∈ Subgroup.normalizer (R' : Set E) ∧
                    GGRootNormInnerDiag (R'.subgroupOf K') (K'.normalizerMonoidHom δ))

end CFSG.StandardType
