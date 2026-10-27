module

public import CFSG.Quasithin.H13.L32A53a
public import CFSG.Quasithin.Vol2.Ch6Vocab

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def Lemma14_5_11Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₂ Y : Subgroup G), Ctx G T L V V₂ Y →
    quasithinO2QuotientIso (xL L V₂ ⊔ T) (Equiv.Perm (Fin 3)) →
    (xL L V₂ ⊔ T) ⊓ (Y ⊔ T) = T →
    pCoreOf 2 (hY T L V₂ Y) ≠ ⊥ → Group.IsSolvable ↥(hY T L V₂ Y) →
    thompsonJ T ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) →
    xL L V₂ = ⁅xL L V₂, thompsonJk 1 T⁆ →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ P : Subgroup G, cH T L V V₂ Y ≤ P → P ≤ hY T L V₂ Y →
      hY T L V₂ Y ≤ Subgroup.normalizer (P : Set G) →
      (∀ g ∈ P, ∃ k : ℕ, g ^ p ^ k ∈ cH T L V V₂ Y) →
      ∀ g ∈ P, ∀ x ∈ xL L V₂, ⁅g, x⁆ ∈ Subgroup.centralizer (vH T L V V₂ Y : Set G)

end CFSG.Quasithin.H13.L32A.T53

end
