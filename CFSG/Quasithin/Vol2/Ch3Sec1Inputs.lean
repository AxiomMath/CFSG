module

public import CFSG.Quasithin.Vol2.Ch3Sec1Defs

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def B513 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), X ≠ ⊥ →
      pCoreOf 2 (X.map (dualAct V)) = ⊥ →
      X.map (dualAct V) =
        @ffJ (V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup (X.map (dualAct V)) →
      (∃ (H : Type) (_ : Group H) (_ : Finite H), SQTKTauCeti.StronglyQuasithin H ∧
        CFSG.SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥(X.map (dualAct V)), Function.Surjective f) →
      qOf X ≤ 2

structure HypE28 {G : Type} [Group G] [Finite G] (H T M V : Subgroup G) : Prop where
  minParabolic : MinParabolic H T M
  sqtk : IsSQTKSub H
  elemAbelian : IsElemAbelian 2 V
  le_T : V ≤ T
  normal_T : T ≤ Subgroup.normalizer (V : Set G)
  le_pCore : V ≤ pCoreOf 2 M
  not_le_ker : ¬ V ≤ kerIn M H

@[expose] def E213Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G) (h : HypE28 H T M V),
    CharTwo H → qhatInt H V h.elemAbelian ≤ 2

@[expose] def E215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G) (h : HypE28 H T M V),
    CharTwo H → IsTISetIn V M → qhatInt H V h.elemAbelian < 2

@[expose] def AS316Sylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M M₀ H V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T → InM T M →
    ∀ h : Hyp315 T M M₀ H V, V ≠ ⊥ →
      (¬ ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
        M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)) →
      ¬ qInt M₀ V h.reduced.2.2.1 ≤ 1 → ¬ IsDualFFInt M₀ V h.reduced.2.2.1 →
      V ≤ pCoreOf 2 H →
      ((pCoreOf 2 M₀ ⊓ pCoreOf 2 H).subgroupOf H).Normal →
      IsElemAbelian 2 (conjClosure V H) →
      IsSylowTwoOf (pCoreOf 2 M₀) (oTwoUpper H ⊔ pCoreOf 2 M₀)

@[expose] def AS317Sylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M M₀ H V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T → InM T M →
    Hyp315 T M M₀ H V → thompsonJ T ≤ pCoreOf 2 M₀ →
    ¬ H ≤ Subgroup.normalizer (thompsonJ T : Set G) →
    ¬ quasithinOmegaOneCenter T ≤ centerOf H →
    IsSylowTwoOf (pCoreOf 2 M₀) (oTwoUpper H ⊔ pCoreOf 2 M₀)

end CFSG.Quasithin
