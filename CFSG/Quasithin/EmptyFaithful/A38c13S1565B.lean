module

public import CFSG.Quasithin.EmptyFaithful.A38c13S1565A
public import CFSG.Quasithin.EmptyFaithful.S1565M14
public import CFSG.Quasithin.EmptyFaithful.S1565G
public import CFSG.Quasithin.EmptyFaithful.S1565I
public import CFSG.Quasithin.EmptyFaithful.S1565M13
public import CFSG.Quasithin.EmptyFaithful.S1565M9

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565

section Inputs

attribute [local instance] commGroupOfFact

@[expose] def Input15365FFnatC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G)
    (D : Data15365C G T Mc M V₁ V₂ H K t),
    ∀ I : Subgroup G, quasithinOmegaOneCenter T ≤ I → ∀ hIU : I ≤ conjClosure (ZS153 T M V₁) H,
    ∀ W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (ZS153 T M V₁) H T, ∀ w ∈ W, t w ∈ W) →
      IsIrrPlusTildeU D.hF I W →
      tildeOf (quasithinOmegaOneCenter T) (conjClosure I H) ≠
        tildeOf (quasithinOmegaOneCenter T)
          ⁅conjClosure (ZS153 T M V₁) H, conjClosure K T⁆ →
      FFAlt15365 D.hF (conjClosure I H) (conjClosure_le_conjClosure_U hIU le_rfl) →
      NoFixedLayer15365 D.hF M I

@[expose] def Input15365FFnatEltC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G)
    (D : Data15365C G T Mc M V₁ V₂ H K t),
    ∀ I : Subgroup G, quasithinOmegaOneCenter T ≤ I → ∀ hIU : I ≤ conjClosure (ZS153 T M V₁) H,
    ∀ W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (ZS153 T M V₁) H T, ∀ w ∈ W, t w ∈ W) →
      IsIrrPlusTildeU D.hF I W →
      tildeOf (quasithinOmegaOneCenter T) (conjClosure I H) ≠
        tildeOf (quasithinOmegaOneCenter T)
          ⁅conjClosure (ZS153 T M V₁) H, conjClosure K T⁆ →
      FFAlt15365 D.hF (conjClosure I H) (conjClosure_le_conjClosure_U hIU le_rfl) →
      haveI := factElem D.hF (le_conjClosure (ZS153 T M V₁) H)
      ∃ t₀ : ↥H, (t₀ : G) ∈ M ∧ ∃ m : ℕ, Odd m ∧
        (∀ a ∈ subM (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)
            ⁅conjClosure (ZS153 T M V₁) H, conjClosure K T⁆,
          ((actH D.hF.H_le_normalizer_V₁
              (le_normalizer_conjClosure (ZS153 T M V₁) H) t₀) ^ m) a = a) ∧
        ∀ a ∈ subM (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)
            ⁅conjClosure (ZS153 T M V₁) H, conjClosure K T⁆,
          actH D.hF.H_le_normalizer_V₁ (le_normalizer_conjClosure (ZS153 T M V₁) H) t₀ a * a⁻¹ ∈
            subM (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)
                ⁅conjClosure (ZS153 T M V₁) H, conjClosure K T⁆ ⊓
              S1565.fixModSub
                (actH D.hF.H_le_normalizer_V₁ (le_normalizer_conjClosure (ZS153 T M V₁) H))
                ((conjClosure K T).subgroupOf H)
                (subM (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)
                  (conjClosure I H)) →
          a ∈ subM (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)
                ⁅conjClosure (ZS153 T M V₁) H, conjClosure K T⁆ ⊓
              S1565.fixModSub
                (actH D.hF.H_le_normalizer_V₁ (le_normalizer_conjClosure (ZS153 T M V₁) H))
                ((conjClosure K T).subgroupOf H)
                (subM (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)
                  (conjClosure I H))

@[expose] def Input15365TypesFourEltC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G)
    (D : Data15365C G T Mc M V₁ V₂ H K t), conjClosure K T = K →
    ∀ I : Subgroup G, quasithinOmegaOneCenter T ≤ I → ∀ hIU : I ≤ conjClosure (ZS153 T M V₁) H,
    ∀ W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (ZS153 T M V₁) H T, ∀ w ∈ W, t w ∈ W) →
      IsIrrPlusTildeU D.hF I W →
      haveI := factElem D.hF hIU
      ∃ t₀ : ↥H, (t₀ : G) ∈ M ∧ ∃ m : ℕ, Odd m ∧
        (actH D.hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) t₀) ^ m = 1 ∧
        ∀ w : ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure I H)),
          actH D.hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) t₀ w * w⁻¹ ∈
            fixV (autIH (quasithinOmegaOneCenter T) I H (conjClosure K T)) →
          w ∈ fixV (autIH (quasithinOmegaOneCenter T) I H (conjClosure K T))

@[expose] def Input15365TypesFourTwistC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G)
    (D : Data15365C G T Mc M V₁ V₂ H K t), conjClosure K T = K →
    ∀ I : Subgroup G, quasithinOmegaOneCenter T ≤ I → ∀ hIU : I ≤ conjClosure (ZS153 T M V₁) H,
    ∀ W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (ZS153 T M V₁) H T, ∀ w ∈ W, t w ∈ W) →
      IsIrrPlusTildeU D.hF I W →
      TypesFourTwistHyp D.hF I hIU → TypesFourEltConcl D.hF M I hIU

@[expose] def Input15365TwistFieldBigC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G)
    (D : Data15365C G T Mc M V₁ V₂ H K t), conjClosure K T = K →
    ∀ I : Subgroup G, quasithinOmegaOneCenter T ≤ I → ∀ hIU : I ≤ conjClosure (ZS153 T M V₁) H,
    ∀ W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (ZS153 T M V₁) H T, ∀ w ∈ W, t w ∈ W) →
      IsIrrPlusTildeU D.hF I W → TwistFieldBig D.hF I hIU

@[expose] def Input15365TypesFourNatModuleC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G)
    (D : Data15365C G T Mc M V₁ V₂ H K t), conjClosure K T = K →
    ∀ I : Subgroup G, quasithinOmegaOneCenter T ≤ I → ∀ hIU : I ≤ conjClosure (ZS153 T M V₁) H,
    ∀ W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (ZS153 T M V₁) H T, ∀ w ∈ W, t w ∈ W) →
      IsIrrPlusTildeU D.hF I W →
      haveI := factElem D.hF hIU
      (H ≤ Subgroup.normalizer (I : Set G) ∨
        (subM (quasithinOmegaOneCenter T) (conjClosure I H) I =
            orbSup (autIH (quasithinOmegaOneCenter T) I H T)
              (subM (quasithinOmegaOneCenter T) (conjClosure I H) I) ∧
          IsFFModule (autSec (autIH (quasithinOmegaOneCenter T) I H K ⊔
              autIH (quasithinOmegaOneCenter T) I H T)
            (subM (quasithinOmegaOneCenter T) (conjClosure I H) I)
            (fixV (autIH (quasithinOmegaOneCenter T) I H (conjClosure K T)))))) →
      TypesFourShapeNatW (autIH (quasithinOmegaOneCenter T) I H K)

@[expose] def Input15365FFnatEltTwoC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G)
    (D : Data15365C G T Mc M V₁ V₂ H K t), conjClosure K T ≠ K →
    ∀ I : Subgroup G, quasithinOmegaOneCenter T ≤ I → ∀ hIU : I ≤ conjClosure (ZS153 T M V₁) H,
    ∀ W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (ZS153 T M V₁) H T, ∀ w ∈ W, t w ∈ W) →
      IsIrrPlusTildeU D.hF I W →
      tildeOf (quasithinOmegaOneCenter T) (conjClosure I H) ≠
        tildeOf (quasithinOmegaOneCenter T)
          ⁅conjClosure (ZS153 T M V₁) H, conjClosure K T⁆ →
      FFAlt15365 D.hF (conjClosure I H) (conjClosure_le_conjClosure_U hIU le_rfl) →
      FFnatEltConcl D.hF M I

end Inputs

namespace S153M

section Inputs

attribute [local instance] commGroupOfFact

@[expose] def Input15365FFnatEltOneC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G)
    (D : Data15365C G T Mc M V₁ V₂ H K t), conjClosure K T = K →
    ∀ I : Subgroup G, quasithinOmegaOneCenter T ≤ I → ∀ hIU : I ≤ conjClosure (ZS153 T M V₁) H,
    ∀ W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (ZS153 T M V₁) H T, ∀ w ∈ W, t w ∈ W) →
      IsIrrPlusTildeU D.hF I W →
      tildeOf (quasithinOmegaOneCenter T) (conjClosure I H) ≠
        tildeOf (quasithinOmegaOneCenter T)
          ⁅conjClosure (ZS153 T M V₁) H, conjClosure K T⁆ →
      FFAlt15365 D.hF (conjClosure I H) (conjClosure_le_conjClosure_U hIU le_rfl) →
      FFnatEltConcl D.hF M I

@[expose] def Input15365NoStrongFFOneC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G)
    (D : Data15365C G T Mc M V₁ V₂ H K t), conjClosure K T = K →
    ∀ I : Subgroup G, quasithinOmegaOneCenter T ≤ I → ∀ hIU : I ≤ conjClosure (ZS153 T M V₁) H,
    ∀ W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (ZS153 T M V₁) H T, ∀ w ∈ W, t w ∈ W) →
      IsIrrPlusTildeU D.hF I W →
      tildeOf (quasithinOmegaOneCenter T) (conjClosure I H) ≠
        tildeOf (quasithinOmegaOneCenter T)
          ⁅conjClosure (ZS153 T M V₁) H, conjClosure K T⁆ →
      ¬ F9.IsStrongFFInt
        (tildeOf (quasithinOmegaOneCenter T) (conjClosure K T ⊔ T))
        (tildeOf (quasithinOmegaOneCenter T) (conjClosure I H))
        (D.hF.isElemAbelian_tilde_of_le (conjClosure_le_conjClosure_U hIU le_rfl))

@[expose] def Input15365NoStrongFFTwoC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ H K : Subgroup G) (t : G)
    (D : Data15365C G T Mc M V₁ V₂ H K t), conjClosure K T ≠ K →
    ∀ I : Subgroup G, quasithinOmegaOneCenter T ≤ I → ∀ hIU : I ≤ conjClosure (ZS153 T M V₁) H,
    ∀ W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (ZS153 T M V₁) H T, ∀ w ∈ W, t w ∈ W) →
      IsIrrPlusTildeU D.hF I W →
      tildeOf (quasithinOmegaOneCenter T) (conjClosure I H) ≠
        tildeOf (quasithinOmegaOneCenter T)
          ⁅conjClosure (ZS153 T M V₁) H, conjClosure K T⁆ →
      ¬ F9.IsStrongFFInt
        (tildeOf (quasithinOmegaOneCenter T) (conjClosure K T ⊔ T))
        (tildeOf (quasithinOmegaOneCenter T) (conjClosure I H))
        (D.hF.isElemAbelian_tilde_of_le (conjClosure_le_conjClosure_U hIU le_rfl))

end Inputs

end S153M

end CFSG.Quasithin
