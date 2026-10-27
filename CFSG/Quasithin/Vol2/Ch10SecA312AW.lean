module

public import CFSG.Quasithin.Vol2.Ch10SecA312AB

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def A312ZCentRestRuA5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T B : Subgroup X), IsAlt 5 (ModO2 B) →
    Nat.card (CFSG.pCore 2 ↥B) = 2 ^ 11 → IsSporadic .Ru ↥(⊤ : Subgroup X) →
    ZCentConf X T B → False

@[expose] def A312ZCentRestM23 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T B : Subgroup X),
    (IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsPSL 3 2 1 Y) ∨
      IsExt ↥B (fun V _ => IsE2 3 V) (fun Y _ => IsPSL 3 2 1 Y)) →
    IsSporadic .M23 ↥(⊤ : Subgroup X) → ZCentConf X T B → False

@[expose] def A312ZCentRestJ4A5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T B : Subgroup X), IsAlt 5 (ModO2 B) →
    IsSporadic .J4 ↥(⊤ : Subgroup X) → ZCentConf X T B → False

@[expose] def A312ZCentRestJ4L32 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T B : Subgroup X), IsPSL 3 2 1 (ModO2 B) →
    IsSporadic .J4 ↥(⊤ : Subgroup X) → ZCentConf X T B → False

@[expose] def A312ZCentRestJ4 : Prop := A312ZCentRestJ4A5 ∧ A312ZCentRestJ4L32

end CFSG.Quasithin.Vol2.Ch10.A312A
