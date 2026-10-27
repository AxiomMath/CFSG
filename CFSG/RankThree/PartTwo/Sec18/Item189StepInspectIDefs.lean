module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.Assembly.RankThreeEven (projSL projSU)

section Inspect

variable {Y : Type} [Group Y]

structure InspectData189 (X Q : Subgroup Y) (x : Y) : Prop where
  normal : X.Normal
  simple : IsSimpleGroup X
  sup_eq : X ⊔ Q = ⊤
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 Q ⊤
  centralizer_eq : Subgroup.centralizer (X : Set Y) = ⊥
  mem : x ∈ X
  orderOf_eq : orderOf x = 3
  mem_normalizer : x ∈ Subgroup.normalizer (Q : Set Y)

@[expose] def InspectGen189 (X Q : Subgroup Y) (x : Y) : Prop :=
  X ≤ (X ⊓ Subgroup.normalizer (Q : Set Y)) ⊔
    (X ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set Y))

end Inspect

@[expose] def Inspect189L2Even : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X Q : Subgroup Y) (x : Y) (n : ℕ),
    InspectData189 X Q x → 2 ≤ n → Nonempty (↥X ≃* projSL 2 (GaloisField 2 n)) →
      InspectGen189 X Q x

@[expose] def Inspect189L3Even : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X Q : Subgroup Y) (x : Y) (n : ℕ),
    InspectData189 X Q x → Odd n → Nonempty (↥X ≃* projSL 3 (GaloisField 2 n)) →
      InspectGen189 X Q x

@[expose] def Inspect189U3Even : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X Q : Subgroup Y) (x : Y) (n : ℕ),
    InspectData189 X Q x → Even n → 2 ≤ n → Nonempty (↥X ≃* projSU 3 2 n) →
      InspectGen189 X Q x

@[expose] def Inspect189L2Odd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X Q : Subgroup Y) (x : Y) (p f : ℕ) [Fact p.Prime],
    InspectData189 X Q x → p ≠ 2 → p ≠ 3 → 1 ≤ f →
      Nonempty (↥X ≃* projSL 2 (GaloisField p f)) → InspectGen189 X Q x

@[expose] def Inspect189L3Odd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X Q : Subgroup Y) (x : Y) (p f : ℕ) [Fact p.Prime],
    InspectData189 X Q x → p ≠ 2 → 1 ≤ f → p ^ f % 3 = 2 →
      Nonempty (↥X ≃* projSL 3 (GaloisField p f)) → InspectGen189 X Q x

@[expose] def Inspect189U3Odd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X Q : Subgroup Y) (x : Y) (p f : ℕ) [Fact p.Prime],
    InspectData189 X Q x → p ≠ 2 → 1 ≤ f → p ^ f % 3 = 1 →
      Nonempty (↥X ≃* projSU 3 p f) → InspectGen189 X Q x

@[expose] def Inspect189J1 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X Q : Subgroup Y) (x : Y),
    InspectData189 X Q x → Nonempty (↥X ≃* CFSG.Blueprint.NativeSporadic.J1) →
      InspectGen189 X Q x

end CFSG.RankThree.PartTwo.Sec18
