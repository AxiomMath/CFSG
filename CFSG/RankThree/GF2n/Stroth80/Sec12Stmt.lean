module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Conc78 (hc : Ctx M Q Z B) (n : ℕ) (t : G) (m : ℕ) : Prop :=
  (m = 3 ∧ n = 10 ∧ Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 9) ∨
  (m = 4 ∧ n = 16 ∧ Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 17) ∨
  (m = 4 ∧ OmegaPlusNat hc t 4 ∧ n = 12 ∧
    Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 9) ∨
  (m = 5 ∧ OmegaPlusNat hc t 5 ∧ n = 18 ∧
    Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 17) ∨
  (m = 6 ∧ OmegaPlusNat hc t 6 ∧ n = 28 ∧ Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 33)

@[expose] def Stroth78Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN t) → ¬ OmegaPlusNat hc t 2 →
    ∀ m : ℕ, 2 ≤ m → (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) → Conc78 hc n t m

@[expose] def Conc79 (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop :=
  (∃ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q ∧
    IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0) ∨
  OmegaPlusNat hc t 3 ∨ (OmegaPlusNat hc t 4 ∧ n = 16)

@[expose] def Stroth79Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN t) → ¬ OmegaPlusNat hc t 2 →
    (∃ m : ℕ, 2 ≤ m ∧ (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m)) → Conc79 hc n t

@[expose] def Stroth717Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN t) → OmegaPlusNat hc t 3 →
    SubConfig M Q Z (hc.CN t) ∨ FStarL6 M Q Z

@[expose] def Conc83 (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop :=
  (n = 11 ∧ SpMNat hc t 3 ∧ Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 9) ∨
  (n = 17 ∧ SpMNat hc t 4 ∧ Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 17)

@[expose] def Stroth83Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → (∃ m : ℕ, 2 ≤ m ∧ SpMNat hc t m) → Conc83 hc n t

@[expose] def Stroth86Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → (∃ m : ℕ, 2 ≤ m ∧ SpMNat hc t m) → SubConfig M Q Z (hc.CN t)

@[expose] def Stroth98Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    (∀ τ ∈ LB M Q B, τ ∉ Q → Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN τ)) →
    ∀ t ∈ LB M Q B, t ∉ Q → OmegaPlusNat hc t 2 → False

@[expose] def Stroth108Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    (∀ t ∈ LB M Q B, t ∉ Q → Rt M (LB M Q B) t = LB M Q B ∨ SLlike hc t) →
    (∃ t ∈ LB M Q B, t ∉ Q ∧ SLlike hc t) → False

@[expose] def Stroth1111Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → (∃ a ∈ LB M Q B, IsA2 Q Z a) →
    CaseVI M Q Z (Lgen M (LB M Q B))

@[expose] def Stroth123Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B → Width Q Z 2 →
    QuotSat (Lgen M (LB M Q B)) Q (IsSLModel 2 (Nat.card Z))

@[expose] def OmegaExcluded (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop :=
  ((OmegaMinusNat hc t 4 ∨ OmegaPlusNat hc t 5) ∧
    Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 17) ∨
  (OmegaPlusNat hc t 4 ∧ n = 12 ∧ Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 9)

@[expose] def StrothGenByBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B → ∀ n : ℕ,
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B

@[expose] def StrothNtStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ t ∈ LB M Q B, t ∉ Q → Nt M (LB M Q B) t = hc.CN t

@[expose] def Stroth6NbarGeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ t ∈ LB M Q B, t ∉ Q → Nat.card Q * Nat.card Z ≤ Nat.card ↥(hc.CN t)

@[expose] def Stroth1111NotTIStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → (∃ a ∈ LB M Q B, IsA2 Q Z a) →
    ¬ IsTIMod M Q (LB M Q B)

end CFSG.RankThree.GF2n.Stroth80
