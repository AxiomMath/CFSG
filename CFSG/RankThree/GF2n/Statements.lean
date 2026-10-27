module

public import CFSG.Open.GLADefs
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.Foundations.Catalog

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def GF2TypeList (G : Type) [Group G] : Prop :=
  (∃ n : ℕ, 3 ≤ n ∧ LieModel G .PSL n 2 1) ∨
  (∃ n : ℕ, 4 ≤ n ∧ LieModel G .PSU n 2 1) ∨
  (∃ (s : StatedLieTag) (n : ℕ), s ∈ ({.POmegaPlus, .POmegaMinus} : Set StatedLieTag) ∧
    4 ≤ n ∧ LieModel G s n 2 1) ∨
  (∃ s : StatedLieTag, s ∈ ({.trialityD4, .E6, .twistedE6, .E7, .E8} : Set StatedLieTag) ∧
    LieModel G s 0 2 1) ∨
  (∃ p f m : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 3 ≤ m ∧ (p ^ f = 2 ^ m - 1 ∨ p ^ f = 2 ^ m + 1) ∧
    LieModel G .PSL 2 p f) ∨
  (∃ (s : StatedLieTag) (n : ℕ), (s, n) ∈ ({(.PSL, 3), (.PSU, 3), (.PSL, 4), (.PSU, 4), (.G2, 0),
    (.POmegaPlus, 4)} : Set (StatedLieTag × ℕ)) ∧ LieModel G s n 3 1) ∨
  (∃ k : ℕ, k ∈ ({6, 8, 9} : Set ℕ) ∧ Nonempty (G ≃* alternatingGroup (Fin k))) ∨
  (∃ s : TauCeti.SporadicName, s ∈ ({.M11, .M12, .M24, .J2, .J3, .J4, .Co2, .Co1, .HS, .Suz, .He,
    .Fi24Prime, .HN, .Th, .B, .M} : Set TauCeti.SporadicName) ∧ NativeSporadic.IsSporadic G s)

@[expose] def GF2TypeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ t : G, orderOf t = 2 →
      CFSG.Open.GLASymplecticType
        (inSubgroup generalizedFitting (Subgroup.centralizer ({t} : Set G))) →
      GF2TypeList G

@[expose] def Tim81UnitaryStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharacteristicPType G 2 →
    ∀ M : Subgroup G, IsMaximalTwoLocal M →
    ∀ B : Subgroup G, Maximal (fun W : Subgroup G => W ≤ M ∧
      M ≤ Subgroup.normalizer (W : Set G) ∧ Assembly.IsElemAbelian 2 W) B →
    IsTI B → 4 ≤ Nat.card B →
    WeaklyClosedIn B (inSubgroup (pCore 2) M) → ¬ WeaklyClosedIn B M →
    ∃ f : ℕ, Nat.card B = 2 ^ f ∧ 2 ≤ f ∧ ∃ m : ℕ, 4 ≤ m ∧ StatedClassicalModel G .PSU m 2 f

@[expose] def IsSpecialWithCentre {G : Type*} [Group G] (Q B : Subgroup G) : Prop :=
  ⁅Q, Q⁆ = B ∧ (frattini Q).map Q.subtype = B ∧ (Subgroup.center Q).map Q.subtype = B

@[expose] def StrothSmithList (G : Type) [Group G] (f : ℕ) : Prop :=
  LieModel G .PSU 4 2 f ∨
  (∃ (s : StatedLieTag) (m : ℕ), s ∈ ({.POmegaPlus, .POmegaMinus} : Set StatedLieTag) ∧
    4 ≤ m ∧ LieModel G s m 2 f) ∨
  (∃ s : StatedLieTag, s ∈ ({.G2, .trialityD4, .twistedE6, .E6, .E7, .E8} : Set StatedLieTag) ∧
    LieModel G s 0 2 f)

@[expose] def StrothSmithStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G →
    ∀ M : Subgroup G, IsMaximalTwoLocal M → generalizedFitting M = pCore 2 M →
    ∀ B : Subgroup G, Maximal (fun W : Subgroup G => W ≤ M ∧
      M ≤ Subgroup.normalizer (W : Set G) ∧ Assembly.IsElemAbelian 2 W) B →
    IsTI B → 4 ≤ Nat.card B →
    inSubgroup (pCore 2) M =
      ⨆ (g : G) (_ : conjSubgroup g B ≤ inSubgroup (pCore 2) M), conjSubgroup g B →
    IsSpecialWithCentre (inSubgroup (pCore 2) M) B →
    ∃ f : ℕ, Nat.card B = 2 ^ f ∧ 2 ≤ f ∧ StrothSmithList G f

@[expose] def Tim78TrichotomyStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharacteristicPType G 2 →
    ∀ M : Subgroup G, IsMaximalTwoLocal M →
    ∀ B : Subgroup G, Maximal (fun W : Subgroup G => W ≤ M ∧
      M ≤ Subgroup.normalizer (W : Set G) ∧ Assembly.IsElemAbelian 2 W) B →
    IsTI B → 4 ≤ Nat.card B →
    WeaklyClosedIn B (inSubgroup (pCore 2) M) ∨
      (inSubgroup (pCore 2) M =
          ⨆ (g : G) (_ : conjSubgroup g B ≤ inSubgroup (pCore 2) M), conjSubgroup g B ∧
        IsSpecialWithCentre (inSubgroup (pCore 2) M) B)

@[expose] def GF2nTypeConclusion {G : Type} [Group G] (M B : Subgroup G) : Prop :=
  (Nat.card B = 2 ∧ CFSG.Open.GLASymplecticType (inSubgroup (pCore 2) M) ∧ GF2TypeList G) ∨
  (4 ≤ Nat.card B ∧ WeaklyClosedIn B (inSubgroup (pCore 2) M) ∧
    ((¬ WeaklyClosedIn B M ∧
        ∃ f m : ℕ, Nat.card B = 2 ^ f ∧ 4 ≤ m ∧ StatedClassicalModel G .PSU m 2 f) ∨
      (WeaklyClosedIn B M ∧ ListGroup G))) ∨
  (4 ≤ Nat.card B ∧
    inSubgroup (pCore 2) M =
      ⨆ (g : G) (_ : conjSubgroup g B ≤ inSubgroup (pCore 2) M), conjSubgroup g B ∧
    IsSpecialWithCentre (inSubgroup (pCore 2) M) B ∧
    ∃ f : ℕ, Nat.card B = 2 ^ f ∧ StrothSmithList G f)

@[expose] def GF2nTypeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharacteristicPType G 2 →
    ∀ M : Subgroup G, IsMaximalTwoLocal M →
    ∀ B : Subgroup G, Maximal (fun W : Subgroup G => W ≤ M ∧
      M ≤ Subgroup.normalizer (W : Set G) ∧ Assembly.IsElemAbelian 2 W) B →
    IsTI B →
    GF2nTypeConclusion M B ∧ Blueprint.Catalog G

end CFSG.RankThree.GF2n
