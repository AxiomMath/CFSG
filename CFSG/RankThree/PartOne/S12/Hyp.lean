module

public import CFSG.RankThree.GroupTheory.SteinbergBMSectionTenSetup
public import CFSG.RankThree.GroupTheory.SteinbergCESectionTenStrata

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement Pointwise

structure Sec12Hyp (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G)
    (L E : Subgroup G) : Prop where
  setup : SteinbergBM.SectionTenSetup G p A
  c_mem : c ∈ A
  c_ne_one : c ≠ 1
  L_mem : L ∈ sectionTenAt p (sectionTenZeroStar p A ∩ sectionTenOne p A) c
  E_elem : IsElementaryAbelian p E
  E_le : E ≤ Subgroup.centralizer (A : Set G)
  E_max : ∀ F : Subgroup G, IsElementaryAbelian p F → F ≤ Subgroup.centralizer (A : Set G) →
    E ≤ F → F = E

variable {G : Type} [Group G]

@[expose] def torusNormalizer (E : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (E : Set G)

@[expose] noncomputable def torusWeyl (E : Subgroup G) : Subgroup (MulAut E) :=
  E.normalizerMonoidHom.range

@[expose] noncomputable def torusImage (E Y : Subgroup G) : Subgroup (MulAut E) :=
  (Y.subgroupOf (Subgroup.normalizer (E : Set G))).map E.normalizerMonoidHom

@[expose] def autFixed (E : Subgroup G) (φ : MulAut E) : Subgroup E :=
  MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id E)

@[expose] def autMoved (E : Subgroup G) (φ : MulAut E) : Subgroup E :=
  Subgroup.closure (Set.range fun e : E => φ e * e⁻¹)

@[expose] def IsAutReflection (p : ℕ) (E : Subgroup G) (φ : MulAut E) : Prop :=
  orderOf φ = 2 ∧ Nat.card (autMoved E φ) = p

@[expose] def IsAutTransvection (p : ℕ) (E : Subgroup G) (φ : MulAut E) : Prop :=
  φ ≠ 1 ∧ Nat.card (autMoved E φ) = p ∧ autMoved E φ ≤ autFixed E φ

@[expose] def admissibleTriples (p : ℕ) (E : Subgroup G) : Set (Subgroup G) :=
  {B | B ≤ E ∧ IsElementaryAbelian p B ∧ Nat.card B = p ^ 3 ∧
    ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set G)}

@[expose] def thetaCompE (p : ℕ) (E : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ B ∈ admissibleTriples p E, X ∈ thetaComponentFamily p B}

@[expose] def thetaCompStarE (p : ℕ) (E : Subgroup G) : Set (Subgroup G) :=
  {I | I ∈ thetaCompE p E ∧ ∀ J ∈ thetaCompE p E, sectionTenRel p I J → sectionTenRel p J I}

@[expose] def thetaCompZeroE (p : ℕ) (E : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ B ∈ admissibleTriples p E, X ∈ sectionTenZero p B}

@[expose] def thetaCompZeroStarE (p : ℕ) (E : Subgroup G) : Set (Subgroup G) :=
  thetaCompZeroE p E ∩ thetaCompStarE p E

@[expose] def reflectionSet (p : ℕ) (E : Subgroup G) : Set (MulAut E) :=
  {t | IsAutReflection p E t ∧ ∃ X ∈ thetaCompZeroStarE p E, t ∈ torusImage E X}

@[expose] def autFixedInG (E : Subgroup G) (t : MulAut E) : Subgroup G :=
  (autFixed E t).map E.subtype

@[expose] def autMovedInG (E : Subgroup G) (t : MulAut E) : Subgroup G :=
  (autMoved E t).map E.subtype

@[expose] def pElementSubgroup (p : ℕ) (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, orderOf x = p ^ k}

@[expose] noncomputable def kZero (p : ℕ) (E : Subgroup G) (t : MulAut E) : Subgroup G :=
  pElementSubgroup p (inSubgroup (fun K _ => layer K)
    (Subgroup.centralizer (autFixedInG E t : Set G)))

@[expose] def kExceptional (p : ℕ) (K0 : Subgroup G) (f : ℕ) : Prop :=
  1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ StatedClassicalModel (K0 ⧸ Subgroup.center K0) .PSU 3 2 f

@[expose] def IsKt (p : ℕ) (E : Subgroup G) (t : MulAut E) (K : Subgroup G) : Prop :=
  (∀ f, kExceptional p (kZero p E t) f →
    K ≤ kZero p E t ∧ StatedClassicalModel K .PSL 2 2 f ∧ autMovedInG E t ≤ K) ∧
  ((¬ ∃ f, kExceptional p (kZero p E t) f) → K = kZero p E t)

@[expose] def lieGenerated (p : ℕ) (E : Subgroup G) : Subgroup G :=
  sSup {K | ∃ t ∈ reflectionSet p E, IsKt p E t K}

@[expose] def lieNormalizer (p : ℕ) (E : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (lieGenerated p E : Set G)

@[expose] def reflectionGroup (p : ℕ) (E : Subgroup G) : Subgroup (MulAut E) :=
  Subgroup.closure (reflectionSet p E)

@[expose] def cNormalizer (c : G) : Subgroup G :=
  Subgroup.normalizer (Subgroup.zpowers c : Set G)

@[expose] def torusInvariant (E Γ B : Subgroup G) : Prop :=
  ∀ w ∈ Γ ⊓ torusNormalizer E, ∀ b ∈ B, w * b * w⁻¹ ∈ B

@[expose] def torusIrreducible (E : Subgroup G) : Prop :=
  ∀ B : Subgroup G, B ≤ E → torusInvariant E ⊤ B → B = ⊥ ∨ B = E

@[expose] def torusHasTransvection (p : ℕ) (E : Subgroup G) : Prop :=
  ∃ φ ∈ torusWeyl E, IsAutTransvection p E φ

structure Sec15Hyp (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G)
    (L E : Subgroup G) : Prop where
  h12 : Sec12Hyp G p A c L E
  I_ne_top : lieGenerated p E ≠ ⊤

@[expose] def Outcome152One (p : ℕ) (E A I : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ Nonempty (I ≃* projSL 4 (GaloisField 2 f)) ∧
    Nonempty (reflectionGroup p E ≃* Equiv.Perm (Fin 4)) ∧ E = A ∧ Even (Nat.card I)

@[expose] def Outcome152Two (p : ℕ) (E A I : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ Nonempty (I ≃* projSp 3 (GaloisField 2 f)) ∧
    Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧ E = A ∧
    Even (Nat.card I)

@[expose] def Outcome152Three (p : ℕ) (E A I : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
    (∃ b c : GaloisField 2 f, (∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (I ≃* projOmegaMinus 3 (GaloisField 2 f) b c)) ∧
    Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧ E = A ∧
    Even (Nat.card I)

@[expose] def Outcome152Four (p : ℕ) (E A I : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
    (∃ b c : GaloisField 2 f, (∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (I ≃* projOmegaMinus 3 (GaloisField 2 f) b c)) ∧
    Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧ E = A ∧
    Even (Nat.card I)

@[expose] def Outcome152Five (p : ℕ) (E A I : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ Nonempty ((I ⧸ Subgroup.center I) ≃* projSU 5 2 f) ∧
    Nonempty (reflectionGroup p E ≃* Equiv.Perm (Fin 5)) ∧ Nat.card E = p ^ 4 ∧ E ≠ A ∧
    Even (Nat.card I)

@[expose] def Outcome152 (p : ℕ) (E A I : Subgroup G) : Prop :=
  Outcome152One p E A I ∨ Outcome152Two p E A I ∨ Outcome152Three p E A I ∨
    Outcome152Four p E A I ∨ Outcome152Five p E A I

end CFSG.RankThree.PartOne
