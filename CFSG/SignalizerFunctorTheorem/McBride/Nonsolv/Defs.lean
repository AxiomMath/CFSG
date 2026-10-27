module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.SrSubgroup

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G] [Finite G]

abbrev Msig (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) : Set (Subgroup G) :=
  signalizers p A θ (signalizerMcBrideHypothesisB p)

@[expose] def NearASolvableII (p : ℕ) (A X : Subgroup G) : Prop :=
  IsElemAbelian p A ∧ signalizerMcBrideHypothesisB p X ∧
    Group.IsSolvable (X ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)

@[expose] def nsSet (p : ℕ) (A X : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ≤ X ∧ X ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Y : Set G) ∧
    A ≤ Subgroup.normalizer (Y : Set G) ∧ NearASolvableII p A Y}

@[expose] def nsOf (p : ℕ) (A X : Subgroup G) : Subgroup G :=
  ⨆ Y ∈ nsSet p A X, Y

@[expose] def thetaNs (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) : G → Subgroup G :=
  fun a => nsOf p A (θ a)

@[expose] def jTilde (H J : Subgroup G) : Subgroup G :=
  H ⊓ Subgroup.centralizer ((kOf H ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) : Set G)

@[expose] def zOf (X : Subgroup G) : Subgroup G :=
  (Subgroup.center ↥X).map X.subtype

@[expose] def bC (A : Subgroup G) (θ : G → Subgroup G) (B : Subgroup G) : Subgroup G :=
  A ⊓ Subgroup.centralizer (kOf (thetaOf θ B) : Set G)

@[expose] def bN (A : Subgroup G) (θ : G → Subgroup G) (B : Subgroup G) : Subgroup G :=
  A ⊓ khat (thetaOf θ B ⊔ A)

@[expose] def sSet (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (i : ℕ) : Set (Subgroup G) :=
  {F | F ∈ signalizerFunctorEk p 1 A ∧ Nat.card (lcal (thetaOf θ F)) = p ^ i}

structure TypeA (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) : Prop where
  simple_D : IsSimpleGroup (thetaOf θ A) ∧ ¬ IsMulCommutative (thetaOf θ A)
  wreath : ∀ F ∈ signalizerFunctorEk p 1 A, ∃ K : Subgroup G,
    IsWreath (thetaOf θ F ⊔ A) K A F F ∧ Nonempty (↥K ≃* ↥(thetaOf θ A))
  maximal : ∀ a ∈ A, a ≠ 1 → Maximal (· ∈ Msig p A θ) (thetaOf θ (Subgroup.zpowers a))
  kOf_eq : ∀ a ∈ A, a ≠ 1 → kOf (thetaOf θ (Subgroup.zpowers a)) = thetaOf θ (Subgroup.zpowers a)
  bN_eq : ∀ F ∈ signalizerFunctorEk p 1 A, bN A θ F = F

structure TypeBCore (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (E K : Subgroup G) : Prop where
  mem : E ∈ signalizerFunctorEk p 1 A
  simple_K : IsSimpleGroup K ∧ ¬ IsMulCommutative K
  simple_fitting_D : IsSimpleGroup (CFSG.inSubgroup CFSG.generalizedFitting (thetaOf θ A)) ∧
    ¬ IsMulCommutative (CFSG.inSubgroup CFSG.generalizedFitting (thetaOf θ A))
  wreath_E : ∃ L : Subgroup G, IsWreath (thetaOf θ E ⊔ A) L A E E ∧
    Nonempty (↥L ≃* ↥(thetaOf θ A))
  wreath_F : ∀ F ∈ signalizerFunctorEk p 1 A, F ≠ E → ∃ L C : Subgroup G,
    IsWreath (thetaOf θ F ⊔ A) L A (E ⊔ F) C ∧ Nonempty (↥L ≃* ↥K)
  kOf_eq : ∀ a ∈ A, a ∉ E → kOf (thetaOf θ (Subgroup.zpowers a)) = thetaOf θ (Subgroup.zpowers a)
  bN_eq : ∀ F ∈ signalizerFunctorEk p 1 A, bN A θ F = F ⊔ E

structure TypeB (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (E K : Subgroup G) : Prop
    extends TypeBCore p A θ E K where
  maximal : ∀ a ∈ A, a ∉ E → Maximal (· ∈ Msig p A θ) (thetaOf θ (Subgroup.zpowers a))
  wreath_F' : ∀ F ∈ signalizerFunctorEk p 1 A, F ≠ E → ∃ L : Subgroup G,
    IsWreath (thetaOf θ F ⊔ A) L A (E ⊔ F) F ∧ Nonempty (↥L ≃* ↥K)

@[expose] def InPiTheta (A : Subgroup G) (θ : G → Subgroup G) (r : ℕ) : Prop :=
  r.Prime ∧ ∃ a ∈ A, a ≠ 1 ∧ r ∣ Nat.card (θ a)

abbrev MsigR (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (r : ℕ) : Set (Subgroup G) :=
  signalizersOfPrime p A θ (signalizerMcBrideHypothesisB p) r

abbrev IsSr (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (r : ℕ) (S : Subgroup G) : Prop :=
  IsSrSubgroup p A θ (signalizerMcBrideHypothesisB p) r S

@[expose] def indSB (θ : G → Subgroup G) (S B : Subgroup G) : Set (Subgroup G) :=
  {Y | ∃ L ∈ Ind (thetaOf θ B), Y = S ⊓ L}

@[expose] def lHat (H L : Subgroup G) : Subgroup G :=
  sSup {R | R ∈ lcal H ∧ ¬ L ≤ Subgroup.centralizer (R : Set G)}

@[expose] def wK (θ : G → Subgroup G) (E K : Subgroup G) : Subgroup G :=
  K ⊔ lHat (thetaOf θ E) (K ⊓ Subgroup.centralizer (E : Set G))

structure KSetting (p : ℕ) (A H : Subgroup G) : Prop where
  prime : p.Prime
  elemAbelian : IsElemAbelian p A
  normalizes : A ≤ Subgroup.normalizer (H : Set G)
  hypB : signalizerMcBrideHypothesisB p H

@[expose] def IsDAInvariant (A H X : Subgroup G) : Prop :=
  X ≤ H ∧ H ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (X : Set G) ∧
    A ≤ Subgroup.normalizer (X : Set G)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
