module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G] (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G)

@[expose] def rSet : Set (Subgroup G) :=
  {B | B ≠ ⊥ ∧ B ≤ A ∧ thetaOf θ B ∈ cset p A θ ⊥}

@[expose] def rSetN (i : ℕ) : Set (Subgroup G) :=
  {B | B ∈ rSet p A θ ∧ Nat.card B = p ^ i}

@[expose] def ssol : Subgroup G :=
  ⨆ X ∈ signalizers p A (thetaSolFun p A θ) (NearASolvable p A), X

@[expose] def thetaN (X : Subgroup G) : Subgroup G :=
  ⨆ Y ∈ {Y : Subgroup G | Y ∈ assoc p A θ ∧ Y ≤ Subgroup.normalizer (X : Set G)}, Y

@[expose] def dZero : Subgroup G :=
  ⨆ B ∈ rSet p A θ, dsub A θ ⊓ kOf (thetaOf θ B)

@[expose] def dOne : Subgroup G :=
  CFSG.fittingSubgroupOf (dZero p A θ)

@[expose] def dTwo : Subgroup G :=
  dZero p A θ ⊓ sectionCentralizer (dOne p A θ) (dZero p A θ)

@[expose] def sOne : Subgroup G :=
  thetaN p A θ (dOne p A θ) ⊓ Subgroup.centralizer (dOne p A θ : Set G)

@[expose] def sTwo : Subgroup G :=
  thetaN p A θ (dTwo p A θ ⊔ sOne p A θ) ⊓
    sectionCentralizer (sOne p A θ) (dTwo p A θ ⊔ sOne p A θ)

@[expose] def sThree : Subgroup G :=
  thetaN p A θ (dZero p A θ ⊔ sOne p A θ) ⊓
    sectionCentralizer (sOne p A θ) (dZero p A θ ⊔ sOne p A θ)

@[expose] def thetaStarFun : G → Subgroup G :=
  fun a => perfRes (θ a) ⊔ (θ a ⊓ sTwo p A θ)

@[expose] def IsPSL3 (J : Subgroup G) : Prop :=
  Nonempty (↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))

end CFSG.SignalizerFunctorTheorem.McBride.Near
