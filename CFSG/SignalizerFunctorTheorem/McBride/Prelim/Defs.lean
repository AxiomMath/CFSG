module

public import CFSG.SignalizerFunctorTheorem.McBride.Defs
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.ASimple

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

@[expose] def orbitClosure (X A : Subgroup G) : Subgroup G :=
  ⨆ a ∈ A, X.map (MulAut.conj a).toMonoidHom

@[expose] def smear (X A : Subgroup G) : Subgroup G :=
  orbitClosure X A ⊓ Subgroup.centralizer (A : Set G)

@[expose] def lcalOf (H : Type*) [Group H] : Set (Subgroup H) :=
  {J | J.IsSubnormal ∧ IsSimpleGroup J ∧ ¬ IsMulCommutative J}

@[expose] def lcal (X : Subgroup G) : Set (Subgroup G) :=
  {J | J ≤ X ∧ J.subgroupOf X ∈ lcalOf ↥X}

@[expose] def mcal (X : Subgroup G) : Set (Subgroup G) :=
  {M | M ≤ X ∧ sol X ≤ M ∧
    (M.subgroupOf X).map (QuotientGroup.mk' (CFSG.solvableRadical ↥X)) ∈
      lcalOf (↥X ⧸ CFSG.solvableRadical ↥X)}

@[expose] def ltilde (X : Subgroup G) : Set (Subgroup G) :=
  {M | (Group.IsSolvable X ∧ M = X) ∨ (¬ Group.IsSolvable X ∧ M ∈ mcal X)}

@[expose] def khat (X : Subgroup G) : Subgroup G :=
  X ⊓ ⨅ M ∈ ltilde X, Subgroup.normalizer (M : Set G)

@[expose] def lcalA (X A : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ lcal X ∧ ¬ Group.IsSolvable (smear J A)}

@[expose] def mcalA (X A : Subgroup G) : Set (Subgroup G) :=
  {M | M ∈ mcal X ∧ ¬ Group.IsSolvable (smear M A)}

@[expose] def kUp (X A : Subgroup G) : Subgroup G :=
  ⨆ M ∈ mcalA X A, M

@[expose] def kDown (X A : Subgroup G) : Subgroup G :=
  (Subgroup.comap (QuotientGroup.mk' (CFSG.solvableRadical ↥X))
    (Subgroup.centralizer ((((kUp X A).subgroupOf X).map
      (QuotientGroup.mk' (CFSG.solvableRadical ↥X)) :
        Subgroup (↥X ⧸ CFSG.solvableRadical ↥X)) :
          Set (↥X ⧸ CFSG.solvableRadical ↥X)))).map X.subtype

structure IsDirectProduct (S : Set (Subgroup G)) (K : Subgroup G) : Prop where
  commute : ∀ J ∈ S, ∀ L ∈ S, J ≠ L → ∀ x ∈ J, ∀ y ∈ L, Commute x y
  indep : sSupIndep S
  sSup_eq : sSup S = K

@[expose] def proj (J L X : Subgroup G) : Subgroup G :=
  Subgroup.closure {j | j ∈ J ∧ ∃ l ∈ L, j * l ∈ X}

@[expose] def projIn (S : Set (Subgroup G)) (J X : Subgroup G) : Subgroup G :=
  proj J (sSup (S \ {J})) X

@[expose] def IsDiagonal (S : Set (Subgroup G)) (X : Subgroup G) : Prop :=
  X ≤ sSup S ∧ ∀ J ∈ S, X ⊓ sSup (S \ {J}) = ⊥ ∧ projIn S J X = J

structure IsWreath (W H A N C : Subgroup G) : Prop where
  isMulCommutative : IsMulCommutative A
  A_le : A ≤ W
  H_le : H ≤ W
  sup_eq : H ⊔ A = W
  isDirectProduct : IsDirectProduct {K | ∃ g ∈ W, K = H.map (MulAut.conj g).toMonoidHom}
    (⨆ g ∈ W, H.map (MulAut.conj g).toMonoidHom)
  N_eq : N = A ⊓ Subgroup.normalizer (H : Set G)
  C_eq : C = A ⊓ Subgroup.centralizer (H : Set G)

structure IsDirectPair (K L W : Subgroup G) : Prop where
  commute : ∀ x ∈ K, ∀ y ∈ L, Commute x y
  inf_eq_bot : K ⊓ L = ⊥
  sup_eq : K ⊔ L = W

@[expose] def IsDirectFactor (K W : Subgroup G) : Prop :=
  ∃ L, IsDirectPair K L W

@[expose] def IsIndecomposable (W : Subgroup G) : Prop :=
  ∀ K, IsDirectFactor K W → K = ⊥ ∨ K = W

@[expose] def Ind (W : Subgroup G) : Set (Subgroup G) :=
  {K | K ≠ ⊥ ∧ IsDirectFactor K W ∧ IsIndecomposable K}

@[expose] def IsSemisimple (K : Subgroup G) : Prop :=
  IsDirectProduct (CFSG.SignalizerFunctorTheorem.Nonsolvable.simpleComponents K) K

@[expose] def IsKSubgroup (X : Subgroup G) : Prop :=
  IsSemisimple (⊤ : Subgroup (↥X ⧸ CFSG.solvableRadical ↥X))

@[expose] def sectionCentralizer (X Y : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (X : Set G) ∧ g ∈ Subgroup.normalizer (Y : Set G) ∧
    ∀ y ∈ Y, ⁅g, y⁆ ∈ X}
  one_mem' := ⟨one_mem _, one_mem _, fun y _ => by simp [commutatorElement_def]⟩
  mul_mem' := by
    rintro a b ⟨haX, haY, ha⟩ ⟨hbX, hbY, hb⟩
    refine ⟨mul_mem haX hbX, mul_mem haY hbY, fun y hy => ?_⟩
    have h := mul_mem ((Subgroup.mem_normalizer_iff.mp haX _).mp (hb y hy)) (ha y hy)
    convert h using 1
    simp only [commutatorElement_def]
    group
  inv_mem' := by
    rintro a ⟨haX, haY, ha⟩
    refine ⟨inv_mem haX, inv_mem haY, fun y hy => ?_⟩
    have hy' : a⁻¹ * y * a ∈ Y := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem haY) y).mp hy
    have h := inv_mem (ha (a⁻¹ * y * a) hy')
    convert h using 1
    simp only [commutatorElement_def]
    group

@[expose] def pResidual (p : ℕ) (H : Type*) [Group H] : Subgroup H :=
  Subgroup.normalClosure {h : H | ¬ p ∣ orderOf h}

end CFSG.SignalizerFunctorTheorem.McBride
