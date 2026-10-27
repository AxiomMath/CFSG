module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Counterexample
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Defs

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G]

@[expose] def IsNormalIn (N H : Subgroup G) : Prop :=
  N ≤ H ∧ H ≤ Subgroup.normalizer (N : Set G)

@[expose] def IsChiefFactorOf (H L N : Subgroup G) : Prop :=
  IsNormalIn N H ∧ IsNormalIn L H ∧ N < L ∧
    ∀ K : Subgroup G, IsNormalIn K H → N ≤ K → K ≤ L → K = N ∨ K = L

@[expose] def secCenIn (H L N : Subgroup G) : Subgroup G :=
  H ⊓ sectionCentralizer N L

@[expose] def cenIn (X : Subgroup G) (S : Set G) : Subgroup G :=
  X ⊓ Subgroup.centralizer S

@[expose] def norIn (X : Subgroup G) (S : Set G) : Subgroup G :=
  X ⊓ Subgroup.normalizer S

@[expose] def Admits (Q X : Subgroup G) : Prop :=
  Q ≤ Subgroup.normalizer (X : Set G)

@[expose] def IsSolvableSection (X₁ X₂ : Subgroup G) : Prop :=
  ∃ n : ℕ, derivedSeries X₁ n ≤ X₂.subgroupOf X₁

@[expose] def IsDirectProductMod (N T P Q : Subgroup G) : Prop :=
  N ≤ P ∧ N ≤ Q ∧ P ⊔ Q = T ∧ P ⊓ Q = N ∧ ⁅P, Q⁆ ≤ N

@[expose] def perfRes (X : Subgroup G) : Subgroup G :=
  (CFSG.perfectResidual ↥X).map X.subtype

@[expose] def CyclicMod (A C : Subgroup G) : Prop :=
  ∃ a ∈ A, A ≤ C ⊔ Subgroup.zpowers a

@[expose] def fittingPre (D D₂ : Subgroup G) [(D₂.subgroupOf D).Normal] : Subgroup G :=
  ((CFSG.fittingSubgroup (↥D ⧸ D₂.subgroupOf D)).comap
    (QuotientGroup.mk' (D₂.subgroupOf D))).map D.subtype

structure NearFunctor (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  elemAbelian : IsElemAbelian p A
  ne_bot : A ≠ ⊥
  isFunctor : IsFunctor p A θ
  near : ∀ a ∈ A, a ≠ 1 → NearASolvable p A (θ a)

theorem NearHyp.nearFunctor {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}
    (h : NearHyp p A θ) : NearFunctor p A θ where
  prime := h.prime
  odd := h.odd
  elemAbelian := h.elemAbelian
  ne_bot := by
    rintro rfl
    have := h.card
    rw [Subgroup.card_bot] at this
    exact (Nat.one_lt_pow (by norm_num) h.prime.one_lt).ne this
  isFunctor := h.isFunctor
  near := h.near

section Vocabulary

variable (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G)

@[expose] def assoc : Set (Subgroup G) :=
  signalizers p A θ (NearASolvable p A)

@[expose] def wsub : Subgroup G :=
  sSup (assoc p A θ)

@[expose] def dsub : Subgroup G :=
  thetaOf θ A

@[expose] def mhat : Set (Subgroup G) :=
  {X | X ∈ assoc p A θ ∧ dsub A θ ≤ Subgroup.normalizer (X : Set G)}

@[expose] def mtil : Set (Subgroup G) :=
  {X | X ∈ assoc p A θ ∧ dsub A θ ≤ X}

@[expose] def pairsP : Set (Subgroup G × Subgroup G) :=
  {P | P.1 ∈ mhat p A θ ∧ P.2 ∈ mhat p A θ ∧
    IsChiefFactorOf (P.1 ⊔ dsub A θ ⊔ A) P.1 P.2 ∧
    secCenIn (P.1 ⊔ dsub A θ) P.1 P.2 = P.2}

@[expose] def dset : Set (Subgroup G) :=
  {Y | ∃ P ∈ pairsP p A θ, Y = dsub A θ ⊓ P.2}

variable (Y X : Subgroup G)

@[expose] def pairsY : Set (Subgroup G × Subgroup G) :=
  {P | P ∈ pairsP p A θ ∧ P.2 ⊓ dsub A θ = Y}

@[expose] def pairsYX : Set (Subgroup G × Subgroup G) :=
  {P | P ∈ pairsY p A θ Y ∧ P.1 ≤ X}

@[expose] def cset : Set (Subgroup G) :=
  {X | X ∈ mtil p A θ ∧ (pairsYX p A θ Y X).Nonempty}

@[expose] def uset : Set (Subgroup G) :=
  {Z | Z ∈ mtil p A θ ∧ orbitClosure Y Z ⊓ dsub A θ = Y}

@[expose] def usetX : Set (Subgroup G) :=
  {Z | Z ∈ uset p A θ Y ∧ Z ≤ X}

@[expose] def eset : Set (Subgroup G) :=
  {Z | Z ∈ mhat p A θ ∧ Z ⊓ dsub A θ = Y}

@[expose] def esetX : Set (Subgroup G) :=
  {Z | Z ∈ eset p A θ Y ∧ Z ≤ X}

@[expose] def thetaY : Subgroup G :=
  ⨆ Z ∈ esetX p A θ Y X, Z

@[expose] def thetaU : Subgroup G :=
  ⨆ Z ∈ usetX p A θ Y X, Z

@[expose] def thetaL : Subgroup G :=
  ⨆ P ∈ pairsYX p A θ Y X, P.2

@[expose] def thetaM : Subgroup G :=
  ⨆ P ∈ pairsYX p A θ Y X, P.1

@[expose] def thetaLG (Y : Subgroup G) : Subgroup G :=
  ⨆ X ∈ cset p A θ Y, thetaL p A θ Y X

@[expose] def thetaMG (Y : Subgroup G) : Subgroup G :=
  ⨆ X ∈ cset p A θ Y, thetaM p A θ Y X

@[expose] def thetaSol (X : Subgroup G) : Subgroup G :=
  ⨆ Z ∈ {Z | Z ∈ mhat p A θ ∧ Z ≤ X ∧ Group.IsSolvable Z}, Z

@[expose] def thetaYFun (Y : Subgroup G) : G → Subgroup G :=
  fun a => thetaY p A θ Y (θ a)

@[expose] def thetaSolFun : G → Subgroup G :=
  fun a => thetaSol p A θ (θ a)

end Vocabulary

end CFSG.SignalizerFunctorTheorem.McBride.Near
