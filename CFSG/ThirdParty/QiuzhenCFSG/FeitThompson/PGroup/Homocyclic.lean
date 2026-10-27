module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative

/-!
# Standard homocyclic coordinate covers

This file collects basic facts about the standard finite homocyclic group
`Multiplicative (κ → ZMod q)`.
-/

noncomputable section

universe u

/-- The standard free homocyclic `q`-torsion group on the finite index type `κ`. -/
public abbrev CFSG.StandardHomocyclicCover (κ : Type u) (q : ℕ) :=
  Multiplicative (κ → ZMod q)

/-- The tautological additive coordinate equivalence for the standard homocyclic cover. -/
public def CFSG.standardHomocyclicCoverCoordinateEquiv (κ : Type u) (q : ℕ) :
    (κ → ZMod q) ≃+ Additive (StandardHomocyclicCover κ q) :=
  (AddEquiv.toAdditive_toMultiplicative (G := κ → ZMod q)).symm


/-- The standard homocyclic cover is commutative. -/
public theorem CFSG.standardHomocyclicCover_commutative (κ : Type u) (q : ℕ) :
    IsMulCommutative (StandardHomocyclicCover κ q) := by
  exact ⟨⟨fun x y => by
    ext i
    exact add_comm (Multiplicative.toAdd x i) (Multiplicative.toAdd y i)⟩⟩

/-- The standard `ZMod (p ^ e)` coordinate cover is a `p`-group. -/
public theorem CFSG.standardHomocyclicCover_isPGroup
    (κ : Type u) [Fintype κ] (p e : ℕ) [Fact p.Prime] :
    IsPGroup p (StandardHomocyclicCover κ (p ^ e)) := by
  classical
  refine IsPGroup.of_card (p := p) (G := StandardHomocyclicCover κ (p ^ e))
    (n := e * Fintype.card κ) ?_
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (MulEquiv.funMultiplicative κ (ZMod (p ^ e))).toEquiv]
  simp [ZMod.card, pow_mul]

private theorem Finset.lcm_const_of_nonempty {ι : Type u} [Fintype ι] [Nonempty ι] (q : ℕ) :
    Finset.univ.lcm (fun _ : ι => q) = q := by
  classical
  refine dvd_antisymm ?_ ?_
  · apply Finset.lcm_dvd
    intro i _hi
    exact dvd_rfl
  · exact Finset.dvd_lcm (Finset.mem_univ (Classical.arbitrary ι))

/-- The standard homocyclic cover over a nonempty index type has exponent `q`. -/
public theorem CFSG.standardHomocyclicCover_exponent
    (κ : Type u) [Fintype κ] [Nonempty κ] (q : ℕ) :
    Monoid.exponent (StandardHomocyclicCover κ q) = q := by
  classical
  rw [show Monoid.exponent (StandardHomocyclicCover κ q) =
      AddMonoid.exponent (κ → ZMod q) from rfl]
  rw [AddMonoid.exponent_pi]
  simp [ZMod.exponent, Finset.lcm_const_of_nonempty]

/-- Coordinatewise reduction from `ZMod (p ^ e)` to `ZMod p`. -/
@[expose] public def CFSG.standardHomocyclicCoverAddReduction
    (κ : Type u) (p e : ℕ) (he : 1 ≤ e) :
    (κ → ZMod (p ^ e)) →+ (κ → ZMod p) :=
  let hpdiv : p ∣ p ^ e := dvd_pow_self p (Nat.ne_of_gt he)
  { toFun := fun x i => ZMod.castHom hpdiv (ZMod p) (x i)
    map_zero' := by
      ext i
      exact map_zero (ZMod.castHom hpdiv (ZMod p))
    map_add' := by
      intro x y
      ext i
      exact map_add (ZMod.castHom hpdiv (ZMod p)) (x i) (y i) }

/-- Coordinatewise reduction from `ZMod (p ^ e)` to `ZMod p` is onto. -/
public theorem CFSG.standardHomocyclicCoverAddReduction_surjective
    (κ : Type u) (p e : ℕ) (he : 1 ≤ e) :
    Function.Surjective (standardHomocyclicCoverAddReduction κ p e he) := by
  intro y
  let hpdiv : p ∣ p ^ e := dvd_pow_self p (Nat.ne_of_gt he)
  choose x hx using fun i => ZMod.castHom_surjective hpdiv (y i)
  refine ⟨x, ?_⟩
  ext i
  exact hx i

/-- Multiplicative form of coordinatewise reduction from `ZMod (p ^ e)` to `ZMod p`. -/
@[expose] public def CFSG.standardHomocyclicCoverReduction
    (κ : Type u) (p e : ℕ) (he : 1 ≤ e) :
    StandardHomocyclicCover κ (p ^ e) →* StandardHomocyclicCover κ p :=
  AddMonoidHom.toMultiplicative (standardHomocyclicCoverAddReduction κ p e he)

/-- The multiplicative reduction is the additive coordinate reduction under type tags. -/
public theorem CFSG.standardHomocyclicCoverReduction_toAdd
    (κ : Type u) (p e : ℕ) (he : 1 ≤ e)
    (x : StandardHomocyclicCover κ (p ^ e)) :
    Multiplicative.toAdd (standardHomocyclicCoverReduction κ p e he x) =
      standardHomocyclicCoverAddReduction κ p e he (Multiplicative.toAdd x) :=
  rfl

/-- The kernel of multiplicative reduction is the additive reduction kernel under type tags. -/
public theorem CFSG.standardHomocyclicCoverReduction_ker
    (κ : Type u) (p e : ℕ) (he : 1 ≤ e) :
    (standardHomocyclicCoverReduction κ p e he).ker =
      AddSubgroup.toSubgroup (standardHomocyclicCoverAddReduction κ p e he).ker :=
  rfl

/-- The multiplicative coordinatewise reduction map is onto. -/
public theorem CFSG.standardHomocyclicCoverReduction_surjective
    (κ : Type u) (p e : ℕ) (he : 1 ≤ e) :
    Function.Surjective (standardHomocyclicCoverReduction κ p e he) := by
  intro y
  obtain ⟨x, hx⟩ :=
    standardHomocyclicCoverAddReduction_surjective κ p e he (Multiplicative.toAdd y)
  refine ⟨Multiplicative.ofAdd x, ?_⟩
  apply Multiplicative.toAdd.injective
  change standardHomocyclicCoverAddReduction κ p e he x = Multiplicative.toAdd y
  exact hx

/-- Transport a `G`-action across a chosen standard mod-`p` quotient
equivalence. -/
public noncomputable def CFSG.standardHomocyclicCoverModPActionOfEquiv
    {G V κ : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ}
    (quotientToV : StandardHomocyclicCover κ p ≃* V) :
    G →* MulAut (StandardHomocyclicCover κ p) := by
  classical
  exact {
    toFun := fun g => (quotientToV.trans (MulDistribMulAction.toMulAut G V g)).trans
      quotientToV.symm
    map_one' := by
      ext w
      simp
    map_mul' := by
      intro g h
      ext w
      simp [map_mul] }

/-- The transported mod-`p` action agrees with the original action after
applying the chosen quotient map. -/
public theorem CFSG.standardHomocyclicCoverModPActionOfEquiv_quotientToV
    {G V κ : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ}
    (quotientToV : StandardHomocyclicCover κ p ≃* V)
    (g : G) (w : StandardHomocyclicCover κ p) :
    quotientToV (standardHomocyclicCoverModPActionOfEquiv
        (G := G) (V := V) (p := p) quotientToV g w) =
      g • quotientToV w := by
  classical
  dsimp [standardHomocyclicCoverModPActionOfEquiv]
  simp

/-- The transported mod-`p` action, expressed linearly on additive
coordinates. -/
public noncomputable def CFSG.standardHomocyclicCoverModPLinearActionOfEquiv
    {G V κ : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ}
    (quotientToV : StandardHomocyclicCover κ p ≃* V) :
    G →* (Module.End (ZMod p) (κ → ZMod p))ˣ := by
  classical
  let eAdd : G → (κ → ZMod p) ≃+ (κ → ZMod p) := fun g =>
    (standardHomocyclicCoverCoordinateEquiv κ p).trans
      ((MulEquiv.toAdditive
        (standardHomocyclicCoverModPActionOfEquiv
          (G := G) (V := V) (p := p) quotientToV g)).trans
        (standardHomocyclicCoverCoordinateEquiv κ p).symm)
  let eLin : G → (κ → ZMod p) ≃ₗ[ZMod p] (κ → ZMod p) := fun g =>
    (eAdd g).toLinearEquiv (fun c x => by
      simpa using (ZMod.map_smul (eAdd g).toAddMonoidHom c x))
  let ψfun : G → LinearMap.GeneralLinearGroup (ZMod p) (κ → ZMod p) := fun g =>
    LinearMap.GeneralLinearGroup.ofLinearEquiv (eLin g)
  exact {
    toFun := ψfun
    map_one' := by
      ext x i
      change (eLin 1 x) i = x i
      dsimp [eLin, eAdd]
      simp [standardHomocyclicCoverModPActionOfEquiv]
    map_mul' := by
      intro g h
      ext x i
      change (eLin (g * h) x) i = (eLin g (eLin h x)) i
      dsimp [eLin, eAdd]
      simp [standardHomocyclicCoverModPActionOfEquiv, map_mul] }

/-- The transported mod-`p` linear action is the additive form of
`standardHomocyclicCoverModPActionOfEquiv`. -/
public theorem CFSG.standardHomocyclicCoverModPLinearActionOfEquiv_coordinate
    {G V κ : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ}
    (quotientToV : StandardHomocyclicCover κ p ≃* V)
    (g : G) (x : κ → ZMod p) :
    Multiplicative.ofAdd
        (((standardHomocyclicCoverModPLinearActionOfEquiv
            (G := G) (V := V) (p := p) quotientToV g :
            (Module.End (ZMod p) (κ → ZMod p))ˣ) :
          Module.End (ZMod p) (κ → ZMod p)) x) =
      standardHomocyclicCoverModPActionOfEquiv
        (G := G) (V := V) (p := p) quotientToV g (Multiplicative.ofAdd x) := by
  classical
  dsimp [standardHomocyclicCoverModPLinearActionOfEquiv]
  rfl


/-- A standard mod-`p` cover equivalent to a nontrivial group has at least one
coordinate. -/
public theorem CFSG.standardHomocyclicCoverQuotientEquiv_nonempty_index
    {V κ : Type u} {p : ℕ} [Group V] [Nontrivial V]
    (quotientToV : StandardHomocyclicCover κ p ≃* V) :
    Nonempty κ := by
  classical
  by_contra hκ
  have hE : IsEmpty κ := not_nonempty_iff.mp hκ
  have hcoverSubsingleton : Subsingleton (StandardHomocyclicCover κ p) := by
    constructor
    intro x y
    apply Multiplicative.toAdd.injective
    funext i
    exact @isEmptyElim κ hE (fun i => Multiplicative.toAdd x i = Multiplicative.toAdd y i) i
  have hVSubsingleton : Subsingleton V := ⟨fun v w => by
    rcases quotientToV.surjective v with ⟨v', rfl⟩
    rcases quotientToV.surjective w with ⟨w', rfl⟩
    congr
    exact Subsingleton.elim v' w'⟩
  exact not_subsingleton V hVSubsingleton


/-- A standard mod-`p` cover equivalent to a nontrivial group has at least one
coordinate. -/
public theorem CFSG.standardHomocyclicCoverQuotientEquiv_nonempty_matrixIndex
    {V κ : Type u} [Group V] [Nontrivial V]
    {p : ℕ} [Fact p.Prime]
    (quotientToV : StandardHomocyclicCover κ p ≃* V) :
    Nonempty κ := by
  exact standardHomocyclicCoverQuotientEquiv_nonempty_index
    (p := p) quotientToV

/-- Canonical equivalence from the standard mod-`p` coordinate cover on a
finite basis index to an elementary abelian group. -/
public noncomputable def CFSG.standardHomocyclicCoverToElementaryAbelianEquiv
    (V : Type u) [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V] :
    StandardHomocyclicCover (ULift (Fin (Module.finrank (ZMod p) (Additive V)))) p ≃* V := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let b : Module.Basis (Fin (Module.finrank (ZMod p) (Additive V))) (ZMod p) (Additive V) :=
    Module.finBasis (ZMod p) (Additive V)
  let reindexEquiv :
      (ULift (Fin (Module.finrank (ZMod p) (Additive V))) → ZMod p) ≃+
        (Fin (Module.finrank (ZMod p) (Additive V)) → ZMod p) := {
    toFun := fun f i => f (ULift.up i)
    invFun := fun f i => f i.down
    left_inv := by
      intro f
      ext i
      cases i
      rfl
    right_inv := by
      intro f
      ext i
      rfl
    map_add' := by
      intro f g
      ext i
      rfl }
  exact AddEquiv.toMultiplicativeLeft (reindexEquiv.trans b.equivFun.symm.toAddEquiv)

/-- Canonical basis index for the standard homocyclic cover attached to `V`. -/
public abbrev CFSG.StandardHomocyclicCanonicalIndex
    (V : Type u) [Group V] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V] :
    Type u :=
  ULift.{u} (Fin (Module.finrank (ZMod p) (Additive V)))

/-- The canonical standard-cover index has cardinality equal to the `ZMod p`
dimension of the attached elementary abelian group. -/
public theorem CFSG.standardHomocyclicCanonicalIndex_card
    (V : Type u) [Group V] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V] :
    Fintype.card (StandardHomocyclicCanonicalIndex (p := p) V) =
      Module.finrank (ZMod p) (Additive V) := by
  simp [StandardHomocyclicCanonicalIndex]

/-- The canonical standard-cover index is nonempty when the attached elementary
abelian group is nontrivial. -/
public theorem CFSG.standardHomocyclicCanonicalIndex_nonempty
    (V : Type u) [Group V] [Finite V] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V] :
    Nonempty (StandardHomocyclicCanonicalIndex (p := p) V) := by
  exact standardHomocyclicCoverQuotientEquiv_nonempty_matrixIndex
    (V := V) (p := p) (standardHomocyclicCoverToElementaryAbelianEquiv (p := p) V)

/-- The checked mod-`p` action on standard coordinates, transported from the
original action on `V` through the canonical coordinate equivalence. -/
@[expose] public noncomputable def CFSG.standardHomocyclicCoverModPAction
    (G V : Type u) [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V] :
    G →* MulAut (StandardHomocyclicCover (StandardHomocyclicCanonicalIndex (p := p) V) p) :=
  standardHomocyclicCoverModPActionOfEquiv
    (G := G) (V := V) (p := p)
    (standardHomocyclicCoverToElementaryAbelianEquiv (p := p) V)

/-- The transported standard mod-`p` action agrees with the original action on
`V` after applying the canonical coordinate equivalence. -/
public theorem CFSG.standardHomocyclicCoverModPAction_quotientToV
    {G V : Type u} [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (g : G) (w : StandardHomocyclicCover (StandardHomocyclicCanonicalIndex (p := p) V) p) :
    standardHomocyclicCoverToElementaryAbelianEquiv (p := p) V
        (standardHomocyclicCoverModPAction G V (p := p) g w) =
      g • standardHomocyclicCoverToElementaryAbelianEquiv (p := p) V w := by
  exact standardHomocyclicCoverModPActionOfEquiv_quotientToV
    (G := G) (V := V) (p := p)
    (standardHomocyclicCoverToElementaryAbelianEquiv (p := p) V) g w

/-- The checked mod-`p` action, expressed linearly on the canonical additive
coordinate module. -/
@[expose] public noncomputable def CFSG.standardHomocyclicCoverModPLinearAction
    (G V : Type u) [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V] :
    G →* (Module.End (ZMod p)
      (StandardHomocyclicCanonicalIndex (p := p) V → ZMod p))ˣ :=
  standardHomocyclicCoverModPLinearActionOfEquiv
    (G := G) (V := V) (p := p)
    (standardHomocyclicCoverToElementaryAbelianEquiv (p := p) V)

/-- The canonical mod-`p` linear action is the additive form of
`standardHomocyclicCoverModPAction`. -/
public theorem CFSG.standardHomocyclicCoverModPLinearAction_coordinate
    {G V : Type u} [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (g : G) (x : StandardHomocyclicCanonicalIndex (p := p) V → ZMod p) :
    Multiplicative.ofAdd
        (((standardHomocyclicCoverModPLinearAction G V (p := p) g :
            (Module.End (ZMod p)
              (StandardHomocyclicCanonicalIndex (p := p) V → ZMod p))ˣ) :
          Module.End (ZMod p)
            (StandardHomocyclicCanonicalIndex (p := p) V → ZMod p)) x) =
      standardHomocyclicCoverModPAction G V (p := p) g (Multiplicative.ofAdd x) := by
  exact standardHomocyclicCoverModPLinearActionOfEquiv_coordinate
    (G := G) (V := V) (p := p)
    (standardHomocyclicCoverToElementaryAbelianEquiv (p := p) V) g x
