module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Bracket
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct

import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Basic
import Mathlib.Tactic.TypeStar

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core

namespace CFSG
end CFSG
open CFSG

section SemidirectInfrastructure

variable {A K0 Kk : Type*} [Group A] [Group K0] [Group Kk]
variable [MulDistribMulAction A K0] [MulDistribMulAction A Kk]

public lemma CFSG.semidirect_lift_inr_apply
    (conjHomKk : Kk →* MulAut K0)
    (hsemi :
      ∀ a : A,
        conjHomKk.comp ((MulDistribMulAction.toMulAut A Kk) a).toMonoidHom =
          (MulAut.conj ((MulDistribMulAction.toMulAut A K0) a)).toMonoidHom.comp conjHomKk)
    (a : A) (x : K0) :
    ((SemidirectProduct.lift (fn := conjHomKk) (fg := MulDistribMulAction.toMulAut A K0) hsemi)
      (SemidirectProduct.inr a)) x = a • x := by
  calc
    ((SemidirectProduct.lift (fn := conjHomKk) (fg := MulDistribMulAction.toMulAut A K0) hsemi)
      (SemidirectProduct.inr a)) x
        = ((MulDistribMulAction.toMulAut A K0) a) x := by
            exact congrArg (fun e : MulAut K0 => e x)
              (SemidirectProduct.lift_inr (fn := conjHomKk)
                (fg := MulDistribMulAction.toMulAut A K0) (h := hsemi) a)
    _ = a • x := by rfl

public lemma CFSG.semidirect_lift_inl_apply
    (conjHomKk : Kk →* MulAut K0)
    (hsemi :
      ∀ a : A,
        conjHomKk.comp ((MulDistribMulAction.toMulAut A Kk) a).toMonoidHom =
          (MulAut.conj ((MulDistribMulAction.toMulAut A K0) a)).toMonoidHom.comp conjHomKk)
    (n : Kk) (x : K0) :
    ((SemidirectProduct.lift (fn := conjHomKk) (fg := MulDistribMulAction.toMulAut A K0) hsemi)
      (SemidirectProduct.inl n)) x = (conjHomKk n) x := by
  exact
    congrArg (fun e : MulAut K0 => e x)
      (SemidirectProduct.lift_inl (fn := conjHomKk)
        (fg := MulDistribMulAction.toMulAut A K0) (h := hsemi) n)

end SemidirectInfrastructure
/-!
### Coprime action: choosing an invariant complement (infrastructure)

This section implements the key “invariant complement” step used in Proposition 1.5(a):
for an abelian normal subgroup `H` of coprime index, an external coprime operator group `A`
fixes some complement of `H`.

The proof follows the standard `H¹(A, H) = 0` argument, using the existing cocycle lemma
`exists_coboundary_of_cocycle_of_coprime_card` and Schur–Zassenhaus’ `QuotientDiff` torsor.
-/

section CoprimeInvariantComplement

open scoped Pointwise
open scoped IsMulCommutative
open MulAction

variable {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]

namespace Subgroup

namespace leftTransversals

open scoped Pointwise

open Finset

variable (H : Subgroup G) [IsMulCommutative H] [Subgroup.FiniteIndex H]
variable [QuotientAction A H] [MulDistribMulAction A H]

/-- Naturality of `diff` for pointwise actions by automorphisms. For `ϕ = id`, applying `a`
to the transversals applies `a` to the resulting element of `H`. -/
lemma diff_id_smul
    (hcoe_smul : ∀ a : A, ∀ x : H, ((a • x : H) : G) = a • (x : G))
    (a : A) (S T : H.LeftTransversal) :
    diff (MonoidHom.id H) (a • S) (a • T) =
      a • diff (MonoidHom.id H) S T := by
  classical
  let _ := H.fintypeQuotientOfFiniteIndex
  -- Abbreviate the chosen representatives of cosets coming from the transversals.
  let α := S.2.leftQuotientEquiv
  let β := T.2.leftQuotientEquiv
  let α' := (a • S).2.leftQuotientEquiv
  let β' := (a • T).2.leftQuotientEquiv

  -- The `diff` factors for the two pairs of transversals.
  let f₀ : G ⧸ H → H := fun q =>
    ⟨(α q : G)⁻¹ * β q,
      QuotientGroup.leftRel_apply.mp <|
        Quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩
  let f₁ : G ⧸ H → H := fun q =>
    ⟨(α' q : G)⁻¹ * β' q,
      QuotientGroup.leftRel_apply.mp <|
        Quotient.exact' ((α'.symm_apply_apply q).trans (β'.symm_apply_apply q).symm)⟩

  have hdiff₀ : diff (MonoidHom.id H) S T = ∏ q : G ⧸ H, f₀ q := by
    simp [diff, f₀, α, β, MonoidHom.id_apply]
  have hdiff₁ : diff (MonoidHom.id H) (a • S) (a • T) = ∏ q : G ⧸ H, f₁ q := by
    simp [diff, f₁, α', β', MonoidHom.id_apply]

  -- Reindex `f₁` using the permutation `q ↦ a • q` of `G ⧸ H`.
  have hreindex : (∏ q : G ⧸ H, f₁ q) = ∏ q : G ⧸ H, a • f₀ q := by
    refine (Fintype.prod_equiv (e := (MulAction.toPerm a).symm)
      (f := f₁) (g := fun q => a • f₀ q) ?_)
    intro q
    -- Reduce to equality in `G` via `Subtype.ext`.
    ext
    -- Rewrite the coset representatives under the `A`-action.
    have hαq : (α' q : G) = a • (α (a⁻¹ • q) : G) := by
      simpa [α', α] using
        (Subgroup.smul_apply_eq_smul_apply_inv_smul (H := H) (f := a) (S := S) q)
    have hβq : (β' q : G) = a • (β (a⁻¹ • q) : G) := by
      simpa [β', β] using
        (Subgroup.smul_apply_eq_smul_apply_inv_smul (H := H) (f := a) (S := T) q)
    -- Now compute the term; on `G` the `A`-action is by automorphisms.
    simp [f₁, f₀, hαq, hβq, hcoe_smul, smul_mul']

  -- Factor `a` out of the product.
  have hsmul_prod :
      (∏ q : G ⧸ H, a • f₀ q) = a • (∏ q : G ⧸ H, f₀ q) := by
    -- `Finset.smul_prod'` gives `a • ∏ f₀ = ∏ a • f₀`, so we take its symmetry.
    simpa using
      (Finset.smul_prod' (r := a) (f := f₀) (s := (Finset.univ : Finset (G ⧸ H)))).symm

  -- Assemble the calculation.
  calc
    diff (MonoidHom.id H) (a • S) (a • T)
        = ∏ q : G ⧸ H, f₁ q := hdiff₁
    _ = ∏ q : G ⧸ H, a • f₀ q := hreindex
    _ = a • (∏ q : G ⧸ H, f₀ q) := hsmul_prod
    _ = a • diff (MonoidHom.id H) S T := by
          simp [hdiff₀]

end leftTransversals

namespace quotientDiff

open scoped Pointwise
open MulOpposite
open MulAction

variable (H : Subgroup G)
variable [hH : IsInvariant A G H]

local instance : MulAction.QuotientAction A H :=
  quotientAction_of_isInvariant (A := A) H hH

lemma coe_smul (a : A) (x : H) : ((a • x : H) : G) = a • (x : G) := rfl

noncomputable local instance : MulAction A H.LeftTransversal := by
  classical
  infer_instance

variable [H.Normal]

/- A left transversal is a subset of `G` that forms a (left) complement to `H` in `G`. -/

lemma smul_op_smul_leftTransversal (a : A) (g : Gᵐᵒᵖ) (T : H.LeftTransversal) :
    a • (g • T) = op (a • g.unop) • (a • T) := by
  -- Both actions on transversals are defined by pointwise actions on the underlying sets.
  apply Subtype.ext
  ext x
  -- Unfold to a statement about membership in pointwise-set scalar multiples.
  change x ∈ (a • (g • (T : Set G)) : Set G) ↔
      x ∈ (op (a • g.unop) • (a • (T : Set G)) : Set G)
  constructor
  · intro hx
    rcases (Set.mem_smul_set.1 hx) with ⟨y, hy, rfl⟩
    rcases (Set.mem_smul_set.1 hy) with ⟨z, hz, rfl⟩
    refine (Set.mem_smul_set.2 ?_)
    refine ⟨a • z, ?_, ?_⟩
    · exact Set.mem_smul_set.2 ⟨z, hz, rfl⟩
    · -- `a • (g • z) = (a • z) * (a • g.unop)`.
      simp [smul_eq_mul_unop, smul_mul']
  · intro hx
    rcases (Set.mem_smul_set.1 hx) with ⟨y, hy, rfl⟩
    rcases (Set.mem_smul_set.1 hy) with ⟨z, hz, rfl⟩
    refine (Set.mem_smul_set.2 ?_)
    refine ⟨g • z, ?_, ?_⟩
    · exact Set.mem_smul_set.2 ⟨z, hz, rfl⟩
    · -- `a • (g • z) = (a • z) * (a • g.unop)`.
      simp [smul_eq_mul_unop, smul_mul']

variable [IsMulCommutative H] [Subgroup.FiniteIndex H]

/-- An `A`-action on `H.QuotientDiff` induced by an `A`-action on `G` that preserves `H`. -/
@[reducible] noncomputable def mulActionQuotientDiff : MulAction A H.QuotientDiff := by
  classical
  have smul_well (a : A) {S T : H.LeftTransversal}
      (hST : leftTransversals.diff (H := H) (MonoidHom.id H) S T = 1) :
      leftTransversals.diff (H := H) (MonoidHom.id H) (a • S) (a • T) = 1 := by
    have hdiff :
        leftTransversals.diff (H := H) (MonoidHom.id H) (a • S) (a • T) =
          a • leftTransversals.diff (H := H) (MonoidHom.id H) S T :=
      leftTransversals.diff_id_smul (G := G) (A := A) (H := H)
        (hcoe_smul := coe_smul (G := G) (A := A) (H := H)) a S T
    calc
      leftTransversals.diff (H := H) (MonoidHom.id H) (a • S) (a • T)
          = a • leftTransversals.diff (H := H) (MonoidHom.id H) S T := hdiff
      _ = a • (1 : H) := by simp [hST]
      _ = (1 : H) := by simp

  let smulQD : A → H.QuotientDiff → H.QuotientDiff :=
    fun a =>
      Quotient.map' (fun T : H.LeftTransversal => a • T) (fun S T hST =>
        smul_well (a := a) (S := S) (T := T) (by simpa using hST))

  refine
    { smul := smulQD
      one_smul := by
        intro q
        refine Quotient.inductionOn' q (fun T => ?_)
        change smulQD (1 : A) (Quotient.mk'' T) = Quotient.mk'' T
        simp [smulQD]
        rfl
      mul_smul := by
        intro a b q
        refine Quotient.inductionOn' q (fun T => ?_)
        change smulQD (a * b) (Quotient.mk'' T) = smulQD a (smulQD b (Quotient.mk'' T))
        simp [smulQD, mul_smul]
        rfl }

noncomputable local instance (priority := 100) instMulActionQuotientDiffA :
    MulAction A H.QuotientDiff :=
  mulActionQuotientDiff (G := G) (A := A) (H := H)

omit [H.Normal] in
lemma smul_mk (a : A) (T : H.LeftTransversal) :
    (mulActionQuotientDiff (G := G) (A := A) (H := H)).smul a (Quotient.mk'' T) =
      Quotient.mk'' (a • T) := by
  classical
  exact Quotient.map'_mk'' _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma smul_smul_quotientDiff (a : A) (g : G) (q : H.QuotientDiff) :
    (mulActionQuotientDiff (G := G) (A := A) (H := H)).smul a
        ((Subgroup.instMulActionQuotientDiff (H := H) (G := G)).smul g q) =
      (Subgroup.instMulActionQuotientDiff (H := H) (G := G)).smul (a • g)
        ((mulActionQuotientDiff (G := G) (A := A) (H := H)).smul a q) := by
  classical
  refine Quotient.inductionOn' q (fun T => ?_)
  -- Unfold both actions on representatives and use the corresponding commutation on transversals.
  have hT :
      a • (op (g⁻¹ : G) • T) = op ((a • g)⁻¹ : G) • (a • T) := by
    simpa [smul_inv_smul] using
      (smul_op_smul_leftTransversal (G := G) (A := A) (H := H) a (op (g⁻¹ : G)) T)
  calc
    (mulActionQuotientDiff (G := G) (A := A) (H := H)).smul a
          ((Subgroup.instMulActionQuotientDiff (H := H) (G := G)).smul g (Quotient.mk'' T))
        = (mulActionQuotientDiff (G := G) (A := A) (H := H)).smul a
            (Quotient.mk'' (op (g⁻¹ : G) • T) : H.QuotientDiff) := by
              rfl
    _ = Quotient.mk'' (a • (op (g⁻¹ : G) • T)) := by
          exact smul_mk (G := G) (A := A) (H := H) a _
    _ = Quotient.mk'' (op ((a • g)⁻¹ : G) • (a • T)) := by
          simpa using congrArg Quotient.mk'' hT
    _ =
        (Subgroup.instMulActionQuotientDiff (H := H) (G := G)).smul (a • g)
          (Quotient.mk'' (a • T) : H.QuotientDiff) := by
            rfl
    _ =
        (Subgroup.instMulActionQuotientDiff (H := H) (G := G)).smul (a • g)
          ((mulActionQuotientDiff (G := G) (A := A) (H := H)).smul a (Quotient.mk'' T)) := by
            simp [smul_mk]

/-- Commutation between the `A`-action and the `G`-action on `H.QuotientDiff`. -/
lemma smul_smul_quotientDiff' (a : A) (g : G) (q : H.QuotientDiff) :
    a • (g • q) = (a • g) • (a • q) := by
  -- Reduce to `smul_smul_quotientDiff`, which is stated using explicit `MulAction.smul`.
  change
    (mulActionQuotientDiff (G := G) (A := A) (H := H)).smul a
        ((Subgroup.instMulActionQuotientDiff (H := H) (G := G)).smul g q) =
      (Subgroup.instMulActionQuotientDiff (H := H) (G := G)).smul (a • g)
        ((mulActionQuotientDiff (G := G) (A := A) (H := H)).smul a q)
  exact smul_smul_quotientDiff (G := G) (A := A) (H := H) a g q

lemma isCocycle₁_of_smul_basepoint
    [Finite H]
    (hHc : Nat.Coprime (Nat.card H) H.index)
    (α : H.QuotientDiff) (c : A → H) (hc_spec : ∀ a : A, c a • (a • α) = α) :
    IsCocycle₁ (A := A) (N := H) c := by
  intro a b
  -- Let `h := (c (a*b))⁻¹ * (c a * (a • c b))`; show `h • ((a*b)•α) = (a*b)•α`.
  have ha : c a • (a • α) = α := hc_spec a
  have hb : c b • (b • α) = α := hc_spec b
  have hab : c (a * b) • ((a * b) • α) = α := hc_spec (a * b)
  have h_step : (a • c b) • ((a * b) • α) = a • α := by
    -- Apply `a` to `hb : c b • (b • α) = α` and rewrite using equivariance.
    have hb0 : a • (c b • (b • α)) = a • α := by
      simpa using congrArg (fun q : H.QuotientDiff => a • q) hb
    have hb1 : a • (((c b : H) : G) • (b • α)) = a • α := by
      simpa only [MulAction.subgroup_smul_def] using hb0
    have hcomm :=
      smul_smul_quotientDiff' (G := G) (A := A) (H := H) a ((c b : H) : G) (b • α)
    have hb2 : (a • ((c b : H) : G)) • (a • (b • α)) = a • α := by
      simpa [hcomm] using hb1
    have hb3 : (a • c b) • (a • (b • α)) = a • α := by
      have hb2' : ((a • c b : H) : G) • (a • (b • α)) = a • α := by
        simpa [coe_smul (G := G) (A := A) (H := H)] using hb2
      simpa only [MulAction.subgroup_smul_def] using hb2'
    simpa [mul_smul] using hb3
  have h_comp : (c a * (a • c b)) • ((a * b) • α) = α := by
    -- Use `h_step` and then `ha`.
    calc
      (c a * (a • c b)) • ((a * b) • α)
          = c a • ((a • c b) • ((a * b) • α)) := by simp [mul_smul]
      _ = c a • (a • α) := by simp [h_step]
      _ = α := ha
  -- Now use freeness: if two elements send `((a*b)•α)` to `α`, they are equal.
  have hfix :
      ((c (a * b))⁻¹ * (c a * (a • c b))) • ((a * b) • α) = (a * b) • α := by
    calc
      ((c (a * b))⁻¹ * (c a * (a • c b))) • ((a * b) • α)
          = (c (a * b))⁻¹ • ((c a * (a • c b)) • ((a * b) • α)) := by simp [mul_smul]
      _ = (c (a * b))⁻¹ • α := by simp [h_comp]
      _ = (a * b) • α := by
        -- Rearrange `hab`.
        have hab' := congrArg (fun q : H.QuotientDiff => (c (a * b))⁻¹ • q) hab
        simpa [inv_smul_smul] using hab'.symm
  have h_one : (c (a * b))⁻¹ * (c a * (a • c b)) = (1 : H) :=
    Subgroup.eq_one_of_smul_eq_one (H := H) hHc ((a * b) • α) _ hfix
  -- Conclude.
  -- Multiply by `c (a*b)` on the left.
  have hmul : c a * (a • c b) = c (a * b) := by
    simpa [mul_assoc] using congrArg (fun x : H => c (a * b) * x) h_one
  exact hmul.symm

lemma fixedPoint_of_coboundary
    (α : H.QuotientDiff) (c : A → H) (hc_spec : ∀ a : A, c a • (a • α) = α)
    (n : H) (hn : ∀ a : A, c a = (a • n)⁻¹ * n) :
    ∀ a : A, a • (n⁻¹ • α) = n⁻¹ • α := by
  intro a
  -- First, express `a • α` in terms of `c a`.
  have ha : a • α = (c a)⁻¹ • α := by
    have ha' := congrArg (fun q : H.QuotientDiff => (c a)⁻¹ • q) (hc_spec a)
    simpa [inv_smul_smul] using ha'
  -- Now compute `a • (n⁻¹ • α)`.
  calc
    a • (n⁻¹ • α) = (a • (n⁻¹ : H)) • (a • α) := by
      have hcomm :=
        smul_smul_quotientDiff' (G := G) (A := A) (H := H) a ((n⁻¹ : H) : G) α
      simpa [MulAction.subgroup_smul_def, coe_smul (G := G) (A := A) (H := H)] using hcomm
    _ = (a • (n⁻¹ : H)) • ((c a)⁻¹ • α) := by simp [ha]
    _ = ((a • (n⁻¹ : H)) * (c a)⁻¹) • α := by simp [mul_smul]
    _ = n⁻¹ • α := by
      have hmul : (c a) * (a • (n : H)) = n := by
        have hn' := hn a
        simp [hn', mul_left_comm, mul_comm]
      have hscalar : (a • (n⁻¹ : H)) * (c a)⁻¹ = (n⁻¹ : H) := by
        have hmul' := congrArg (fun x : H => x⁻¹) hmul
        simpa [mul_inv_rev, inv_inv, smul_inv_smul, mul_assoc, mul_left_comm, mul_comm] using hmul'
      simpa using congrArg (fun h : H => h • α) hscalar

/-- A coprime action fixes some complement of an abelian normal subgroup of coprime index. -/
public theorem exists_invariant_complement'
    [Finite G] [Finite A]
    (hHc : Nat.Coprime (Nat.card H) H.index)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card H)) :
    ∃ K : Subgroup G, IsComplement' H K ∧ IsInvariant A G K := by
  classical
  -- Make the relevant actions explicit to avoid instance ambiguity.
  let _ := quotientAction_of_isInvariant (A := A) H hH
  -- Work with a fixed basepoint in the Schur–Zassenhaus torsor `H.QuotientDiff`.
  let α : H.QuotientDiff := default

  -- Define the cocycle `c` by choosing `c a` such that `c a • (a • α) = α`.
  have hex (a : A) : ∃ h : H, h • (a • α) = α :=
    Subgroup.exists_smul_eq (H := H) hHc (a • α) α
  let c : A → H := fun a => Classical.choose (hex a)
  have hc_spec (a : A) : c a • (a • α) = α := Classical.choose_spec (hex a)

  have hc : IsCocycle₁ (A := A) (N := H) c :=
    isCocycle₁_of_smul_basepoint (G := G) (A := A) (H := H) hHc α c hc_spec

  -- Coboundary: `c a = (a • n)⁻¹ * n`.
  obtain ⟨n, hn⟩ :=
    exists_coboundary_of_cocycle_of_coprime_card (A := A) (N := H) c hc hcop

  -- Fixed point in the torsor.
  let α₀ : H.QuotientDiff := n⁻¹ • α
  have hfixed : ∀ a : A, a • α₀ = α₀ := by
    simpa [α₀] using fixedPoint_of_coboundary (G := G) (A := A) (H := H) α c hc_spec n hn

  -- Define the complement as the stabilizer of the fixed point.
  refine ⟨stabilizer G α₀, ?_, ?_⟩
  · -- Complement property from Schur–Zassenhaus.
    exact isComplement'_stabilizer_of_coprime (H := H) (G := G) (α := α₀) hHc
  · -- Invariance of the stabilizer from equivariance of the action and `α₀` being fixed.
    refine ⟨?_⟩
    intro a g
    change (g • α₀ = α₀) ↔ ((a • g) • α₀ = α₀)
    constructor
    · intro hg
      have := congrArg (fun q : H.QuotientDiff => a • q) hg
      -- Rewrite using equivariance and the fixed-point property.
      simpa [smul_smul_quotientDiff' (G := G) (A := A) (H := H), hfixed a] using this
    · intro hg
      -- Apply the forward direction to `a⁻¹` and `a • g`.
      have hg' : (a⁻¹ • (a • g)) • α₀ = α₀ := by
        have := congrArg (fun q : H.QuotientDiff => a⁻¹ • q) hg
        simpa [smul_smul_quotientDiff' (G := G) (A := A) (H := H), hfixed a⁻¹] using this
      simpa [inv_smul_smul] using hg'

end quotientDiff

end Subgroup

end CoprimeInvariantComplement

section HallConjugacyComplements

open MulOpposite MulAction Subgroup.leftTransversals

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]
variable {H K₁ K₂ : Subgroup G} [H.Normal] [IsMulCommutative H] [Subgroup.FiniteIndex H]

abbrev transversalOfComplement (K : Subgroup G)
    (hK : Subgroup.IsComplement' H K) : Subgroup.LeftTransversal H :=
  ⟨(K : Set G), (Subgroup.isComplement'_def (H := K) (K := H)).mp hK.symm⟩

abbrev quotientDiffPointOfComplement (K : Subgroup G)
    (hK : Subgroup.IsComplement' H K) : Subgroup.QuotientDiff H :=
  Quotient.mk'' (transversalOfComplement (H := H) K hK)

omit [Finite G] in
lemma smul_quotientDiffPoint_eq_of_mem_complement {K : Subgroup G}
    (hK : Subgroup.IsComplement' H K) (k : G) (hk : k ∈ K) :
    k • quotientDiffPointOfComplement (H := H) K hK =
      quotientDiffPointOfComplement (H := H) K hK := by
  dsimp [quotientDiffPointOfComplement, transversalOfComplement]
  change Quotient.mk'' (op (k⁻¹ : G) •
      (⟨(K : Set G), (Subgroup.isComplement'_def (H := K) (K := H)).mp hK.symm⟩ :
        Subgroup.LeftTransversal H))
    =
      Quotient.mk'' (⟨(K : Set G), (Subgroup.isComplement'_def (H := K) (K := H)).mp hK.symm⟩ :
        Subgroup.LeftTransversal H)
  apply congrArg Quotient.mk''
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
    exact K.mul_mem hy (K.inv_mem hk)
  · intro hx
    refine Set.mem_smul_set.mpr ?_
    refine ⟨x * k, K.mul_mem hx hk, ?_⟩
    simp [mul_assoc]

omit [Finite G] in
lemma complement_le_stabilizer_quotientDiffPoint {K : Subgroup G}
    (hK : Subgroup.IsComplement' H K) :
    K ≤ MulAction.stabilizer G (quotientDiffPointOfComplement (H := H) K hK) := by
  intro k hk
  change k • quotientDiffPointOfComplement (H := H) K hK =
      quotientDiffPointOfComplement (H := H) K hK
  simpa using smul_quotientDiffPoint_eq_of_mem_complement (H := H) hK k hk

lemma stabilizer_quotientDiffPoint_eq_of_complement
    {K : Subgroup G} (hK : Subgroup.IsComplement' H K)
    (hcop : Nat.Coprime (Nat.card H) H.index) :
    MulAction.stabilizer G (quotientDiffPointOfComplement (H := H) K hK) = K := by
  have hcomp_stab :
      Subgroup.IsComplement' H
        (MulAction.stabilizer G (quotientDiffPointOfComplement (H := H) K hK)) :=
    Subgroup.isComplement'_stabilizer_of_coprime (H := H) (G := G)
      (α := quotientDiffPointOfComplement (H := H) K hK) hcop
  have hle : K ≤ MulAction.stabilizer G (quotientDiffPointOfComplement (H := H) K hK) :=
    complement_le_stabilizer_quotientDiffPoint (H := H) hK
  have hcardK : H.index = Nat.card K := hK.symm.index_eq_card
  have hcardStab :
      H.index = Nat.card (MulAction.stabilizer G (quotientDiffPointOfComplement (H := H) K hK)) :=
    hcomp_stab.symm.index_eq_card
  have hcard_eq :
      Nat.card K =
        Nat.card (MulAction.stabilizer G (quotientDiffPointOfComplement (H := H) K hK)) := by
    simpa [hcardK] using hcardStab
  exact (Subgroup.eq_of_le_of_card_ge hle (by simp [hcard_eq])).symm

public lemma exists_conj_eq_of_isComplement'
    (hcop : Nat.Coprime (Nat.card H) H.index)
    (hK₁ : Subgroup.IsComplement' H K₁) (hK₂ : Subgroup.IsComplement' H K₂) :
    ∃ n : H, K₂ = K₁.map (MulAut.conj (n : G)).toMonoidHom := by
  let α₁ : Subgroup.QuotientDiff H := quotientDiffPointOfComplement (H := H) K₁ hK₁
  let α₂ : Subgroup.QuotientDiff H := quotientDiffPointOfComplement (H := H) K₂ hK₂
  obtain ⟨n, hn⟩ := Subgroup.exists_smul_eq (H := H) hcop α₁ α₂
  refine ⟨n, ?_⟩
  have hstab₁ : MulAction.stabilizer G α₁ = K₁ :=
    stabilizer_quotientDiffPoint_eq_of_complement (H := H) (K := K₁) hK₁ hcop
  have hstab₂ : MulAction.stabilizer G α₂ = K₂ :=
    stabilizer_quotientDiffPoint_eq_of_complement (H := H) (K := K₂) hK₂ hcop
  have hmap :
      MulAction.stabilizer G α₂ =
        (MulAction.stabilizer G α₁).map (MulAut.conj (n : G)).toMonoidHom := by
    calc
      MulAction.stabilizer G α₂ = MulAction.stabilizer G ((n : G) • α₁) := by
        simpa only [α₂, MulAction.subgroup_smul_def] using
          congrArg (MulAction.stabilizer G) hn.symm
      _ = (MulAction.stabilizer G α₁).map (MulAut.conj (n : G)).toMonoidHom :=
        MulAction.stabilizer_smul_eq_stabilizer_map_conj (G := G) (g := (n : G)) (a := α₁)
  simpa [hstab₁, hstab₂] using hmap

end Subgroup

end HallConjugacyComplements
