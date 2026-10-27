module

public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RepresentationTheory.Invariants

namespace CFSG
end CFSG
open CFSG

/-!
# Permutation bases and orbit counts

Source-neutral linear algebra for comparing two permutation bases of the same
linear equivalence. Fixed vectors are identified with functions on the orbit
quotient, and Burnside's lemma recovers exact fixed-point counts for
prime-order permutations in every field characteristic.
-/

open scoped BigOperators

noncomputable section

namespace CFSG.Theory.Representation

open _root_.Representation

attribute [local instance] Fintype.ofFinite
private def RespectfulFunctions
    (F ι : Type*) [Field F] (r : Setoid ι) : Submodule F (ι → F) where
  carrier := {f | ∀ ⦃i j⦄, r i j → f i = f j}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg i j hij
    simp [hf hij, hg hij]
  smul_mem' := by
    intro a f hf i j hij
    simp [hf hij]

private noncomputable def quotientFunctionsLinearEquivRespectful
    (F ι : Type*) [Field F] (r : Setoid ι) :
    (Quotient r → F) ≃ₗ[F] RespectfulFunctions F ι r where
  toFun f := ⟨fun i => f (Quotient.mk'' i), by
    intro i j hij
    exact congrArg f (Quotient.sound hij)⟩
  invFun f := Quotient.lift f.1 (by
    intro i j hij
    exact f.2 hij)
  left_inv f := by
    funext q
    induction q using Quotient.inductionOn
    rfl
  right_inv f := by
    ext i
    rfl
  map_add' f g := by
    ext i
    rfl
  map_smul' a f := by
    ext i
    rfl

private theorem quotientFunctionsLinearEquivRespectful_finrank
    (F ι : Type*) [Field F] [Finite ι] (r : Setoid ι) :
    Module.finrank F (RespectfulFunctions F ι r) =
      Nat.card (Quotient r) := by
  rw [← LinearEquiv.finrank_eq (quotientFunctionsLinearEquivRespectful F ι r)]
  rw [Module.finrank_pi_fintype]
  simp [Nat.card_eq_fintype_card]

private theorem equivariantBasis_equivFun_apply
    {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Finite ι] (b : Module.Basis ι F V) (T : V →ₗ[F] V) (σ : Equiv.Perm ι)
    (hT : ∀ i, T (b i) = b (σ i)) (v : V) (i : ι) :
    b.equivFun (T v) (σ i) = b.equivFun v i := by
  classical
  rw [← b.sum_equivFun v, map_sum]
  simp [hT]
  rw [Finset.sum_eq_single i]
  · simp
  · intro x _hx hxi
    have hσxi : σ x ≠ σ i := fun h => hxi (σ.injective h)
    simp [hσxi]
  · simp

private theorem perm_invariant_zpowers
    {F ι : Type*} [Field F] (σ : Equiv.Perm ι) (f : ι → F)
    (hf : ∀ i, f (σ i) = f i) :
    ∀ g : Subgroup.zpowers σ, ∀ i, f (g.1 i) = f i := by
  let S : Subgroup (Equiv.Perm ι) := {
    carrier := {g | ∀ i, f (g i) = f i}
    one_mem' := by simp
    mul_mem' := by
      intro g h hg hh i
      rw [Equiv.Perm.mul_apply, hg, hh]
    inv_mem' := by
      intro g hg i
      symm
      simpa using hg (g⁻¹ i)
  }
  have hσ : σ ∈ S := hf
  have hle : Subgroup.zpowers σ ≤ S := Subgroup.zpowers_le.mpr hσ
  intro g i
  exact hle g.2 i

private theorem equivariantBasis_fixed_iff_respectful
    {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Finite ι] (b : Module.Basis ι F V) (T : V ≃ₗ[F] V) (σ : Equiv.Perm ι)
    (hT : ∀ i, T (b i) = b (σ i)) (v : V) :
    T v = v ↔
      b.equivFun v ∈ RespectfulFunctions F ι
        (MulAction.orbitRel (Subgroup.zpowers σ) ι) := by
  constructor
  · intro hv i j hij
    have hstep : ∀ x, b.equivFun v (σ x) = b.equivFun v x := by
      intro x
      calc
        b.equivFun v (σ x) = b.equivFun (T v) (σ x) := by rw [hv]
        _ = b.equivFun v x :=
          equivariantBasis_equivFun_apply b T.toLinearMap σ hT v x
    rw [MulAction.orbitRel_apply] at hij
    rcases hij with ⟨g, rfl⟩
    exact perm_invariant_zpowers σ (b.equivFun v) hstep g j
  · intro hv
    apply b.equivFun.injective
    funext j
    let i := σ.symm j
    have hrel :
        MulAction.orbitRel (Subgroup.zpowers σ) ι (σ i) i := by
      rw [MulAction.orbitRel_apply]
      exact ⟨⟨σ, Subgroup.mem_zpowers σ⟩, rfl⟩
    calc
      b.equivFun (T v) j =
          b.equivFun (T v) (σ i) := by simp [i]
      _ = b.equivFun v i :=
        equivariantBasis_equivFun_apply b T.toLinearMap σ hT v i
      _ = b.equivFun v (σ i) := (hv hrel).symm
      _ = b.equivFun v j := by simp [i]

private noncomputable def equivariantBasisFixedLinearEquivRespectful
    {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Finite ι] (b : Module.Basis ι F V) (T : V ≃ₗ[F] V) (σ : Equiv.Perm ι)
    (hT : ∀ i, T (b i) = b (σ i)) :
    T.fixedSubmodule ≃ₗ[F]
      RespectfulFunctions F ι
        (MulAction.orbitRel (Subgroup.zpowers σ) ι) where
  toFun v := ⟨b.equivFun v.1,
    (equivariantBasis_fixed_iff_respectful b T σ hT v.1).1 v.2⟩
  invFun f := ⟨b.equivFun.symm f.1,
    (equivariantBasis_fixed_iff_respectful b T σ hT
      (b.equivFun.symm f.1)).2 (by
        rw [b.equivFun.apply_symm_apply]
        exact f.2)⟩
  left_inv v := by
    ext
    simp
  right_inv f := by
    apply Subtype.ext
    exact b.equivFun.apply_symm_apply f.1
  map_add' v w := by
    ext
    simp
  map_smul' a v := by
    ext
    simp

/-- The fixed submodule of a linear equivalence that permutes a finite basis has
dimension equal to the number of orbits of the basis permutation. -/
public theorem equivariantBasis_fixedSubmodule_finrank_eq_orbitQuotient_card
    {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Finite ι] (b : Module.Basis ι F V) (T : V ≃ₗ[F] V) (σ : Equiv.Perm ι)
    (hT : ∀ i, T (b i) = b (σ i)) :
    Module.finrank F T.fixedSubmodule =
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι) := by
  rw [LinearEquiv.finrank_eq
    (equivariantBasisFixedLinearEquivRespectful b T σ hT)]
  exact quotientFunctionsLinearEquivRespectful_finrank F ι _

private theorem fixedBy_eq_fixedPoints_of_zpowers_eq_top
    {G X : Type*} [Group G] [MulAction G X] (g : G)
    (hg : Subgroup.zpowers g = ⊤) :
    MulAction.fixedBy X g = MulAction.fixedPoints G X := by
  ext x
  constructor
  · intro hx h
    have hh : h ∈ Subgroup.zpowers g := by
      rw [hg]
      exact Subgroup.mem_top h
    rcases hh with ⟨z, rfl⟩
    exact MulAction.mem_fixedBy_zpow hx z
  · intro hx
    exact hx g

private theorem primeCard_fixedPoints_orbit_formula
    {p : ℕ} [Fact p.Prime] {G X : Type*}
    [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [∀ g : G, Fintype (MulAction.fixedBy X g)]
    [Fintype (MulAction.fixedPoints G X)]
    [Fintype (MulAction.orbitRel.Quotient G X)]
    (hG : Fintype.card G = p) :
    Fintype.card X +
        (p - 1) * Fintype.card (MulAction.fixedPoints G X) =
      Fintype.card (MulAction.orbitRel.Quotient G X) * p := by
  classical
  have hfixed (g : G) (hg : g ≠ 1) :
      Fintype.card (MulAction.fixedBy X g) =
        Fintype.card (MulAction.fixedPoints G X) := by
    apply Fintype.card_congr
    exact Set.equivOfEq
      (fixedBy_eq_fixedPoints_of_zpowers_eq_top g
        (zpowers_eq_top_of_prime_card
          (by simpa [Nat.card_eq_fintype_card] using hG) hg))
  have hsum :
      (∑ g ∈ Finset.univ.erase (1 : G),
          Fintype.card (MulAction.fixedBy X g)) =
        (Fintype.card G - 1) *
          Fintype.card (MulAction.fixedPoints G X) := by
    calc
      (∑ g ∈ Finset.univ.erase (1 : G),
          Fintype.card (MulAction.fixedBy X g)) =
          ∑ _g ∈ Finset.univ.erase (1 : G),
            Fintype.card (MulAction.fixedPoints G X) := by
        apply Finset.sum_congr rfl
        intro g hg
        rw [hfixed g (by simpa using hg)]
      _ = (Finset.univ.erase (1 : G)).card *
          Fintype.card (MulAction.fixedPoints G X) := by simp
      _ = (Fintype.card G - 1) *
          Fintype.card (MulAction.fixedPoints G X) := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : G)),
          Finset.card_univ]
  have hburnside :
      Fintype.card (MulAction.fixedBy X (1 : G)) +
          ∑ g ∈ Finset.univ.erase (1 : G),
            Fintype.card (MulAction.fixedBy X g) =
        Fintype.card (MulAction.orbitRel.Quotient G X) *
          Fintype.card G := by
    rw [add_comm,
      Finset.sum_erase_add _ _ (Finset.mem_univ (1 : G))]
    exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  calc
    Fintype.card X +
        (p - 1) * Fintype.card (MulAction.fixedPoints G X) =
      Fintype.card (MulAction.fixedBy X (1 : G)) +
        ∑ g ∈ Finset.univ.erase (1 : G),
          Fintype.card (MulAction.fixedBy X g) := by
            rw [hsum, hG]
            simp [MulAction.fixedBy]
    _ = Fintype.card (MulAction.orbitRel.Quotient G X) *
        Fintype.card G := hburnside
    _ = Fintype.card (MulAction.orbitRel.Quotient G X) * p := by rw [hG]
private noncomputable def permFixedPointsEquivZpowersFixedPoints
    {X : Type*} (σ : Equiv.Perm X) :
    Function.fixedPoints σ ≃
      MulAction.fixedPoints (Subgroup.zpowers σ) X where
  toFun x := ⟨x.1, by
    intro g
    rcases g.2 with ⟨z, hz⟩
    change (g.1 : Equiv.Perm X) x.1 = x.1
    rw [← hz]
    exact Function.IsFixedPt.perm_zpow x.2 z⟩
  invFun x := ⟨x.1, x.2 ⟨σ, Subgroup.mem_zpowers σ⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem primeOrder_perm_fixedPoints_orbit_formula
    {X : Type*} [Finite X] (σ : Equiv.Perm X)
    (hprime : (orderOf σ).Prime) :
    Nat.card X +
        (orderOf σ - 1) * Nat.card (Function.fixedPoints σ) =
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) X) *
        orderOf σ := by
  letI : Fact (orderOf σ).Prime := ⟨hprime⟩
  have h := primeCard_fixedPoints_orbit_formula
    (G := Subgroup.zpowers σ) (X := X) (p := orderOf σ)
    (Fintype.card_zpowers (x := σ))
  have hfixed :
      Fintype.card (MulAction.fixedPoints (Subgroup.zpowers σ) X) =
        Fintype.card (Function.fixedPoints σ) :=
    Fintype.card_congr (permFixedPointsEquivZpowersFixedPoints σ).symm
  rw [hfixed] at h
  simpa only [Nat.card_eq_fintype_card] using h


private def trivialPermFixedPointsEquiv
    (X : Type*) :
    Function.fixedPoints (1 : Equiv.Perm X) ≃ X where
  toFun x := x.1
  invFun x := ⟨x, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl
private noncomputable def trivialPermOrbitQuotientEquiv
    (X : Type*) :
    X ≃ MulAction.orbitRel.Quotient
      (Subgroup.zpowers (1 : Equiv.Perm X)) X where
  toFun x := Quotient.mk'' x
  invFun := Quotient.lift id (by
    intro x y hxy
    change
      MulAction.orbitRel
        (Subgroup.zpowers (1 : Equiv.Perm X)) X x y at hxy
    rw [MulAction.orbitRel_apply] at hxy
    rcases hxy with ⟨g, rfl⟩
    have hgmem :
        (g.1 : Equiv.Perm X) ∈ (⊥ : Subgroup (Equiv.Perm X)) := by
      simpa only [Subgroup.zpowers_one_eq_bot] using g.2
    have hg : (g.1 : Equiv.Perm X) = 1 := Subgroup.mem_bot.mp hgmem
    change g.1 y = y
    rw [hg]
    rfl)
  left_inv x := rfl
  right_inv q := by
    induction q using Quotient.inductionOn
    rfl
private theorem primePow_perm_fixedPoints_orbit_formula
    {p : ℕ} (hp : p.Prime) {X : Type*} [Finite X]
    (σ : Equiv.Perm X) (hpow : σ ^ p = 1) :
    Nat.card X + (p - 1) * Nat.card (Function.fixedPoints σ) =
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) X) * p := by
  have hdvd : orderOf σ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hpow
  rcases (Nat.dvd_prime hp).mp hdvd with horder_one | horder_prime
  · have hσ : σ = 1 := orderOf_eq_one_iff.mp horder_one
    subst σ
    have hfixed :
        Nat.card (Function.fixedPoints (1 : Equiv.Perm X)) = Nat.card X :=
      Nat.card_congr (trivialPermFixedPointsEquiv X)
    have hquot :
        Nat.card
            (MulAction.orbitRel.Quotient
              (Subgroup.zpowers (1 : Equiv.Perm X)) X) =
          Nat.card X :=
      Nat.card_congr (trivialPermOrbitQuotientEquiv X).symm
    rw [hfixed, hquot]
    calc
      Nat.card X + (p - 1) * Nat.card X =
          (1 + (p - 1)) * Nat.card X := by
            rw [Nat.add_mul, one_mul]
      _ = p * Nat.card X := by rw [Nat.add_sub_of_le hp.one_le]
      _ = Nat.card X * p := Nat.mul_comm _ _
  · have h := primeOrder_perm_fixedPoints_orbit_formula σ
      (horder_prime ▸ hp)
    simpa [horder_prime] using h

/-- Permutations whose orders divide the same prime have equally many fixed
points when their finite index types and orbit quotients have equal cardinality. -/
public theorem primePow_perm_fixedPoints_ncard_eq_of_orbitQuotient_card_eq
    {p : ℕ} (hp : p.Prime) {X Y : Type*} [Finite X] [Finite Y]
    (σ : Equiv.Perm X) (τ : Equiv.Perm Y)
    (hσpow : σ ^ p = 1) (hτpow : τ ^ p = 1)
    (hcard : Nat.card X = Nat.card Y)
    (horbit :
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) X) =
        Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers τ) Y)) :
    Nat.card (Function.fixedPoints σ) =
      Nat.card (Function.fixedPoints τ) := by
  have hσ := primePow_perm_fixedPoints_orbit_formula hp σ hσpow
  have hτ := primePow_perm_fixedPoints_orbit_formula hp τ hτpow
  rw [← hcard, ← horbit] at hτ
  have hmul :
      (p - 1) * Nat.card (Function.fixedPoints σ) =
        (p - 1) * Nat.card (Function.fixedPoints τ) :=
    Nat.add_left_cancel (hσ.trans hτ.symm)
  exact Nat.mul_left_cancel (Nat.sub_pos_of_lt hp.one_lt) hmul

private theorem equivariantBasis_pow_apply
    {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Finite ι] (b : Module.Basis ι F V) (T : V ≃ₗ[F] V)
    (σ : Equiv.Perm ι) (hT : ∀ i, T (b i) = b (σ i)) :
    ∀ (n : ℕ) (i : ι), (T ^ n) (b i) = b ((σ ^ n) i) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro i
      rw [pow_succ', pow_succ', LinearEquiv.mul_apply, Equiv.Perm.mul_apply,
        ih i, hT]

/-- A permutation induced by a linear equivalence on a basis satisfies every
power identity satisfied by the linear equivalence. -/
public theorem equivariantBasis_perm_pow_eq_one_of_linearEquiv_pow_eq_one
    {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Finite ι] (b : Module.Basis ι F V) (T : V ≃ₗ[F] V)
    (σ : Equiv.Perm ι) (hT : ∀ i, T (b i) = b (σ i))
    {n : ℕ} (hpow : T ^ n = 1) :
    σ ^ n = 1 := by
  ext i
  apply b.injective
  rw [← equivariantBasis_pow_apply b T σ hT n i, hpow]
  simp

/-- Two finite bases permuted by the same prime-period linear equivalence have
equally many fixed basis vectors. -/
public theorem primePow_equivariantBases_fixedPoints_ncard_eq
    {p : ℕ} (hp : p.Prime)
    {F V ι κ : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Finite ι] [Finite κ]
    (b : Module.Basis ι F V) (c : Module.Basis κ F V)
    (T : V ≃ₗ[F] V) (σ : Equiv.Perm ι) (τ : Equiv.Perm κ)
    (hTσ : ∀ i, T (b i) = b (σ i))
    (hTτ : ∀ j, T (c j) = c (τ j))
    (hpow : T ^ p = 1) :
    Nat.card (Function.fixedPoints σ) =
      Nat.card (Function.fixedPoints τ) := by
  apply primePow_perm_fixedPoints_ncard_eq_of_orbitQuotient_card_eq hp σ τ
  · exact equivariantBasis_perm_pow_eq_one_of_linearEquiv_pow_eq_one
      b T σ hTσ hpow
  · exact equivariantBasis_perm_pow_eq_one_of_linearEquiv_pow_eq_one
      c T τ hTτ hpow
  · rw [← Module.finrank_eq_nat_card_basis b,
      ← Module.finrank_eq_nat_card_basis c]
  · rw [← equivariantBasis_fixedSubmodule_finrank_eq_orbitQuotient_card
        b T σ hTσ,
      ← equivariantBasis_fixedSubmodule_finrank_eq_orbitQuotient_card
        c T τ hTτ]

private noncomputable def permutedBasisInvariantsLinearEquivRespectful
    {F G V iota : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    [Finite iota] [MulAction G iota]
    (rho : Representation F G V) (b : Module.Basis iota F V)
    (hb : forall g : G, forall i : iota, rho g (b i) = b (g • i)) :
    rho.invariants ≃ₗ[F]
      RespectfulFunctions F iota (MulAction.orbitRel G iota) where
  toFun v := ⟨b.equivFun v.1, by
    intro i j hij
    rw [MulAction.orbitRel_apply] at hij
    rcases hij with ⟨g, rfl⟩
    simpa [MulAction.toPerm_apply, v.2 g] using
      (equivariantBasis_equivFun_apply b
        (rho g) (MulAction.toPerm g) (hb g) v.1 j)⟩
  invFun f := ⟨b.equivFun.symm f.1, by
    intro g
    apply b.equivFun.injective
    funext j
    let i : iota := g⁻¹ • j
    have hi : g • i = j := by simp [i]
    have hrel : MulAction.orbitRel G iota (g • i) i := by
      rw [MulAction.orbitRel_apply]
      exact ⟨g, rfl⟩
    calc
      b.equivFun (rho g (b.equivFun.symm f.1)) j =
          b.equivFun (rho g (b.equivFun.symm f.1)) (g • i) := by rw [hi]
      _ = b.equivFun (b.equivFun.symm f.1) i := by
        simpa [MulAction.toPerm_apply] using
          (equivariantBasis_equivFun_apply b
            (rho g) (MulAction.toPerm g)
            (hb g) (b.equivFun.symm f.1) i)
      _ = f.1 i :=
        congrFun (b.equivFun.apply_symm_apply f.1) i
      _ = f.1 (g • i) := (f.2 hrel).symm
      _ = f.1 j := by rw [hi]
      _ = b.equivFun (b.equivFun.symm f.1) j :=
        (congrFun (b.equivFun.apply_symm_apply f.1) j).symm⟩
  left_inv v := by
    ext
    simp
  right_inv f := by
    apply Subtype.ext
    exact b.equivFun.apply_symm_apply f.1
  map_add' v w := by
    ext
    simp
  map_smul' a v := by
    ext
    simp

/-- The invariant subspace of a representation that permutes a finite basis has
dimension equal to the number of orbits of the basis action. -/
public theorem permutedBasis_fixedSubspace_finrank_eq_orbitQuotient_card
    {F G V iota : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    [Finite iota] [MulAction G iota]
    (rho : Representation F G V) (b : Module.Basis iota F V)
    (hb : forall g : G, forall i : iota, rho g (b i) = b (g • i)) :
    Module.finrank F rho.invariants =
      Nat.card (MulAction.orbitRel.Quotient G iota) := by
  rw [LinearEquiv.finrank_eq
    (permutedBasisInvariantsLinearEquivRespectful rho b hb)]
  exact quotientFunctionsLinearEquivRespectful_finrank F iota _
end CFSG.Theory.Representation


