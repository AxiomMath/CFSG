module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (11): the bad-fibre bound (`P × E` / `X × E^g`)

This module formalizes Bender's bad-fibre estimate on lines 859--883 of
`refs/bender-dihedral-sylow.tex` (the paragraph starting
"Take any subgroup `Y` of `X × E^g` not lying in `M`" and ending with
"not more than `((q-1)/p) q` conjugates `Y` of `P` ... satisfy `Q ≠ 1`").

## Source content (L859--883)

Fix a conjugate `X = P^g ⊆ A` of the chosen order-`p` subgroup `P`, the
region `X · E^g`, and `PE = P · E`.  For a subgroup `Y ≤ X · E^g` with
`Y ⊄ M` (equivalently `A ⊄ D := C_{PE}(Y)`) the centralizer
`D = C_{PE}(Y)` has `X` as a Sylow-`p` subgroup and `N_D(X)` has a normal
complement `Q` in `D` with `|Q| | q` (the exceptional `|Q| = 4` case is
excluded by the component-centralizer control
`C_G(⟨t,s⟩) = ⟨t,s⟩B ⊆ M`; that exclusion is part of establishing the
structure hypothesis `hD` below, and is never decided by enumeration).
Consequently `Y` centralizes at most `q` conjugates of `P` in `P × E`,
and symmetrically a minimal `X`-invariant `W ≤ PE` with `|W| | q` is
centralized by at most `q` conjugates of `P` in `X · E^g`.  Since the
number of minimal `X`-invariant subgroups `W ≤ PE` with `|W| | q` is at
most `(q-1)/p` (because `X` normalizes at most two subgroups of order `q`
and `2p = 2|X|` divides `|W^#|`), at most `((q-1)/p) · q` conjugates `Y`
of `P` lying in `X · E^g` but not in `M` satisfy `Q ≠ 1`.

## Formal structure

Following the established pattern of
`secondCase_linearEquation11_orbit_card_of_unique_torus_family`, the
counting argument is proven in full here, while the Section-4/PSL₂
group-theoretic facts asserted by the source in single sentences are
explicit hypotheses:

* `hD` — the per-`Y` structure of `D = C_{PE}(Y)`: `X` is a Sylow-`p`
  subgroup of `D` and `N_D(X)` has a normal complement `Q` with
  `|Q| | q` (this packages the source's "`X` is an `S_p`-subgroup of
  `D` ... normal complement `Q` ... with `|Q|` dividing `q`", including
  the `|Q| = 4` exclusion via the component-centralizer control);
* `hW` — the symmetric structure of `D' = C_{X·E^g}(W)` for the minimal
  `X`-invariant `W`'s (the source's "similarly ... W of P×E not
  centralized by A is centralized by at most q conjugates of P in
  X×E^g"); every minimal `X`-invariant `W` with `|W| | q` fails to lie
  in `C_{PE}(A) = PKS₀` because `PKS₀` has no elements of order dividing
  `q`, so no separate "not centralized by `A`" condition is needed;
* `hWcount` — the bound `(q-1)/p` on the number of minimal
  `X`-invariant `W ≤ PE` with `|W| | q` (the source's "X normalizes at
  most two subgroups of order q in P×E and 2p = 2|X| divides |W^#|").

Everything else — the orbit-count `|{order-p subgroups of D}| =
|D : N_D(X)|` from Sylow's theorems, the complement index identity
`|D : N_D(X)| = |Q|`, the "at most `q`" bounds, the existence of a
minimal `X`-invariant `W ≤ Q_Y` for every bad `Y`, and the final union
bound — is proven here.  The conclusion is exported in the exact shape
consumed by `secondCase_linearEquation11_region_producer` (the `hBad`
hypothesis):

```lean
∀ x : Xs,
  Nat.card {Y : Subgroup G // (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
      Y ≤ R x ∧ Y ≠ X x ∧ ¬ (Y ≤ w.M) ∧
      secondCase_linearEquation11_bad_pred PE q (X x) Y} ≤ ((q - 1) / p) * q
```

with NAT division in `((q - 1) / p) * q`.  No `sorry`/`admit`/`axiom`/
`opaque`/compiled evaluation are used.
-/

noncomputable section

open scoped BigOperators

namespace CFSG.GorensteinWalter

universe u

/-- A finite group has finitely many subgroups. -/
instance (priority := 100) instFiniteSubgroupOfFinite {G : Type u} [Group G] [Finite G] :
    Finite (Subgroup G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  refine Finite.of_injective (fun S : Subgroup G => (S : Set G).toFinset) ?_
  intro S T h
  apply SetLike.ext
  intro x
  have hh : x ∈ (S : Set G).toFinset ↔ x ∈ (T : Set G).toFinset := by
    rw [← Finset.ext_iff.mp h x]
  simpa using hh

/-- `W` is a minimal `X`-invariant subgroup: nontrivial, and the only
`X`-invariant subgroups of `W` are `⊥` and `W`. -/
@[expose] public def MinimalXInvariant {G : Type u} [Group G]
    (X W : Subgroup G) : Prop :=
  W ≠ ⊥ ∧
    (∀ x : G, x ∈ X → ∀ w : G, w ∈ W → x * w * x⁻¹ ∈ W) ∧
    ∀ V : Subgroup G, V ≤ W →
    (∀ x : G, x ∈ X → ∀ v : G, v ∈ V → x * v * x⁻¹ ∈ V) → V = ⊥ ∨ V = W

/-- The family of minimal `X`-invariant subgroups `W ≤ PE` of order
dividing `q` (source: "minimal X-invariant subgroups W of P×E with
|W| dividing q"). -/
@[expose] public def MinimalXInvariantFamily {G : Type u} [Group G]
    (PE : Subgroup G) (q : ℕ) (X : Subgroup G) : Set (Subgroup G) :=
  {W : Subgroup G | W ≤ PE ∧ Nat.card W ∣ q ∧ MinimalXInvariant X W}

/-- The bad-fibre predicate for equation (11) (source L859--883): `Y`
carries a nontrivial normal complement `Q` of `N_D(X)` in
`D = C_{PE}(Y)` of order dividing `q` — the "`Q ≠ 1`" condition.  The
complement structure is part of the predicate so that the counting
theorem needs no uniqueness argument for `Q`. -/
public def secondCase_linearEquation11_bad_pred {G : Type u} [Group G]
    (PE : Subgroup G) (q : ℕ) (X Y : Subgroup G) : Prop :=
  ∃ Q : Subgroup G,
    let D : Subgroup G := Subgroup.centralizer (Y : Set G) ⊓ PE
    IsNormalIn Q D ∧
    D = Q ⊔ (D ⊓ Subgroup.normalizer (X : Set G)) ∧
    Q ⊓ (D ⊓ Subgroup.normalizer (X : Set G)) = ⊥ ∧
    Nat.card Q ∣ q ∧ Q ≠ ⊥

/-- Construct the bad-fibre predicate from an explicit nontrivial normal
complement.  This is the public introduction rule used by the region
uniqueness argument without exposing the predicate's implementation. -/
public theorem secondCase_linearEquation11_bad_pred_mk
    {G : Type u} [Group G]
    (PE : Subgroup G) (q : ℕ) (X Y Q : Subgroup G)
    (hQnormal : IsNormalIn Q (Subgroup.centralizer (Y : Set G) ⊓ PE))
    (hD : Subgroup.centralizer (Y : Set G) ⊓ PE =
      Q ⊔ ((Subgroup.centralizer (Y : Set G) ⊓ PE) ⊓
        Subgroup.normalizer (X : Set G)))
    (hQinter : Q ⊓ ((Subgroup.centralizer (Y : Set G) ⊓ PE) ⊓
      Subgroup.normalizer (X : Set G)) = ⊥)
    (hQcard : Nat.card Q ∣ q) (hQne : Q ≠ ⊥) :
    secondCase_linearEquation11_bad_pred PE q X Y := by
  exact ⟨Q, hQnormal, hD, hQinter, hQcard, hQne⟩

/-- The cardinality of `X` viewed inside `D` is `|X|`, when `X ≤ D`. -/
private lemma natCard_subgroupOf_eq
    {G : Type u} [Group G] [Finite G]
    {D X : Subgroup G} (hXleD : X ≤ D) :
    Nat.card (X.subgroupOf D) = Nat.card X := by
  calc
    Nat.card (X.subgroupOf D) =
        Nat.card ((X.subgroupOf D).map D.subtype) := by
      exact (Subgroup.card_map_of_injective D.subtype_injective).symm
    _ = Nat.card (X ⊓ D : Subgroup G) := by rw [Subgroup.subgroupOf_map_subtype]
    _ = Nat.card X := by rw [inf_eq_left.mpr hXleD]

/-- Every order-`p` subgroup of `D` is a Sylow-`p` subgroup of `D`,
whenever `X ≤ D` is a Sylow-`p` subgroup of order `p`. -/
private lemma orderP_subgroup_isSylow
    {G : Type u} [Group G] [Finite G]
    {D X : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hXleD : X ≤ D) (hXcard : Nat.card X = p)
    (hXidx : ¬ p ∣ (X.subgroupOf D).index) :
    ∀ X' : Subgroup G, X' ≤ D → Nat.card X' = p →
      (IsPGroup p (X'.subgroupOf D) ∧ ¬ p ∣ (X'.subgroupOf D).index) := by
  intro X' hX'leD hX'card
  constructor
  · have hX'sd : Nat.card (X'.subgroupOf D) = p := by
      rw [natCard_subgroupOf_eq hX'leD, hX'card]
    exact IsPGroup.of_card (G := X'.subgroupOf D) (p := p) (n := 1)
      (by simpa using hX'sd)
  · -- the two indices agree because the two divisors agree
    have hXidx' : (X'.subgroupOf D).index = Nat.card D / Nat.card (X'.subgroupOf D) := by
      exact (Nat.div_eq_of_eq_mul_right
        (Nat.card_pos (α := X'.subgroupOf D))
        (by simpa [Subgroup.index_eq_card, mul_comm] using
          (Subgroup.card_mul_index (X'.subgroupOf D)).symm)).symm
    have hXidx0 : (X.subgroupOf D).index = Nat.card D / Nat.card (X.subgroupOf D) := by
      exact (Nat.div_eq_of_eq_mul_right
        (Nat.card_pos (α := X.subgroupOf D))
        (by simpa [Subgroup.index_eq_card, mul_comm] using
          (Subgroup.card_mul_index (X.subgroupOf D)).symm)).symm
    have hsame : (X'.subgroupOf D).index = (X.subgroupOf D).index := by
      rw [hXidx', hXidx0]
      congr 1
      rw [natCard_subgroupOf_eq hX'leD, hX'card, natCard_subgroupOf_eq hXleD, hXcard]
    rwa [hsame]

/-- Order-`p` subgroups of `D` are in bijection with Sylow-`p` subgroups
of `D`, when `X ≤ D` is a Sylow-`p` subgroup of order `p`. -/
private noncomputable def orderP_subgroups_equiv_sylow
    {G : Type u} [Group G] [Finite G]
    {D X : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hXleD : X ≤ D) (hXcard : Nat.card X = p)
    (hXidx : ¬ p ∣ (X.subgroupOf D).index) :
    {X' : Subgroup G // X' ≤ D ∧ Nat.card X' = p} ≃ Sylow p D := by
  classical
  have hXpg : IsPGroup p (X.subgroupOf D) := by
    have hXsd : Nat.card (X.subgroupOf D) = p := by
      rw [natCard_subgroupOf_eq hXleD, hXcard]
    exact IsPGroup.of_card (G := X.subgroupOf D) (p := p) (n := 1)
      (by simpa using hXsd)
  let S₀ : Sylow p D := IsPGroup.toSylow hXpg hXidx
  have hS0 : (S₀ : Subgroup D) = X.subgroupOf D := by
    simp [S₀]
  have hpgOf : ∀ X' : Subgroup G, X' ≤ D → Nat.card X' = p →
      IsPGroup p (X'.subgroupOf D) := by
    intro X' hX'leD hX'card
    have hX'sd : Nat.card (X'.subgroupOf D) = p := by
      rw [natCard_subgroupOf_eq hX'leD, hX'card]
    exact IsPGroup.of_card (G := X'.subgroupOf D) (p := p) (n := 1)
      (by simpa using hX'sd)
  have hidxOf : ∀ X' : Subgroup G, X' ≤ D → Nat.card X' = p →
      ¬ p ∣ (X'.subgroupOf D).index := by
    intro X' hX'leD hX'card
    exact (orderP_subgroup_isSylow hXleD hXcard hXidx X' hX'leD hX'card).2
  let toS : {X' : Subgroup G // X' ≤ D ∧ Nat.card X' = p} → Sylow p D := fun X' =>
    IsPGroup.toSylow (hpgOf X'.1 X'.2.1 X'.2.2) (hidxOf X'.1 X'.2.1 X'.2.2)
  -- the inverse: a Sylow-`p` subgroup of `D` has order `p`
  have hcardS : ∀ S : Sylow p D, Nat.card (S : Subgroup D) = p := by
    intro S
    have hEq : (S : Subgroup D) ≃* (S₀ : Subgroup D) := Sylow.equiv S S₀
    calc
      Nat.card (S : Subgroup D) = Nat.card (S₀ : Subgroup D) := by
        exact Nat.card_congr hEq.toEquiv
      _ = Nat.card (X.subgroupOf D) := by rw [hS0]
      _ = Nat.card X := natCard_subgroupOf_eq hXleD
      _ = p := hXcard
  let froS : Sylow p D → {X' : Subgroup G // X' ≤ D ∧ Nat.card X' = p} := fun S =>
    ⟨(S : Subgroup D).map D.subtype, Subgroup.map_subtype_le (S : Subgroup D),
      by
        calc
          Nat.card ((S : Subgroup D).map D.subtype) =
              Nat.card (S : Subgroup D) :=
            Subgroup.card_map_of_injective D.subtype_injective
          _ = p := hcardS S⟩
  refine Equiv.ofBijective toS ?_
  constructor
  · -- injective
    intro X' X'' h
    apply Subtype.ext
    have hsub : X'.1.subgroupOf D = X''.1.subgroupOf D := by
      have hc := congrArg (fun S : Sylow p D => (S : Subgroup D)) h
      simpa [toS] using hc
    apply Subgroup.ext
    intro z
    have hz1 : z ∈ X'.1 ↔ z ∈ (X'.1.subgroupOf D).map D.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr X'.2.1]
    have hz2 : z ∈ X''.1 ↔ z ∈ (X''.1.subgroupOf D).map D.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr X''.2.1]
    rw [hz1, hz2, hsub]
  · -- surjective
    intro S
    refine ⟨froS S, ?_⟩
    apply Sylow.ext
    have hunder : (((S : Subgroup D).map D.subtype).subgroupOf D) = (S : Subgroup D) := by
      ext d
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hd
        rcases Subgroup.mem_map.mp hd with ⟨s, hs, hds⟩
        have hs' : s = d := D.subtype_injective hds
        rw [← hs']
        exact hs
      · intro hd
        apply Subgroup.mem_map.mpr
        refine ⟨d, hd, ?_⟩
        rfl
    simpa [toS, froS] using hunder

/-- The normalizer of `X` inside `D` is `D ∩ N_G(X)`, as subgroups of
`D`. -/
private lemma normalizer_subgroupOf_eq_inf_normalizer
    {G : Type u} [Group G] {D X : Subgroup G} (hXleD : X ≤ D) :
    Subgroup.normalizer (X.subgroupOf D : Set D) =
      (D ⊓ Subgroup.normalizer (X : Set G)).subgroupOf D := by
  have hXmap : (X.subgroupOf D).map D.subtype = X := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXleD]
  have hconv : ∀ d : D, D.subtype.comp (MulAut.conj d).toMonoidHom =
      (MulAut.conj (d : G)).toMonoidHom.comp D.subtype := by
    intro d
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have htransfer : ∀ d : D,
      (X.subgroupOf D).map (MulAut.conj d).toMonoidHom = X.subgroupOf D ↔
        X.map (MulAut.conj (d : G)).toMonoidHom = X := by
    intro d
    have hleft : ((X.subgroupOf D).map (MulAut.conj d).toMonoidHom = X.subgroupOf D) ↔
        (((X.subgroupOf D).map (MulAut.conj d).toMonoidHom).map D.subtype =
          (X.subgroupOf D).map D.subtype) := by
      constructor
      · intro h
        rw [h]
      · intro h
        exact Subgroup.map_injective D.subtype_injective h
    have hsimpl : ((X.subgroupOf D).map (MulAut.conj d).toMonoidHom).map D.subtype =
        X.map (MulAut.conj (d : G)).toMonoidHom := by
      calc
        ((X.subgroupOf D).map (MulAut.conj d).toMonoidHom).map D.subtype =
            (X.subgroupOf D).map (D.subtype.comp (MulAut.conj d).toMonoidHom) := by
          rw [Subgroup.map_map]
        _ = (X.subgroupOf D).map ((MulAut.conj (d : G)).toMonoidHom.comp D.subtype) := by
          rw [hconv d]
        _ = ((X.subgroupOf D).map D.subtype).map (MulAut.conj (d : G)).toMonoidHom := by
          rw [Subgroup.map_map]
        _ = X.map (MulAut.conj (d : G)).toMonoidHom := by rw [hXmap]
    rw [hleft, hsimpl, hXmap]
  ext d
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hd
    refine ⟨d.2, ?_⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (htransfer d).1 (Subgroup.mem_normalizer_iff_map_conj_eq.mp hd)
  · intro hd
    rcases hd with ⟨hd1, hd2⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (htransfer d).2 (Subgroup.mem_normalizer_iff_map_conj_eq.mp hd2)

/-- The orbit-count: the number of order-`p` subgroups of `D` equals the
index of the normalizer `D ∩ N_G(X)` of `X` in `D`, when `X` is a
Sylow-`p` subgroup of `D` of order `p`. -/
private lemma natCard_orderP_subgroups_eq_index_of_sylow
    {G : Type u} [Group G] [Finite G]
    {D X : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hXleD : X ≤ D) (hXcard : Nat.card X = p)
    (hXidx : ¬ p ∣ (X.subgroupOf D).index) :
    Nat.card {X' : Subgroup G // X' ≤ D ∧ Nat.card X' = p} =
      ((D ⊓ Subgroup.normalizer (X : Set G)).subgroupOf D).index := by
  classical
  have hEq := orderP_subgroups_equiv_sylow (D := D) (X := X) (p := p) hXleD hXcard hXidx
  have hXpg : IsPGroup p (X.subgroupOf D) := by
    have hXsd : Nat.card (X.subgroupOf D) = p := by
      rw [natCard_subgroupOf_eq hXleD, hXcard]
    exact IsPGroup.of_card (G := X.subgroupOf D) (p := p) (n := 1)
      (by simpa using hXsd)
  let S₀ : Sylow p D := IsPGroup.toSylow hXpg hXidx
  have hS0 : (S₀ : Subgroup D) = X.subgroupOf D := by
    simp [S₀]
  calc
    Nat.card {X' : Subgroup G // X' ≤ D ∧ Nat.card X' = p} = Nat.card (Sylow p D) := by
      exact Nat.card_congr hEq
    _ = Nat.card (D ⧸ Subgroup.normalizer (S₀ : Set D)) := by
      exact Nat.card_congr (Sylow.equivQuotientNormalizer S₀)
    _ = (Subgroup.normalizer (S₀ : Set D)).index := (Subgroup.index_eq_card _).symm
    _ = (Subgroup.normalizer (X.subgroupOf D : Set D)).index := by
      have hS0' : (S₀ : Set D) = (X.subgroupOf D : Set D) := by
        calc
          (S₀ : Set D) = (S₀ : Subgroup D) := (Sylow.coe_coe S₀).symm
          _ = X.subgroupOf D := by
            exact congrArg (fun H : Subgroup D => (H : Set D)) hS0
      rw [hS0']
    _ = ((D ⊓ Subgroup.normalizer (X : Set G)).subgroupOf D).index := by
      congr 1
      exact normalizer_subgroupOf_eq_inf_normalizer (D := D) (X := X) hXleD

/-- If `D = Q · N` with `Q ◁ D` and `Q ∩ N = ⊥`, then `|D : N| = |Q|`. -/
private lemma index_eq_natCard_of_normal_complement
    {G : Type u} [Group G] [Finite G]
    {D Q N : Subgroup G}
    (hQleD : Q ≤ D) (hNleD : N ≤ D)
    (hD : D = Q ⊔ N) (hQN : Q ⊓ N = ⊥)
    (hQnormal : IsNormalIn Q D) :
    (N.subgroupOf D).index = Nat.card Q := by
  classical
  -- (1) the multiplication map Q × N → D is bijective, so |D| = |Q|·|N|
  let φ : Q × N → D := fun qn => ⟨(qn.1 : G) * (qn.2 : G), D.mul_mem (hQleD qn.1.2) (hNleD qn.2.2)⟩
  have hφinj : Function.Injective φ := by
    intro a b h
    have hG : (a.1 : G) * (a.2 : G) = (b.1 : G) * (b.2 : G) := by
      exact congrArg Subtype.val h
    have hqn : (b.1 : G)⁻¹ * (a.1 : G) = (b.2 : G) * (a.2 : G)⁻¹ := by
      calc
        (b.1 : G)⁻¹ * (a.1 : G) =
            (b.1 : G)⁻¹ * ((a.1 : G) * (a.2 : G)) * (a.2 : G)⁻¹ := by group
        _ = (b.1 : G)⁻¹ * ((b.1 : G) * (b.2 : G)) * (a.2 : G)⁻¹ := by rw [hG]
        _ = (b.2 : G) * (a.2 : G)⁻¹ := by group
    have hqN : (b.1 : G)⁻¹ * (a.1 : G) ∈ Q ⊓ N := by
      rw [Subgroup.mem_inf]
      constructor
      · exact Q.mul_mem (Q.inv_mem b.1.2) a.1.2
      · rw [hqn]
        exact N.mul_mem b.2.2 (N.inv_mem a.2.2)
    have h1 : (b.1 : G)⁻¹ * (a.1 : G) = 1 := by
      rw [hQN] at hqN
      exact Subgroup.mem_bot.mp hqN
    have hab : (a.1 : G) = (b.1 : G) := by
      calc
        (a.1 : G) = (b.1 : G) * ((b.1 : G)⁻¹ * (a.1 : G)) := by group
        _ = (b.1 : G) * 1 := by rw [h1]
        _ = (b.1 : G) := by simp
    have h2 : (b.2 : G) * (a.2 : G)⁻¹ = 1 := by
      exact hqn.symm.trans h1
    have han : (a.2 : G) = (b.2 : G) := by
      calc
        (a.2 : G) = ((a.2 : G)⁻¹)⁻¹ := by simp
        _ = ((b.2 : G)⁻¹)⁻¹ := by
          congr 1
          calc
            (a.2 : G)⁻¹ = (b.2 : G)⁻¹ * ((b.2 : G) * (a.2 : G)⁻¹) := by group
            _ = (b.2 : G)⁻¹ * 1 := by rw [h2]
            _ = (b.2 : G)⁻¹ := by simp
        _ = (b.2 : G) := by simp
    apply Prod.ext
    · apply Subtype.ext
      exact hab
    · apply Subtype.ext
      exact han
  have hφsurj : Function.Surjective φ := by
    intro d
    -- S := Q·N (pointwise) is a subgroup, and Q ⊔ N = S
    let S : Subgroup G :=
      { carrier := {g : G | ∃ q : G, q ∈ Q ∧ ∃ n : G, n ∈ N ∧ g = q * n}
        one_mem' := by
          refine ⟨1, Q.one_mem, 1, N.one_mem, ?_⟩
          simp
        mul_mem' := by
          intro g h' hg hh'
          rcases hg with ⟨q1, hq1, n1, hn1, rfl⟩
          rcases hh' with ⟨q2, hq2, n2, hn2, rfl⟩
          refine ⟨q1 * (n1 * q2 * n1⁻¹), ?_, n1 * n2, ?_, ?_⟩
          · exact Q.mul_mem hq1 (hQnormal.2 n1 (hNleD hn1) q2 hq2)
          · exact N.mul_mem hn1 hn2
          · group
        inv_mem' := by
          intro g hg
          rcases hg with ⟨q, hq, n, hn, rfl⟩
          refine ⟨n⁻¹ * q⁻¹ * n, ?_, n⁻¹, ?_, ?_⟩
          · simpa using (hQnormal.2 n⁻¹ (hNleD (N.inv_mem hn)) q⁻¹ (Q.inv_mem hq))
          · exact N.inv_mem hn
          · group }
    have hSup : Q ⊔ N = S := by
      apply le_antisymm
      · exact sup_le (by
          intro q hq
          refine ⟨q, hq, 1, N.one_mem, ?_⟩
          simp) (by
          intro n hn
          refine ⟨1, Q.one_mem, n, hn, ?_⟩
          simp)
      · intro g hg
        rcases hg with ⟨q, hq, n, hn, rfl⟩
        exact (Q ⊔ N).mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hn)
    have hdS : (d : G) ∈ S := by
      rw [← hSup, ← hD]
      exact d.2
    rcases hdS with ⟨q, hq, n, hn, hd⟩
    refine ⟨(⟨q, hq⟩, ⟨n, hn⟩), ?_⟩
    apply Subtype.ext
    exact hd.symm
  have hDcard : Nat.card D = Nat.card Q * Nat.card N := by
    calc
      Nat.card D = Nat.card (Q × N) :=
        Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩).symm
      _ = Nat.card Q * Nat.card N := Nat.card_prod Q N
  -- (2) index of N in D equals |D| / |N| = |Q|
  have hNsub : Nat.card (N.subgroupOf D) = Nat.card N := by
    calc
      Nat.card (N.subgroupOf D) = Nat.card ((N.subgroupOf D).map D.subtype) := by
        exact (Subgroup.card_map_of_injective D.subtype_injective).symm
      _ = Nat.card (N ⊓ D : Subgroup G) := by rw [Subgroup.subgroupOf_map_subtype]
      _ = Nat.card N := by rw [inf_eq_left.mpr hNleD]
  have hindex : (N.subgroupOf D).index = Nat.card D / Nat.card (N.subgroupOf D) := by
    exact (Nat.div_eq_of_eq_mul_right
      (Nat.card_pos (α := N.subgroupOf D))
      (by simpa [Subgroup.index_eq_card, mul_comm] using
        (Subgroup.card_mul_index (N.subgroupOf D)).symm)).symm
  calc
    (N.subgroupOf D).index = Nat.card D / Nat.card (N.subgroupOf D) := hindex
    _ = Nat.card D / Nat.card N := by rw [hNsub]
    _ = (Nat.card Q * Nat.card N) / Nat.card N := by rw [hDcard]
    _ = Nat.card Q := by
      rw [Nat.mul_comm]
      exact Nat.mul_div_right (Nat.card Q) (Nat.card_pos (α := N))

/-- `S` is centralized by at most `q` conjugates of `P` (the source's
"In particular ... at most `q` conjugates", used both for `Y` in
`P × E` and for the minimal `W`'s in `X · E^g`). -/
private lemma orderP_subgroups_of_centralizer_le_q
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G) (q p : ℕ) [Fact p.Prime]
    (hq : 7 ≤ q) (hPcard : Nat.card P = p)
    (H0 : Subgroup G) (X : Subgroup G) (hXcard : Nat.card X = p)
    (S : Set G)
    (D : Subgroup G) (hD : D = Subgroup.centralizer S ⊓ H0)
    (hXleD : X ≤ D) (hXidx : ¬ p ∣ (X.subgroupOf D).index)
    (hDcomp : ∃ Q : Subgroup G, IsNormalIn Q D ∧
        D = Q ⊔ (D ⊓ Subgroup.normalizer (X : Set G)) ∧
        Q ⊓ (D ⊓ Subgroup.normalizer (X : Set G)) = ⊥ ∧ Nat.card Q ∣ q) :
    Nat.card {X' : Subgroup G // (∃ g : G, X' = P.map (MulAut.conj g).toMonoidHom) ∧
        X' ≤ Subgroup.centralizer S ∧ X' ≤ H0} ≤ q := by
  classical
  have hcnt := natCard_orderP_subgroups_eq_index_of_sylow (D := D) (X := X) (p := p)
    hXleD hXcard hXidx
  have hinj : Function.Injective
      (fun X' : {X' : Subgroup G // (∃ g : G, X' = P.map (MulAut.conj g).toMonoidHom) ∧
          X' ≤ Subgroup.centralizer S ∧ X' ≤ H0} =>
        (⟨X'.1, by
          rw [hD]
          exact le_inf X'.2.2.1 X'.2.2.2, by
          rcases X'.2.1 with ⟨g, hg⟩
          rw [hg]
          exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hPcard⟩ :
          {X' : Subgroup G // X' ≤ D ∧ Nat.card X' = p})) := by
    intro X' Y h
    apply Subtype.ext
    simpa using (congrArg (fun Z : {X' : Subgroup G // X' ≤ D ∧ Nat.card X' = p} => Z.1) h)
  have hle : Nat.card {X' : Subgroup G // (∃ g : G, X' = P.map (MulAut.conj g).toMonoidHom) ∧
        X' ≤ Subgroup.centralizer S ∧ X' ≤ H0} ≤
      Nat.card {X' : Subgroup G // X' ≤ D ∧ Nat.card X' = p} :=
    Nat.card_le_card_of_injective _ hinj
  rcases hDcomp with ⟨Q, hQnorm, hQD, hQN, hQdq⟩
  have hindex : ((D ⊓ Subgroup.normalizer (X : Set G)).subgroupOf D).index = Nat.card Q :=
    index_eq_natCard_of_normal_complement (D := D) (Q := Q) (N := D ⊓ Subgroup.normalizer (X : Set G))
      hQnorm.1 inf_le_left hQD hQN hQnorm
  have hQle : Nat.card Q ≤ q := Nat.le_of_dvd (by omega) hQdq
  calc
    Nat.card {X' : Subgroup G // (∃ g : G, X' = P.map (MulAut.conj g).toMonoidHom) ∧
        X' ≤ Subgroup.centralizer S ∧ X' ≤ H0} ≤
        Nat.card {X' : Subgroup G // X' ≤ D ∧ Nat.card X' = p} := hle
    _ = ((D ⊓ Subgroup.normalizer (X : Set G)).subgroupOf D).index := hcnt
    _ = Nat.card Q := hindex
    _ ≤ q := hQle

/-- Every nontrivial `X`-invariant subgroup `Q` of a group containing `X`
contains a minimal `X`-invariant subgroup `W` of order dividing `|Q|`. -/
private lemma exists_minimalXInvariant_le_of_normal_complement
    {G : Type u} [Group G] [Finite G]
    (D Q X : Subgroup G)
    (hQnormal : IsNormalIn Q D) (hQne : Q ≠ ⊥) (hXleD : X ≤ D) :
    ∃ W : Subgroup G, W ≤ Q ∧ MinimalXInvariant X W ∧ Nat.card W ∣ Nat.card Q := by
  classical
  let F : Set (Subgroup G) := {V : Subgroup G | V ≤ Q ∧ V ≠ ⊥ ∧
    ∀ x : G, x ∈ X → ∀ v : G, v ∈ V → x * v * x⁻¹ ∈ V}
  have hFQ : Q ∈ F := by
    refine ⟨le_rfl, hQne, ?_⟩
    intro x hx v hv
    exact hQnormal.2 x (hXleD hx) v hv
  have hFn : ∃ n : ℕ, ∃ V : Subgroup G, V ∈ F ∧ Nat.card V = n :=
    ⟨Nat.card Q, Q, hFQ, rfl⟩
  let m : ℕ := Nat.find hFn
  have hm : ∃ V : Subgroup G, V ∈ F ∧ Nat.card V = m := Nat.find_spec hFn
  let W : Subgroup G := Classical.choose hm
  have hWspec : W ∈ F ∧ Nat.card W = m := Classical.choose_spec hm
  refine ⟨W, hWspec.1.1, ?_, ?_⟩
  · refine ⟨hWspec.1.2.1, hWspec.1.2.2, ?_⟩
    intro V hVleW hVinv
    by_cases hV : V = ⊥
    · exact Or.inl hV
    · right
      have hVF : V ∈ F := ⟨le_trans hVleW hWspec.1.1, hV, hVinv⟩
      have hmV : m ≤ Nat.card V := Nat.find_min' hFn ⟨V, hVF, rfl⟩
      have hVcard : Nat.card V = m := by
        apply le_antisymm
        · exact le_trans (Subgroup.card_le_of_le hVleW) (le_of_eq hWspec.2)
        · exact hmV
      exact Subgroup.eq_of_le_of_card_ge hVleW (by rw [hWspec.2, hVcard])
  · exact Subgroup.card_dvd_of_le hWspec.1.1

/-- A map with fibres of size at most `q` gives the product bound
`|A| ≤ |B| · q`. -/
private lemma natCard_le_mul_of_fiber_le
    {A B : Type u} [Finite A] [Finite B]
    (f : A → B) {q : ℕ}
    (hf : ∀ b : B, Nat.card {a : A // f a = b} ≤ q) :
    Nat.card A ≤ Nat.card B * q := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  calc
    Nat.card A = Nat.card (Σ b : B, {a : A // f a = b}) := by
      exact (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ b : B, Nat.card {a : A // f a = b} := Nat.card_sigma
    _ ≤ ∑ b : B, q := Finset.sum_le_sum (by intro b hb; exact hf b)
    _ = Nat.card B * q := by simp [Nat.card_eq_fintype_card]

/-- The source's "In particular, Y centralizes at most q conjugates of P
in P×E" (L870--873): from the per-`Y` structure of
`D = C_{PE}(Y)` (`X` a Sylow-`p` subgroup, normal complement of order
dividing `q`), at most `q` conjugates of `P` lying in `PE` centralize
`Y`. -/
private lemma centralized_conjugates_le_q
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G) (q p : ℕ) [Fact p.Prime]
    (hq : 7 ≤ q) (hPcard : Nat.card P = p)
    (PE : Subgroup G) (X Y : Subgroup G) (hXcard : Nat.card X = p)
    (hXleD : X ≤ Subgroup.centralizer (Y : Set G) ⊓ PE)
    (hXidx : ¬ p ∣ (X.subgroupOf (Subgroup.centralizer (Y : Set G) ⊓ PE)).index)
    (hDcomp : ∃ Q : Subgroup G, IsNormalIn Q (Subgroup.centralizer (Y : Set G) ⊓ PE) ∧
        Subgroup.centralizer (Y : Set G) ⊓ PE = Q ⊔
          ((Subgroup.centralizer (Y : Set G) ⊓ PE) ⊓ Subgroup.normalizer (X : Set G)) ∧
        Q ⊓ ((Subgroup.centralizer (Y : Set G) ⊓ PE) ⊓ Subgroup.normalizer (X : Set G)) = ⊥ ∧
        Nat.card Q ∣ q) :
    Nat.card {X' : Subgroup G // (∃ g : G, X' = P.map (MulAut.conj g).toMonoidHom) ∧
        X' ≤ Subgroup.centralizer (Y : Set G) ∧ X' ≤ PE} ≤ q := by
  exact orderP_subgroups_of_centralizer_le_q P q p hq hPcard PE X hXcard (Y : Set G)
    (Subgroup.centralizer (Y : Set G) ⊓ PE) rfl hXleD hXidx hDcomp

/-- The bad-fibre bound for equation (11) (source L859--883): at most
`((q-1)/p) · q` conjugates `Y` of `P` lying in the region `R x` but not
in `M` satisfy `Q ≠ 1` (`secondCase_linearEquation11_bad_pred`).  The
three structural hypotheses `hD`, `hW`, `hWcount` package the Section-4
group-theoretic facts asserted by the source (see the module docstring);
everything else is proven here.  The conclusion is exactly the `hBad`
shape consumed by `secondCase_linearEquation11_region_producer`. -/
public theorem secondCase_linearEquation11_badFiber_count
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (P : Subgroup G) (q p : ℕ) [Fact p.Prime]
    (hq : 7 ≤ q) (hPcard : Nat.card P = p)
    (Xs : Type u) [Fintype Xs] [DecidableEq Xs]
    (X : Xs → Subgroup G) (R : Xs → Subgroup G)
    (PE : Subgroup G)
    (hD : ∀ x : Xs, ∀ Y : Subgroup G,
        (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) →
        Y ≤ R x → ¬ Y ≤ w.M →
        (let D : Subgroup G := Subgroup.centralizer (Y : Set G) ⊓ PE
        X x ≤ D ∧ ¬ p ∣ ((X x).subgroupOf D).index ∧
          ∃ Q : Subgroup G, IsNormalIn Q D ∧
            D = Q ⊔ (D ⊓ Subgroup.normalizer (X x : Set G)) ∧
            Q ⊓ (D ⊓ Subgroup.normalizer (X x : Set G)) = ⊥ ∧
            Nat.card Q ∣ q))
    (hW : ∀ x : Xs, ∀ W Y : Subgroup G,
        W ≤ PE → Nat.card W ∣ q → MinimalXInvariant (X x) W →
        (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) →
        Y ≤ R x → Y ≤ Subgroup.centralizer (W : Set G) →
        (let D : Subgroup G := Subgroup.centralizer (W : Set G) ⊓ R x
        Y ≤ D ∧ ¬ p ∣ (Y.subgroupOf D).index ∧
          ∃ Q : Subgroup G, IsNormalIn Q D ∧
            D = Q ⊔ (D ⊓ Subgroup.normalizer (Y : Set G)) ∧
            Q ⊓ (D ⊓ Subgroup.normalizer (Y : Set G)) = ⊥ ∧
            Nat.card Q ∣ q))
    (hWcount : ∀ x : Xs,
        Nat.card (MinimalXInvariantFamily PE q (X x)) ≤ (q - 1) / p) :
    ∀ x : Xs,
      Nat.card {Y : Subgroup G // (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
          Y ≤ R x ∧ Y ≠ X x ∧ ¬ (Y ≤ w.M) ∧
          secondCase_linearEquation11_bad_pred PE q (X x) Y} ≤
        ((q - 1) / p) * q := by
  classical
  intro x
  let A : Set (Subgroup G) := {Y : Subgroup G | (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
      Y ≤ R x ∧ Y ≠ X x ∧ ¬ (Y ≤ w.M) ∧
      secondCase_linearEquation11_bad_pred PE q (X x) Y}
  let Fam : Set (Subgroup G) := MinimalXInvariantFamily PE q (X x)
  -- every bad Y carries a minimal X-invariant W ≤ Q_Y of order dividing q
  have hWY : ∀ Y : Subgroup G, Y ∈ A →
      ∃ W : Subgroup G, W ≤ PE ∧ Nat.card W ∣ q ∧ MinimalXInvariant (X x) W ∧
        Y ≤ Subgroup.centralizer (W : Set G) := by
    intro Y hY
    rcases hY with ⟨hYconj, hYleR, hYne, hYnotM, hYbad⟩
    rcases hYbad with ⟨Q, hQnorm, hQD, hQN, hQdq, hQne⟩
    have hDX := hD x Y hYconj hYleR hYnotM
    have hXleD : X x ≤ Subgroup.centralizer (Y : Set G) ⊓ PE := hDX.1
    rcases exists_minimalXInvariant_le_of_normal_complement
        (Subgroup.centralizer (Y : Set G) ⊓ PE) Q (X x) hQnorm hQne hXleD with
      ⟨W, hWleQ, hWmin, hWQ⟩
    refine ⟨W, ?_, ?_, hWmin, ?_⟩
    · exact le_trans hWleQ (le_trans hQnorm.1 inf_le_right)
    · exact dvd_trans hWQ hQdq
    · have hWleC : W ≤ Subgroup.centralizer (Y : Set G) :=
        le_trans hWleQ (le_trans hQnorm.1 inf_le_left)
      exact (Subgroup.le_centralizer_iff).mpr hWleC
  -- the map from bad Y's to their minimal W's
  let f : {Y : Subgroup G // Y ∈ A} → {W : Subgroup G // W ∈ Fam} := fun Y =>
    let h := hWY Y.1 Y.2
    ⟨Classical.choose h, ⟨(Classical.choose_spec h).1, (Classical.choose_spec h).2.1,
      (Classical.choose_spec h).2.2.1⟩⟩
  -- the fibres of f have size at most q
  have hfiber : ∀ W₀ : {W : Subgroup G // W ∈ Fam},
      Nat.card {Y : {Y0 : Subgroup G // Y0 ∈ A} // f Y = W₀} ≤ q := by
    intro W₀
    let Fib : Type u := {Y : {Y0 : Subgroup G // Y0 ∈ A} // f Y = W₀}
    by_cases hFib : Nonempty Fib
    · let Y₀ : Fib := Classical.choice hFib
      have hY₀conj : ∃ g : G, Y₀.1.1 = P.map (MulAut.conj g).toMonoidHom :=
        Y₀.1.2.1
      have hY₀leR : Y₀.1.1 ≤ R x := Y₀.1.2.2.1
      have hY₀cent : Y₀.1.1 ≤ Subgroup.centralizer (W₀.1 : Set G) := by
        let WY : Subgroup G := Classical.choose (hWY Y₀.1.1 Y₀.1.2)
        have hYchosen : WY = W₀.1 := by
          simpa [f, WY] using congrArg Subtype.val Y₀.2
        have hYc : Y₀.1.1 ≤ Subgroup.centralizer (WY : Set G) := by
          simpa [WY] using (Classical.choose_spec (hWY Y₀.1.1 Y₀.1.2)).2.2.2
        simpa [hYchosen] using hYc
      have hY₀card : Nat.card Y₀.1.1 = p := by
        rcases hY₀conj with ⟨g, hg⟩
        rw [hg]
        exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hPcard
      have hW0 : Y₀.1.1 ≤ Subgroup.centralizer (W₀.1 : Set G) ⊓ R x ∧
          ¬ p ∣ (Y₀.1.1.subgroupOf
            (Subgroup.centralizer (W₀.1 : Set G) ⊓ R x)).index ∧
          ∃ Q : Subgroup G,
            IsNormalIn Q (Subgroup.centralizer (W₀.1 : Set G) ⊓ R x) ∧
            Subgroup.centralizer (W₀.1 : Set G) ⊓ R x = Q ⊔
              ((Subgroup.centralizer (W₀.1 : Set G) ⊓ R x) ⊓
                Subgroup.normalizer (Y₀.1.1 : Set G)) ∧
            Q ⊓ ((Subgroup.centralizer (W₀.1 : Set G) ⊓ R x) ⊓
                Subgroup.normalizer (Y₀.1.1 : Set G)) = ⊥ ∧
            Nat.card Q ∣ q := by
        simpa using (hW x W₀.1 Y₀.1.1 W₀.2.1 W₀.2.2.1 W₀.2.2.2
          hY₀conj hY₀leR hY₀cent)
      have hSle : Nat.card {Y : Subgroup G //
          (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
          Y ≤ Subgroup.centralizer (W₀.1 : Set G) ∧ Y ≤ R x} ≤ q := by
        exact orderP_subgroups_of_centralizer_le_q P q p hq hPcard
          (R x) Y₀.1.1 hY₀card (W₀.1 : Set G)
          (Subgroup.centralizer (W₀.1 : Set G) ⊓ R x) rfl
          hW0.1 hW0.2.1 hW0.2.2
      have hinj : Function.Injective
          (fun Y : Fib =>
            (⟨Y.1.1, Y.1.2.1, by
              let WY : Subgroup G := Classical.choose (hWY Y.1.1 Y.1.2)
              have hYchosen : WY = W₀.1 := by
                simpa [f, WY, Fib] using congrArg Subtype.val Y.2
              have hYc : Y.1.1 ≤ Subgroup.centralizer (WY : Set G) := by
                simpa [WY] using
                  (Classical.choose_spec (hWY Y.1.1 Y.1.2)).2.2.2
              simpa [hYchosen] using hYc, Y.1.2.2.1⟩ :
              {Y : Subgroup G //
                (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
                Y ≤ Subgroup.centralizer (W₀.1 : Set G) ∧ Y ≤ R x})) := by
        intro Y Z h
        apply Subtype.ext
        apply Subtype.ext
        simpa using congrArg
          (fun W : {Y : Subgroup G //
            (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
            Y ≤ Subgroup.centralizer (W₀.1 : Set G) ∧ Y ≤ R x} => W.1) h
      exact le_trans (Nat.card_le_card_of_injective _ hinj) hSle
    · have : IsEmpty Fib := ⟨fun Y => hFib ⟨Y⟩⟩
      have hz : Nat.card Fib = 0 := Nat.card_eq_zero.mpr (Or.inl inferInstance)
      simpa [Fib, hz]
  -- the union bound
  change Nat.card {Y : Subgroup G // Y ∈ A} ≤ ((q - 1) / p) * q
  exact le_trans (natCard_le_mul_of_fiber_le f hfiber) (Nat.mul_le_mul_right q (hWcount x))

end CFSG.GorensteinWalter
