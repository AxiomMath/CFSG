/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.OrbitalGraph
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Index

/-!
# Isaacs, Finite Group Theory — Ch. 8: subdegrees (Thm 8.37, 8.38, Lem 8.39)

Formalizes **Isaacs Thm 8.37** (p. 246): if `G` acts primitively on `Ω`
with subdegrees `1 = m₁ ≤ m₂ ≤ ⋯ ≤ m_r`, then `m_{i+1} ≤ m₂ · m_i`;
**Isaacs Lem 8.39** (p. 248) — the "arrow" index arithmetic, clauses
(a), (b) (`relIndex_le_and_dvd_of_coprime`) and (c)
(`mul_subset_mul_of_coprime`); **Isaacs Thm 8.38** (p. 247, Weiss) — a
subdegree coprime to the largest subdegree is `1`
(`subdegree_eq_one_of_coprime_of_max`); and **Isaacs Thm 8.40**
(p. 248, Manning).

We state the gap form (`subdegree_gap_le`): if `s ≥ 1`, some suborbit at
`α` has size `> s`, and no suborbit size lies strictly between `s` and `t`,
then `t ≤ |Δ(α)| · s` for *every* non-diagonal orbital `Δ` (the book's
bound follows by instantiating `Δ` with an orbital of size `m₂`, `s = mᵢ`,
`t = m_{i+1}`; Isaacs's proof never uses the minimality of `m₂`).

Proof: grade the `Δ`-graph reachability by path length (`reachIn`);
connectivity (Thm 8.35) makes every point reachable.  Choose `β` with
suborbit size `> s` at minimal distance `d`.  If `d ≤ 1` then the suborbit
of `β` is trivial or equal to `Δ(α)`, and the bound is direct.  Otherwise
the predecessor `γ` of `β` has suborbit size `≤ s` by minimality, every
point of the suborbit of `β` is reached by a `Δ`-arrow from the suborbit of
`γ`, and all the sets `Δ(c)` have size `|Δ(α)|`, so
`t ≤ |orbit β| ≤ |orbit γ| · |Δ(α)| ≤ s · |Δ(α)|`.
-/

public section

namespace CFSG

namespace FiveTransitive.OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

variable {G Ω : Type*} [Group G] [MulAction G Ω]

section ReachIn

/-- Reachability in exactly `n` steps of a relation. -/
private def reachIn (r : Ω → Ω → Prop) (α : Ω) : ℕ → Ω → Prop
  | 0, γ => γ = α
  | (n + 1), γ => ∃ c, reachIn r α n c ∧ r c γ

private lemma exists_reachIn_of_reflTransGen {r : Ω → Ω → Prop} {α β : Ω}
    (h : Relation.ReflTransGen r α β) : ∃ n, reachIn r α n β := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ h₂ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, _, hn, h₂⟩

end ReachIn

section Theorem837

variable [Finite Ω]

omit [Finite Ω] in
/-- The suborbit of `α` at `α` itself is `{α}`. -/
lemma orbit_stabilizer_self (α : Ω) :
    orbit (stabilizer G α) α = {α} := by
  ext γ
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    exact mem_stabilizer_iff.mp hh
  · rintro rfl
    exact mem_orbit_self _

omit [Finite Ω] in
/-- All orbital functions of one orbital have equal size (transitivity). -/
private lemma ncard_orbitalAt_eq [IsPretransitive G Ω] (p : Ω × Ω)
    (α c : Ω) :
    Set.ncard (orbitalAt (orbit G p) c) =
      Set.ncard (orbitalAt (orbit G p) α) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G α c
  rw [orbitalAt_orbit_smul]
  have himg : (g • orbitalAt (orbit G p) α) =
      (fun β => g • β) '' orbitalAt (orbit G p) α := rfl
  rw [himg, Set.ncard_image_of_injective _ (MulAction.injective g)]

/-- **Isaacs Thm 8.37**, gap form — let `G` act primitively on the finite
set `Ω`, let `α : Ω`, and let `Δ` be a non-diagonal orbital.  If `s ≥ 1`,
some suborbit at `α` has size `> s`, and every suborbit size is `≤ s` or
`≥ t`, then `t ≤ |Δ(α)| · s`.  (With `Δ` an orbital of minimal non-trivial
size `m₂`, `s = mᵢ` and `t = m_{i+1}` this is the book's
`m_{i+1} ≤ m₂ · mᵢ`.) -/
theorem subdegree_gap_le [IsPreprimitive G Ω] (α : Ω)
    {q : Ω × Ω} (hq : q.1 ≠ q.2) {s t : ℕ} (hs : 1 ≤ s)
    (hex : ∃ β : Ω, s < Set.ncard (orbit (stabilizer G α) β))
    (hgap : ∀ γ : Ω, Set.ncard (orbit (stabilizer G α) γ) ≤ s ∨
      t ≤ Set.ncard (orbit (stabilizer G α) γ)) :
    t ≤ Set.ncard (orbitalAt (orbit G q) α) * s := by
  classical
  set r : Ω → Ω → Prop := fun a b => (a, b) ∈ orbit G q with hrdef
  set M : ℕ := Set.ncard (orbitalAt (orbit G q) α) with hM
  -- the set of distances of points with large suborbits is nonempty
  have hDex : ∃ n : ℕ, ∃ γ : Ω,
      s < Set.ncard (orbit (stabilizer G α) γ) ∧ reachIn r α n γ := by
    obtain ⟨β, hβ⟩ := hex
    obtain ⟨n, hn⟩ := exists_reachIn_of_reflTransGen
      (orbital_connected_of_isPreprimitive (G := G) hq α β)
    exact ⟨n, β, hβ, hn⟩
  obtain ⟨β, hβs, hβreach⟩ := Nat.find_spec hDex
  have hmin : ∀ n < Nat.find hDex, ∀ γ : Ω, reachIn r α n γ →
      Set.ncard (orbit (stabilizer G α) γ) ≤ s := by
    intro n hn γ hγ
    by_contra hc
    exact Nat.find_min hDex hn ⟨γ, lt_of_not_ge hc, hγ⟩
  -- `t ≤ ncard (orbit β)` from the gap
  have htβ : t ≤ Set.ncard (orbit (stabilizer G α) β) :=
    (hgap β).resolve_left (not_le.mpr hβs)
  -- case on the distance
  match hd' : Nat.find hDex, hβreach with
  | 0, hreach =>
    -- `β = α` has suborbit `{α}` of size `1 ≤ s`
    exfalso
    have hβα : β = α := hreach
    rw [hβα, orbit_stabilizer_self, Set.ncard_singleton] at hβs
    omega
  | (n + 1), hreach =>
    obtain ⟨γ, hγreach, hγβ⟩ := hreach
    -- the suborbit of `γ` is small (its distance is below the minimum)
    have hγs : Set.ncard (orbit (stabilizer G α) γ) ≤ s := by
      apply hmin n _ γ hγreach
      omega
    -- the suborbit of `β` is covered by `Δ`-arrows from the suborbit of `γ`
    have hcover : orbit (stabilizer G α) β ⊆
        ⋃ c ∈ orbit (stabilizer G α) γ, orbitalAt (orbit G q) c := by
      rintro u ⟨h, rfl⟩
      refine Set.mem_biUnion (mem_orbit γ h) ?_
      rw [mem_orbitalAt_iff]
      exact smul_pair_mem_orbit ((h : G)) hγβ
    -- cardinality bookkeeping
    have := Fintype.ofFinite Ω
    have hU2 : Set.ncard (⋃ c ∈ orbit (stabilizer G α) γ,
        orbitalAt (orbit G q) c) ≤
        Set.ncard (orbit (stabilizer G α) γ) * M := by
      have hfin : (⋃ c ∈ orbit (stabilizer G α) γ,
          orbitalAt (orbit G q) c).toFinset ⊆
          (orbit (stabilizer G α) γ).toFinset.biUnion
            (fun c => (orbitalAt (orbit G q) c).toFinset) := by
        intro z hz
        rw [Set.mem_toFinset, Set.mem_iUnion₂] at hz
        obtain ⟨c, hc, hzc⟩ := hz
        rw [Finset.mem_biUnion]
        exact ⟨c, Set.mem_toFinset.mpr hc, Set.mem_toFinset.mpr hzc⟩
      calc Set.ncard (⋃ c ∈ orbit (stabilizer G α) γ,
            orbitalAt (orbit G q) c)
          = (⋃ c ∈ orbit (stabilizer G α) γ,
              orbitalAt (orbit G q) c).toFinset.card := by
            rw [Set.ncard_eq_toFinset_card']
        _ ≤ ((orbit (stabilizer G α) γ).toFinset.biUnion
              (fun c => (orbitalAt (orbit G q) c).toFinset)).card :=
            Finset.card_le_card hfin
        _ ≤ ∑ c ∈ (orbit (stabilizer G α) γ).toFinset,
              (orbitalAt (orbit G q) c).toFinset.card :=
            Finset.card_biUnion_le
        _ = ∑ _c ∈ (orbit (stabilizer G α) γ).toFinset, M := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [← Set.ncard_eq_toFinset_card', hM, ncard_orbitalAt_eq]
        _ = (orbit (stabilizer G α) γ).toFinset.card * M := by
            rw [Finset.sum_const, smul_eq_mul]
        _ = Set.ncard (orbit (stabilizer G α) γ) * M := by
            rw [Set.ncard_eq_toFinset_card']
    have hchain : t ≤ Set.ncard (orbit (stabilizer G α) γ) * M :=
      le_trans htβ (le_trans
        (Set.ncard_le_ncard hcover (Set.toFinite _)) hU2)
    calc t ≤ Set.ncard (orbit (stabilizer G α) γ) * M := hchain
      _ ≤ s * M := Nat.mul_le_mul_right M hγs
      _ = M * s := Nat.mul_comm s M

end Theorem837

/-! ### Isaacs Lem 8.39 (a), (b) — arrow arithmetic -/

section Lemma839

/-- **Isaacs Lem 8.39 (a), (b)** — in a finite group, write `m = |A : A∩B|`,
`n = |A : A∩C|` and `u = |B : B∩C|` (the `m`-, `n`- and `u`-arrows of the
book, with `A, B, C` the three point stabilizers).  If `|A| = |B|` and
`m, n` are coprime, then `n ≤ u` and `u ∣ m n`.  (Clause (c) is
`mul_subset_mul_of_coprime` below.) -/
theorem relIndex_le_and_dvd_of_coprime {M : Type*} [Group M] [Finite M]
    {A B C : Subgroup M} (hAB : Nat.card A = Nat.card B)
    (hcop : Nat.Coprime (B.relIndex A) (C.relIndex A)) :
    C.relIndex A ≤ C.relIndex B ∧
      C.relIndex B ∣ B.relIndex A * C.relIndex A := by
  set m := B.relIndex A with hm
  set n := C.relIndex A with hn
  have hne : ∀ (X Y : Subgroup M), X.relIndex Y ≠ 0 := by
    intro X Y
    exact Subgroup.index_ne_zero_of_finite
  -- `q = |A∩B : A∩B∩C| = n` by coprimality
  set q := C.relIndex (B ⊓ A) with hq
  have hchain : q * m = (C ⊓ B).relIndex A :=
    Subgroup.relIndex_inf_mul_relIndex C B A
  have hndvd : n ∣ q * m := by
    rw [hchain]
    exact Subgroup.relIndex_dvd_of_le_left A inf_le_left
  have hnq : n ∣ q := (Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.symm hcop) hndvd)
  have hqn : q ≤ n := by
    have h2 := Subgroup.relIndex_le_of_le_right (H := C)
      (inf_le_right : B ⊓ A ≤ A) (hne C A)
    rw [← hq, ← hn] at h2
    exact h2
  have hqeq : q = n := Nat.le_antisymm hqn
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (by rw [hq]; exact hne _ _)) hnq)
  constructor
  · -- (a): `n = q ≤ u`
    rw [← hqeq, hq]
    have h2 := Subgroup.relIndex_le_of_le_right (H := C)
      (inf_le_left : B ⊓ A ≤ B) (hne C B)
    exact h2
  · -- (b): `u ∣ |B : W| = |A : W| = m n` with `W = C ⊓ B ⊓ A`
    set W := C ⊓ B ⊓ A with hW
    have hWB : W ≤ B := le_trans inf_le_left inf_le_right
    have hWA : W ≤ A := inf_le_right
    have hu_dvd : C.relIndex B ∣ W.relIndex B := by
      have h2 : W ≤ C := le_trans inf_le_left inf_le_left
      exact Subgroup.relIndex_dvd_of_le_left B h2
    have hWrel : W.relIndex A = n * m := by
      have h2 : (C ⊓ B).relIndex A = W.relIndex A := by
        rw [hW, ← Subgroup.inf_relIndex_right (C ⊓ B) A]
      rw [← h2, ← hchain, hqeq]
    -- `|B : W| = |A : W|` from `|A| = |B|`
    have hcardrel : ∀ (X : Subgroup M) (hWX : W ≤ X),
        W.relIndex X * Nat.card W = Nat.card X := by
      intro X hWX
      have h2 : (W.subgroupOf X).index * Nat.card (W.subgroupOf X) =
          Nat.card X := Subgroup.index_mul_card _
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv] at h2
    have hWeq : W.relIndex B = W.relIndex A := by
      have h1 := hcardrel B hWB
      have h2 := hcardrel A hWA
      rw [← hAB] at h1
      have hpos : 0 < Nat.card W := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    rw [Nat.mul_comm]
    rw [← hWrel, ← hWeq]
    exact hu_dvd

/-- In a finite group, two subgroups with coprime indices cover the group:
`X Y = H`.  (Proof: the `X`-orbit of the trivial coset of `Y` has size
`|X : X ∩ Y| = |H : Y|`, so `X` is transitive on `H ⧸ Y`.) -/
private lemma coe_mul_coe_eq_univ_of_coprime_index {H : Type*} [Group H]
    [Finite H] {X Y : Subgroup H}
    (hcop : Nat.Coprime X.index Y.index) :
    (X : Set H) * (Y : Set H) = Set.univ := by
  classical
  -- `|X : X ∩ Y| = |H : Y|`
  have hrel : Y.relIndex X = Y.index := by
    have hle : Y.relIndex X ≤ Y.index := by
      have h2 := Subgroup.relIndex_le_of_le_right (H := Y) (le_top : X ≤ ⊤)
        (by rw [Subgroup.relIndex_top_right]
            exact Subgroup.index_ne_zero_of_finite)
      rwa [Subgroup.relIndex_top_right] at h2
    have hdvd : Y.index ∣ Y.relIndex X := by
      have h2 : Y.relIndex X * X.index = (Y ⊓ X).index := by
        rw [← Subgroup.inf_relIndex_right Y X]
        exact Subgroup.relIndex_mul_index inf_le_right
      have h3 : Y.index ∣ (Y ⊓ X).index :=
        Subgroup.index_dvd_of_le inf_le_left
      rw [← h2] at h3
      exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm hcop) h3
    have hpos : 0 < Y.relIndex X :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact Nat.le_antisymm hle (Nat.le_of_dvd hpos hdvd)
  -- the `X`-orbit of the trivial coset in `H ⧸ Y` is everything
  have hstab : stabilizer (↥X) ((1 : H) : H ⧸ Y) = Y.subgroupOf X := by
    ext x
    rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    have hkey : (x • ((1 : H) : H ⧸ Y) = ((1 : H) : H ⧸ Y)) ↔
        ((↑x * 1 : H) : H ⧸ Y) = ((1 : H) : H ⧸ Y) := Iff.rfl
    rw [hkey, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]
  have horb : orbit (↥X) ((1 : H) : H ⧸ Y) = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    have hcard : Set.ncard (orbit (↥X) ((1 : H) : H ⧸ Y)) = Y.index := by
      rw [← Nat.card_coe_set_eq,
        Nat.card_congr (orbitEquivQuotientStabilizer (↥X)
          ((1 : H) : H ⧸ Y)), hstab]
      exact hrel
    rw [Set.ncard_univ, hcard]
    exact le_rfl
  -- extract the product decomposition
  ext h
  simp only [Set.mem_univ, iff_true]
  have h2 : ((h : H) : H ⧸ Y) ∈ orbit (↥X) ((1 : H) : H ⧸ Y) := by
    rw [horb]
    exact Set.mem_univ _
  obtain ⟨x, hx⟩ := h2
  have hx' : (↑x : H) • ((1 : H) : H ⧸ Y) = ((h : H) : H ⧸ Y) := hx
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at hx'
  have h3 := QuotientGroup.eq.mp hx'
  rw [Set.mem_mul]
  exact ⟨↑x, x.2, (↑x)⁻¹ * h, h3,
    by rw [← mul_assoc, mul_inv_cancel, one_mul]⟩

/-- Under the coprimality of Lem 8.39, `A = (A ∩ C)(A ∩ B)`. -/
private lemma inf_mul_inf_eq_of_coprime {M : Type*} [Group M] [Finite M]
    {A B C : Subgroup M}
    (hcop : Nat.Coprime (B.relIndex A) (C.relIndex A)) :
    ((A ⊓ C : Subgroup M) : Set M) * ((A ⊓ B : Subgroup M) : Set M) =
      (A : Set M) := by
  apply Set.Subset.antisymm
  · intro z hz
    rw [Set.mem_mul] at hz
    obtain ⟨u, hu, v, hv, huv⟩ := hz
    rw [← huv]
    exact A.mul_mem (Subgroup.mem_inf.mp hu).1 (Subgroup.mem_inf.mp hv).1
  · intro a ha
    have hcop' : Nat.Coprime (C.subgroupOf A).index (B.subgroupOf A).index :=
      Nat.Coprime.symm hcop
    have h2 := coe_mul_coe_eq_univ_of_coprime_index hcop'
    have h3 : (⟨a, ha⟩ : ↥A) ∈
        (C.subgroupOf A : Set ↥A) * (B.subgroupOf A : Set ↥A) := by
      rw [h2]
      exact Set.mem_univ _
    rw [Set.mem_mul] at h3
    obtain ⟨u, hu, v, hv, huv⟩ := h3
    rw [Set.mem_mul]
    refine ⟨↑u, Subgroup.mem_inf.mpr ⟨u.2, Subgroup.mem_subgroupOf.mp hu⟩,
      ↑v, Subgroup.mem_inf.mpr ⟨v.2, Subgroup.mem_subgroupOf.mp hv⟩, ?_⟩
    have h4 := congrArg Subtype.val huv
    rw [Subgroup.coe_mul] at h4
    exact h4

/-- **Isaacs Lem 8.39 (c)** — with `A, B, C` three subgroups of a finite
group, if `|A : A ∩ B|` and `|A : A ∩ C|` are coprime then
`C A ⊆ C B` (as subsets; only coprimality is needed). -/
theorem mul_subset_mul_of_coprime {M : Type*} [Group M] [Finite M]
    {A B C : Subgroup M}
    (hcop : Nat.Coprime (B.relIndex A) (C.relIndex A)) :
    (C : Set M) * (A : Set M) ⊆ (C : Set M) * (B : Set M) := by
  have h1 : (C : Set M) * (A : Set M) =
      (C : Set M) * ((A ⊓ B : Subgroup M) : Set M) := by
    rw [← inf_mul_inf_eq_of_coprime hcop, ← mul_assoc]
    congr 1
    apply Set.Subset.antisymm
    · intro z hz
      rw [Set.mem_mul] at hz
      obtain ⟨u, hu, v, hv, huv⟩ := hz
      rw [← huv]
      exact C.mul_mem hu (Subgroup.mem_inf.mp hv).2
    · intro z hz
      rw [Set.mem_mul]
      exact ⟨z, hz, 1, Subgroup.one_mem _, mul_one z⟩
  rw [h1]
  exact Set.mul_subset_mul_left fun z hz => (Subgroup.mem_inf.mp hz).2

end Lemma839

/-! ### Isaacs Thm 8.38 — Weiss's theorem -/

section Theorem838

variable [Finite Ω]

omit [Finite Ω] in
/-- The size of a suborbit is a relative index of stabilizers. -/
lemma ncard_suborbit_eq_relIndex (α β : Ω) :
    Set.ncard (orbit (stabilizer G α) β) =
      (stabilizer G β).relIndex (stabilizer G α) := by
  have hstab : stabilizer (↥(stabilizer G α)) β =
      (stabilizer G β).subgroupOf (stabilizer G α) := by
    ext h
    rfl
  rw [← Nat.card_coe_set_eq,
    Nat.card_congr (orbitEquivQuotientStabilizer (↥(stabilizer G α)) β),
    hstab]
  rfl

omit [Finite Ω] in
/-- Suborbit sizes are invariant under translation. -/
lemma ncard_suborbit_smul_eq (g : G) (α β : Ω) :
    Set.ncard (orbit (stabilizer G (g • α)) (g • β)) =
      Set.ncard (orbit (stabilizer G α) β) := by
  have horb : orbit (stabilizer G (g • α)) (g • β) =
      (fun x => g • x) '' orbit (stabilizer G α) β := by
    ext z
    constructor
    · rintro ⟨⟨h, hh⟩, rfl⟩
      refine ⟨(g⁻¹ * h * g) • β, ⟨⟨g⁻¹ * h * g, ?_⟩, rfl⟩, ?_⟩
      · rw [mem_stabilizer_iff] at hh ⊢
        rw [mul_smul, mul_smul, hh, inv_smul_smul]
      · change g • (g⁻¹ * h * g) • β = h • g • β
        rw [smul_smul, smul_smul, mul_assoc g⁻¹ h g, mul_inv_cancel_left]
    · rintro ⟨w, ⟨⟨h, hh⟩, rfl⟩, rfl⟩
      refine ⟨⟨g * h * g⁻¹, ?_⟩, ?_⟩
      · rw [mem_stabilizer_iff] at hh ⊢
        rw [mul_smul, mul_smul, inv_smul_smul, hh]
      · change (g * h * g⁻¹) • g • β = g • h • β
        rw [smul_smul, smul_smul, inv_mul_cancel_right]
  rw [horb, Set.ncard_image_of_injective _ (MulAction.injective g)]

omit [Finite Ω] in
/-- Conjugate stabilizers have equal cardinality. -/
lemma card_stabilizer_eq [IsPretransitive G Ω] (α β : Ω) :
    Nat.card (stabilizer G α) = Nat.card (stabilizer G β) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G α β
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective _ _ (MulEquiv.injective (MulAut.conj g))).toEquiv

/-- `|B : A ∩ B| · |A ∩ B| = |B|` — the relative index against the
intersection. -/
lemma relIndex_mul_card_inf {M : Type*} [Group M] [Finite M]
    (A B : Subgroup M) :
    A.relIndex B * Nat.card ↥(A ⊓ B) = Nat.card B := by
  have h2 := Subgroup.index_mul_card ((A ⊓ B).subgroupOf B)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_right : A ⊓ B ≤ B)).toEquiv] at h2
  rw [← Subgroup.inf_relIndex_right A B]
  exact h2

/-- Relative indices of equal-order subgroups are symmetric:
`|K : H ∩ K| = |H : K ∩ H|` when `|H| = |K|`. -/
lemma relIndex_comm_of_card_eq {M : Type*} [Group M] [Finite M]
    {H K : Subgroup M} (hcard : Nat.card H = Nat.card K) :
    H.relIndex K = K.relIndex H := by
  have h1 := relIndex_mul_card_inf H K
  have h2 := relIndex_mul_card_inf K H
  rw [inf_comm K H, hcard] at h2
  have hpos : 0 < Nat.card ↥(H ⊓ K) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

/-- **Isaacs Thm 8.38** (Weiss; p. 247) — let a finite group `G` act
primitively on `Ω`, let `n` be the largest subdegree at `α` (attained on
the suborbit of `β₀`), and let `m` be a subdegree at `α` coprime to `n`.
Then `m = 1`.

Proof: by Lem 8.34/8.35 the orbital `Δ` of `(α, γ₀)` is non-diagonal and
its graph is connected; every `Δ`-arrow `δ → γ` is an "`m`-arrow"
(`|G_δ : G_δ ∩ G_γ| = m`).  By induction along paths from `α`, using
Lem 8.39(a) with `A = G_δ`, `B = G_γ`, `C = G_{β₀}` and maximality of `n`,
every reachable `γ` has `|G_γ : G_γ ∩ G_{β₀}| = n`.  An out-neighbor `ε`
of `β₀` then gives `m = |G_{β₀} : G_{β₀} ∩ G_ε| = |G_ε : G_ε ∩ G_{β₀}| = n`
by index symmetry, so `m = n` and coprimality forces `m = 1`. -/
theorem subdegree_eq_one_of_coprime_of_max [Finite G] [IsPreprimitive G Ω]
    (α : Ω) {n m : ℕ} {β₀ γ₀ : Ω}
    (hn : Set.ncard (orbit (stabilizer G α) β₀) = n)
    (hmax : ∀ δ : Ω, Set.ncard (orbit (stabilizer G α) δ) ≤ n)
    (hm : Set.ncard (orbit (stabilizer G α) γ₀) = m)
    (hcop : Nat.Coprime m n) : m = 1 := by
  classical
  by_contra hm1
  -- `γ₀ ≠ α`, so the orbital of `(α, γ₀)` is non-diagonal
  have hγ₀α : γ₀ ≠ α := by
    rintro rfl
    rw [orbit_stabilizer_self, Set.ncard_singleton] at hm
    exact hm1 hm.symm
  have hq : (α, γ₀).1 ≠ (α, γ₀).2 := Ne.symm hγ₀α
  have hm1' : 1 ≤ m := by
    have h2 : 0 < Set.ncard (orbit (stabilizer G α) γ₀) :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨γ₀, mem_orbit_self _⟩
    omega
  -- the largest subdegree bounds the suborbits at every point
  have hmaxall : ∀ γ δ : Ω, Set.ncard (orbit (stabilizer G γ) δ) ≤ n := by
    intro γ δ
    obtain ⟨g, rfl⟩ := exists_smul_eq G α γ
    have h2 := ncard_suborbit_smul_eq g α (g⁻¹ • δ)
    rw [smul_inv_smul] at h2
    rw [h2]
    exact hmax _
  -- every arrow of the orbital of `(α, γ₀)` is an `m`-arrow
  have harrow : ∀ γ δ : Ω, (γ, δ) ∈ orbit G (α, γ₀) →
      Set.ncard (orbit (stabilizer G γ) δ) = m := by
    intro γ δ hδ
    have h3 : orbit G (α, γ₀) = orbit G (γ, δ) := (orbit_eq_iff.mpr hδ).symm
    have h2 : orbitalAt (orbit G (α, γ₀)) γ = orbit (stabilizer G γ) δ := by
      rw [h3, orbitalAt_orbit_eq]
    rw [← h2, ncard_orbitalAt_eq (α := α) (p := (α, γ₀)), orbitalAt_orbit_eq]
    exact hm
  -- induction along paths: every reachable point sees `β₀` in an `n`-suborbit
  have hclaim : ∀ k : ℕ, ∀ γ : Ω,
      reachIn (fun a b => (a, b) ∈ orbit G (α, γ₀)) α k γ →
      Set.ncard (orbit (stabilizer G γ) β₀) = n := by
    intro k
    induction k with
    | zero =>
      intro γ hγ
      obtain rfl : γ = α := hγ
      exact hn
    | succ k ih =>
      rintro γ ⟨δ, hδ, hδγ⟩
      have hmδγ : Set.ncard (orbit (stabilizer G δ) γ) = m := harrow δ γ hδγ
      have hnδ : Set.ncard (orbit (stabilizer G δ) β₀) = n := ih δ hδ
      -- Lem 8.39(a) with `A = G_δ`, `B = G_γ`, `C = G_{β₀}`
      have hcardAB : Nat.card (stabilizer G δ) = Nat.card (stabilizer G γ) :=
        card_stabilizer_eq δ γ
      have hcop' : Nat.Coprime
          ((stabilizer G γ).relIndex (stabilizer G δ))
          ((stabilizer G β₀).relIndex (stabilizer G δ)) := by
        rw [← ncard_suborbit_eq_relIndex, ← ncard_suborbit_eq_relIndex,
          hmδγ, hnδ]
        exact hcop
      obtain ⟨hge, -⟩ := relIndex_le_and_dvd_of_coprime hcardAB hcop'
      rw [← ncard_suborbit_eq_relIndex, ← ncard_suborbit_eq_relIndex,
        hnδ] at hge
      exact Nat.le_antisymm (hmaxall γ β₀) hge
  -- an out-neighbor `ε` of `β₀` (the orbital function at `β₀` has size `m`)
  have hεex : (orbitalAt (orbit G (α, γ₀)) β₀).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [ncard_orbitalAt_eq (α := α) (p := (α, γ₀)), orbitalAt_orbit_eq, hm]
    omega
  obtain ⟨ε, hε⟩ := hεex
  rw [mem_orbitalAt_iff] at hε
  have hmε : Set.ncard (orbit (stabilizer G β₀) ε) = m := harrow β₀ ε hε
  -- `ε` is reachable, so its suborbit of `β₀` has size `n`
  obtain ⟨k, hk⟩ := exists_reachIn_of_reflTransGen
    (orbital_connected_of_isPreprimitive (G := G) hq α ε)
  have hnε : Set.ncard (orbit (stabilizer G ε) β₀) = n := hclaim k ε hk
  -- index symmetry: the `β₀ → ε` and `ε → β₀` suborbits have equal size
  have hsym : Set.ncard (orbit (stabilizer G β₀) ε) =
      Set.ncard (orbit (stabilizer G ε) β₀) := by
    rw [ncard_suborbit_eq_relIndex, ncard_suborbit_eq_relIndex]
    exact relIndex_comm_of_card_eq (card_stabilizer_eq ε β₀)
  rw [hmε, hnε] at hsym
  rw [hsym] at hm1 hcop
  have h9 : Nat.gcd n n = 1 := hcop
  rw [Nat.gcd_self] at h9
  exact hm1 h9

end Theorem838

/-! ### Isaacs Thm 8.40 — Manning's theorem -/

section Theorem840

variable [Finite Ω]

/-- **Isaacs Thm 8.40** (Manning; p. 248) — let a finite group `G` act
primitively on `Ω`, let `n ≥ 3` be the largest subdegree, and suppose a
point stabilizer acts `2`-transitively on some suborbit of size `n`.  Then
`|Ω| = n + 1` and `G` is `3`-transitive on `Ω`.

Proof: let `S = Δ(α)` be the given suborbit and `X` the orbital of a pair
of distinct points of `S`.  By `2`-transitivity every arrow between
distinct points of `S` is an `X`-arrow, and `X` is self-paired.  Then
`X(b₀) ⊇ S \ {b₀}` for `b₀ ∈ S`, and since `n - 1` is coprime to `n` and
is not `1`, Thm 8.38 shows `n - 1` is not a subdegree, so `|X(b₀)| = n`
and there is a unique `γ ∈ X(b₀) \ S`.  The two-point stabilizer of
`α, b₀` fixes `γ`, whence arrows out of `γ` cover `S \ {b₀}` and every
two distinct points of any `X(δ)` are `X`-joined.  Connectivity of the
`X`-graph (Thm 8.35) then forces `{b₀} ∪ X(b₀) = Ω`, so
`|Ω| = n + 1`, `S = Ω \ {α}`, and `G_α` is `2`-transitive on
`Ω \ {α}`, i.e. `G` is `3`-transitive (Lem 8.2). -/
theorem natCard_eq_and_isMultiplyPretransitive_of_two_trans_suborbit
    [Finite G] [IsPreprimitive G Ω] (α : Ω) {n : ℕ} {β₀ : Ω}
    (hn : Set.ncard (orbit (stabilizer G α) β₀) = n)
    (hmax : ∀ δ : Ω, Set.ncard (orbit (stabilizer G α) δ) ≤ n)
    (hn3 : 3 ≤ n)
    (h2t : ∀ b c b' c' : Ω, b ∈ orbit (stabilizer G α) β₀ →
      c ∈ orbit (stabilizer G α) β₀ → b' ∈ orbit (stabilizer G α) β₀ →
      c' ∈ orbit (stabilizer G α) β₀ → b ≠ c → b' ≠ c' →
      ∃ g ∈ stabilizer G α, g • b = b' ∧ g • c = c') :
    Nat.card Ω = n + 1 ∧ IsMultiplyPretransitive G Ω 3 := by
  classical
  set S : Set Ω := orbit (stabilizer G α) β₀ with hSdef
  -- `α ∉ S`
  have hαS : α ∉ S := by
    intro hα
    have h2 : S = {α} := by
      rw [hSdef, ← orbit_eq_iff.mpr hα, orbit_stabilizer_self]
    rw [h2, Set.ncard_singleton] at hn
    omega
  -- two distinct points of `S`, and the auxiliary orbital `X`
  have h2card : 1 < Set.ncard S := by omega
  obtain ⟨b₀, c₀, hb₀, hc₀, hb₀c₀⟩ :=
    (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2card
  set X : Set (Ω × Ω) := orbit G (b₀, c₀) with hXdef
  -- `S` is invariant under the stabilizer of `α`
  have hSinv : ∀ g ∈ stabilizer G α, ∀ u ∈ S, g • u ∈ S := by
    intro g hg u hu
    have h2 := mem_orbit u (⟨g, hg⟩ : stabilizer G α)
    rw [orbit_eq_iff.mpr hu] at h2
    exact h2
  -- every arrow between distinct points of `S` is an `X`-arrow
  have hjoin : ∀ x y : Ω, x ∈ S → y ∈ S → x ≠ y → (x, y) ∈ X := by
    intro x y hx hy hxy
    obtain ⟨g, hg, hgb, hgc⟩ := h2t b₀ c₀ x y hb₀ hc₀ hx hy hb₀c₀ hxy
    have h2 := smul_pair_mem_orbit g (mem_orbit_self (b₀, c₀))
    rw [hgb, hgc] at h2
    exact h2
  -- `X` is non-diagonal…
  have hXne : ∀ x y : Ω, (x, y) ∈ X → x ≠ y := by
    intro x y hxy
    obtain ⟨g, hg⟩ := hxy
    have hg' : g • (b₀, c₀) = (x, y) := hg
    rw [Prod.smul_mk, Prod.mk_inj] at hg'
    intro hxy'
    exact hb₀c₀ (MulAction.injective g (by
      change g • b₀ = g • c₀
      rw [hg'.1, hg'.2, hxy']))
  -- …and self-paired
  have hpairX : ∀ x y : Ω, (x, y) ∈ X → (y, x) ∈ X := by
    intro x y hxy
    obtain ⟨g, hg⟩ := hxy
    have hg' : g • (b₀, c₀) = (x, y) := hg
    rw [Prod.smul_mk, Prod.mk_inj] at hg'
    have h2 := smul_pair_mem_orbit g (hjoin c₀ b₀ hc₀ hb₀ (Ne.symm hb₀c₀))
    rw [hg'.1, hg'.2] at h2
    exact h2
  -- `X(b₀) ⊇ S \ {b₀}`
  have hXβsub : S \ {b₀} ⊆ orbitalAt X b₀ := by
    intro y hy
    rw [mem_orbitalAt_iff]
    exact hjoin b₀ y hb₀ hy.1 (fun h => hy.2 h.symm)
  have hcardX : ∀ δ : Ω,
      Set.ncard (orbitalAt X δ) = Set.ncard (orbitalAt X b₀) := by
    intro δ
    rw [hXdef]
    exact ncard_orbitalAt_eq (b₀, c₀) b₀ δ
  -- `|X(b₀)| = n`, using Thm 8.38 to exclude `n - 1`
  have hXb₀card : Set.ncard (orbitalAt X b₀) = n := by
    have hge : n - 1 ≤ Set.ncard (orbitalAt X b₀) := by
      have h2 := Set.ncard_le_ncard hXβsub (Set.toFinite _)
      rwa [Set.ncard_sdiff_singleton_of_mem hb₀, hn] at h2
    have hne0 : (orbitalAt X α).Nonempty := by
      apply Set.nonempty_of_ncard_ne_zero
      rw [hcardX α]
      omega
    obtain ⟨w, hw⟩ := hne0
    have hXw : X = orbit G (α, w) := by
      rw [mem_orbitalAt_iff] at hw
      rw [hXdef, ← orbit_eq_iff.mpr hw]
    have hsub : orbitalAt X α = orbit (stabilizer G α) w := by
      rw [hXw, orbitalAt_orbit_eq]
    have hle : Set.ncard (orbitalAt X b₀) ≤ n := by
      rw [← hcardX α, hsub]
      exact hmax w
    rcases Nat.lt_or_ge (Set.ncard (orbitalAt X b₀)) n with hlt | hge2
    · exfalso
      have hm' : Set.ncard (orbit (stabilizer G α) w) = n - 1 := by
        rw [← hsub, hcardX α]
        omega
      have hcop : Nat.Coprime (n - 1) n := by
        have h2 : Nat.Coprime (n - 1) ((n - 1) + 1) := by
          rw [Nat.coprime_self_add_right]
          exact Nat.gcd_one_right _
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h2
      have h1 := subdegree_eq_one_of_coprime_of_max α hn hmax hm' hcop
      omega
    · exact Nat.le_antisymm hle hge2
  -- the unique point `γ` of `X(b₀)` outside `S`
  have hb₀X : b₀ ∉ orbitalAt X b₀ := by
    rw [mem_orbitalAt_iff]
    intro h2
    exact hXne b₀ b₀ h2 rfl
  obtain ⟨γ, hγ⟩ : ∃ γ, orbitalAt X b₀ \ (S \ {b₀}) = {γ} := by
    rw [← Set.ncard_eq_one, Set.ncard_sdiff hXβsub (Set.toFinite _),
      Set.ncard_sdiff_singleton_of_mem hb₀, hXb₀card, hn]
    omega
  have hγX : γ ∈ orbitalAt X b₀ := by
    have h2 : γ ∈ ({γ} : Set Ω) := rfl
    rw [← hγ] at h2
    exact h2.1
  have hγb₀ : γ ≠ b₀ := by
    intro h4
    subst h4
    exact hb₀X hγX
  have hγS : γ ∉ S := by
    intro h2
    have h3 : γ ∈ ({γ} : Set Ω) := rfl
    rw [← hγ] at h3
    exact h3.2 ⟨h2, fun h5 => hγb₀ h5⟩
  -- `X(b₀) = (S \ {b₀}) ∪ {γ}`
  have hdecomp : orbitalAt X b₀ = insert γ (S \ {b₀}) := by
    ext z
    constructor
    · intro hz
      by_cases hz2 : z ∈ S \ {b₀}
      · exact Set.mem_insert_of_mem _ hz2
      · have h3 : z ∈ orbitalAt X b₀ \ (S \ {b₀}) := ⟨hz, hz2⟩
        rw [hγ] at h3
        have h4 : z = γ := h3
        rw [h4]
        exact Set.mem_insert _ _
    · intro hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz2
      · exact hγX
      · exact hXβsub hz2
  -- the two-point stabilizer of `α, b₀` fixes `γ`
  have hfixγ : ∀ g ∈ stabilizer G α, g • b₀ = b₀ → g • γ = γ := by
    intro g hg hgb₀
    have h2 : g • γ ∈ orbitalAt X b₀ := by
      rw [mem_orbitalAt_iff]
      have h3 := smul_pair_mem_orbit g (mem_orbitalAt_iff.mp hγX)
      rwa [hgb₀] at h3
    rw [hdecomp] at h2
    rcases Set.mem_insert_iff.mp h2 with h3 | h3
    · exact h3
    · exfalso
      apply hγS
      have h4 := hSinv g⁻¹ (inv_mem hg) (g • γ) h3.1
      rwa [inv_smul_smul] at h4
  -- `X(b₀)` is the suborbit of `γ` at `b₀`
  have hXb₀orb : orbitalAt X b₀ = orbit (stabilizer G b₀) γ := by
    have h2 : X = orbit G (b₀, γ) := by
      rw [hXdef, ← orbit_eq_iff.mpr (mem_orbitalAt_iff.mp hγX)]
    rw [h2, orbitalAt_orbit_eq]
  -- joining within a suborbit
  have hjoinorb : ∀ x y : Ω, x ∈ orbit (stabilizer G b₀) γ →
      y ∈ orbit (stabilizer G b₀) γ → ∃ k : stabilizer G b₀, k • x = y := by
    intro x y hx hy
    rw [← orbit_eq_iff.mpr hx] at hy
    obtain ⟨k, hk⟩ := hy
    exact ⟨k, hk⟩
  -- arrows out of `γ` reach all of `S \ {b₀}`
  have hγarrow : ∀ y' ∈ S \ {b₀}, (γ, y') ∈ X := by
    have h1lt : 1 < Set.ncard (S \ {b₀}) := by
      rw [Set.ncard_sdiff_singleton_of_mem hb₀, hn]
      omega
    obtain ⟨u, v, hu, hv, huv⟩ :=
      (Set.one_lt_ncard_iff (Set.toFinite _)).mp h1lt
    have hseed : (u, v) ∈ X := hjoin u v hu.1 hv.1 huv
    obtain ⟨k₂, hk₂⟩ := hjoinorb u γ
      (by rw [← hXb₀orb]; exact hXβsub hu) (mem_orbit_self _)
    have hv'orb : k₂ • v ∈ orbit (stabilizer G b₀) γ := by
      have hvX : v ∈ orbit (stabilizer G b₀) γ := by
        rw [← hXb₀orb]
        exact hXβsub hv
      rw [MulAction.mem_orbit_iff] at hvX ⊢
      obtain ⟨k', hk'⟩ := hvX
      exact ⟨k₂ * k', by rw [mul_smul, hk']⟩
    have hv'ne : k₂ • v ≠ γ := by
      intro h2
      rw [← hk₂] at h2
      exact huv (MulAction.injective k₂ h2).symm
    have hv'S : k₂ • v ∈ S \ {b₀} := by
      have h2 : k₂ • v ∈ orbitalAt X b₀ := by
        rw [hXb₀orb]
        exact hv'orb
      rw [hdecomp] at h2
      rcases Set.mem_insert_iff.mp h2 with h3 | h3
      · exact absurd h3 hv'ne
      · exact h3
    have hv'X : (γ, k₂ • v) ∈ X := by
      have h2 := smul_pair_mem_orbit (↑k₂ : G) hseed
      have h3 : (↑k₂ : G) • u = γ := hk₂
      have h4 : (↑k₂ : G) • v = k₂ • v := rfl
      rw [h3, h4] at h2
      exact h2
    intro y' hy'
    obtain ⟨g, hg, hgb₀, hgv⟩ := h2t b₀ (k₂ • v) b₀ y' hb₀ hv'S.1 hb₀ hy'.1
      (fun h => hv'S.2 h.symm) (fun h => hy'.2 h.symm)
    have hgγ : g • γ = γ := hfixγ g hg hgb₀
    have h2 := smul_pair_mem_orbit g hv'X
    rw [hgγ, hgv] at h2
    exact h2
  -- every two distinct points of `X(b₀)` are `X`-joined
  have hQ : ∀ x y : Ω, x ∈ orbitalAt X b₀ → y ∈ orbitalAt X b₀ → x ≠ y →
      (x, y) ∈ X := by
    intro x y hx hy hxy
    obtain ⟨k, hk⟩ := hjoinorb γ x (mem_orbit_self _)
      (by rw [← hXb₀orb]; exact hx)
    have hy' : k⁻¹ • y ∈ orbit (stabilizer G b₀) γ := by
      have h2 : y ∈ orbit (stabilizer G b₀) γ := by
        rw [← hXb₀orb]
        exact hy
      rw [MulAction.mem_orbit_iff] at h2 ⊢
      obtain ⟨k', hk'⟩ := h2
      exact ⟨k⁻¹ * k', by rw [mul_smul, hk']⟩
    have hyγ : k⁻¹ • y ≠ γ := by
      intro h2
      apply hxy
      rw [← hk, ← h2, smul_inv_smul]
    have hy'' : k⁻¹ • y ∈ S \ {b₀} := by
      have h2 : k⁻¹ • y ∈ orbitalAt X b₀ := by
        rw [hXb₀orb]
        exact hy'
      rw [hdecomp] at h2
      rcases Set.mem_insert_iff.mp h2 with h3 | h3
      · exact absurd h3 hyγ
      · exact h3
    have h3 := hγarrow (k⁻¹ • y) hy''
    have h4 := smul_pair_mem_orbit (↑k : G) h3
    have h5 : (↑k : G) • γ = x := hk
    have h6 : (↑k : G) • k⁻¹ • y = y := by
      change k • k⁻¹ • y = y
      rw [smul_inv_smul]
    rw [h5, h6] at h4
    exact h4
  -- transport: every two distinct points of any `X(δ)` are `X`-joined
  have hP : ∀ δ x y : Ω, x ∈ orbitalAt X δ → y ∈ orbitalAt X δ → x ≠ y →
      (x, y) ∈ X := by
    intro δ x y hx hy hxy
    obtain ⟨g, hg⟩ := exists_smul_eq G b₀ δ
    rw [mem_orbitalAt_iff] at hx hy
    have hx' : g⁻¹ • x ∈ orbitalAt X b₀ := by
      rw [mem_orbitalAt_iff]
      have h2 := smul_pair_mem_orbit g⁻¹ hx
      rwa [← hg, inv_smul_smul] at h2
    have hy2 : g⁻¹ • y ∈ orbitalAt X b₀ := by
      rw [mem_orbitalAt_iff]
      have h2 := smul_pair_mem_orbit g⁻¹ hy
      rwa [← hg, inv_smul_smul] at h2
    have hne2 : g⁻¹ • x ≠ g⁻¹ • y := fun h2 => hxy (MulAction.injective g⁻¹ h2)
    have h3 := hQ _ _ hx' hy2 hne2
    have h4 := smul_pair_mem_orbit g h3
    rwa [smul_inv_smul, smul_inv_smul] at h4
  -- connectivity forces `{b₀} ∪ X(b₀) = Ω`
  have hT : insert b₀ (orbitalAt X b₀) = Set.univ := by
    by_contra hne
    obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ insert b₀ (orbitalAt X b₀) := by
      by_contra h2
      push Not at h2
      exact hne (Set.eq_univ_of_forall h2)
    obtain ⟨δ, hδ, ε, hε, hedge⟩ := exists_exit
      (orbital_connected_of_isPreprimitive (G := G)
        (show (b₀, c₀).1 ≠ (b₀, c₀).2 from hb₀c₀) b₀ ω)
      (Set.mem_insert b₀ _) hω
    have hδb₀ : δ ≠ b₀ := by
      rintro rfl
      exact hε (Set.mem_insert_of_mem _ (mem_orbitalAt_iff.mpr hedge))
    have hδX : δ ∈ orbitalAt X b₀ := by
      rcases Set.mem_insert_iff.mp hδ with h2 | h2
      · exact absurd h2 hδb₀
      · exact h2
    have hb₀δ : b₀ ∈ orbitalAt X δ :=
      mem_orbitalAt_iff.mpr (hpairX b₀ δ (mem_orbitalAt_iff.mp hδX))
    have hεX : ε ∈ orbitalAt X δ := mem_orbitalAt_iff.mpr hedge
    have hb₀ε : b₀ ≠ ε := by
      rintro rfl
      exact hε (Set.mem_insert _ _)
    have h5 := hP δ b₀ ε hb₀δ hεX hb₀ε
    exact hε (Set.mem_insert_of_mem _ (mem_orbitalAt_iff.mpr h5))
  -- cardinality: `|Ω| = n + 1`
  have hcardΩ : Nat.card Ω = n + 1 := by
    rw [← Set.ncard_univ, ← hT,
      Set.ncard_insert_of_notMem hb₀X (Set.toFinite _), hXb₀card]
  -- hence `S = Ω \ {α}`
  have hScompl : S = Set.univ \ {α} := by
    apply Set.eq_of_subset_of_ncard_le
    · intro z hz
      exact ⟨Set.mem_univ z,
        fun h2 => hαS ((Set.mem_singleton_iff.mp h2) ▸ hz)⟩
    · rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ α), Set.ncard_univ,
        hcardΩ, hn]
      omega
    · exact Set.toFinite _
  -- `3`-transitivity via the stabilizer bridge (Lem 8.2)
  refine ⟨hcardΩ, ?_⟩
  rw [show (3 : ℕ) = Nat.succ 2 from rfl,
    SubMulAction.ofStabilizer.isMultiplyPretransitive (a := α),
    is_two_pretransitive_iff]
  intro x y z w hxy hzw
  have hmem : ∀ p : SubMulAction.ofStabilizer G α, (p : Ω) ∈ S := by
    intro p
    rw [hScompl]
    exact ⟨Set.mem_univ _,
      fun h2 => SubMulAction.neq_of_mem_ofStabilizer G α
        (Set.mem_singleton_iff.mp h2)⟩
  have hxyne : (x : Ω) ≠ (y : Ω) := fun h2 => hxy (Subtype.coe_injective h2)
  have hzwne : (z : Ω) ≠ (w : Ω) := fun h2 => hzw (Subtype.coe_injective h2)
  obtain ⟨g, hg, hgxz, hgyw⟩ :=
    h2t x y z w (hmem x) (hmem y) (hmem z) (hmem w) hxyne hzwne
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · apply Subtype.coe_injective
    change (↑((⟨g, hg⟩ : stabilizer G α) • x) : Ω) = ↑z
    rw [SubMulAction.val_smul]
    exact hgxz
  · apply Subtype.coe_injective
    change (↑((⟨g, hg⟩ : stabilizer G α) • y) : Ω) = ↑w
    rw [SubMulAction.val_smul]
    exact hgyw

end Theorem840

end FiveTransitive.OddOrder.Isaacs.Ch08

end CFSG
