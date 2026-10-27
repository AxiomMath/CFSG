module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Equiv.TypeTags

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman, Lemma 3.4 — a non-identity `p`-subgroup fixes a proper non-zero subspace

Statement (paper `refs/glauberman-p-stable.tex` L530–L546): let `p` be a prime and let
`G` be a group of linear transformations on a finite-dimensional vector space `V` over a
finite field of characteristic `p`.  If `P` is a non-identity `p`-subgroup of `G`, then
`1 < C_V(P) < V`.

## Formal shape

The action of `G` on `V` is given by a homomorphism `φ : G →* MulAut (Multiplicative V)`
into the automorphism group of the additive group of `V` (the type synonym
`Multiplicative V` carries the multiplicative group structure induced by the addition of
`V`; this is the same convention as `qdAction` in `Glauberman/ZJTheorem.lean`).  The
fixed points `C_V(P)` are the subgroup

    fixedPoints φ P := { v | ∀ g ∈ P, (φ g) v = v }   ≤  Multiplicative V

whose carrier is exactly the additive subgroup of `V` fixed by `P` (the fixed subspace of
the paper).  The paper's `1 < C_V(P) < V` is the statement
`⊥ < fixedPoints φ P ∧ fixedPoints φ P < ⊤` (in `Multiplicative V` the identity element
is the zero vector, and `⊥`/`⊤` are the trivial/full additive subgroups).

Two hypotheses encode the paper's setup:

* `hφ : Function.Injective φ` — faithfulness.  A group of linear transformations is a
  subgroup of `GL(V)`, so its action is faithful.
* `[Finite V]` and `hVp : IsPGroup p (Multiplicative V)` — the paper's "finite field of
  characteristic `p`" is used only to conclude that the additive group of `V` is a finite
  `p`-group (`|V| = |F|^dim V` with `|F|` a power of `p`).  Taking this as a hypothesis
  makes the result directly applicable to elementary Abelian `p`-groups, which is how
  Lemma 6.3 uses it (`G` irreducible on elementary Abelian `K`).
* `[Nontrivial V]` — the degenerate case `V = 0` is excluded (the paper's conclusion
  `1 < C_V(P)` forces `V ≠ 0`).

The proof follows the paper's two-step argument:

1. `C_V(P) < V`: if every vector were fixed by `P`, then `P ≤ ker φ`, and faithfulness
   gives `P = 1`.  (No `p`-group or finiteness hypothesis is needed for this direction.)
2. `1 < C_V(P)`: the paper forms the semidirect product `PV`, in which `V` is a
   non-trivial normal subgroup, and applies Lemma 3.3 (a non-trivial normal subgroup of a
   finite `p`-group meets the centre).  We give the equivalent direct counting argument:
   `P` acts on the finite set underlying `V`, and for a `p`-group every orbit has
   `p`-power size; if no non-zero vector were fixed, the fixed set would be `{0}`, of size
   1, contradicting `p ∣ |V|`.  This is exactly the counting content of Lemma 3.3.
-/

namespace CFSG.Glauberman

variable {V : Type*} [AddCommGroup V] {G : Type*} [Group G]

/-- The fixed points `C_V(P) = {v ∈ V | ∀ g ∈ P, g·v = v}` of a subgroup `P` of the
acting group `G` (the action given by `φ : G →* MulAut (Multiplicative V)`), as a subgroup
of the multiplicative-tagged additive group of `V`. -/
public def fixedPoints (φ : G →* MulAut (Multiplicative V)) (P : Subgroup G) :
    Subgroup (Multiplicative V) where
  carrier := {v | ∀ g : G, g ∈ P → (φ g) v = v}
  one_mem' := by
    intro g hg
    simp
  mul_mem' := by
    intro a b ha hb g hg
    rw [map_mul, ha g hg, hb g hg]
  inv_mem' := by
    intro a ha g hg
    rw [map_inv, ha g hg]

/-- Membership in `fixedPoints φ P`. -/
public theorem mem_fixedPoints {φ : G →* MulAut (Multiplicative V)} {P : Subgroup G}
    {v : Multiplicative V} : v ∈ fixedPoints φ P ↔ ∀ g : G, g ∈ P → (φ g) v = v :=
  Iff.rfl

/-- If `P ⊴ G`, then `C_V(P)` is `G`-invariant: conjugating a fixed vector by `g ∈ G`
(equivalently, applying the automorphism `φ g`) gives another vector fixed by `P`. -/
public theorem fixedPoints_invariant_of_normal {φ : G →* MulAut (Multiplicative V)}
    {P : Subgroup G} [P.Normal] {v : Multiplicative V} (hv : v ∈ fixedPoints φ P) (g : G) :
    (φ g) v ∈ fixedPoints φ P := by
  intro p hp
  have hconj : g⁻¹ * (p : G) * g ∈ P :=
    (inferInstance : P.Normal).conj_mem' (p : G) hp g
  calc
    (φ p) ((φ g) v) = (φ ((p : G) * g)) v := by rw [map_mul]; rfl
    _ = (φ g) ((φ (g⁻¹ * (p : G) * g)) v) := by
      have h : (p : G) * g = g * (g⁻¹ * (p : G) * g) := by
        rw [← mul_assoc g (g⁻¹ * (p : G)) g, ← mul_assoc g g⁻¹ (p : G), mul_inv_cancel,
          one_mul]
      rw [h, map_mul]; rfl
    _ = (φ g) v := by rw [hv (g⁻¹ * (p : G) * g) hconj]

/-- Lemma 3.4, `C_V(P) < V` part: a non-identity subgroup of a faithfully acting group
does not fix all of `V` (contrapositive: if `P` fixes every vector then `P ≤ ker φ = 1`). -/
public theorem fixedPoints_lt_top {φ : G →* MulAut (Multiplicative V)}
    (hφ : Function.Injective φ) (P : Subgroup G) (hPne : P ≠ ⊥) :
    fixedPoints φ P < (⊤ : Subgroup (Multiplicative V)) := by
  rw [lt_top_iff_ne_top]
  intro htop
  apply hPne
  refine le_antisymm ?_ bot_le
  intro g hg
  apply hφ
  apply MulEquiv.ext
  intro v
  have hv : v ∈ fixedPoints φ P := by
    rw [htop]
    trivial
  simpa using hv g hg

/-- Lemma 3.4, `1 < C_V(P)` part: `V` is a finite `p`-group and `P` a `p`-subgroup, so the
`p`-group fixed-point theorem forces a non-zero fixed vector.  (This direction does not
need `P ≠ 1`; the paper's hypothesis is used in `fixedPoints_lt_top`.) -/
public theorem bot_lt_fixedPoints {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Finite V] {G : Type*} [Group G] (φ : G →* MulAut (Multiplicative V))
    [Nontrivial V] (hVp : IsPGroup p (Multiplicative V)) (P : Subgroup G)
    (hPp : IsPGroup p P) :
    (⊥ : Subgroup (Multiplicative V)) < fixedPoints φ P := by
  rw [bot_lt_iff_ne_bot]
  intro hbot
  -- `P` acts on `Multiplicative V` through `φ`.
  let φP : P →* MulAut (Multiplicative V) := φ.comp P.subtype
  letI : MulAction P (Multiplicative V) := MulAction.compHom (Multiplicative V) φP
  -- The two descriptions of the fixed set agree.
  have hfixeq : ((fixedPoints φ P : Subgroup (Multiplicative V)) : Set (Multiplicative V)) =
      MulAction.fixedPoints P (Multiplicative V) := by
    ext v
    constructor
    · intro hv p
      change (φ (p : G)) v = v
      exact hv (p : G) p.2
    · intro hp g hg
      change (⟨g, hg⟩ : P) • v = v
      exact hp ⟨g, hg⟩
  -- `V ≠ 0` is a `p`-group, so `p ∣ |V|`.
  have hVnontriv : Nontrivial (Multiplicative V) := inferInstance
  have hVcard : ∃ n > 0, Nat.card (Multiplicative V) = p ^ n :=
    (hVp.nontrivial_iff_card).mp hVnontriv
  rcases hVcard with ⟨n, hn0, hn⟩
  have hp_dvd : p ∣ Nat.card (Multiplicative V) := by
    rw [hn]
    exact dvd_pow_self p (ne_of_gt hn0)
  -- `P` fixes `0`, and a `p`-group action on a set of cardinality divisible by `p` has
  -- another fixed point: a non-zero fixed vector, contradicting `fixedPoints φ P = ⊥`.
  have h1fix : (1 : Multiplicative V) ∈ MulAction.fixedPoints P (Multiplicative V) := by
    intro p
    change (φ (p : G)) 1 = 1
    simp
  obtain ⟨b, hb, hbne⟩ :=
    hPp.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := Multiplicative V) hp_dvd h1fix
  have hbmem : b ∈ (fixedPoints φ P : Set (Multiplicative V)) := by
    rw [hfixeq]
    exact hb
  have hb1 : b = 1 := by
    have : b ∈ (⊥ : Subgroup (Multiplicative V)) := by
      rw [← hbot]
      exact hbmem
    simpa using this
  exact hbne hb1.symm

/-- Glauberman, Lemma 3.4 ([6], §3, p. 1106): let `p` be a prime and let `G` be a group
of linear transformations on a finite vector space `V` over a field of characteristic
`p` (formalised: `G` acts faithfully on the additive group of `V` via `φ`, and the
additive group of `V` is a finite `p`-group).  If `P` is a non-identity `p`-subgroup of
`G`, then `1 < C_V(P) < V`. -/
public theorem lemma3_4 {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Finite V]
    {G : Type*} [Group G] (φ : G →* MulAut (Multiplicative V)) (hφ : Function.Injective φ)
    [Nontrivial V] (hVp : IsPGroup p (Multiplicative V)) (P : Subgroup G)
    (hPp : IsPGroup p P) (hPne : P ≠ ⊥) :
    (⊥ : Subgroup (Multiplicative V)) < fixedPoints φ P ∧
      fixedPoints φ P < (⊤ : Subgroup (Multiplicative V)) :=
  ⟨bot_lt_fixedPoints φ hVp P hPp, fixedPoints_lt_top hφ P hPne⟩

/-- Irreducibility of the action of `G` on the additive group of `V`: no proper
non-trivial `G`-invariant additive subgroup exists. -/
public def IrreducibleAction (φ : G →* MulAut (Multiplicative V)) : Prop :=
  ∀ W : Subgroup (Multiplicative V),
    (∀ g : G, ∀ w : Multiplicative V, w ∈ W → (φ g) w ∈ W) → W = ⊥ ∨ W = ⊤

/-- Exposed constructor/eliminator interface for `IrreducibleAction`. -/
public theorem irreducibleAction_iff {φ : G →* MulAut (Multiplicative V)} :
    IrreducibleAction φ ↔
      ∀ W : Subgroup (Multiplicative V),
        (∀ g : G, ∀ w : Multiplicative V, w ∈ W → (φ g) w ∈ W) → W = ⊥ ∨ W = ⊤ :=
  Iff.rfl

/-- Corollary (used in the proof of Lemma 6.3 to show `O_p(G/C_G(K)) = 1`): if
`P ⊴ G` is a non-identity `p`-subgroup and `G` acts faithfully and irreducibly on `V`,
then `C_V(P) = ⊥`.  Indeed `C_V(P)` is a non-zero `G`-invariant additive subgroup
(Lemma 3.4 and normality of `P`), hence all of `V` by irreducibility, and faithfulness of
the action then forces `P = 1`, a contradiction.  Faithfulness is automatic in the
application, where the acting group is `G/C_G(K)`; without it the statement is false
(e.g. a trivial action on a one-dimensional space). -/
public theorem fixedPoints_eq_bot_of_irreducible_of_normal_pSubgroup
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Finite V]
    {G : Type*} [Group G] (φ : G →* MulAut (Multiplicative V)) (hφ : Function.Injective φ)
    [Nontrivial V] (hVp : IsPGroup p (Multiplicative V)) (P : Subgroup G) [P.Normal]
    (hPp : IsPGroup p P) (hPne : P ≠ ⊥) (hirr : IrreducibleAction φ) :
    fixedPoints φ P = ⊥ := by
  have hne : fixedPoints φ P ≠ ⊥ := (bot_lt_fixedPoints φ hVp P hPp).ne'
  have htop : fixedPoints φ P = ⊤ :=
    (hirr (fixedPoints φ P) (fun g w hw => fixedPoints_invariant_of_normal hw g)).resolve_left
      hne
  have hlt : fixedPoints φ P < (⊤ : Subgroup (Multiplicative V)) :=
    fixedPoints_lt_top hφ P hPne
  exact (hlt.ne htop).elim

end CFSG.Glauberman
