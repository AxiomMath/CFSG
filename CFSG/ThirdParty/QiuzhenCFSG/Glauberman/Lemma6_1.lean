module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

/-!
# Glauberman, "A Characteristic Subgroup of a p-Stable Group" — Lemma 6.1 (Baer's lemma)

This file proves Lemma 6.1 of [6] (Glauberman, *A Characteristic Subgroup of a p-Stable
Group*, Canad. J. Math. 20 (1968), 1101–1135), following the validated transcription in
`refs/glauberman-p-stable.tex` L1599–L1613:

> **Lemma (Baer).** Let `g` be a `p`-element of a finite group `G`.  Suppose that for every
> `x ∈ G`, `g` and `gˣ` generate a `p`-group.  Then `g ∈ O_p(G)`.

Formal statement (`lemma6_1`): if `IsPGroup p (Subgroup.zpowers g)` and for every `x`,
`Subgroup.closure {g, x * g * x⁻¹}` is a `p`-group, then `g ∈ pCore p G`.  (The paper writes
the conjugate of `g` as `gˣ = x⁻¹gx`; the pinned statement uses `x * g * x⁻¹ = g^{x⁻¹}`,
which is immaterial since the quantifier ranges over all of `G`.)

## Proof route

The repository already contains the source-faithful Alperin--Lyons form of
Baer--Suzuki,
`BenderSuzuki.gorenstein_3_8_2_conjugacy_class_le_pCore`.  The wrapper
`BaerSuzuki.baer_suzuki` adapts it to exactly this theorem's pair-generation
hypothesis, so `lemma6_1` is a direct application.  The Engel definitions and
proved helper lemmas below are retained as independent public infrastructure;
the former registered Baer bridge has been deleted.

We also extract, as `baer_contrapositive`, the exact contrapositive shape used in the proof
of Lemma 6.3 ([6], L1694–L1701): if `C ⊴ G` and `⟨xC, (x^w)C⟩` is a `p`-group for every
`w ∈ G`, then `xC ∈ O_p(G/C)`.
-/

namespace CFSG.Glauberman

variable {G : Type*} [Group G]

/-- The iterated left-normed commutator `[x, g, ..., g]` with `n` copies of `g`
(paper notation `[x, g; n]`), formed with Mathlib's (right-convention) commutator element
`⁅a, b⁆ = a*b*a⁻¹*b⁻¹`. -/
public def engelCommutator (x g : G) : ℕ → G
  | 0 => x
  | n + 1 => ⁅engelCommutator x g n, g⁆

@[simp] theorem engelCommutator_zero (x g : G) : engelCommutator x g 0 = x :=
  rfl

@[simp] theorem engelCommutator_succ (x g : G) (n : ℕ) :
    engelCommutator x g (n + 1) = ⁅engelCommutator x g n, g⁆ :=
  rfl

/-! ## Machinery for the bounded left Engel step -/

/-- The iterated commutator unwinds: `[x, g; n+1] = [[x, g], g; n]`. -/
private lemma engelCommutator_iterate (x g : G) :
    ∀ n : ℕ, engelCommutator x g (n + 1) = engelCommutator (engelCommutator x g 1) g n
  | 0 => rfl
  | n + 1 => by
    change ⁅engelCommutator x g (n + 1), g⁆ = ⁅engelCommutator (engelCommutator x g 1) g n, g⁆
    congr 1
    exact engelCommutator_iterate x g n

/-- Commutators computed inside a subgroup agree with those computed in the ambient group
(the coercion `↥H → G` is the inclusion homomorphism). -/
private lemma engelCommutator_coe (H : Subgroup G) (a b : ↥H) :
    ∀ n : ℕ, (↑(engelCommutator a b n) : G) = engelCommutator (a : G) (b : G) n
  | 0 => rfl
  | n + 1 => by
    rw [engelCommutator_succ, engelCommutator_succ]
    have hcomm : (↑⁅engelCommutator a b n, b⁆ : G) =
        ⁅(↑(engelCommutator a b n) : G), (↑b : G)⁆ := by
      change (H.subtype ⁅engelCommutator a b n, b⁆ : G) =
        ⁅H.subtype (engelCommutator a b n), H.subtype b⁆
      rw [map_commutatorElement]
    rw [hcomm]
    rw [engelCommutator_coe H a b n]

/-- If `x ∈ Z_m(G)`, then `[x, g; n] ∈ Z_{m-n}(G)` for every `n ≤ m`. -/
private lemma engelCommutator_mem_upperCentralSeries_sub (x g : G) :
    ∀ {n m : ℕ}, n ≤ m → x ∈ Subgroup.upperCentralSeries G m →
      engelCommutator x g n ∈ Subgroup.upperCentralSeries G (m - n)
  | 0, m, hnm, hx => by
    simpa using hx
  | n + 1, m, hnm, hx => by
    have hrec := engelCommutator_mem_upperCentralSeries_sub x g (n := n) (m := m) (by omega) hx
    have hm' : m - n = (m - (n + 1)) + 1 := by omega
    rw [hm'] at hrec
    rw [engelCommutator_succ]
    exact
      (Subgroup.mem_upperCentralSeries_succ_iff (n := m - (n + 1))
        (x := engelCommutator x g n)).1 hrec g

/-- If a subgroup `H` of `G` has nilpotency class at most `c` and both `⁅x, g⁆` and `g` lie
in `H`, then the iterated commutator `[x, g, ..., g]` with `c + 2` copies of `g` is trivial
(weight `c + 3 > c + 1`, the bound for a group of class `≤ c`). -/
private lemma engelCommutator_eq_one_of_nilpotencyClass_le {G : Type*} [Group G] {H : Subgroup G}
    {c : ℕ} [Group.IsNilpotent (↥H)] (hclass : Group.nilpotencyClass (↥H) ≤ c)
    {x g : G} (hx : ⁅x, g⁆ ∈ H) (hg : g ∈ H) :
    engelCommutator x g (c + 2) = 1 := by
  have htop : Subgroup.upperCentralSeries (↥H) (c + 1) = ⊤ := by
    exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := ↥H) (n := c + 1)).mpr
      (by omega)
  let a : ↥H := ⟨⁅x, g⁆, hx⟩
  let b : ↥H := ⟨g, hg⟩
  have hmem := engelCommutator_mem_upperCentralSeries_sub a b
    (n := c + 1) (m := c + 1) le_rfl (by simp [htop])
  have hmem0 : engelCommutator a b (c + 1) ∈ (⊥ : Subgroup (↥H)) := by
    simpa using hmem
  have h1 : engelCommutator a b (c + 1) = 1 := Subgroup.mem_bot.mp hmem0
  rw [engelCommutator_iterate (x := x) (g := g) (n := c + 1)]
  rw [show engelCommutator (engelCommutator x g 1) g (c + 1) =
      engelCommutator (a : G) (b : G) (c + 1) by rfl]
  rw [← engelCommutator_coe H a b (c + 1)]
  exact congrArg (fun y : ↥H => (y : G)) h1

/-- The nilpotency class is invariant under group isomorphism. -/
private lemma nilpotencyClass_eq_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : Group.nilpotencyClass G = Group.nilpotencyClass H := by
  classical
  by_cases hG : Group.IsNilpotent G
  · have hH : Group.IsNilpotent H := (Group.isNilpotent_congr e).1 hG
    have : Group.IsNilpotent G := hG
    have : Group.IsNilpotent H := hH
    have hmin : ∀ n : ℕ, Subgroup.upperCentralSeries G n = ⊤ ↔ Subgroup.upperCentralSeries H n = ⊤ := by
      intro n
      have hcomap : (Subgroup.upperCentralSeries G n).comap (e.symm : H →* G) =
          Subgroup.upperCentralSeries H n :=
        Subgroup.comap_upperCentralSeries e.symm n
      rw [← hcomap]
      constructor
      · intro h
        rw [h]
        exact Subgroup.comap_top (f := (e.symm : H →* G))
      · intro h
        have hmap : ((Subgroup.upperCentralSeries G n).comap (e.symm : H →* G)).map
              (e.symm : H →* G) = Subgroup.upperCentralSeries G n :=
          Subgroup.map_comap_eq_self_of_surjective (f := (e.symm : H →* G)) e.symm.surjective
            (Subgroup.upperCentralSeries G n)
        simpa [h] using hmap.symm
    rw [Group.nilpotencyClass_def, Group.nilpotencyClass_def]
    apply le_antisymm
    · apply le_of_not_gt
      intro hgt
      exact (Nat.find_min (Group.IsNilpotent.nilpotent G) hgt) (by
        rw [hmin (Nat.find (Group.IsNilpotent.nilpotent H))]
        exact Nat.find_spec (Group.IsNilpotent.nilpotent H))
    · apply le_of_not_gt
      intro hgt
      exact (Nat.find_min (Group.IsNilpotent.nilpotent H) hgt) (by
        rw [← hmin (Nat.find (Group.IsNilpotent.nilpotent G))]
        exact Nat.find_spec (Group.IsNilpotent.nilpotent G))
  · have hH : ¬ Group.IsNilpotent H := by
      intro hH
      exact hG ((Group.isNilpotent_congr e).2 hH)
    rw [Group.nilpotencyClass_of_not_nilpotent hG, Group.nilpotencyClass_of_not_nilpotent hH]

/-! ## Machinery for the `O_p` step -/

/-- The image of a Sylow `p`-subgroup of a normal nilpotent subgroup `N` of `G` is contained
in `O_p(G)`.  (Re-derivation of the module-private `Sylow.map_le_pCore` from
`FeitThompson/PCore/PCore.lean`, which is not exported.) -/
private lemma sylow_map_le_pCore {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : N.Normal) (hnil : Group.IsNilpotent (↥N)) (p : ℕ) [Fact p.Prime]
    (P : Sylow p (↥N)) : (P : Subgroup (↥N)).map N.subtype ≤ pCore p G := by
  have hP_normal : (P : Subgroup (↥N)).Normal := Group.IsNilpotent.sylow_normal hnil p P
  have hP_char : (P : Subgroup (↥N)).Characteristic :=
    Sylow.characteristic_of_normal P hP_normal
  have : N.Normal := hN
  have : (P : Subgroup (↥N)).Characteristic := hP_char
  have : ((P : Subgroup (↥N)).map N.subtype).Normal := inferInstance
  have hpg : IsPGroup p ((P : Subgroup (↥N)).map N.subtype) := IsPGroup.map P.isPGroup' N.subtype
  exact le_sSup ⟨inferInstance, hpg⟩

/-! ## Lemma 6.1 (Baer's lemma) -/

/-- **Lemma 6.1 (Baer)** ([6], §6; `refs/glauberman-p-stable.tex` L1599–L1613): if `g` is a
`p`-element of the finite group `G` and, for every `x ∈ G`, `g` and its conjugate
`x * g * x⁻¹` generate a `p`-group, then `g ∈ O_p(G)` (`pCore p G`).

The proof uses the already established Baer--Suzuki theorem in the exact
`O_p`-membership form. -/
public theorem lemma6_1 {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (g : G) (hg : IsPGroup p (Subgroup.zpowers g))
    (hall : ∀ x : G, IsPGroup p (Subgroup.closure {g, x * g * x⁻¹} : Subgroup G)) :
    g ∈ pCore p G := by
  exact BaerSuzuki.baer_suzuki g hg (fun x => by simpa using hall x)

/-! ## The contrapositive in the shape used by Lemma 6.3 -/

/-- The exact contrapositive of Lemma 6.1 needed in the proof of Lemma 6.3
([6], §6, L1694–L1701): if `C ⊴ G` and for every `w ∈ G` the subgroup
`⟨xC, (x^w)C⟩ = ⟨x, x^w, C⟩/C` of `G/C` is a `p`-group (where `x^w = w*x*w⁻¹`), then the
coset `xC` lies in `O_p(G/C)`.

In the paper's application, `x` is an element with coset outside `O_p(N(H)/C(H))`; the
contrapositive then produces the `w` with `⟨x, x^w, C⟩/C` not a `p`-group.  The `p`-element
hypothesis of Lemma 6.1 is automatic: taking `w = 1` shows the cyclic subgroup generated by
`xC` is a `p`-group. -/
public theorem baer_contrapositive {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (C : Subgroup G) [C.Normal] (x : G) :
    (∀ w : G,
        IsPGroup p
          (Subgroup.closure {QuotientGroup.mk' C x, QuotientGroup.mk' C (w * x * w⁻¹)} :
            Subgroup (G ⧸ C))) →
      QuotientGroup.mk' C x ∈ pCore p (G ⧸ C) := by
  intro hall
  have hg : IsPGroup p (Subgroup.zpowers (QuotientGroup.mk' C x)) := by
    rw [Subgroup.zpowers_eq_closure]
    have h1 := hall 1
    have hEq : 1 * x * 1⁻¹ = x := by simp
    rw [hEq] at h1
    have hdup : Subgroup.closure {QuotientGroup.mk' C x, QuotientGroup.mk' C x} =
        Subgroup.closure {QuotientGroup.mk' C x} := by
      congr 1
      ext y
      simp
    rw [← hdup]
    exact h1
  have hall' : ∀ y : G ⧸ C,
      IsPGroup p
        (Subgroup.closure
          {QuotientGroup.mk' C x, y * QuotientGroup.mk' C x * y⁻¹} : Subgroup (G ⧸ C)) := by
    intro y
    rcases QuotientGroup.mk'_surjective C y with ⟨w, rfl⟩
    have hEq : QuotientGroup.mk' C w * QuotientGroup.mk' C x * (QuotientGroup.mk' C w)⁻¹ =
        QuotientGroup.mk' C (w * x * w⁻¹) := by
      simp [MonoidHom.map_mul, MonoidHom.map_inv]
    rw [hEq]
    exact hall w
  exact lemma6_1 (p := p) (G := G ⧸ C) (g := QuotientGroup.mk' C x) hg hall'

-- Axiom audit: both declarations are sorry-free.
#print axioms lemma6_1
#print axioms baer_contrapositive

end CFSG.Glauberman
