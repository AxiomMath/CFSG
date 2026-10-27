module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.DegreeBounds
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.GroupTheory.Subgroup.Center

namespace CFSG
end CFSG
open CFSG
/-!
# Peterfalvi, Section 1, Proposition (1.8)

This file is the Lean target for `PFtest/Blueprint/section1/proposition_1_8.tex`.

Current scope discipline:

* Only Mathlib modules are imported.
* No Lean files outside `PFtest` are imported or read.
* The book proposition is stated for an irreducible `Representation`; the
  condition \(D/B \le Z(C/B)\) is represented by the direct commutator
  predicate `Theory.Character.IsCentralModulo` on the subgroups of `C`.
-/

noncomputable section

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section1
universe u
universe v

/-! ## Basic notation for Proposition (1.8) -/

/-! ## Honest helper lemmas -/

lemma subgroup_card_pos {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    (0 : ℝ) < Nat.card H := by
  exact_mod_cast (show 0 < Nat.card H by exact Nat.card_pos)

theorem proposition_1_8_from_square_bound
    {G : Type*} [Group G] [Finite G] (C D : Subgroup G) (psiDeg : ℝ)
    (_hpsi_nonneg : 0 ≤ psiDeg)
    (hsq :
      psiDeg ^ 2 ≤
        (Nat.card G : ℝ) ^ 2 / ((Nat.card C : ℝ) * Nat.card D)) :
    psiDeg ≤ Nat.card G / Real.sqrt ((Nat.card C : ℝ) * Nat.card D) := by
  have hpsi_nonneg := _hpsi_nonneg
  have hCpos : (0 : ℝ) < Nat.card C := subgroup_card_pos C
  have hDpos : (0 : ℝ) < Nat.card D := subgroup_card_pos D
  have hCDpos : 0 < (Nat.card C : ℝ) * Nat.card D := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((Nat.card C : ℝ) * Nat.card D) := Real.sqrt_nonneg _
  have hbound_nonneg : 0 ≤ Nat.card G / Real.sqrt ((Nat.card C : ℝ) * Nat.card D) := by
    positivity
  have hsqrt_sq :
      Real.sqrt ((Nat.card C : ℝ) * Nat.card D) ^ 2 =
        (Nat.card C : ℝ) * Nat.card D := by
    rw [sq, Real.mul_self_sqrt (show 0 ≤ (Nat.card C : ℝ) * Nat.card D by positivity)]
  have hsqrt_ne : Real.sqrt ((Nat.card C : ℝ) * Nat.card D) ≠ 0 := by
    apply Real.sqrt_ne_zero'.2
    positivity
  have hbound_sq :
      (Nat.card G / Real.sqrt ((Nat.card C : ℝ) * Nat.card D)) ^ 2 =
        (Nat.card G : ℝ) ^ 2 / ((Nat.card C : ℝ) * Nat.card D) := by
    field_simp [hsqrt_ne]
    rw [hsqrt_sq]
  nlinarith [hsq, hbound_sq, hpsi_nonneg, hbound_nonneg]

private abbrev orbitSpanGenerators {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {C : Subgroup G} (S : Subrepresentation (ρ.comp C.subtype)) : Set V :=
  Set.range fun gw : G × S.toSubmodule => ρ gw.1 (gw.2 : V)

private def orbitSpanSubrepresentation {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {C : Subgroup G} (S : Subrepresentation (ρ.comp C.subtype)) :
    Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (orbitSpanGenerators ρ S)
  apply_mem_toSubmodule g v hv := by
    refine Submodule.span_induction (p := fun v _ => ρ g v ∈
        Submodule.span ℂ (orbitSpanGenerators ρ S)) ?_ ?_ ?_ ?_ hv
    · intro v hv
      rcases hv with ⟨⟨x, w⟩, rfl⟩
      refine Submodule.subset_span ?_
      refine ⟨(g * x, w), ?_⟩
      simp [map_mul, Module.End.mul_apply]
    · simp
    · intro x y _ _ hx hy
      simpa [map_add] using Submodule.add_mem _ hx hy
    · intro a x _ hx
      simpa [map_smul] using Submodule.smul_mem _ a hx

private theorem subrepresentation_le_orbitSpan {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {C : Subgroup G} (S : Subrepresentation (ρ.comp C.subtype)) :
    S.toSubmodule ≤ (orbitSpanSubrepresentation ρ S).toSubmodule := by
  intro v hv
  refine Submodule.subset_span ?_
  refine ⟨(1, ⟨v, hv⟩), ?_⟩
  simp

private theorem orbitSpanSubrepresentation_eq_top_of_irreducible
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    {C : Subgroup G} (S : Subrepresentation (ρ.comp C.subtype))
    [Representation.IsIrreducible S.toRepresentation] :
    orbitSpanSubrepresentation ρ S = ⊤ := by
  haveI : Nontrivial S.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial S.toRepresentation
  have hS_ne_bot : S.toSubmodule ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp inferInstance
  have hU_ne_bot : orbitSpanSubrepresentation ρ S ≠ ⊥ := by
    intro hU
    have hS_le_bot : S.toSubmodule ≤ (⊥ : Submodule ℂ V) := by
      have hUsub :
          (orbitSpanSubrepresentation ρ S).toSubmodule = (⊥ : Submodule ℂ V) := by
        calc
          (orbitSpanSubrepresentation ρ S).toSubmodule =
              (⊥ : Subrepresentation ρ).toSubmodule :=
            congrArg Subrepresentation.toSubmodule hU
          _ = (⊥ : Submodule ℂ V) := rfl
      rw [← hUsub]
      exact subrepresentation_le_orbitSpan (ρ := ρ) S
    exact hS_ne_bot (le_antisymm hS_le_bot bot_le)
  rcases (inferInstance : Representation.IsIrreducible ρ).eq_bot_or_eq_top
      (orbitSpanSubrepresentation ρ S) with hbot | htop
  · exact (hU_ne_bot hbot).elim
  · exact htop

private def cosetOrbitMap {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (C : Subgroup G) (S : Subrepresentation (ρ.comp C.subtype)) :
    ((G ⧸ C) → S.toSubmodule) →ₗ[ℂ] V where
  toFun f := ∑ q : G ⧸ C, ρ (Quotient.out q) (f q : V)
  map_add' f f' := by
    simp [map_add, Finset.sum_add_distrib]
  map_smul' a f := by
    simp [map_smul, Finset.smul_sum]

private theorem left_coset_out_inv_mul_mem {G : Type*} [Group G]
    (C : Subgroup G) (g : G) :
    (Quotient.out (Quotient.mk (QuotientGroup.leftRel C) g))⁻¹ * g ∈ C := by
  simpa [QuotientGroup.leftRel_apply] using
    (Quotient.mk_out (s := QuotientGroup.leftRel C) g)

private theorem orbit_generator_mem_cosetOrbitMap_range
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (C : Subgroup G) (S : Subrepresentation (ρ.comp C.subtype))
    (g : G) (w : S.toSubmodule) :
    ρ g (w : V) ∈ LinearMap.range (cosetOrbitMap ρ C S) := by
  classical
  let q : G ⧸ C := Quotient.mk (QuotientGroup.leftRel C) g
  let c : C := ⟨(Quotient.out q)⁻¹ * g, by
    simpa [q] using left_coset_out_inv_mul_mem C g⟩
  let u : S.toSubmodule :=
    ⟨(ρ.comp C.subtype) c (w : V), S.apply_mem_toSubmodule c w.2⟩
  let f : (G ⧸ C) → S.toSubmodule := fun q' => if q' = q then u else 0
  refine ⟨f, ?_⟩
  calc
    cosetOrbitMap ρ C S f = ρ (Quotient.out q) (u : V) := by
      dsimp [cosetOrbitMap]
      rw [Finset.sum_eq_single q]
      · simp [f]
      · intro q' _ hq'
        simp [f, hq']
      · intro hq
        simp at hq
    _ = ρ g (w : V) := by
      simp [u, c, map_mul, Module.End.mul_apply]

private theorem orbitSpan_le_cosetOrbitMap_range
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (C : Subgroup G) (S : Subrepresentation (ρ.comp C.subtype)) :
    (orbitSpanSubrepresentation ρ S).toSubmodule ≤
      LinearMap.range (cosetOrbitMap ρ C S) := by
  refine Submodule.span_le.mpr ?_
  intro v hv
  rcases hv with ⟨⟨g, w⟩, rfl⟩
  exact orbit_generator_mem_cosetOrbitMap_range ρ C S g w

private theorem cosetOrbitMap_range_eq_top_of_irreducible
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ]
    (C : Subgroup G) (S : Subrepresentation (ρ.comp C.subtype))
    [Representation.IsIrreducible S.toRepresentation] :
    LinearMap.range (cosetOrbitMap ρ C S) = ⊤ := by
  have hUtop :
      (orbitSpanSubrepresentation ρ S).toSubmodule = (⊤ : Submodule ℂ V) := by
    calc
      (orbitSpanSubrepresentation ρ S).toSubmodule =
          (⊤ : Subrepresentation ρ).toSubmodule :=
        congrArg Subrepresentation.toSubmodule
          (orbitSpanSubrepresentation_eq_top_of_irreducible (ρ := ρ) S)
      _ = (⊤ : Submodule ℂ V) := rfl
  apply top_unique
  rw [← hUtop]
  exact orbitSpan_le_cosetOrbitMap_range ρ C S

private theorem irreducible_finrank_le_index_mul_subrepresentation_finrank
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (C : Subgroup G) (S : Subrepresentation (ρ.comp C.subtype))
    [Representation.IsIrreducible S.toRepresentation] :
    Module.finrank ℂ V ≤ C.index * Module.finrank ℂ S.toSubmodule := by
  classical
  let Φ := cosetOrbitMap ρ C S
  have htop : LinearMap.range Φ = (⊤ : Submodule ℂ V) :=
    cosetOrbitMap_range_eq_top_of_irreducible (ρ := ρ) C S
  have hle : Module.finrank ℂ (LinearMap.range Φ) ≤
      Module.finrank ℂ ((G ⧸ C) → S.toSubmodule) :=
    LinearMap.finrank_range_le Φ
  calc
    Module.finrank ℂ V = Module.finrank ℂ (LinearMap.range Φ) := by
      rw [htop, finrank_top]
    _ ≤ Module.finrank ℂ ((G ⧸ C) → S.toSubmodule) := hle
    _ = Fintype.card (G ⧸ C) * Module.finrank ℂ S.toSubmodule := by
      simpa using
        (Module.finrank_pi_fintype (R := ℂ) (M := fun _ : G ⧸ C => S.toSubmodule))
    _ = C.index * Module.finrank ℂ S.toSubmodule := by
      rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]

private theorem subgroupOf_nat_card_eq {G : Type*} [Group G] [Finite G]
    {D C : Subgroup G} (hDC : D ≤ C) :
    Nat.card (D.subgroupOf C) = Nat.card D := by
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv

private theorem proposition_1_8_square_bound
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (B C D : Subgroup G)
    (hBker : ∀ b : B, ρ b = (1 : Module.End ℂ V))
    (_hBD : B ≤ D) (hDC : D ≤ C)
    (hcentral :
      Theory.Character.IsCentralModulo
        (B.subgroupOf C) (D.subgroupOf C)) :
    (Module.finrank ℂ V : ℝ) ^ 2 ≤
      (Nat.card G : ℝ) ^ 2 / ((Nat.card C : ℝ) * Nat.card D) := by
  classical
  haveI : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let ρC : Representation ℂ C V := ρ.comp C.subtype
  obtain ⟨S, hSirr⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρC
  letI : Representation.IsIrreducible S.toRepresentation := hSirr
  let Bsub : Subgroup C := B.subgroupOf C
  let Dsub : Subgroup C := D.subgroupOf C
  have hdim_le :
      Module.finrank ℂ V ≤ C.index * Module.finrank ℂ S.toSubmodule :=
    irreducible_finrank_le_index_mul_subrepresentation_finrank (ρ := ρ) C S
  have hBker_sub : ∀ b : Bsub,
      S.toRepresentation b = (1 : Module.End ℂ S.toSubmodule) := by
    intro b
    ext w
    have hbB : ((b : Bsub) : C) ∈ Bsub := b.2
    have hbG : (((b : Bsub) : C) : G) ∈ B := by
      exact (Subgroup.mem_subgroupOf.mp hbB)
    have hρb := hBker ⟨(((b : Bsub) : C) : G), hbG⟩
    simpa [Subrepresentation.toRepresentation, ρC] using
      congrArg (fun f : Module.End ℂ V => f (w : V)) hρb
  have hSsq :
      Module.finrank ℂ S.toSubmodule ^ 2 ≤ Dsub.index :=
    Theory.Character.irreducible_finrank_sq_le_index_of_centralModulo_kernel
      (ρ := S.toRepresentation) Bsub Dsub hBker_sub (by
        simpa [Bsub, Dsub] using hcentral)
  have hsq_nat :
      Module.finrank ℂ V ^ 2 ≤ C.index ^ 2 * Dsub.index := by
    calc
      Module.finrank ℂ V ^ 2
          ≤ (C.index * Module.finrank ℂ S.toSubmodule) ^ 2 :=
            Nat.pow_le_pow_left hdim_le 2
      _ = C.index ^ 2 * Module.finrank ℂ S.toSubmodule ^ 2 := by ring
      _ ≤ C.index ^ 2 * Dsub.index := Nat.mul_le_mul_left _ hSsq
  have hsq_real :
      (Module.finrank ℂ V : ℝ) ^ 2 ≤ (C.index : ℝ) ^ 2 * Dsub.index := by
    exact_mod_cast hsq_nat
  have hCpos : (0 : ℝ) < Nat.card C := subgroup_card_pos C
  have hDpos : (0 : ℝ) < Nat.card D := subgroup_card_pos D
  have hCindex :
      (C.index : ℝ) * Nat.card C = Nat.card G := by
    exact_mod_cast C.index_mul_card
  have hDsub_card : Nat.card Dsub = Nat.card D := by
    simpa [Dsub] using subgroupOf_nat_card_eq (D := D) (C := C) hDC
  have hDindex :
      (Dsub.index : ℝ) * Nat.card D = Nat.card C := by
    have hDindex_nat : Dsub.index * Nat.card D = Nat.card C := by
      rw [← hDsub_card]
      exact Dsub.index_mul_card
    exact_mod_cast hDindex_nat
  have htarget :
      (C.index : ℝ) ^ 2 * Dsub.index =
        (Nat.card G : ℝ) ^ 2 / ((Nat.card C : ℝ) * Nat.card D) := by
    rw [← hCindex, ← hDindex]
    field_simp [hCpos.ne', hDpos.ne']
  exact hsq_real.trans_eq htarget

/-- Peterfalvi, Proposition (1.8), in `Representation` form.

The hypothesis `Theory.Character.IsCentralModulo (B.subgroupOf C) (D.subgroupOf C)`
is the direct commutator form of \(D/B \le Z(C/B)\). -/
public theorem proposition_1_8
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (B C D : Subgroup G)
    (hBker : ∀ b : B, ρ b = (1 : Module.End ℂ V))
    (hBD : B ≤ D) (hDC : D ≤ C)
    (_hBnormal : (B.subgroupOf C).Normal)
    (hcentral :
      Theory.Character.IsCentralModulo
        (B.subgroupOf C) (D.subgroupOf C)) :
    (Module.finrank ℂ V : ℝ) ≤
      Nat.card G / Real.sqrt ((Nat.card C : ℝ) * Nat.card D) := by
  exact proposition_1_8_from_square_bound C D (Module.finrank ℂ V)
    (by positivity)
    (proposition_1_8_square_bound (ρ := ρ) B C D hBker hBD hDC hcentral)

end CFSG.Section1
