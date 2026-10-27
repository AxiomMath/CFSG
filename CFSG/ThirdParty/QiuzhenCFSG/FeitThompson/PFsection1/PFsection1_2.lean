module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Unbundled

namespace CFSG
end CFSG
open CFSG
/-!
# Peterfalvi, Section 1, Proposition (1.2)

This file is the Lean target for `PFtest/Blueprint/section1/proposition_1_2.tex`.

Current scope discipline:

* Only Mathlib modules are imported.
* No Lean files outside `PFtest` are imported or read.
* Theorem proofs are introduced in blueprint order and should be decomposed
  into named local nodes before being closed directly.
-/

noncomputable section

open scoped BigOperators

namespace CFSG.Section1
universe u
universe v

/-! ## Basic notation for Proposition (1.2) -/

/-- `subgroupInKernel ρ H` means that the restriction of `ρ` to `H` is trivial,
so `H` is contained in the kernel of the character afforded by `ρ`. -/
public def subgroupInKernel
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) : Prop :=
  Representation.IsTrivial (ρ.comp H.subtype)

public theorem subgroupInKernel_iff
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) :
    subgroupInKernel ρ H ↔ Representation.IsTrivial (ρ.comp H.subtype) :=
  Iff.rfl

/-! ## Small representation-theoretic nodes for Proposition (1.2) -/

lemma invariants_eq_bot_of_nontrivial
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (H : Subgroup G) [H.Normal]
    (hHker : ¬ subgroupInKernel ρ H) :
    Representation.invariants (ρ.comp H.subtype) = ⊥ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := Representation.invariants (ρ.comp H.subtype)
      apply_mem_toSubmodule := Representation.le_comap_invariants ρ H }
  rcases IsSimpleOrder.eq_bot_or_eq_top S with hS | hS
  · exact (by
      have h := congrArg Subrepresentation.toSubmodule hS
      change Representation.invariants (ρ.comp H.subtype) = (⊥ : Submodule ℂ V) at h
      exact h)
  · have hStop : Representation.invariants (ρ.comp H.subtype) = ⊤ := by
      have h := congrArg Subrepresentation.toSubmodule hS
      change Representation.invariants (ρ.comp H.subtype) = (⊤ : Submodule ℂ V) at h
      exact h
    exfalso
    apply hHker
    refine ⟨?_⟩
    intro h
    ext v
    have hv : v ∈ Representation.invariants (ρ.comp H.subtype) := by
      rw [hStop]
      simp
    exact hv h

lemma subgroup_norm_eq_zero
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (H : Subgroup G) [Fintype ↥H]
    (hInv : Representation.invariants (ρ.comp H.subtype) = ⊥) :
    Representation.norm (ρ.comp H.subtype) = 0 := by
  ext v
  have hv : Representation.norm (ρ.comp H.subtype) v ∈
      Representation.invariants (ρ.comp H.subtype) := by
    intro h
    simpa using Representation.self_norm_apply (ρ.comp H.subtype) h v
  rw [hInv] at hv
  simpa using hv

lemma subgroup_mul_character_sum_eq_card_mul_character
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    {H : Subgroup G} [Fintype ↥H] [H.Normal]
    {g : G}
    (hg : H ⊓ Subgroup.centralizer ({g} : Set G) = ⊥) :
    ∑ h : H, ρ.character ((h : G) * g) = (Nat.card H : ℂ) * ρ.character g := by
  let δ : H → H := by
    intro h
    refine ⟨(h : G) * g * h⁻¹ * g⁻¹, ?_⟩
    have hgmem : g * ((h : G)⁻¹) * g⁻¹ ∈ H := by
      exact Subgroup.Normal.conj_mem ‹H.Normal› ((h : G)⁻¹) (H.inv_mem h.2) g
    simpa [mul_assoc] using H.mul_mem h.2 hgmem
  have hδ_inj : Function.Injective δ := by
    intro a b hab
    apply Subtype.ext
    have hab' : ((δ a : H) : G) = (δ b : H) := congrArg Subtype.val hab
    have hcomm : ((b⁻¹ * a : H) : G) * g = g * ((b⁻¹ * a : H) : G) := by
      have hab1 : (a : G) * g * a⁻¹ = (b : G) * g * b⁻¹ := by
        have := congrArg (fun x : G => x * g) hab'
        simpa [δ, mul_assoc] using this
      have hab2 := congrArg (fun x : G => (b : G)⁻¹ * x * (a : G)) hab1
      simpa [mul_assoc] using hab2
    have hmem :
        (((b⁻¹ * a : H) : G)) ∈ H ⊓ Subgroup.centralizer ({g} : Set G) := by
      refine ⟨(b⁻¹ * a : H).2, ?_⟩
      show (((b⁻¹ * a : H) : G)) ∈ Subgroup.centralizer ({g} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hcomm.symm
    have hone_mem : (((b⁻¹ * a : H) : G)) ∈ (⊥ : Subgroup G) := by
      simpa [hg] using hmem
    have hone : ((b⁻¹ * a : H) : G) = 1 := by
      simpa using hone_mem
    have hone' : b⁻¹ * a = (1 : H) := by
      apply Subtype.ext
      simpa using hone
    exact by
      have := congrArg (fun x : H => b * x) hone'
      simpa using this
  have hδ_bij : Function.Bijective δ :=
    ⟨hδ_inj, Finite.surjective_of_injective hδ_inj⟩
  calc
    ∑ h : H, ρ.character ((h : G) * g)
        = ∑ h : H, ρ.character (((δ h : H) : G) * g) := by
            symm
            exact Function.Bijective.sum_comp hδ_bij
              (fun h : H => ρ.character ((h : G) * g))
    _ = ∑ h : H, ρ.character ((h : G) * g * h⁻¹) := by
      refine Finset.sum_congr rfl ?_
      intro h hh
      simp [δ, mul_assoc]
    _ = ∑ _h : H, ρ.character g := by
      refine Finset.sum_congr rfl ?_
      intro h hh
      simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g (h : G)
    _ = (Nat.card H : ℂ) * ρ.character g := by
      simp

/-! ## Proposition (1.2) -/

public theorem proposition_1_2
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    {H : Subgroup G} [H.Normal]
    (hHker : ¬ subgroupInKernel ρ H)
    {g : G}
    (hg : H ⊓ Subgroup.centralizer ({g} : Set G) = ⊥) :
    ρ.character g = 0 := by
  classical
  letI : Fintype ↥H := Fintype.ofFinite ↥H
  have hInv : Representation.invariants (ρ.comp H.subtype) = ⊥ :=
    invariants_eq_bot_of_nontrivial ρ H hHker
  have hnorm : Representation.norm (ρ.comp H.subtype) = 0 :=
    subgroup_norm_eq_zero ρ H hInv
  have htrace_zero :
      LinearMap.trace ℂ V (Representation.norm (ρ.comp H.subtype) * ρ g) = 0 := by
    rw [hnorm]
    simp
  have htrace_sum :
      LinearMap.trace ℂ V (Representation.norm (ρ.comp H.subtype) * ρ g) =
        ∑ h : H, ρ.character ((h : G) * g) := by
    simp [Representation.norm, Representation.character, Finset.sum_mul]
  have hsum :
      ∑ h : H, ρ.character ((h : G) * g) = (Nat.card H : ℂ) * ρ.character g :=
    subgroup_mul_character_sum_eq_card_mul_character ρ hg
  have hcard_ne : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card H ≠ 0)
  have hmain : (Nat.card H : ℂ) * ρ.character g = 0 := by
    rw [← hsum, ← htrace_sum]
    exact htrace_zero
  exact by
    apply mul_eq_zero.mp at hmain
    rcases hmain with hcard | hchar
    · exact (hcard_ne hcard).elim
    · exact hchar

end CFSG.Section1
