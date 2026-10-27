module

public import CFSG.RepresentationTheory.ScalarCommutatorDimension
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.RepresentationTheory

open Subgroup
open scoped commutatorElement

theorem scalar_subgroup_le_center_and_isCyclic
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [Nontrivial V]
    (ρ : Representation k G V) (hρ : Function.Injective ρ)
    (A : Subgroup G)
    (hA : ∀ a ∈ A, ∃ c : k, ρ a = c • (1 : Module.End k V)) :
    A ≤ Subgroup.center G ∧ IsCyclic A := by
  classical
  have : Finite A := Subtype.finite
  let c : A → k := fun a => Classical.choose (hA a.1 a.2)
  have hc : ∀ a : A, ρ (a : G) = c a • (1 : Module.End k V) :=
    fun a => Classical.choose_spec (hA a.1 a.2)
  have hc_unique : ∀ (a : A) (d : k),
      ρ (a : G) = d • (1 : Module.End k V) → c a = d := by
    intro a d hd
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h : c a • (1 : Module.End k V) = d • (1 : Module.End k V) := by
      rw [← hc a, hd]
    have h1 : c a • v = d • v := congrArg (fun f : Module.End k V => f v) h
    have h2 : (c a - d) • v = 0 := by
      rw [sub_smul, h1, sub_self]
    have h3 : c a - d = 0 := by
      rcases smul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hv
    exact sub_eq_zero.mp h3
  have hc_ne : ∀ a : A, c a ≠ 0 := by
    intro a h0
    have hρa : ρ (a : G) = 0 := by rw [hc a, h0, zero_smul]
    have hinv : ρ (a : G) * ρ ((a : G)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    rw [hρa, zero_mul] at hinv
    have h10 : (1 : Module.End k V) = 0 := hinv.symm
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have := congrArg (fun f : Module.End k V => f v) h10
    exact hv (by simpa using this)
  let χ : A →* kˣ :=
  { toFun := fun a => Units.mk0 (c a) (hc_ne a)
    map_one' := by
      apply Units.ext
      exact hc_unique 1 1 (by simp)
    map_mul' := by
      intro a b
      apply Units.ext
      apply hc_unique (a * b) (c a * c b)
      change ρ ((a : G) * (b : G)) = (c a * c b) • (1 : Module.End k V)
      rw [map_mul, hc a, hc b]
      rw [smul_mul_smul]
      simp }
  have hχinj : Function.Injective χ := by
    intro a b h
    have hc_eq : c a = c b := by
      have := congrArg (fun u : kˣ => (u : k)) h
      simpa [χ] using this
    have hρ_eq : ρ (a : G) = ρ (b : G) := by
      rw [hc a, hc b, hc_eq]
    exact Subtype.ext (hρ hρ_eq)
  have hχrange_fin : Finite χ.range :=
    Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  have hχrange_cyc : IsCyclic χ.range := subgroup_units_cyclic χ.range
  have hAcyc : IsCyclic A := by
    have hχ' : Function.Injective χ.rangeRestrict := by
      intro a b h
      apply hχinj
      exact congrArg Subtype.val h
    exact isCyclic_of_injective χ.rangeRestrict hχ'
  have hAcenter : A ≤ Subgroup.center G := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro g
    apply hρ
    calc
      ρ (g * a) = ρ g * ρ a := map_mul ρ g a
      _ = ρ g * (c ⟨a, ha⟩ • (1 : Module.End k V)) := by rw [hc ⟨a, ha⟩]
      _ = c ⟨a, ha⟩ • ρ g := by rw [mul_smul_comm, mul_one]
      _ = (c ⟨a, ha⟩ • (1 : Module.End k V)) * ρ g := by
        rw [smul_mul_assoc, one_mul]
      _ = ρ a * ρ g := by rw [hc ⟨a, ha⟩]
      _ = ρ (a * g) := by rw [map_mul]
  exact ⟨hAcenter, hAcyc⟩

theorem normal_map_center_and_isMulCommutative
    {G : Type*} [Group G] (Q : Subgroup G) [Q.Normal] :
    ((Subgroup.center Q).map Q.subtype).Normal ∧
      IsMulCommutative ((Subgroup.center Q).map Q.subtype) := by
  refine ⟨?_, ?_⟩
  · exact ConjAct.normal_of_characteristic_of_normal (H := Q) (K := Subgroup.center Q)
  · exact Subgroup.map_isMulCommutative (Subgroup.center Q) Q.subtype

theorem card_quotient_center_le_finrank_sq_of_scalar
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k G V) (hρ : Function.Injective ρ)
    (hA : ∀ (A : Subgroup G) [A.Normal], IsMulCommutative A →
      ∀ a ∈ A, ∃ c : k, ρ a = c • (1 : Module.End k V))
    (Q : Subgroup G) [Q.Normal]
    (hclass : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q) :
    Nat.card (Q ⧸ Subgroup.center Q) ≤ Module.finrank k V ^ 2 := by
  classical
  have : Finite Q := Subtype.finite
  let Z : Subgroup G := (Subgroup.center Q).map Q.subtype
  have hZ : Z.Normal ∧ IsMulCommutative Z := by
    simpa [Z] using normal_map_center_and_isMulCommutative Q
  have hscalar : ∀ z ∈ Subgroup.center Q,
      ∃ c : k, ((ρ.asGroupHom.comp Q.subtype) z : Module.End k V) = c • 1 := by
    intro z hz
    have hzZ : (z : G) ∈ Z := Subgroup.mem_map_of_mem Q.subtype hz
    have : Z.Normal := hZ.1
    obtain ⟨c, hc⟩ := hA Z hZ.2 (z : G) hzZ
    exact ⟨c, by simpa [Representation.asGroupHom_apply] using hc⟩
  have hρQ : Function.Injective (ρ.asGroupHom.comp Q.subtype) := by
    intro x y hxy
    apply Subtype.ext
    apply hρ
    have := congrArg Units.val hxy
    simpa [Representation.asGroupHom_apply] using this
  exact card_quotient_center_le_finrank_sq (ρ.asGroupHom.comp Q.subtype) hρQ hscalar hclass

end CFSG.RepresentationTheory
