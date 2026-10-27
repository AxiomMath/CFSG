module

public import CFSG.RankThree.PartOne.TAIL.ConjOrbit
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

variable {G : Type} [Group G]

theorem exists_conj_sylow [Finite G] {C P₁ P₂ : Subgroup G}
    (h₁ : P₁ ≤ C ∧ IsPGroup 7 P₁ ∧ ¬ 7 ∣ P₁.relIndex C)
    (h₂ : P₂ ≤ C ∧ IsPGroup 7 P₂ ∧ ¬ 7 ∣ P₂.relIndex C) :
    ∃ g ∈ C, ∀ x, x ∈ P₂ ↔ g⁻¹ * x * g ∈ P₁ := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨hP₁C, hP₁p, hidx₁⟩ := h₁
  obtain ⟨hP₂C, hP₂p, hidx₂⟩ := h₂
  have hp₁ : IsPGroup 7 (P₁.subgroupOf C) :=
    hP₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₁C).symm
  have hp₂ : IsPGroup 7 (P₂.subgroupOf C) :=
    hP₂p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₂C).symm
  let S₁ : Sylow 7 ↥C := hp₁.toSylow hidx₁
  let S₂ : Sylow 7 ↥C := hp₂.toSylow hidx₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C S₁ S₂
  refine ⟨g, g.2, fun x => ?_⟩
  by_cases hx : x ∈ C
  · have h1 : (⟨x, hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) ↔ g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥C) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [mul_assoc]
    have e1 : (⟨x, hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) ↔ x ∈ P₂ := Subgroup.mem_subgroupOf
    have e2 : g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥C) ↔ (g : G)⁻¹ * x * g ∈ P₁ :=
      Subgroup.mem_subgroupOf (H := P₁) (K := C) (h := g⁻¹ * ⟨x, hx⟩ * g)
    rw [← e1, h1]
    exact e2
  · have hxP₂ : x ∉ P₂ := fun h => hx (hP₂C h)
    have hxP₁ : (g : G)⁻¹ * x * g ∉ P₁ := fun h => hx (by
      have := C.mul_mem (C.mul_mem g.2 (hP₁C h)) (C.inv_mem g.2)
      simpa [mul_assoc] using this)
    exact ⟨fun h => absurd h hxP₂, fun h => absurd h hxP₁⟩

theorem conjSub_card (n : G) (P : Subgroup G) : Nat.card (conjSub n P) = Nat.card P := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj n⁻¹).toEquiv (fun a => ?_))
  show n⁻¹ * a * n ∈ P ↔ (MulAut.conj n⁻¹) a ∈ P
  simp

theorem conjSub_pgroup {n : G} {P : Subgroup G} (hP : IsPGroup 7 P) : IsPGroup 7 ↥(conjSub n P) := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : n⁻¹ * (g : G) * n ∈ P := g.2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨n⁻¹ * (g : G) * n, hg⟩
  refine ⟨k, ?_⟩
  rw [← Subgroup.orderOf_coe]
  rw [Subgroup.orderOf_mk] at hk
  rw [← hk]
  have := orderOf_injective (MulAut.conj n⁻¹).toMonoidHom (MulAut.conj n⁻¹).injective (g : G)
  simpa using this.symm

theorem conjSub_sylow [Finite G] {X P : Subgroup G} {n : G}
    (hP : P ≤ X ∧ IsPGroup 7 P ∧ ¬ 7 ∣ P.relIndex X) (hle : conjSub n P ≤ X) :
    conjSub n P ≤ X ∧ IsPGroup 7 ↥(conjSub n P) ∧ ¬ 7 ∣ (conjSub n P).relIndex X := by
  refine ⟨hle, conjSub_pgroup hP.2.1, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (conjSub n P) X
  have h2 := Subgroup.relIndex_mul_card P X
  rw [inf_eq_left.mpr hle] at h1
  rw [inf_eq_left.mpr hP.1] at h2
  rw [conjSub_card] at h1
  have : (conjSub n P).relIndex X = P.relIndex X := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := P))
    rw [h1, h2]
  rw [this]
  exact hP.2.2

theorem frattini [Finite G] {X P M : Subgroup G} (hMX : M ≤ Subgroup.normalizer (X : Set G))
    (hP : P ≤ X ∧ IsPGroup 7 P ∧ ¬ 7 ∣ P.relIndex X) :
    ∀ m ∈ M, ∃ x ∈ X, ∃ n ∈ Subgroup.normalizer (P : Set G), m = x * n := by
  intro m hm
  have hmX : m ∈ Subgroup.normalizer (X : Set G) := hMX hm
  have hle : conjSub m P ≤ X := by
    intro x hx
    have h1 : m⁻¹ * x * m ∈ X := hP.1 hx
    have h2 := (Subgroup.mem_normalizer_iff.mp hmX _).mp h1
    have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rwa [e] at h2
  obtain ⟨g, hgX, hg⟩ := exists_conj_sylow (C := X) (P₁ := conjSub m P) (P₂ := P)
    (conjSub_sylow hP hle) hP
  refine ⟨g⁻¹, X.inv_mem hgX, g * m, ?_, by group⟩
  have hn : ∀ y, y ∈ P ↔ (g * m)⁻¹ * y * (g * m) ∈ P := by
    intro y
    rw [hg y, mem_conjSub]
    have e1 : (g * m)⁻¹ * y * (g * m) = m⁻¹ * (g⁻¹ * y * g) * m := by group
    rw [e1]
  rw [← inv_mem_iff (G := G) (H := Subgroup.normalizer (P : Set G)), Subgroup.mem_normalizer_iff]
  intro y
  have := hn y
  simpa using this

end CFSG.RankThree.PartOne.TAIL
