module

public import CFSG.RankThree.PartOne.HNB.Tools
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup
open scoped commutatorElement

variable {V N : Type*} [Group V] [Group N]

@[expose] def innerPart (Φ : N →* MulAut V) (R₀ : Subgroup N) : Subgroup V :=
  (R₀.map Φ).comap (MulAut.conj : V →* MulAut V)

theorem mem_innerPart {Φ : N →* MulAut V} {R₀ : Subgroup N} {v : V} :
    v ∈ innerPart Φ R₀ ↔ MulAut.conj v ∈ R₀.map Φ := Iff.rfl

theorem conj_injective_of_center_eq_bot (hV : Subgroup.center V = ⊥) :
    Function.Injective (MulAut.conj : V →* MulAut V) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro v hv
  rw [MonoidHom.mem_ker] at hv
  have hc : v ∈ Subgroup.center V := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun σ : MulAut V => σ g) hv
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * v = (v * g * v⁻¹) * v := by rw [this]
      _ = v * g := by group
  rw [hV] at hc
  exact hc

theorem isPGroup_innerPart (hV : Subgroup.center V = ⊥) {p : ℕ} {Φ : N →* MulAut V}
    {R₀ : Subgroup N} (hR : IsPGroup p R₀) : IsPGroup p (innerPart Φ R₀) := by
  have h1 : IsPGroup p (R₀.map Φ) := hR.map Φ
  let f : innerPart Φ R₀ →* (R₀.map Φ) :=
    ((MulAut.conj : V →* MulAut V).comp (innerPart Φ R₀).subtype).codRestrict (R₀.map Φ)
      fun v => v.2
  have hf : Function.Injective f := fun x y hxy => by
    have := congrArg Subtype.val hxy
    exact Subtype.ext (conj_injective_of_center_eq_bot hV this)
  exact h1.of_injective f hf

theorem Φ_mem_innerPart {Φ : N →* MulAut V} {R₀ : Subgroup N} {n : N}
    (hn : n ∈ Subgroup.normalizer (R₀ : Set N)) {u : V} (hu : u ∈ innerPart Φ R₀) :
    Φ n u ∈ innerPart Φ R₀ := by
  rw [mem_innerPart] at hu ⊢
  obtain ⟨r, hr, hru⟩ := hu
  rw [conj_automorphism_apply]
  refine ⟨n * r * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn r).mp hr, ?_⟩
  rw [map_mul, map_mul, map_inv, hru]

theorem conj_mem_innerPart {Φ : N →* MulAut V} {R₀ : Subgroup N} {n : N}
    (hn : n ∈ Subgroup.normalizer (R₀ : Set N)) {w : V} (hw : MulAut.conj w = Φ n) {u : V}
    (hu : u ∈ innerPart Φ R₀) : w * u * w⁻¹ ∈ innerPart Φ R₀ := by
  rw [mem_innerPart] at hu ⊢
  obtain ⟨r, hr, hru⟩ := hu
  refine ⟨n * r * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn r).mp hr, ?_⟩
  rw [map_mul, map_mul, map_inv, hru, ← hw]
  simp [map_mul, map_inv]

theorem exists_mem_innerPart {Φ : N →* MulAut V} {R₀ : Subgroup N}
    (hinner : ∀ r ∈ R₀, Φ r ∈ (MulAut.conj : V →* MulAut V).range) {r : N} (hr : r ∈ R₀) :
    ∃ u ∈ innerPart Φ R₀, MulAut.conj u = Φ r := by
  obtain ⟨u, hu⟩ := hinner r hr
  exact ⟨u, ⟨r, hr, hu.symm⟩, hu⟩

theorem closure_eq_innerPart (hV : Subgroup.center V = ⊥) {Φ : N →* MulAut V} {R₀ : Subgroup N}
    (hinner : ∀ r ∈ R₀, Φ r ∈ (MulAut.conj : V →* MulAut V).range) {c : N}
    (hc : c ∈ Subgroup.normalizer (R₀ : Set N)) (hc5 : c ^ 5 = 1)
    (hRc : ⁅R₀, Subgroup.zpowers c⁆ = R₀) :
    Subgroup.closure {x | ∃ u ∈ innerPart Φ R₀, x = u⁻¹ * Φ c u} = innerPart Φ R₀ := by
  have hstable : ∀ u ∈ innerPart Φ R₀, Φ c u ∈ innerPart Φ R₀ := fun u hu =>
    Φ_mem_innerPart hc hu
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) (hstable u hu)
  · set W := Subgroup.closure {x | ∃ u ∈ innerPart Φ R₀, x = u⁻¹ * Φ c u} with hW
    set Rsub : Subgroup N := (W.map (MulAut.conj : V →* MulAut V)).comap Φ with hRsub
    have hR : R₀ ≤ Rsub := by
      rw [← hRc]
      refine Subgroup.commutator_le.mpr fun r hr g hg => ?_
      obtain ⟨u, hu, hur⟩ := exists_mem_innerPart hinner hr
      obtain ⟨m, rfl⟩ := exists_pow_of_mem_zpowers hc5 hg
      have hu' : u⁻¹ ∈ innerPart Φ R₀ := Subgroup.inv_mem _ hu
      have hmem := inv_mul_pow_mem_closure (Φ c) (innerPart Φ R₀) hstable hu' m
      rw [inv_inv] at hmem
      rw [hRsub, Subgroup.mem_comap]
      refine ⟨u * ((Φ c) ^ m) u⁻¹, ?_, ?_⟩
      · simpa using hmem
      · rw [map_commutatorElement, map_pow, ← hur, map_mul, conj_automorphism_apply,
          commutatorElement_def]
        simp [mul_assoc]
    intro v hv
    obtain ⟨r, hr, hrv⟩ := hv
    have h1 : Φ r ∈ W.map (MulAut.conj : V →* MulAut V) := hR hr
    rw [hrv] at h1
    obtain ⟨w, hw, hwv⟩ := h1
    have : w = v := conj_injective_of_center_eq_bot hV hwv
    exact this ▸ hw

end CFSG.RankThree.PartOne.HNB
