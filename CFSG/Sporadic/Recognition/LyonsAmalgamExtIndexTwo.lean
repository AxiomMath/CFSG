module

public import CFSG.Monster.B.Recog.GenericIndexTwo
public import Mathlib.GroupTheory.IndexNormal

public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

section Inner

variable {M : Type*} [Group M]

theorem ker_mulAutConj_eq_center : (MulAut.conj : M →* MulAut M).ker = center M := by
  ext z
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun σ : MulAut M => σ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * z = (z * g * z⁻¹) * z := by rw [this]
      _ = z * g := by group
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h g]
    group

noncomputable def centerQuotEquivRangeConj :
    M ⧸ center M ≃* (MulAut.conj : M →* MulAut M).range :=
  (QuotientGroup.quotientMulEquivOfEq ker_mulAutConj_eq_center.symm).trans
    (QuotientGroup.quotientKerEquivRange _)

theorem card_range_conj : Nat.card (MulAut.conj : M →* MulAut M).range =
    Nat.card (M ⧸ center M) :=
  (Nat.card_congr centerQuotEquivRangeConj.toEquiv).symm

theorem index_range_conj_le_two [Finite M]
    (hout : Nat.card (MulAut M) ≤ 2 * Nat.card (M ⧸ center M)) :
    (MulAut.conj : M →* MulAut M).range.index ≤ 2 := by
  have h1 := (MulAut.conj : M →* MulAut M).range.index_mul_card
  rw [card_range_conj] at h1
  have hpos : 0 < Nat.card (M ⧸ center M) := Nat.card_pos
  rw [← h1] at hout
  by_contra hlt
  have : 3 * Nat.card (M ⧸ center M) ≤
      (MulAut.conj : M →* MulAut M).range.index * Nat.card (M ⧸ center M) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem inv_mul_mem_range_conj [Finite M]
    (hout : Nat.card (MulAut M) ≤ 2 * Nat.card (M ⧸ center M)) {a b : MulAut M}
    (ha : a ∉ (MulAut.conj : M →* MulAut M).range)
    (hb : b ∉ (MulAut.conj : M →* MulAut M).range) :
    a⁻¹ * b ∈ (MulAut.conj : M →* MulAut M).range := by
  have hle := index_range_conj_le_two hout
  have h0 : (MulAut.conj : M →* MulAut M).range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (MulAut.conj : M →* MulAut M).range.index ≠ 1 := by
    intro h
    exact ha ((Subgroup.index_eq_one.mp h).symm ▸ Subgroup.mem_top a)
  have h2 : (MulAut.conj : M →* MulAut M).range.index = 2 := by omega
  rw [Subgroup.mul_mem_iff_of_index_two h2]
  exact iff_of_false (fun h => ha (by simpa using h)) hb

end Inner

section CenterThree

variable {M : Type*} [Group M]

theorem eq_one_of_mem_center_of_eq_inv (hZ : Nat.card (center M) = 3) {z : M}
    (hz : z ∈ center M) (h : z = z⁻¹) : z = 1 := by
  have h3 : (⟨z, hz⟩ : center M) ^ 3 = 1 := by
    rw [← hZ]
    exact pow_card_eq_one'
  have h3' : z ^ 3 = 1 := congrArg Subtype.val h3
  have h2 : z * z = 1 := mul_eq_one_iff_eq_inv.mpr h
  calc z = z ^ 3 * (z * z)⁻¹ := by group
    _ = 1 := by rw [h3', h2]; group

theorem exists_mem_center_ne_one_of_card_eq_three (hZ : Nat.card (center M) = 3) :
    ∃ z ∈ center M, z ≠ 1 := by
  by_contra h
  push Not at h
  have : Nat.card (center M) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩, ⟨1⟩⟩
  omega

theorem not_mem_range_conj_of_inv (hZ : Nat.card (center M) = 3) {α : MulAut M}
    (hα : ∀ z ∈ center M, α z = z⁻¹) : α ∉ (MulAut.conj : M →* MulAut M).range := by
  rintro ⟨m, rfl⟩
  obtain ⟨z, hz, hz1⟩ := exists_mem_center_ne_one_of_card_eq_three hZ
  apply hz1
  apply eq_one_of_mem_center_of_eq_inv hZ hz
  have h1 := hα z hz
  rw [MulAut.conj_apply] at h1
  have hc := (Subgroup.mem_center_iff.mp hz) m
  rw [← h1, hc]
  group

end CenterThree

theorem exists_notMem_of_index_two {B : Type*} [Group B] {M : Subgroup B} (hM : M.index = 2) :
    ∃ s : B, s ∉ M := by
  obtain ⟨a, ha, -⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hM
  exact ⟨a, ha⟩

section Three

theorem zpow_eq_one_or_self_or_inv {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g ∨ g ^ k = g⁻¹ := by
  have h3 : g ^ (3 * (k / 3)) = 1 := by
    rw [zpow_mul]
    simp [hg]
  have hk : g ^ k = g ^ (k % 3) := by
    calc g ^ k = g ^ (k % 3 + 3 * (k / 3)) := by rw [Int.emod_add_mul_ediv]
      _ = g ^ (k % 3) * g ^ (3 * (k / 3)) := zpow_add _ _ _
      _ = g ^ (k % 3) := by rw [h3, mul_one]
  have h2 : g ^ (2 : ℤ) = g⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← hg]
    group
  have hc : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hc with h | h | h <;> rw [hk, h]
  · simp
  · simp
  · exact Or.inr (Or.inr h2)

theorem eq_one_or_self_or_inv_of_mem_center {M : Type*} [Group M] (hZ : Nat.card (center M) = 3)
    {z w : M} (hz : z ∈ center M) (hw : w ∈ center M) (hz1 : z ≠ 1) :
    w = 1 ∨ w = z ∨ w = z⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz1' : (⟨z, hz⟩ : center M) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hmem : (⟨w, hw⟩ : center M) ∈ Subgroup.zpowers (⟨z, hz⟩ : center M) :=
    mem_zpowers_of_prime_card hZ hz1'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h3 : (⟨z, hz⟩ : center M) ^ 3 = 1 := by
    rw [← hZ]
    exact pow_card_eq_one'
  have hv : w = z ^ k := by
    have := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at this
    exact this.symm
  have hz3 : z ^ 3 = 1 := congrArg Subtype.val h3
  rw [hv]
  exact zpow_eq_one_or_self_or_inv hz3 k

end Three

section Main

variable {B₁ B₂ : Type*} [Group B₁] [Group B₂] {M₁ : Subgroup B₁} {M₂ : Subgroup B₂}

theorem exists_mulEquiv_extend_of_index_two [Finite M₂] (hM₁ : M₁.index = 2)
    (hM₂ : M₂.index = 2) (μ : M₁ ≃* M₂) (hZ₂ : Nat.card (center M₂) = 3)
    (hout₂ : Nat.card (MulAut M₂) ≤ 2 * Nat.card (M₂ ⧸ center M₂))
    (hinv₁ : ∀ b : B₁, b ∉ M₁ → ∀ z : M₁, z ∈ center M₁ → b * (z : B₁) * b⁻¹ = (z : B₁)⁻¹)
    (hinv₂ : ∀ b : B₂, b ∉ M₂ → ∀ z : M₂, z ∈ center M₂ → b * (z : B₂) * b⁻¹ = (z : B₂)⁻¹) :
    ∃ ν : B₁ ≃* B₂, ∀ m : M₁, ν m = μ m := by
  have : M₁.Normal := normal_of_index_eq_two hM₁
  have : M₂.Normal := normal_of_index_eq_two hM₂
  obtain ⟨s₁, hs₁⟩ := exists_notMem_of_index_two hM₁
  obtain ⟨s₂, hs₂⟩ := exists_notMem_of_index_two hM₂
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : MulAut M₁, σ₁ = MulAut.conjNormal s₁ := ⟨_, rfl⟩
  obtain ⟨σ₂, hσ₂⟩ : ∃ σ₂ : MulAut M₂, σ₂ = MulAut.conjNormal s₂ := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : MulAut M₂, τ = MulAut.congr μ σ₁ := ⟨_, rfl⟩
  have hτapp : ∀ x : M₂, τ x = μ (σ₁ (μ.symm x)) := fun x => by rw [hτ]; rfl
  have hμc : ∀ z : M₂, z ∈ center M₂ → μ.symm z ∈ center M₁ := fun z hz => by
    rw [Subgroup.mem_center_iff]
    intro g
    apply μ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_center_iff.mp hz) (μ g)
  have hσ₂inv : ∀ z ∈ center M₂, σ₂ z = z⁻¹ := fun z hz => by
    apply Subtype.ext
    rw [Subgroup.coe_inv, hσ₂]
    exact (MulAut.conjNormal_apply s₂ z).trans (hinv₂ s₂ hs₂ z hz)
  have hτinv : ∀ z ∈ center M₂, τ z = z⁻¹ := fun z hz => by
    have h1 : σ₁ (μ.symm z) = (μ.symm z)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_inv, hσ₁]
      exact (MulAut.conjNormal_apply s₁ _).trans (hinv₁ s₁ hs₁ _ (hμc z hz))
    rw [hτapp, h1, map_inv, MulEquiv.apply_symm_apply]
  obtain ⟨b, hb⟩ := inv_mul_mem_range_conj hout₂ (not_mem_range_conj_of_inv hZ₂ hτinv)
    (not_mem_range_conj_of_inv hZ₂ hσ₂inv)
  have hσ₂b : ∀ a : M₂, σ₂ a = τ (b * a * b⁻¹) := fun a => by
    have h1 := congrArg (fun f : MulAut M₂ => τ (f a)) hb
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.apply_inv_self] at h1
    exact h1.symm
  have hnorm : ∀ c ∈ center M₂, τ c = c → ∃ d ∈ center M₂, c = d * τ d := fun c hc hτc => by
    have hc1 : c = 1 := eq_one_of_mem_center_of_eq_inv hZ₂ hc (hτc.symm.trans (hτinv c hc))
    exact ⟨1, Subgroup.one_mem _, by rw [hc1, map_one, mul_one]⟩
  obtain ⟨ι₁, hι₁⟩ : ∃ ι₁ : M₂ →* B₁, ι₁ = M₁.subtype.comp μ.symm.toMonoidHom := ⟨_, rfl⟩
  have hι₁app : ∀ a : M₂, ι₁ a = ((μ.symm a : M₁) : B₁) := fun a => by rw [hι₁]; rfl
  have hι₁inj : Function.Injective ι₁ := fun a a' h => by
    rw [hι₁app, hι₁app] at h
    exact μ.symm.injective (Subtype.ext h)
  have hran₁ : ι₁.range = M₁ := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      rw [hι₁app]
      exact (μ.symm a).2
    · intro hx
      exact ⟨μ ⟨x, hx⟩, by rw [hι₁app, MulEquiv.symm_apply_apply]⟩
  have hran₂ : M₂.subtype.range = M₂ := Subgroup.range_subtype M₂
  have hσ₁' : ∀ a : M₂, s₁ * ι₁ a * s₁⁻¹ = ι₁ (τ a) := fun a => by
    rw [hι₁app, hι₁app, hτapp, MulEquiv.symm_apply_apply, hσ₁, MulAut.conjNormal_apply]
  have hσ₂' : ∀ a : M₂, s₂ * M₂.subtype a * s₂⁻¹ = M₂.subtype (σ₂ a) := fun a => by
    rw [hσ₂, Subgroup.subtype_apply, Subgroup.subtype_apply, MulAut.conjNormal_apply]
  obtain ⟨e, he⟩ := CFSG.Monster.B.Recog.exists_mulEquiv_of_index_two ι₁ M₂.subtype hι₁inj
    (Subgroup.subtype_injective M₂) (by rw [hran₁]; exact hM₁) (by rw [hran₂]; exact hM₂)
    (s₁ := s₁) (s₂ := s₂) (by rw [hran₁]; exact hs₁) (by rw [hran₂]; exact hs₂) τ σ₂ hσ₁' hσ₂'
    b hσ₂b hnorm
  refine ⟨e, fun m => ?_⟩
  have h1 := he (μ m)
  rw [hι₁app, MulEquiv.symm_apply_apply] at h1
  exact h1

theorem exists_mulEquiv_extend_of_index_two_twist [Finite M₂] (hM₁ : M₁.index = 2)
    (hM₂ : M₂.index = 2) (μ : M₁ ≃* M₂) (hZ₂ : Nat.card (center M₂) = 3)
    (hout₂ : Nat.card (MulAut M₂) ≤ 2 * Nat.card (M₂ ⧸ center M₂))
    (hinv₁ : ∀ b : B₁, b ∉ M₁ → ∀ z : M₁, z ∈ center M₁ → b * (z : B₁) * b⁻¹ = (z : B₁)⁻¹)
    (hinv₂ : ∀ b : B₂, b ∉ M₂ → ∀ z : M₂, z ∈ center M₂ → b * (z : B₂) * b⁻¹ = (z : B₂)⁻¹)
    (α : MulAut M₂) : ∃ ν : B₁ ≃* B₂, ∀ m : M₁, ν m = α (μ m) :=
  exists_mulEquiv_extend_of_index_two hM₁ hM₂ (μ.trans α) hZ₂ hout₂ hinv₁ hinv₂

theorem exists_mulEquiv_of_index_two [Finite M₂] (hM₁ : M₁.index = 2) (hM₂ : M₂.index = 2)
    (μ : M₁ ≃* M₂) (hZ₂ : Nat.card (center M₂) = 3)
    (hout₂ : Nat.card (MulAut M₂) ≤ 2 * Nat.card (M₂ ⧸ center M₂))
    (hinv₁ : ∀ b : B₁, b ∉ M₁ → ∀ z : M₁, z ∈ center M₁ → b * (z : B₁) * b⁻¹ = (z : B₁)⁻¹)
    (hinv₂ : ∀ b : B₂, b ∉ M₂ → ∀ z : M₂, z ∈ center M₂ → b * (z : B₂) * b⁻¹ = (z : B₂)⁻¹) :
    ∃ ν : B₁ ≃* B₂, ∃ α : MulAut M₂, ∀ m : M₁, ν m = α (μ m) := by
  obtain ⟨ν, hν⟩ := exists_mulEquiv_extend_of_index_two hM₁ hM₂ μ hZ₂ hout₂ hinv₁ hinv₂
  exact ⟨ν, 1, fun m => by rw [hν, MulAut.one_apply]⟩

theorem mem_center_iff_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    e x ∈ center Y ↔ x ∈ center X := by
  rw [← Subgroup.map_center_eq e]
  exact Subgroup.mem_map_iff_mem e.injective

theorem mem_center_iff_of_extend {ν : B₁ ≃* B₂} {α : MulAut M₂} {μ : M₁ ≃* M₂}
    (hν : ∀ m : M₁, ν m = α (μ m)) (z : M₁) :
    z ∈ center M₁ ↔ ∃ w : M₂, w ∈ center M₂ ∧ (w : B₂) = ν z := by
  constructor
  · intro hz
    exact ⟨α (μ z), (mem_center_iff_mulEquiv α _).mpr ((mem_center_iff_mulEquiv μ z).mpr hz),
      (hν z).symm⟩
  · rintro ⟨w, hw, hwz⟩
    have hw' : w = α (μ z) := Subtype.ext (hwz.trans (hν z))
    rw [hw'] at hw
    exact (mem_center_iff_mulEquiv μ z).mp ((mem_center_iff_mulEquiv α _).mp hw)

theorem map_center_eq_of_extend {ν : B₁ ≃* B₂} {α : MulAut M₂} {μ : M₁ ≃* M₂}
    (hν : ∀ m : M₁, ν m = α (μ m)) :
    ((center M₁).map M₁.subtype).map ν.toMonoidHom = (center M₂).map M₂.subtype := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.subtype_apply]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨w, hw, hwz⟩ := (mem_center_iff_of_extend hν z).mp hz
    exact ⟨w, hw, hwz⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨z, hzdef⟩ : ∃ z : M₁, μ z = α.symm w := ⟨μ.symm (α.symm w), by simp⟩
    have hνz : ν z = (w : B₂) := by rw [hν, hzdef]; simp
    have hz : z ∈ center M₁ := (mem_center_iff_of_extend hν z).mpr ⟨w, hw, hνz.symm⟩
    exact ⟨z, ⟨z, hz, rfl⟩, hνz⟩

theorem exists_mulEquiv_of_index_two_center [Finite M₂] (hM₁ : M₁.index = 2)
    (hM₂ : M₂.index = 2) (μ : M₁ ≃* M₂) (hZ₂ : Nat.card (center M₂) = 3)
    (hout₂ : Nat.card (MulAut M₂) ≤ 2 * Nat.card (M₂ ⧸ center M₂))
    (hinv₁ : ∀ b : B₁, b ∉ M₁ → ∀ z : M₁, z ∈ center M₁ → b * (z : B₁) * b⁻¹ = (z : B₁)⁻¹)
    (hinv₂ : ∀ b : B₂, b ∉ M₂ → ∀ z : M₂, z ∈ center M₂ → b * (z : B₂) * b⁻¹ = (z : B₂)⁻¹)
    {z₁ : M₁} {z₂ : M₂} (hz₁ : z₁ ∈ center M₁) (hz₂ : z₂ ∈ center M₂) (h₁ : z₁ ≠ 1)
    (h₂ : z₂ ≠ 1) :
    ∃ ν : B₁ ≃* B₂, ν (z₁ : B₁) = (z₂ : B₂) ∧ ∃ α : MulAut M₂, ∀ m : M₁, ν m = α (μ m) := by
  obtain ⟨ν₀, hν₀⟩ := exists_mulEquiv_extend_of_index_two hM₁ hM₂ μ hZ₂ hout₂ hinv₁ hinv₂
  have hw : μ z₁ ∈ center M₂ := (mem_center_iff_mulEquiv μ z₁).mpr hz₁
  have hw1 : μ z₁ ≠ 1 := fun h => h₁ ((map_eq_one_iff μ μ.injective).mp h)
  rcases eq_one_or_self_or_inv_of_mem_center hZ₂ hz₂ hw h₂ with h | h | h
  · exact absurd h hw1
  · refine ⟨ν₀, ?_, 1, fun m => by rw [hν₀, MulAut.one_apply]⟩
    rw [hν₀, h]
  · obtain ⟨s₂, hs₂⟩ := exists_notMem_of_index_two hM₂
    have : M₂.Normal := normal_of_index_eq_two hM₂
    refine ⟨ν₀.trans (MulAut.conj s₂), ?_, MulAut.conjNormal s₂, fun m => ?_⟩
    · simp only [MulEquiv.trans_apply, MulAut.conj_apply, hν₀]
      rw [hinv₂ s₂ hs₂ _ hw, h]
      simp
    · simp [hν₀, MulAut.conjNormal_apply]

end Main

end CFSG.Sporadic.Recognition.LyonsSims
