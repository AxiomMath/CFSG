module

public import CFSG.RankThree.PartOne.S12.ReflLoc
public import CFSG.Permutation.SymmetricCoxeter
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.RankThree.PartOne

namespace ReflF

open Module LinearMap Equiv Equiv.Perm CFSG.Permutation.SymmetricCoxeter

section Chain

open scoped _root_.Classical

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_chain3 {𝒟 : Finset (V ≃ₗ[K] V)} (hconn : Conn 𝒟) {a c : V ≃ₗ[K] V} (ha : a ∈ 𝒟)
    (hc : c ∈ 𝒟) (hac : a ≠ c) (hcomm : a * c = c * a) :
    ∃ x ∈ 𝒟, ∃ y ∈ 𝒟, ∃ z ∈ 𝒟, x ≠ z ∧ x * z = z * x ∧ x * y ≠ y * x ∧ y * z ≠ z * y := by
  by_contra hno
  push Not at hno
  have hP : insert a (𝒟.filter fun x => a * x ≠ x * a) = 𝒟 := by
    apply hconn
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ha
      · exact (Finset.mem_filter.1 hx).1
    · exact ⟨a, Finset.mem_insert_self _ _⟩
    · intro T hT S hS hTS
      by_cases hSa : S = a
      · rw [hSa]
        exact Finset.mem_insert_self _ _
      · by_cases hac' : a * S = S * a
        · exfalso
          rcases Finset.mem_insert.1 hT with rfl | hT'
          · exact hTS (by rw [← hac'])
          · have hTf := Finset.mem_filter.1 hT'
            have := hno S hS T hTf.1 a ha hSa hac'.symm (fun e => hTS e.symm)
            exact hTf.2 this.symm
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hS, hac'⟩)
  have hcP : c ∈ insert a (𝒟.filter fun x => a * x ≠ x * a) := by rw [hP]; exact hc
  rcases Finset.mem_insert.1 hcP with h | h
  · exact hac h.symm
  · exact (Finset.mem_filter.1 h).2 hcomm

end Chain

section Coxeter

variable {H : Type*} [Group H]

theorem perm_four_reps : ∀ σ : Perm (Fin 4), σ = 1 ∨
    (∃ g : Perm (Fin 4), g * σ * g⁻¹ = swap 0 1 ∨ g * σ * g⁻¹ = swap 0 1 * swap 1 2 ∨
      g * σ * g⁻¹ = swap 0 1 * swap 2 3) ∨
    (∃ g : Perm (Fin 4), g * (σ * σ) * g⁻¹ = swap 0 1 * swap 2 3) := by
  decide +kernel

theorem exists_perm_four {x y z : H} (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    (hxy : x * y * x = y * x * y) (hyz : y * z * y = z * y * z) (hxz : x * z = z * x)
    (hx1 : x ≠ 1) (hxzne : x ≠ z) (hxyne : x ≠ y) :
    ∃ Ψ : Perm (Fin 4) →* H, Function.Injective Ψ ∧ Ψ (swap 0 1) = x ∧ Ψ (swap 1 2) = y ∧
      Ψ (swap 2 3) = z := by
  let g : ℕ → H := fun i => if i = 0 then x else if i = 1 then y else if i = 2 then z else 1
  have hcox : IsCoxeterA 3 g := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      interval_cases i
      · simpa [g] using hx
      · simpa [g] using hy
      · simpa [g] using hz
    · intro i hi
      have hi' : i < 2 := by omega
      interval_cases i
      · simpa [g] using hxy
      · simpa [g] using hyz
    · intro i j hij hj
      have hi' : i < 1 := by omega
      interval_cases i
      have hj' : j = 2 := by omega
      subst hj'
      simpa [g] using hxz
  obtain ⟨Ψ, hΨ⟩ := exists_hom_perm 3 g hcox
  have h0 : Ψ (swap 0 1) = x := by
    have := hΨ 0 (by norm_num)
    rw [adjSwap_of_lt (by norm_num)] at this
    simpa [g] using this
  have h1 : Ψ (swap 1 2) = y := by
    have := hΨ 1 (by norm_num)
    rw [adjSwap_of_lt (by norm_num)] at this
    simpa [g] using this
  have h2 : Ψ (swap 2 3) = z := by
    have := hΨ 2 (by norm_num)
    rw [adjSwap_of_lt (by norm_num)] at this
    simpa [g] using this
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hxy1 : x * y ≠ 1 := fun h => hxyne (by
    have := eq_inv_of_mul_eq_one_left h
    rw [hyi] at this
    exact this)
  have hxz1 : x * z ≠ 1 := fun h => hxzne (by
    have := eq_inv_of_mul_eq_one_left h
    rw [inv_eq_of_mul_eq_one_right hz] at this
    exact this)
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    rcases perm_four_reps σ with h | ⟨g, hg⟩ | ⟨g, hg⟩
    · exact h
    · exfalso
      have hr : Ψ (g * σ * g⁻¹) = 1 := by
        rw [map_mul, map_mul, hσ, mul_one, map_inv, mul_inv_cancel]
      rcases hg with h | h | h
      · rw [h, h0] at hr
        exact hx1 hr
      · rw [h, map_mul, h0, h1] at hr
        exact hxy1 hr
      · rw [h, map_mul, h0, h2] at hr
        exact hxz1 hr
    · exfalso
      have hr : Ψ (g * (σ * σ) * g⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, hσ, mul_one, mul_one, map_inv, mul_inv_cancel]
      rw [hg, map_mul, h0, h2] at hr
      exact hxz1 hr
  exact ⟨Ψ, hinj, h0, h1, h2⟩

end Coxeter

section Swaps

@[expose] def swapSet (n : ℕ) : Finset (Perm (Fin n)) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter fun q => q.1 < q.2).image
    fun q => swap q.1 q.2

theorem mem_swapSet {n : ℕ} {σ : Perm (Fin n)} : σ ∈ swapSet n ↔ σ.IsSwap := by
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h
    exact ⟨q.1, q.2, (Finset.mem_filter.1 hq).2.ne, rfl⟩
  · rintro ⟨x, y, hxy, rfl⟩
    rcases lt_or_gt_of_ne hxy with h | h
    · exact Finset.mem_image.2 ⟨(x, y), Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, rfl⟩
    · refine Finset.mem_image.2 ⟨(y, x), Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, ?_⟩
      exact swap_comm y x

theorem swapSet_conj {n : ℕ} (σ : Perm (Fin n)) {τ : Perm (Fin n)} (hτ : τ ∈ swapSet n) :
    σ * τ * σ⁻¹ ∈ swapSet n := by
  rw [mem_swapSet] at hτ ⊢
  obtain ⟨a, b, hab, rfl⟩ := hτ
  exact ⟨σ a, σ b, σ.injective.ne hab, by rw [← Equiv.swap_apply_apply]⟩

theorem swapSet_conj' {n : ℕ} {σ τ : Perm (Fin n)} (hσ : σ ∈ swapSet n) (hτ : τ ∈ swapSet n) :
    σ * τ * σ ∈ swapSet n := by
  have hinv : σ⁻¹ = σ := by
    obtain ⟨a, b, -, rfl⟩ := mem_swapSet.1 hσ
    exact Equiv.swap_inv a b
  have := swapSet_conj σ hτ
  rwa [hinv] at this

theorem swapSet_card_four : (swapSet 4).card = 6 := by decide

theorem swap_ord_four : ∀ σ ∈ swapSet 4, ∀ τ ∈ swapSet 4,
    (σ * τ) ^ 1 = 1 ∨ (σ * τ) ^ 2 = 1 ∨ (σ * τ) ^ 3 = 1 := by decide +kernel

theorem swap_dist_four : ∀ σ ∈ swapSet 4, ∀ τ ∈ swapSet 4, σ = τ ∨ σ * τ ≠ τ * σ ∨
    ∃ ρ ∈ swapSet 4, σ * ρ ≠ ρ * σ ∧ ρ * τ ≠ τ * ρ := by decide +kernel

theorem swap_noncomm_card_four : ∀ σ ∈ swapSet 4,
    ((swapSet 4).filter fun τ => σ * τ ≠ τ * σ).card = 4 := by decide +kernel

theorem swap_line : ∀ σ ∈ swapSet 4, ∀ τ ∈ swapSet 4, σ * τ ≠ τ * σ →
    τ * (σ * τ * σ) * τ = σ := by decide +kernel

@[expose] def sw6 : Fin 6 → Perm (Fin 4) :=
  ![swap 0 1, swap 0 2, swap 0 3, swap 1 2, swap 1 3, swap 2 3]

theorem sw6_injective : Function.Injective sw6 := by decide +kernel

theorem swapSet_four_eq : swapSet 4 = Finset.univ.image sw6 := by decide +kernel

theorem sw6_mem (i : Fin 6) : sw6 i ∈ swapSet 4 := by
  rw [swapSet_four_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

theorem exists_sw6 {σ : Perm (Fin 4)} (hσ : σ ∈ swapSet 4) : ∃ k, sw6 k = σ := by
  rw [swapSet_four_eq] at hσ
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hσ
  exact ⟨k, hk⟩

@[expose] def LineClosed (b : Fin 6 → Bool) : Prop :=
  ∀ i j : Fin 6, sw6 i * sw6 j ≠ sw6 j * sw6 i → b i = true →
    b j = true ∨ ∃ k : Fin 6, sw6 k = sw6 i * sw6 j * sw6 i ∧ b k = true

instance (b : Fin 6 → Bool) : Decidable (LineClosed b) :=
  inferInstanceAs (Decidable (∀ i j : Fin 6, sw6 i * sw6 j ≠ sw6 j * sw6 i → b i = true →
    b j = true ∨ ∃ k : Fin 6, sw6 k = sw6 i * sw6 j * sw6 i ∧ b k = true))

@[expose] def cnt6 (b : Fin 6 → Bool) : ℕ := (Finset.univ.filter fun i => b i = true).card

@[expose] def StarGood (b : Fin 6 → Bool) : Prop :=
  cnt6 b ≠ 1 ∧ cnt6 b ≠ 2 ∧ (cnt6 b = 3 → ∃ a : Fin 4, ∀ i, b i = true ↔ sw6 i a ≠ a)

instance (b : Fin 6 → Bool) : Decidable (StarGood b) :=
  inferInstanceAs (Decidable (cnt6 b ≠ 1 ∧ cnt6 b ≠ 2 ∧
    (cnt6 b = 3 → ∃ a : Fin 4, ∀ i, b i = true ↔ sw6 i a ≠ a)))

theorem star_cases : ∀ b : Fin 6 → Bool, LineClosed b → StarGood b := by decide +kernel

theorem swap_pair_conj_five : ∀ σ₁ ∈ swapSet 5, ∀ σ₂ ∈ swapSet 5, σ₁ * σ₂ ≠ σ₂ * σ₁ →
    ∃ π : Perm (Fin 5), π * σ₁ * π⁻¹ = swap 0 1 ∧ π * σ₂ * π⁻¹ = swap 1 2 := by decide +kernel

theorem swap_pairs_conj_five {σ₁ σ₂ τ₁ τ₂ : Perm (Fin 5)} (h1 : σ₁ ∈ swapSet 5)
    (h2 : σ₂ ∈ swapSet 5) (h3 : τ₁ ∈ swapSet 5) (h4 : τ₂ ∈ swapSet 5)
    (hσ : σ₁ * σ₂ ≠ σ₂ * σ₁) (hτ : τ₁ * τ₂ ≠ τ₂ * τ₁) :
    ∃ π : Perm (Fin 5), π * σ₁ * π⁻¹ = τ₁ ∧ π * σ₂ * π⁻¹ = τ₂ := by
  obtain ⟨π, hπ1, hπ2⟩ := swap_pair_conj_five σ₁ h1 σ₂ h2 hσ
  obtain ⟨ρ, hρ1, hρ2⟩ := swap_pair_conj_five τ₁ h3 τ₂ h4 hτ
  refine ⟨ρ⁻¹ * π, ?_, ?_⟩
  · calc ρ⁻¹ * π * σ₁ * (ρ⁻¹ * π)⁻¹ = ρ⁻¹ * (π * σ₁ * π⁻¹) * ρ := by group
      _ = ρ⁻¹ * (ρ * τ₁ * ρ⁻¹) * ρ := by rw [hπ1, ← hρ1]
      _ = τ₁ := by group
  · calc ρ⁻¹ * π * σ₂ * (ρ⁻¹ * π)⁻¹ = ρ⁻¹ * (π * σ₂ * π⁻¹) * ρ := by group
      _ = ρ⁻¹ * (ρ * τ₂ * ρ⁻¹) * ρ := by rw [hπ2, ← hρ2]
      _ = τ₂ := by group

theorem exists_point_missing_four : ∀ a b a' b' : Fin 4, a ≠ b → a' ≠ b' →
    swap a b * swap a' b' ≠ swap a' b' * swap a b →
    ∃ d : Fin 4, d ≠ a ∧ d ≠ b ∧ d ≠ a' ∧ d ≠ b' := by decide +kernel

theorem exists_point_missing_five : ∀ a b a' b' : Fin 5, a ≠ b → a' ≠ b' →
    swap a b * swap a' b' ≠ swap a' b' * swap a b →
    ∃ d : Fin 5, d ≠ a ∧ d ≠ b ∧ d ≠ a' ∧ d ≠ b' := by decide +kernel

theorem exists_pair_fixing : ∀ b : Fin 4, ∃ σ₁ ∈ swapSet 4, ∃ σ₂ ∈ swapSet 4,
    σ₁ b = b ∧ σ₂ b = b ∧ σ₁ * σ₂ ≠ σ₂ * σ₁ := by decide +kernel

end Swaps

section Transfer

open scoped _root_.Classical

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] noncomputable def imgSwaps {H : Type*} [Group H] (n : ℕ) (Ψ : Perm (Fin n) →* H) :
    Finset H :=
  (swapSet n).image Ψ

theorem mem_imgSwaps {H : Type*} [Group H] {n : ℕ} {Ψ : Perm (Fin n) →* H} {x : H} :
    x ∈ imgSwaps n Ψ ↔ ∃ σ ∈ swapSet n, Ψ σ = x := by
  simp [imgSwaps, Finset.mem_image]

theorem card_imgSwaps {H : Type*} [Group H] {n : ℕ} {Ψ : Perm (Fin n) →* H}
    (hinj : Function.Injective Ψ) : (imgSwaps n Ψ).card = (swapSet n).card :=
  Finset.card_image_of_injective _ hinj

theorem conj_inv_mem {𝒟 : Finset (V ≃ₗ[K] V)} {g : V ≃ₗ[K] V}
    (hg : ∀ T ∈ 𝒟, g * T * g⁻¹ ∈ 𝒟) {T : V ≃ₗ[K] V} (hT : T ∈ 𝒟) : g⁻¹ * T * g ∈ 𝒟 := by
  have hinj : Function.Injective (fun T : V ≃ₗ[K] V => g * T * g⁻¹) := fun a b hab =>
    mul_left_cancel (mul_right_cancel hab)
  have himg : 𝒟.image (fun T : V ≃ₗ[K] V => g * T * g⁻¹) = 𝒟 := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hy
      exact hg S hS
    · rw [Finset.card_image_of_injective _ hinj]
  have : T ∈ 𝒟.image (fun T : V ≃ₗ[K] V => g * T * g⁻¹) := by rw [himg]; exact hT
  obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 this
  simpa [mul_assoc] using hT'

theorem conj_closure {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.closure (𝒟 : Set (V ≃ₗ[K] V))) : ∀ T ∈ 𝒟, g * T * g⁻¹ ∈ 𝒟 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact fun T hT => h.conj x hx T hT
  | one => intro T hT; simpa using hT
  | mul x y _ _ ihx ihy =>
    intro T hT
    have := ihx _ (ihy T hT)
    simpa [mul_assoc] using this
  | inv x _ ihx =>
    intro T hT
    rw [inv_inv]
    exact conj_inv_mem (fun T hT => ihx T hT) hT

theorem hom_swap_mem {m : ℕ} (hm : 1 ≤ m) {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟)
    (Ψ : Perm (Fin (m + 1)) →* V ≃ₗ[K] V) (hgen : ∀ i < m, Ψ (adjSwap m i) ∈ 𝒟)
    {σ : Perm (Fin (m + 1))} (hσ : σ ∈ swapSet (m + 1)) : Ψ σ ∈ 𝒟 := by
  rw [mem_swapSet] at hσ
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  have h01 : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨π, hπ⟩ := isConj_iff.1 (Perm.isConj_swap h01 hxy)
  have hs : Ψ (swap (⟨0, by omega⟩ : Fin (m + 1)) ⟨1, by omega⟩) ∈ 𝒟 := by
    have := hgen 0 (by omega)
    rwa [adjSwap_of_lt (by omega)] at this
  have hall : ∀ π : Perm (Fin (m + 1)), Ψ π ∈ Subgroup.closure (𝒟 : Set (V ≃ₗ[K] V)) := by
    intro π
    have hπt : π ∈ Subgroup.closure (adjSwap m '' Set.Iio m) := by
      rw [closure_adjSwap m]
      trivial
    induction hπt using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨i, hi, rfl⟩ := hz
      exact Subgroup.subset_closure (hgen i hi)
    | one => rw [map_one]; exact one_mem _
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  have hπc := hall π
  rw [← hπ, map_mul, map_mul, map_inv]
  exact conj_closure h hπc _ hs

theorem isRSet_imgSwaps {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {n : ℕ}
    (Ψ : Perm (Fin n) →* V ≃ₗ[K] V) (hsub : ∀ σ ∈ swapSet n, Ψ σ ∈ 𝒟)
    (hord : ∀ σ ∈ swapSet n, ∀ τ ∈ swapSet n,
      (σ * τ) ^ 1 = 1 ∨ (σ * τ) ^ 2 = 1 ∨ (σ * τ) ^ 3 = 1) : IsRSet (imgSwaps n Ψ) where
  refl T hT := by
    obtain ⟨σ, hσ, rfl⟩ := mem_imgSwaps.1 hT
    exact h.refl _ (hsub σ hσ)
  conj T hT S hS := by
    obtain ⟨σ, hσ, rfl⟩ := mem_imgSwaps.1 hT
    obtain ⟨τ, hτ, rfl⟩ := mem_imgSwaps.1 hS
    refine mem_imgSwaps.2 ⟨σ * τ * σ⁻¹, swapSet_conj σ hτ, ?_⟩
    rw [map_mul, map_mul, map_inv]
  ord T hT S hS _ := by
    obtain ⟨σ, hσ, rfl⟩ := mem_imgSwaps.1 hT
    obtain ⟨τ, hτ, rfl⟩ := mem_imgSwaps.1 hS
    rw [← map_mul, ← map_pow, ← map_pow, ← map_pow]
    rcases hord σ hσ τ hτ with h1 | h1 | h1
    · left; rw [h1, map_one]
    · right; left; rw [h1, map_one]
    · right; right; rw [h1, map_one]

theorem Ψ_comm_iff {H : Type*} [Group H] {n : ℕ} {Ψ : Perm (Fin n) →* H}
    (hinj : Function.Injective Ψ) {σ τ : Perm (Fin n)} :
    Ψ σ * Ψ τ = Ψ τ * Ψ σ ↔ σ * τ = τ * σ := by
  rw [← map_mul, ← map_mul]
  exact hinj.eq_iff

theorem conn_imgSwaps {n : ℕ} (Ψ : Perm (Fin n) →* V ≃ₗ[K] V) (hinj : Function.Injective Ψ)
    (hdist : ∀ σ ∈ swapSet n, ∀ τ ∈ swapSet n, σ = τ ∨ σ * τ ≠ τ * σ ∨
      ∃ ρ ∈ swapSet n, σ * ρ ≠ ρ * σ ∧ ρ * τ ≠ τ * ρ) : Conn (imgSwaps n Ψ) := by
  intro P hPsub hPne hPcl
  obtain ⟨x, hx⟩ := hPne
  obtain ⟨σ₀, hσ₀, rfl⟩ := mem_imgSwaps.1 (hPsub hx)
  apply Finset.Subset.antisymm hPsub
  intro T hT
  obtain ⟨τ, hτ, rfl⟩ := mem_imgSwaps.1 hT
  rcases hdist σ₀ hσ₀ τ hτ with h | h | ⟨ρ, hρ, h1, h2⟩
  · rw [← h]; exact hx
  · exact hPcl _ hx _ hT (fun e => h ((Ψ_comm_iff hinj).1 e))
  · have hρP : Ψ ρ ∈ P :=
      hPcl _ hx _ (mem_imgSwaps.2 ⟨ρ, hρ, rfl⟩) (fun e => h1 ((Ψ_comm_iff hinj).1 e))
    exact hPcl _ hρP _ hT (fun e => h2 ((Ψ_comm_iff hinj).1 e))

end Transfer

section Extras

open scoped _root_.Classical

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem card_filter_imgSwaps {H : Type*} [Group H] {n : ℕ} {Ψ : Perm (Fin n) →* H}
    (hinj : Function.Injective Ψ) (P : H → Prop) [DecidablePred P] :
    ((imgSwaps n Ψ).filter P).card = ((swapSet n).filter fun σ => P (Ψ σ)).card := by
  unfold imgSwaps
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ hinj

theorem card_noncomm {H : Type*} [Group H] {n : ℕ} {Ψ : Perm (Fin n) →* H}
    (hinj : Function.Injective Ψ) (σ : Perm (Fin n)) :
    ((imgSwaps n Ψ).filter fun S => Ψ σ * S ≠ S * Ψ σ).card =
      ((swapSet n).filter fun τ => σ * τ ≠ τ * σ).card := by
  rw [card_filter_imgSwaps hinj (fun S => Ψ σ * S ≠ S * Ψ σ)]
  congr 1
  refine Finset.filter_congr fun τ _ => ?_
  rw [Ne, Ne, Ψ_comm_iff hinj]

variable [FiniteDimensional K V]

theorem four_trace (hdim : finrank K V = 3) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (Ψ : Perm (Fin 4) →* V ≃ₗ[K] V)
    (hinj : Function.Injective Ψ) (hsub : ∀ σ ∈ swapSet 4, Ψ σ ∈ 𝒟) :
    ∀ y : V, Ssum (imgSwaps 4 Ψ) y = (4 : K) • y := by
  have hΔ := isRSet_imgSwaps h Ψ hsub swap_ord_four
  have hconn := conn_imgSwaps Ψ hinj swap_dist_four
  have hcard : (imgSwaps 4 Ψ).card = 6 := by rw [card_imgSwaps hinj, swapSet_card_four]
  have hne : (imgSwaps 4 Ψ).Nonempty := Finset.card_pos.1 (by rw [hcard]; norm_num)
  obtain ⟨lam, -, hb, hdimU, hs⟩ := trace_identity h2 h3 hΔ hconn hne
  have hs01 : swap (0 : Fin 4) 1 ∈ swapSet 4 := by decide
  have hlam : lam = 4 := by
    have := hb (Ψ (swap 0 1)) (mem_imgSwaps.2 ⟨_, hs01, rfl⟩)
    rw [card_noncomm hinj, swap_noncomm_card_four _ hs01] at this
    have h8 : (2 : K) * lam = 2 * 4 := by rw [this]; push_cast; ring
    exact mul_left_cancel₀ h2 h8
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hU3 : finrank K (Uspan (imgSwaps 4 Ψ)) = 3 := by
    rw [hcard, hlam] at hdimU
    have hk : (finrank K (Uspan (imgSwaps 4 Ψ)) : K) = 3 := by
      have : (finrank K (Uspan (imgSwaps 4 Ψ)) : K) * 4 = 3 * 4 := by
        rw [hdimU]; push_cast; ring
      exact mul_right_cancel₀ h4 this
    have hle : finrank K (Uspan (imgSwaps 4 Ψ)) ≤ 3 := hdim ▸ Submodule.finrank_le _
    generalize finrank K (Uspan (imgSwaps 4 Ψ)) = k at hk hle ⊢
    interval_cases k
    · exfalso; apply h3; rw [← hk]; simp
    · exfalso; apply h2; have : (3 : K) = 1 := hk.symm.trans (by simp); linear_combination this
    · exfalso
      have : (3 : K) = 2 := hk.symm.trans (by norm_num)
      apply one_ne_zero (α := K); linear_combination this
    · rfl
  have htop : Uspan (imgSwaps 4 Ψ) = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hU3, hdim])
  intro y
  rw [hs y (by rw [htop]; trivial), hlam]

theorem extra_count (hdim : finrank K V = 3) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (Ψ : Perm (Fin 4) →* V ≃ₗ[K] V)
    (hinj : Function.Injective Ψ) (hsub : ∀ σ ∈ swapSet 4, Ψ σ ∈ 𝒟) {v : V ≃ₗ[K] V}
    (hv : v ∈ 𝒟) (hvn : v ∉ imgSwaps 4 Ψ) :
    (((swapSet 4).filter fun σ => Ψ σ * v ≠ v * Ψ σ).card : K) = 8 := by
  obtain ⟨r, φ, hd⟩ := h.refl v hv
  have hS := four_trace hdim h2 h3 h Ψ hinj hsub
  have h1 : LinearMap.trace K V (Ssum (imgSwaps 4 Ψ) ∘ₗ Nop v) = 8 := by
    have : Ssum (imgSwaps 4 Ψ) ∘ₗ Nop v = (4 : K) • Nop v := by
      ext x
      simp only [LinearMap.comp_apply, hS, LinearMap.smul_apply]
    rw [this, map_smul, hd.trace_nop, smul_eq_mul]
    norm_num
  have hterm : ∀ T ∈ imgSwaps 4 Ψ, LinearMap.trace K V (Nop T ∘ₗ Nop v) =
      if T * v ≠ v * T then 1 else 0 := by
    intro T hT
    have hTne : T ≠ v := fun e => hvn (e ▸ hT)
    obtain ⟨σ, hσ, rfl⟩ := mem_imgSwaps.1 hT
    rcases h.dich h2 h3 (hsub σ hσ) hv hTne with ⟨h0, -, hc⟩ | ⟨ht, -, -, hnc⟩
    · rw [h0, map_zero]
      simp [hc]
    · rw [ht]
      simp [hnc]
  have h2' : LinearMap.trace K V (Ssum (imgSwaps 4 Ψ) ∘ₗ Nop v) =
      (((imgSwaps 4 Ψ).filter fun T => T * v ≠ v * T).card : K) := by
    have hcomp : Ssum (imgSwaps 4 Ψ) ∘ₗ Nop v = ∑ T ∈ imgSwaps 4 Ψ, Nop T ∘ₗ Nop v := by
      ext x
      simp only [LinearMap.comp_apply, Ssum_apply, LinearMap.sum_apply]
    rw [hcomp, map_sum, Finset.sum_congr rfl hterm, Finset.sum_boole]
  rw [← h1, h2', card_filter_imgSwaps hinj (fun T => T * v ≠ v * T)]

theorem card_filter_swap_four (P : Perm (Fin 4) → Prop) [DecidablePred P] :
    ((swapSet 4).filter P).card = (Finset.univ.filter fun i : Fin 6 => P (sw6 i)).card := by
  rw [swapSet_four_eq, Finset.filter_image]
  exact Finset.card_image_of_injective _ sw6_injective

theorem extra_star (hdim : finrank K V = 3) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (Ψ : Perm (Fin 4) →* V ≃ₗ[K] V)
    (hinj : Function.Injective Ψ) (hsub : ∀ σ ∈ swapSet 4, Ψ σ ∈ 𝒟) {v : V ≃ₗ[K] V}
    (hv : v ∈ 𝒟) (hvn : v ∉ imgSwaps 4 Ψ) :
    (5 : K) = 0 ∧ ∃ a : Fin 4, ∀ σ ∈ swapSet 4, (Ψ σ * v ≠ v * Ψ σ ↔ σ a ≠ a) := by
  have hcount := extra_count hdim h2 h3 h Ψ hinj hsub hv hvn
  rw [card_filter_swap_four (fun σ => Ψ σ * v ≠ v * Ψ σ)] at hcount
  let b : Fin 6 → Bool := fun i => decide (Ψ (sw6 i) * v ≠ v * Ψ (sw6 i))
  have hb : ∀ i, b i = true ↔ Ψ (sw6 i) * v ≠ v * Ψ (sw6 i) := fun i => by simp [b]
  have hcnt : cnt6 b =
      (Finset.univ.filter fun i : Fin 6 => Ψ (sw6 i) * v ≠ v * Ψ (sw6 i)).card := by
    unfold cnt6
    congr 1
  rw [← hcnt] at hcount
  have hcl : LineClosed b := by
    intro i j hne hbi
    by_contra hcon
    push Not at hcon
    obtain ⟨hbj, hρ⟩ := hcon
    obtain ⟨k, hk⟩ := exists_sw6 (swapSet_conj' (sw6_mem i) (sw6_mem j))
    have hτc : Ψ (sw6 j) * v = v * Ψ (sw6 j) := by
      by_contra e; exact hbj ((hb j).2 e)
    have hρc : Ψ (sw6 k) * v = v * Ψ (sw6 k) := by
      by_contra e; exact hρ k hk ((hb k).2 e)
    have hσc : Ψ (sw6 i) * v = v * Ψ (sw6 i) := by
      have hsig := swap_line _ (sw6_mem i) _ (sw6_mem j) hne
      have hv' : Ψ (sw6 i) = Ψ (sw6 j) * Ψ (sw6 k) * Ψ (sw6 j) := by
        rw [← map_mul, ← map_mul, hk, hsig]
      rw [hv']
      have hτ' : Commute (Ψ (sw6 j)) v := hτc
      have hρ' : Commute (Ψ (sw6 k)) v := hρc
      exact ((hτ'.mul_left hρ').mul_left hτ' : Commute (Ψ (sw6 j) * Ψ (sw6 k) * Ψ (sw6 j)) v)
    exact (hb i).1 hbi hσc
  obtain ⟨h1, h2', h3'⟩ := star_cases b hcl
  have hle : cnt6 b ≤ 6 := by
    have := Finset.card_le_univ (Finset.univ.filter fun i : Fin 6 => b i = true)
    simpa [cnt6] using this
  have hK8 : (8 : K) ≠ 0 := by
    have : (8 : K) = 2 * 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h2
  have h4K : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hc3 : cnt6 b = 3 ∧ (5 : K) = 0 := by
    generalize cnt6 b = k at hcount h1 h2' hle h3'
    interval_cases k
    · exfalso; apply hK8; rw [← hcount]; simp
    · exact absurd rfl h1
    · exact absurd rfl h2'
    · refine ⟨rfl, ?_⟩
      push_cast at hcount
      linear_combination -hcount
    · exfalso; apply h4K
      push_cast at hcount
      linear_combination -hcount
    · exfalso; apply h3
      push_cast at hcount
      linear_combination -hcount
    · exfalso; apply h2
      push_cast at hcount
      linear_combination -hcount
  refine ⟨hc3.2, ?_⟩
  obtain ⟨a, ha⟩ := h3' hc3.1
  refine ⟨a, fun σ hσ => ?_⟩
  obtain ⟨i, rfl⟩ := exists_sw6 hσ
  rw [← ha i, hb]

end Extras

section Five

open scoped _root_.Classical

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def incl45 : Perm (Fin 4) →* Perm (Fin 5) :=
  Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 4 ↪ Fin 5)

theorem incl45_castSucc (σ : Perm (Fin 4)) (x : Fin 4) :
    incl45 σ (Fin.castSucc x) = Fin.castSucc (σ x) :=
  Equiv.Perm.viaEmbedding_apply σ (Fin.castSuccEmb : Fin 4 ↪ Fin 5) x

theorem incl45_last (σ : Perm (Fin 4)) : incl45 σ (Fin.last 4) = Fin.last 4 := by
  refine Equiv.Perm.viaEmbedding_apply_of_notMem σ (Fin.castSuccEmb : Fin 4 ↪ Fin 5) _ ?_
  rintro ⟨x, hx⟩
  exact absurd hx (Fin.castSucc_lt_last x).ne

theorem incl45_swap (x y : Fin 4) :
    incl45 (swap x y) = swap (Fin.castSucc x) (Fin.castSucc y) := by
  refine Equiv.ext fun z => ?_
  induction z using Fin.lastCases with
  | last =>
    rw [incl45_last, Equiv.swap_apply_of_ne_of_ne]
    · exact (Fin.castSucc_lt_last x).ne'
    · exact (Fin.castSucc_lt_last y).ne'
  | cast w =>
    rw [incl45_castSucc]
    exact ((Fin.castSucc_injective 4).swap_apply x y w).symm

theorem incl45_mem_swapSet {σ : Perm (Fin 4)} (hσ : σ ∈ swapSet 4) : incl45 σ ∈ swapSet 5 := by
  obtain ⟨x, y, hxy, rfl⟩ := mem_swapSet.1 hσ
  rw [incl45_swap, mem_swapSet]
  exact ⟨_, _, (Fin.castSucc_injective 4).ne hxy, rfl⟩

theorem swap_last_comm_iff : ∀ σ ∈ swapSet 4, ∀ b : Fin 4,
    (incl45 σ * swap (Fin.castSucc b) (Fin.last 4) = swap (Fin.castSucc b) (Fin.last 4) * incl45 σ
      ↔ σ b = b) := by
  intro σ hσ b
  obtain ⟨x, y, hxy, rfl⟩ := mem_swapSet.1 hσ
  rw [incl45_swap]
  revert x y b
  decide +kernel

end Five

section Unique

open scoped _root_.Classical

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem isRSet_mul_self {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {T : V ≃ₗ[K] V} (hT : T ∈ 𝒟) :
    T * T = 1 := by
  obtain ⟨r, φ, hd⟩ := h.refl T hT
  exact hd.mul_self

theorem braid_of_noncomm {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {T S : V ≃ₗ[K] V}
    (hT : T ∈ 𝒟) (hS : S ∈ 𝒟) (hne : T * S ≠ S * T) : T * S * T = S * T * S := by
  have hTS : T ≠ S := fun e => hne (by rw [e])
  have hTi : T⁻¹ = T := h.inv_eq hT
  have hSi : S⁻¹ = S := h.inv_eq hS
  rcases h.ord T hT S hS hTS with h1 | h1 | h1
  · exfalso
    apply hTS
    have : T * S = 1 := by simpa using h1
    calc T = T * (S * S) := by rw [isRSet_mul_self h hS, mul_one]
      _ = (T * S) * S := by rw [mul_assoc]
      _ = S := by rw [this, one_mul]
  · exfalso
    apply hne
    have h2' : T * S * (T * S) = 1 := by rw [← pow_two]; exact h1
    have h3 := eq_inv_of_mul_eq_one_left h2'
    rw [mul_inv_rev, hTi, hSi] at h3
    exact h3
  · have h1' : (T * S * T) * (S * T * S) = 1 := by
      calc (T * S * T) * (S * T * S) = (T * S) ^ 3 := by rw [pow_three']; group
        _ = 1 := h1
    have h2 := eq_inv_of_mul_eq_one_left h1'
    rw [h2, mul_inv_rev, mul_inv_rev, hTi, hSi, mul_assoc]

variable [FiniteDimensional K V]

theorem common_kernel_line (hdim : finrank K V = 3) (h3 : (3 : K) ≠ 0)
    {T₁ T₂ : V ≃ₗ[K] V} {r₁ r₂ : V} {φ₁ φ₂ : V →ₗ[K] K} (d₁ : ReflData T₁ r₁ φ₁)
    (d₂ : ReflData T₂ r₂ φ₂) (hbr : φ₁ r₂ * φ₂ r₁ = 1) {s : V} (hs : s ≠ 0) (hs1 : φ₁ s = 0)
    (hs2 : φ₂ s = 0) {x : V} (hx1 : φ₁ x = 0) (hx2 : φ₂ x = 0) : ∃ c : K, x = c • s := by
  let Φ : V →ₗ[K] K × K := φ₁.prod φ₂
  have hrange : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨u₁, u₂⟩
    set α : K := (2 * u₁ - φ₁ r₂ * u₂) / 3 with hα
    set β : K := (2 * u₂ - φ₂ r₁ * u₁) / 3 with hβ
    refine ⟨α • r₁ + β • r₂, ?_⟩
    have e1 : φ₁ (α • r₁ + β • r₂) = 2 * α + φ₁ r₂ * β := by
      rw [map_add, map_smul, map_smul, d₁.pair, smul_eq_mul, smul_eq_mul]
      ring
    have e2 : φ₂ (α • r₁ + β • r₂) = φ₂ r₁ * α + 2 * β := by
      rw [map_add, map_smul, map_smul, d₂.pair, smul_eq_mul, smul_eq_mul]
      ring
    show (φ₁ (α • r₁ + β • r₂), φ₂ (α • r₁ + β • r₂)) = (u₁, u₂)
    rw [e1, e2]
    refine Prod.ext ?_ ?_
    · show 2 * α + φ₁ r₂ * β = u₁
      rw [hα, hβ]
      field_simp
      linear_combination (-u₁) * hbr
    · show φ₂ r₁ * α + 2 * β = u₂
      rw [hα, hβ]
      field_simp
      linear_combination (-u₂) * hbr
  have hker : finrank K (LinearMap.ker Φ) = 1 := by
    have := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hrange, finrank_top, Module.finrank_prod, finrank_self, hdim] at this
    omega
  have hsker : s ∈ LinearMap.ker Φ := by
    simp [Φ, hs1, hs2]
  have hxker : x ∈ LinearMap.ker Φ := by
    simp [Φ, hx1, hx2]
  have hnz : (⟨s, hsker⟩ : LinearMap.ker Φ) ≠ 0 := fun e => hs (congrArg Subtype.val e)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hnz).1 hker ⟨x, hxker⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem eq_of_comm_pair (hdim : finrank K V = 3) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {T₁ T₂ w w' : V ≃ₗ[K] V} (hT₁ : T₁ ∈ 𝒟)
    (hT₂ : T₂ ∈ 𝒟) (hw : w ∈ 𝒟) (hw' : w' ∈ 𝒟) (hT : T₁ * T₂ ≠ T₂ * T₁) (hw1 : w ≠ T₁)
    (hw2 : w ≠ T₂) (hw1' : w' ≠ T₁) (hw2' : w' ≠ T₂) (hc1 : T₁ * w = w * T₁)
    (hc2 : T₂ * w = w * T₂) (hc1' : T₁ * w' = w' * T₁) (hc2' : T₂ * w' = w' * T₂) : w = w' := by
  obtain ⟨r₁, φ₁, d₁⟩ := h.refl T₁ hT₁
  obtain ⟨r₂, φ₂, d₂⟩ := h.refl T₂ hT₂
  obtain ⟨s, χ, d⟩ := h.refl w hw
  obtain ⟨s', χ', d'⟩ := h.refl w' hw'
  have hne12 : T₁ ≠ T₂ := fun e => hT (by rw [e])
  have hbr : φ₁ r₂ * φ₂ r₁ = 1 := by
    rcases dichotomy h2 h3 d₁ d₂ hne12 (h.ord T₁ hT₁ T₂ hT₂ hne12) with ⟨e1, e2⟩ | e
    · exact absurd (commute_of_orth d₁ d₂ e1 e2) hT
    · exact e
  obtain ⟨hs1, -⟩ := commute_orth h2 h3 d₁ d hw1.symm hc1
  obtain ⟨hs2, -⟩ := commute_orth h2 h3 d₂ d hw2.symm hc2
  obtain ⟨hs1', -⟩ := commute_orth h2 h3 d₁ d' hw1'.symm hc1'
  obtain ⟨hs2', -⟩ := commute_orth h2 h3 d₂ d' hw2'.symm hc2'
  obtain ⟨c, hc⟩ := common_kernel_line hdim h3 d₁ d₂ hbr d.ne hs1 hs2 hs1' hs2'
  exact (h.eq_of_parallel h2 h3 hw' hw d' d hc).symm

theorem conn_aux (hdim : finrank K V = 3) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 P Q : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (Γ : Subgroup (V ≃ₗ[K] V))
    (hΓ : ∀ g ∈ Γ, ∀ T ∈ 𝒟, g * T * g⁻¹ ∈ 𝒟)
    (hirr : ∀ U : Submodule K V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hP : P ⊆ 𝒟) (hQ : Q ⊆ 𝒟) (hdisj : Disjoint P Q) (hcover : ∀ T ∈ 𝒟, T ∈ P ∨ T ∈ Q)
    (hcomm : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) {T₁ T₂ : V ≃ₗ[K] V} (hT₁ : T₁ ∈ P) (hT₂ : T₂ ∈ P)
    (hbr : T₁ * T₂ ≠ T₂ * T₁) : Q = ∅ := by
  by_contra hne
  obtain ⟨w, hwQ⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have hw𝒟 : w ∈ 𝒟 := hQ hwQ
  have hwT₁ : w ≠ T₁ := fun e => Finset.disjoint_left.1 hdisj hT₁ (e ▸ hwQ)
  have hwT₂ : w ≠ T₂ := fun e => Finset.disjoint_left.1 hdisj hT₂ (e ▸ hwQ)
  have hQw : ∀ y ∈ Q, y = w := by
    intro y hyQ
    have hy1 : y ≠ T₁ := fun e => Finset.disjoint_left.1 hdisj hT₁ (e ▸ hyQ)
    have hy2 : y ≠ T₂ := fun e => Finset.disjoint_left.1 hdisj hT₂ (e ▸ hyQ)
    exact (eq_of_comm_pair hdim h2 h3 h (hP hT₁) (hP hT₂) hw𝒟 (hQ hyQ) hbr hwT₁ hwT₂ hy1 hy2
      (hcomm _ hT₁ _ hwQ) (hcomm _ hT₂ _ hwQ) (hcomm _ hT₁ _ hyQ) (hcomm _ hT₂ _ hyQ)).symm
  have hwiso : ∀ s ∈ 𝒟, s ≠ w → w * s = s * w := by
    intro s hs hsw
    rcases hcover s hs with hsP | hsQ
    · exact (hcomm s hsP w hwQ).symm
    · exact absurd (hQw s hsQ) hsw
  have hfix : ∀ g ∈ Γ, g * w * g⁻¹ = w := by
    intro g hg
    have hw' : g * w * g⁻¹ ∈ 𝒟 := hΓ g hg w hw𝒟
    have hiso' : ∀ s ∈ 𝒟, s ≠ g * w * g⁻¹ → (g * w * g⁻¹) * s = s * (g * w * g⁻¹) := by
      intro s hs hsne
      have hs' : g⁻¹ * s * g ∈ 𝒟 := by
        have := hΓ g⁻¹ (Γ.inv_mem hg) s hs
        simpa using this
      have hne' : g⁻¹ * s * g ≠ w := by
        intro e
        apply hsne
        calc s = g * (g⁻¹ * s * g) * g⁻¹ := by group
          _ = g * w * g⁻¹ := by rw [e]
      have := hwiso _ hs' hne'
      calc (g * w * g⁻¹) * s = g * (w * (g⁻¹ * s * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * s * g) * w) * g⁻¹ := by rw [this]
        _ = s * (g * w * g⁻¹) := by group
    by_contra hwne
    have hy1 : g * w * g⁻¹ ≠ T₁ := by
      intro e
      apply hbr
      have := hiso' T₂ (hP hT₂) (fun e' => hbr (by
        have : T₁ = T₂ := e.symm.trans e'.symm
        rw [this]))
      rw [e] at this
      exact this
    have hy2 : g * w * g⁻¹ ≠ T₂ := by
      intro e
      apply hbr
      have := hiso' T₁ (hP hT₁) (fun e' => hbr (by
        have : T₁ = T₂ := e'.trans e
        rw [this]))
      rw [e] at this
      exact this.symm
    exact hwne (eq_of_comm_pair hdim h2 h3 h (hP hT₁) (hP hT₂) hw' hw𝒟 hbr hy1 hy2 hwT₁ hwT₂
      (hiso' _ (hP hT₁) hy1.symm |>.symm) (hiso' _ (hP hT₂) hy2.symm |>.symm)
      (hwiso _ (hP hT₁) hwT₁.symm |>.symm) (hwiso _ (hP hT₂) hwT₂.symm |>.symm))
  obtain ⟨r, φ, hd⟩ := h.refl w hw𝒟
  have hinv : ∀ g ∈ Γ, ∀ x ∈ K ∙ r, g x ∈ K ∙ r := by
    intro g hg x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    have hd' := hd.conj g
    rw [hfix g hg] at hd'
    have h1 : g r ∈ LinearMap.range (Nop w) := by
      rw [hd'.range_nop h2]
      exact Submodule.mem_span_singleton_self _
    rwa [hd.range_nop h2] at h1
  rcases hirr _ hinv with h0 | h1
  · exact hd.ne ((Submodule.span_singleton_eq_bot).1 h0)
  · have := finrank_span_singleton hd.ne (K := K)
    rw [h1, finrank_top, hdim] at this
    omega

theorem conn_of_irreducible (hdim : finrank K V = 3) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (Γ : Subgroup (V ≃ₗ[K] V))
    (hΓ : ∀ g ∈ Γ, ∀ T ∈ 𝒟, g * T * g⁻¹ ∈ 𝒟)
    (hirr : ∀ U : Submodule K V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    {T₁ T₂ : V ≃ₗ[K] V} (hT₁ : T₁ ∈ 𝒟) (hT₂ : T₂ ∈ 𝒟) (hbr : T₁ * T₂ ≠ T₂ * T₁) : Conn 𝒟 := by
  intro P hPsub hPne hPcl
  by_contra hne
  have hQsub : 𝒟 \ P ⊆ 𝒟 := Finset.sdiff_subset
  have hdisj : Disjoint P (𝒟 \ P) := Finset.disjoint_sdiff
  have hcover : ∀ T ∈ 𝒟, T ∈ P ∨ T ∈ 𝒟 \ P := fun T hT => by
    by_cases hTP : T ∈ P
    · exact Or.inl hTP
    · exact Or.inr (Finset.mem_sdiff.2 ⟨hT, hTP⟩)
  have hcomm : ∀ x ∈ P, ∀ y ∈ 𝒟 \ P, x * y = y * x := by
    intro x hx y hy
    by_contra e
    exact (Finset.mem_sdiff.1 hy).2 (hPcl x hx y (Finset.mem_sdiff.1 hy).1 e)
  rcases hcover T₁ hT₁ with h1 | h1
  · have h2' : T₂ ∈ P := hPcl T₁ h1 T₂ hT₂ hbr
    have hQ := conn_aux hdim h2 h3 h Γ hΓ hirr hPsub hQsub hdisj hcover hcomm h1 h2' hbr
    apply hne
    refine Finset.Subset.antisymm hPsub fun T hT => ?_
    rcases hcover T hT with hTP | hTQ
    · exact hTP
    · rw [hQ] at hTQ
      exact absurd hTQ (Finset.notMem_empty _)
  · have h2' : T₂ ∈ 𝒟 \ P := by
      refine Finset.mem_sdiff.2 ⟨hT₂, fun hT₂P => ?_⟩
      exact (Finset.mem_sdiff.1 h1).2 (hPcl T₂ hT₂P T₁ hT₁ (fun e => hbr e.symm))
    have hcover' : ∀ T ∈ 𝒟, T ∈ 𝒟 \ P ∨ T ∈ P := fun T hT => (hcover T hT).symm
    have hcomm' : ∀ x ∈ 𝒟 \ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
    have hPe := conn_aux hdim h2 h3 h Γ hΓ hirr hQsub hPsub hdisj.symm hcover' hcomm' h1 h2' hbr
    obtain ⟨x, hx⟩ := hPne
    rw [hPe] at hx
    exact Finset.notMem_empty _ hx

theorem perm_five_injective {H : Type*} [Group H] (Ψ : Perm (Fin 5) →* H)
    (h : Ψ (swap 0 1) * Ψ (swap 1 2) ≠ 1) : Function.Injective Ψ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have hnt : Nontrivial Ψ.ker := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 5) (by simp) (N := Ψ.ker) hnt
  have hmem : swap (0 : Fin 5) 1 * swap 1 2 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  exact h (by simpa using hle hmem)

omit [FiniteDimensional K V] in
theorem extend_five {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (Ψ : Perm (Fin 4) →* V ≃ₗ[K] V)
    (hinj : Function.Injective Ψ) (hsub : ∀ σ ∈ swapSet 4, Ψ σ ∈ 𝒟) {v : V ≃ₗ[K] V}
    (hv : v ∈ 𝒟) (hpat : ∀ σ ∈ swapSet 4, (Ψ σ * v ≠ v * Ψ σ ↔ σ 3 ≠ 3)) :
    ∃ Ψ₁ : Perm (Fin 5) →* V ≃ₗ[K] V, Function.Injective Ψ₁ ∧ (∀ σ, Ψ₁ (incl45 σ) = Ψ σ) ∧
      Ψ₁ (swap (Fin.castSucc (3 : Fin 4)) (Fin.last 4)) = v ∧
      ∀ σ ∈ swapSet 5, Ψ₁ σ ∈ 𝒟 := by
  have s01 : swap (0 : Fin 4) 1 ∈ swapSet 4 := by decide
  have s12 : swap (1 : Fin 4) 2 ∈ swapSet 4 := by decide
  have s23 : swap (2 : Fin 4) 3 ∈ swapSet 4 := by decide
  have hvv : v * v = 1 := isRSet_mul_self h hv
  let g : ℕ → V ≃ₗ[K] V := fun i =>
    match i with
    | 0 => Ψ (swap 0 1)
    | 1 => Ψ (swap 1 2)
    | 2 => Ψ (swap 2 3)
    | 3 => v
    | _ => 1
  have hΨsq : ∀ σ : Perm (Fin 4), σ * σ = 1 → Ψ σ * Ψ σ = 1 := fun σ hσ => by
    rw [← map_mul, hσ, map_one]
  have hcox : IsCoxeterA 4 g := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      interval_cases i
      · exact hΨsq _ (by decide)
      · exact hΨsq _ (by decide)
      · exact hΨsq _ (by decide)
      · exact hvv
    · intro i hi
      have hi' : i < 3 := by omega
      interval_cases i
      · show Ψ (swap 0 1) * Ψ (swap 1 2) * Ψ (swap 0 1) =
          Ψ (swap 1 2) * Ψ (swap 0 1) * Ψ (swap 1 2)
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
        congr 1
        decide +kernel
      · show Ψ (swap 1 2) * Ψ (swap 2 3) * Ψ (swap 1 2) =
          Ψ (swap 2 3) * Ψ (swap 1 2) * Ψ (swap 2 3)
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
        congr 1
        decide +kernel
      · have hnc : Ψ (swap 2 3) * v ≠ v * Ψ (swap 2 3) :=
          (hpat _ s23).2 (by decide)
        exact braid_of_noncomm h (hsub _ s23) hv hnc
    · intro i j hij hj
      have hi' : i < 2 := by omega
      interval_cases i
      · interval_cases j
        · show Ψ (swap 0 1) * Ψ (swap 2 3) = Ψ (swap 2 3) * Ψ (swap 0 1)
          rw [← map_mul, ← map_mul]
          congr 1
          decide +kernel
        · have hc : Ψ (swap 0 1) * v = v * Ψ (swap 0 1) := by
            by_contra e
            exact (not_not.2 (by decide : (swap (0 : Fin 4) 1) 3 = 3)) ((hpat _ s01).1 e)
          exact hc
      · interval_cases j
        have hc : Ψ (swap 1 2) * v = v * Ψ (swap 1 2) := by
          by_contra e
          exact (not_not.2 (by decide : (swap (1 : Fin 4) 2) 3 = 3)) ((hpat _ s12).1 e)
        exact hc
  obtain ⟨Ψ₁, hΨ₁⟩ := exists_hom_perm 4 g hcox
  have hgi : ∀ i < 4, Ψ₁ (adjSwap 4 i) = g i := hΨ₁
  have e0 : Ψ₁ (swap (0 : Fin 5) 1) = Ψ (swap 0 1) := by
    have := hgi 0 (by norm_num)
    rw [adjSwap_of_lt (by norm_num)] at this
    exact this
  have e1 : Ψ₁ (swap (1 : Fin 5) 2) = Ψ (swap 1 2) := by
    have := hgi 1 (by norm_num)
    rw [adjSwap_of_lt (by norm_num)] at this
    exact this
  have e2 : Ψ₁ (swap (2 : Fin 5) 3) = Ψ (swap 2 3) := by
    have := hgi 2 (by norm_num)
    rw [adjSwap_of_lt (by norm_num)] at this
    exact this
  have e3 : Ψ₁ (swap (3 : Fin 5) 4) = v := by
    have := hgi 3 (by norm_num)
    rw [adjSwap_of_lt (by norm_num)] at this
    exact this
  have hinj1 : Function.Injective Ψ₁ := by
    refine perm_five_injective Ψ₁ ?_
    rw [e0, e1, ← map_mul]
    intro h1
    have := hinj (h1.trans (map_one Ψ).symm)
    revert this
    decide
  have hres : ∀ σ : Perm (Fin 4), Ψ₁ (incl45 σ) = Ψ σ := by
    intro σ
    have hσ : σ ∈ Subgroup.closure (adjSwap 3 '' Set.Iio 3) := by
      rw [closure_adjSwap 3]; trivial
    induction hσ using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨i, hi, rfl⟩ := hz
      have hi' : i < 3 := hi
      interval_cases i
      · rw [adjSwap_of_lt (by norm_num), incl45_swap]
        exact e0
      · rw [adjSwap_of_lt (by norm_num), incl45_swap]
        exact e1
      · rw [adjSwap_of_lt (by norm_num), incl45_swap]
        exact e2
    | one => rw [map_one, map_one, map_one]
    | mul a b _ _ ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, map_inv, map_inv, ha]
  refine ⟨Ψ₁, hinj1, hres, e3, fun σ hσ => ?_⟩
  refine hom_swap_mem (m := 4) (by norm_num) h Ψ₁ (fun i hi => ?_) hσ
  rw [hgi i hi]
  interval_cases i
  · exact hsub _ s01
  · exact hsub _ s12
  · exact hsub _ s23
  · exact hv

theorem classify_dim_three (hdim : finrank K V = 3) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hconn : Conn 𝒟) {a c : V ≃ₗ[K] V} (ha : a ∈ 𝒟)
    (hc : c ∈ 𝒟) (hac : a ≠ c) (hcomm : a * c = c * a) :
    ∃ (n : ℕ) (Ψ : Perm (Fin n) →* V ≃ₗ[K] V), (n = 4 ∨ n = 5) ∧ Function.Injective Ψ ∧
      (n = 5 → (5 : K) = 0) ∧ 𝒟 = imgSwaps n Ψ := by
  obtain ⟨x, hx, y, hy, z, hz, hxz, hxzc, hxy, hyz⟩ := exists_chain3 hconn ha hc hac hcomm
  have hxyne : x ≠ y := fun e => hxy (by rw [e])
  have hx1 : x ≠ 1 := fun e => hxy (by rw [e, one_mul, mul_one])
  obtain ⟨Ψ₀, hinj₀, h01, h12, h23⟩ := exists_perm_four (isRSet_mul_self h hx)
    (isRSet_mul_self h hy) (isRSet_mul_self h hz) (braid_of_noncomm h hx hy hxy)
    (braid_of_noncomm h hy hz hyz) hxzc hx1 hxz hxyne
  have hsub₀ : ∀ σ ∈ swapSet 4, Ψ₀ σ ∈ 𝒟 := by
    intro σ hσ
    refine hom_swap_mem (m := 3) (by norm_num) h Ψ₀ (fun i hi => ?_) hσ
    interval_cases i
    · rw [adjSwap_of_lt (by norm_num)]
      show Ψ₀ (swap 0 1) ∈ 𝒟
      rw [h01]; exact hx
    · rw [adjSwap_of_lt (by norm_num)]
      show Ψ₀ (swap 1 2) ∈ 𝒟
      rw [h12]; exact hy
    · rw [adjSwap_of_lt (by norm_num)]
      show Ψ₀ (swap 2 3) ∈ 𝒟
      rw [h23]; exact hz
  by_cases hext : ∃ v ∈ 𝒟, v ∉ imgSwaps 4 Ψ₀
  swap
  · refine ⟨4, Ψ₀, Or.inl rfl, hinj₀, fun h5 => absurd h5 (by norm_num), ?_⟩
    refine Finset.Subset.antisymm (fun v hv => ?_) (fun T hT => ?_)
    · by_contra hn
      exact hext ⟨v, hv, hn⟩
    · obtain ⟨σ, hσ, rfl⟩ := mem_imgSwaps.1 hT
      exact hsub₀ σ hσ
  obtain ⟨v, hv, hvn⟩ := hext
  obtain ⟨h5, a₀, hpat⟩ := extra_star hdim h2 h3 h Ψ₀ hinj₀ hsub₀ hv hvn
  set π : Perm (Fin 4) := swap a₀ 3 with hπ
  let Ψ' : Perm (Fin 4) →* V ≃ₗ[K] V := Ψ₀.comp (MulAut.conj π).toMonoidHom
  have hΨ' : ∀ σ, Ψ' σ = Ψ₀ (π * σ * π⁻¹) := fun σ => rfl
  have hinj' : Function.Injective Ψ' := hinj₀.comp (MulAut.conj π).injective
  have hsub' : ∀ σ ∈ swapSet 4, Ψ' σ ∈ 𝒟 := fun σ hσ => by
    rw [hΨ']; exact hsub₀ _ (swapSet_conj π hσ)
  have himg : imgSwaps 4 Ψ' = imgSwaps 4 Ψ₀ := by
    refine Finset.Subset.antisymm (fun T hT => ?_) (fun T hT => ?_)
    · obtain ⟨σ, hσ, rfl⟩ := mem_imgSwaps.1 hT
      exact mem_imgSwaps.2 ⟨_, swapSet_conj π hσ, (hΨ' σ).symm⟩
    · obtain ⟨σ, hσ, rfl⟩ := mem_imgSwaps.1 hT
      refine mem_imgSwaps.2 ⟨π⁻¹ * σ * π, ?_, ?_⟩
      · have := swapSet_conj π⁻¹ hσ
        simpa using this
      · rw [hΨ']
        congr 1
        group
  have hvn' : v ∉ imgSwaps 4 Ψ' := by rw [himg]; exact hvn
  have hpat' : ∀ σ ∈ swapSet 4, (Ψ' σ * v ≠ v * Ψ' σ ↔ σ 3 ≠ 3) := by
    intro σ hσ
    rw [hΨ', hpat _ (swapSet_conj π hσ)]
    have hπa : π a₀ = 3 := by rw [hπ]; exact Equiv.swap_apply_left _ _
    have hπ3 : π 3 = a₀ := by rw [hπ]; exact Equiv.swap_apply_right _ _
    have hπi : π⁻¹ = π := by rw [hπ]; exact Equiv.swap_inv _ _
    rw [hπi]
    show π (σ (π a₀)) ≠ a₀ ↔ σ 3 ≠ 3
    rw [hπa]
    constructor
    · intro hne e
      apply hne
      rw [e, hπ3]
    · intro hne e
      apply hne
      apply π.injective
      rw [e.trans hπ3.symm]
  obtain ⟨Ψ₁, hinj₁, hres, hlast, hsub₁⟩ := extend_five h Ψ' hinj' hsub' hv hpat'
  refine ⟨5, Ψ₁, Or.inr rfl, hinj₁, fun _ => h5, ?_⟩
  refine Finset.Subset.antisymm (fun w hw => ?_) (fun T hT => ?_)
  swap
  · obtain ⟨σ, hσ, rfl⟩ := mem_imgSwaps.1 hT
    exact hsub₁ σ hσ
  by_cases hw' : w ∈ imgSwaps 4 Ψ'
  · obtain ⟨σ, hσ, rfl⟩ := mem_imgSwaps.1 hw'
    exact mem_imgSwaps.2 ⟨incl45 σ, incl45_mem_swapSet hσ, hres σ⟩
  · obtain ⟨-, b, hpatb⟩ := extra_star hdim h2 h3 h Ψ' hinj' hsub' hw hw'
    set u := Ψ₁ (swap (Fin.castSucc b) (Fin.last 4)) with hu
    have hswap5 : swap (Fin.castSucc b) (Fin.last 4) ∈ swapSet 5 := by
      rw [mem_swapSet]
      exact ⟨_, _, (Fin.castSucc_lt_last b).ne, rfl⟩
    have hu_mem : u ∈ 𝒟 := hsub₁ _ hswap5
    have hu_not : u ∉ imgSwaps 4 Ψ' := by
      intro hu'
      obtain ⟨τ, hτ, hτu⟩ := mem_imgSwaps.1 hu'
      have h1 : Ψ₁ (incl45 τ) = Ψ₁ (swap (Fin.castSucc b) (Fin.last 4)) := by
        rw [hres τ]; exact hτu
      have h2' := hinj₁ h1
      have h3' := congrArg (fun π => π (Fin.last 4)) h2'
      simp only [incl45_last, Equiv.swap_apply_right] at h3'
      exact (Fin.castSucc_lt_last b).ne h3'.symm
    have hpat_u : ∀ σ ∈ swapSet 4, (Ψ' σ * u = u * Ψ' σ ↔ σ b = b) := by
      intro σ hσ
      rw [← swap_last_comm_iff σ hσ b, hu, ← hres σ, ← map_mul, ← map_mul]
      exact hinj₁.eq_iff
    obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hb1, hb2, hnc⟩ := exists_pair_fixing b
    have hc1 : Ψ' σ₁ * w = w * Ψ' σ₁ := by
      by_contra e; exact ((hpatb σ₁ hσ₁).1 e) hb1
    have hc2 : Ψ' σ₂ * w = w * Ψ' σ₂ := by
      by_contra e; exact ((hpatb σ₂ hσ₂).1 e) hb2
    have hc1u : Ψ' σ₁ * u = u * Ψ' σ₁ := (hpat_u σ₁ hσ₁).2 hb1
    have hc2u : Ψ' σ₂ * u = u * Ψ' σ₂ := (hpat_u σ₂ hσ₂).2 hb2
    have hTi1 : Ψ' σ₁ ∈ imgSwaps 4 Ψ' := mem_imgSwaps.2 ⟨σ₁, hσ₁, rfl⟩
    have hTi2 : Ψ' σ₂ ∈ imgSwaps 4 Ψ' := mem_imgSwaps.2 ⟨σ₂, hσ₂, rfl⟩
    have hwu : w = u := eq_of_comm_pair hdim h2 h3 h (hsub' σ₁ hσ₁) (hsub' σ₂ hσ₂) hw hu_mem
      (fun e => hnc ((Ψ_comm_iff hinj').1 e)) (fun e => hw' (e ▸ hTi1)) (fun e => hw' (e ▸ hTi2))
      (fun e => hu_not (e ▸ hTi1)) (fun e => hu_not (e ▸ hTi2)) hc1 hc2 hc1u hc2u
    rw [hwu]
    exact mem_imgSwaps.2 ⟨_, hswap5, rfl⟩

end Unique

end ReflF

end CFSG.RankThree.PartOne
