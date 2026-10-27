module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

private theorem tawe_exists_eq_of_mul_diagonal {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] (y : GL ι K) {d d' : ι → K}
    (h : (y : Matrix ι ι K) * diagonal d = diagonal d' * y) (i : ι) : ∃ j, d' j = d i := by
  by_contra hne
  refine ((isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
    (det_eq_zero_of_column_eq_zero i fun j => ?_)
  have e := congrFun (congrFun h j) i
  rw [mul_diagonal, diagonal_mul] at e
  have h0 : (y : Matrix ι ι K) j i * (d i - d' j) = 0 := by
    rw [mul_sub, e]
    ring
  exact (mul_eq_zero.1 h0).resolve_right (sub_ne_zero.2 fun h => hne ⟨j, h.symm⟩)

theorem range_eq_of_mul_diagonal_eq_diagonal_mul {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] (y : GL ι K) {d d' : ι → K}
    (h : (y : Matrix ι ι K) * diagonal d = diagonal d' * y) : Set.range d = Set.range d' := by
  have h' : ((y⁻¹ : GL ι K) : Matrix ι ι K) * diagonal d' =
      diagonal d * ((y⁻¹ : GL ι K) : Matrix ι ι K) := by
    have := congrArg (fun M => ((y⁻¹ : GL ι K) : Matrix ι ι K) * M *
      ((y⁻¹ : GL ι K) : Matrix ι ι K)) h
    simpa [Matrix.mul_assoc] using this.symm
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact tawe_exists_eq_of_mul_diagonal y h i
  · rintro _ ⟨j, rfl⟩
    exact tawe_exists_eq_of_mul_diagonal y⁻¹ h' j

private theorem tawe_mem_range {K : Type} [Field K] {u : Fin 2 → Kˣ} {a : Kˣ} :
    a ∈ Set.range (Sum.elim u fun i => (u i)⁻¹) ↔
      u 0 = a ∨ u 1 = a ∨ (u 0)⁻¹ = a ∨ (u 1)⁻¹ = a := by
  simp only [Set.mem_range, Sum.exists, Sum.elim_inl, Sum.elim_inr, Fin.exists_fin_two, or_assoc]

private theorem tawe_range_conj {K : Type} [Field K] {y : StatedSp 2 K} {s t : Fin 2 → Kˣ}
    (h : y * torusHom t * y⁻¹ = torusHom s) :
    Set.range (Sum.elim t fun i => (t i)⁻¹) = Set.range (Sum.elim s fun i => (s i)⁻¹) := by
  have h' : y * torusHom t = torusHom s * y := by rw [← h, inv_mul_cancel_right]
  have hm := congrArg (fun g : StatedSp 2 K =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h'
  simp only [coe_mul_statedSp, coe_torusHom] at hm
  have key : ∀ u : Fin 2 → Kˣ, (Sum.elim (fun i => (u i : K)) fun i => (((u i)⁻¹ : Kˣ) : K)) =
      Units.val ∘ Sum.elim u fun i => (u i)⁻¹ := fun u => by
    funext x
    cases x <;> rfl
  have hr := range_eq_of_mul_diagonal_eq_diagonal_mul (y : GL (Fin 2 ⊕ Fin 2) K) hm
  rw [key, key, Set.range_comp, Set.range_comp] at hr
  exact Set.image_injective.2 Units.val_injective hr

private theorem tawe_exists_hom {K : Type} [Field K] {y : StatedSp 2 K}
    (hy : y ∈ normalizer ((torus 2 K : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K))) :
    ∃ W : (Fin 2 → Kˣ) →* (Fin 2 → Kˣ), ∀ t, y * torusHom t * y⁻¹ = torusHom (W t) := by
  have h : ∀ t : Fin 2 → Kˣ, ∃ s, torusHom s = y * torusHom t * y⁻¹ := fun t =>
    (mem_normalizer_iff.1 hy (torusHom t)).1 (torusHom_mem_torus t)
  choose w hw using h
  refine ⟨MonoidHom.mk' w fun s t => torusHom_injective ?_, fun t => (hw t).symm⟩
  rw [hw, map_mul torusHom s t, map_mul torusHom (w s) (w t), hw, hw]
  group

private theorem tawe_gen_ne_one {K : Type} [Field K] [Finite K] (hK : 3 ≤ Nat.card K) {ζ : Kˣ}
    (hgen : ∀ x : Kˣ, x ∈ zpowers ζ) : ζ ≠ 1 := by
  rintro rfl
  have h2 : 1 < Nat.card Kˣ := by
    have := Nat.card_eq_card_units_add_one K
    omega
  have := Finite.one_lt_card_iff_nontrivial.1 h2
  obtain ⟨a, ha⟩ := exists_ne (1 : Kˣ)
  exact ha (by simpa using hgen a)

private theorem tawe_pm {K : Type} [Field K] {ζ x : Kˣ} (h : x = ζ ∨ x⁻¹ = ζ) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ x = ζ ^ ε := by
  rcases h with rfl | rfl
  · exact ⟨1, Or.inl rfl, (zpow_one _).symm⟩
  · exact ⟨-1, Or.inr rfl, by rw [_root_.zpow_neg_one, inv_inv]⟩

private theorem tawe_shape {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ≠ 1) {u : Fin 2 → Kˣ}
    (h1 : (1 : Kˣ) ∈ Set.range (Sum.elim u fun i => (u i)⁻¹))
    (hz : ζ ∈ Set.range (Sum.elim u fun i => (u i)⁻¹)) :
    (u 0 = 1 ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ u 1 = ζ ^ ε) ∨
      (u 1 = 1 ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ u 0 = ζ ^ ε) := by
  rw [tawe_mem_range] at h1 hz
  have h1' : u 0 = 1 ∨ u 1 = 1 := by
    rcases h1 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl (inv_eq_one.1 h)
    · exact Or.inr (inv_eq_one.1 h)
  rcases h1' with h | h
  · refine Or.inl ⟨h, tawe_pm ?_⟩
    rw [h, inv_one] at hz
    rcases hz with hz | hz | hz | hz
    · exact absurd hz.symm hζ
    · exact Or.inl hz
    · exact absurd hz.symm hζ
    · exact Or.inr hz
  · refine Or.inr ⟨h, tawe_pm ?_⟩
    rw [h, inv_one] at hz
    rcases hz with hz | hz | hz | hz
    · exact Or.inl hz
    · exact absurd hz.symm hζ
    · exact Or.inr hz
    · exact absurd hz.symm hζ

private theorem tawe_ne_one {K : Type} [Field K] {t v : Fin 2 → Kˣ} (ht : ∀ k, t k ≠ 1)
    (h : Set.range (Sum.elim t fun i => (t i)⁻¹) = Set.range (Sum.elim v fun i => (v i)⁻¹))
    (k : Fin 2) : v k ≠ 1 := by
  intro hk
  obtain ⟨x, hx⟩ : (1 : Kˣ) ∈ Set.range (Sum.elim t fun i => (t i)⁻¹) :=
    h ▸ ⟨Sum.inl k, hk⟩
  rcases x with x | x
  · exact ht x hx
  · exact ht x (inv_eq_one.1 hx)

private theorem tawe_apply {K : Type} [Field K] (W : (Fin 2 → Kˣ) →* (Fin 2 → Kˣ)) {ζ : Kˣ}
    {t : Fin 2 → Kˣ} {i j : ℤ} (hi : ζ ^ i = t 0) (hj : ζ ^ j = t 1) (k : Fin 2) :
    W t k = W ![ζ, 1] k ^ i * W ![1, ζ] k ^ j := by
  have ht : t = ![ζ, 1] ^ i * ![1, ζ] ^ j := by
    funext l
    fin_cases l <;> simp [← hi, ← hj]
  rw [ht, map_mul, map_zpow, map_zpow]
  rfl

theorem exists_signedPerm_of_mem_normalizer_torus {K : Type} [Field K] [Finite K]
    (hK : 3 ≤ Nat.card K) {y : StatedSp 2 K}
    (hy : y ∈ normalizer ((torus 2 K : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K))) :
    ∃ (ε δ : ℤ) (b : Bool), (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧ ∀ t : Fin 2 → Kˣ,
      y * torusHom t * y⁻¹ =
        torusHom (if b then ![t 1 ^ δ, t 0 ^ ε] else ![t 0 ^ ε, t 1 ^ δ]) := by
  obtain ⟨W, hW⟩ := tawe_exists_hom hy
  obtain ⟨ζ, hgen⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hζ : ζ ≠ 1 := tawe_gen_ne_one hK hgen
  have hr : ∀ t, Set.range (Sum.elim t fun i => (t i)⁻¹) =
      Set.range (Sum.elim (W t) fun i => (W t i)⁻¹) := fun t => tawe_range_conj (hW t)
  have hs₁ := tawe_shape hζ ((hr ![ζ, 1]).subset ⟨Sum.inl 1, rfl⟩)
    ((hr ![ζ, 1]).subset ⟨Sum.inl 0, rfl⟩)
  have hs₂ := tawe_shape hζ ((hr ![1, ζ]).subset ⟨Sum.inl 0, rfl⟩)
    ((hr ![1, ζ]).subset ⟨Sum.inl 1, rfl⟩)
  have hne := tawe_ne_one (t := ![ζ, 1] * ![1, ζ]) (by intro k; fin_cases k <;> simp [hζ])
    (hr _)
  rw [map_mul] at hne
  rcases hs₁ with ⟨h10, ε, hε, h11⟩ | ⟨h11, ε, hε, h10⟩ <;>
    rcases hs₂ with ⟨h20, δ, hδ, h21⟩ | ⟨h21, δ, hδ, h20⟩
  · exact absurd (by simp [h10, h20]) (hne 0)
  · refine ⟨ε, δ, true, hε, hδ, fun t => ?_⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 (hgen (t 0))
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hgen (t 1))
    rw [hW t, if_pos rfl]
    refine congrArg _ (funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩))
    · simp [tawe_apply W hi hj, h10, h20, ← hi, ← hj, ← _root_.zpow_mul, mul_comm]
    · simp [tawe_apply W hi hj, h11, h21, ← hi, ← hj, ← _root_.zpow_mul, mul_comm]
  · refine ⟨ε, δ, false, hε, hδ, fun t => ?_⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 (hgen (t 0))
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hgen (t 1))
    rw [hW t, if_neg Bool.false_ne_true]
    refine congrArg _ (funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩))
    · simp [tawe_apply W hi hj, h10, h20, ← hi, ← hj, ← _root_.zpow_mul, mul_comm]
    · simp [tawe_apply W hi hj, h11, h21, ← hi, ← hj, ← _root_.zpow_mul, mul_comm]
  · exact absurd (by simp [h11, h21]) (hne 1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
