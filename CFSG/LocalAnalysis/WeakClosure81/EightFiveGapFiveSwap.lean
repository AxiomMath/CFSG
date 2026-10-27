module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltAut
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.PermAut
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFivePerm

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm

private noncomputable def w85g_phi {n : ℕ} {Y U : Type} [Group Y] [Group U]
    (e : Y ≃* Perm (Fin n)) (α : U →* MulAut Y) (u : U) : MulAut (Perm (Fin n)) :=
  (e.symm.trans (α u)).trans e

private noncomputable def w85g_aChoice {n : ℕ} (hn6 : n ≠ 6) {Y U : Type} [Group Y] [Group U]
    (e : Y ≃* Perm (Fin n)) (α : U →* MulAut Y) (u : U) : Perm (Fin n) :=
  Classical.choose
    (CFSG.ComponentClassification.RankTwoAlt.mulAut_perm_inner (by simpa using hn6)
      (w85g_phi e α u))

private lemma w85g_aChoice_spec {n : ℕ} (hn6 : n ≠ 6) {Y U : Type} [Group Y] [Group U]
    (e : Y ≃* Perm (Fin n)) (α : U →* MulAut Y) (u : U) :
    ∀ σ : Perm (Fin n),
      w85g_phi e α u σ = w85g_aChoice hn6 e α u * σ * (w85g_aChoice hn6 e α u)⁻¹ :=
  Classical.choose_spec
    (CFSG.ComponentClassification.RankTwoAlt.mulAut_perm_inner (by simpa using hn6)
      (w85g_phi e α u))

private lemma w85g_conj_injective {n : ℕ} (hn3 : 3 ≤ n) {β β' : Perm (Fin n)}
    (h : ∀ σ : Perm (Fin n), β * σ * β⁻¹ = β' * σ * β'⁻¹) : β = β' := by
  have hγ : ∀ σ : Perm (Fin n), (β'⁻¹ * β) * σ = σ * (β'⁻¹ * β) := by
    intro σ
    have h1 := h σ
    calc
      β'⁻¹ * β * σ = β'⁻¹ * (β * σ * β⁻¹) * β := by group
      _ = β'⁻¹ * (β' * σ * β'⁻¹) * β := by rw [h1]
      _ = σ * β'⁻¹ * β := by group
  have hγ1 : β'⁻¹ * β = 1 :=
    CFSG.EvenSmallLie.OddTranspAlt.perm_center_trivial hn3 _ hγ
  calc
    β = β' * (β'⁻¹ * β) := by group
    _ = β' * 1 := by rw [hγ1]
    _ = β' := by group

private noncomputable def w85g_aHom {n : ℕ} (hn3 : 3 ≤ n) (hn6 : n ≠ 6) {Y U : Type} [Group Y]
    [Group U] (e : Y ≃* Perm (Fin n)) (α : U →* MulAut Y) : U →* Perm (Fin n) :=
  { toFun := w85g_aChoice hn6 e α
    map_one' := by
      apply w85g_conj_injective hn3 (β' := 1)
      intro σ
      rw [← w85g_aChoice_spec hn6 e α 1 σ]
      simp [w85g_phi]
    map_mul' := by
      intro u v
      apply w85g_conj_injective hn3
      intro σ
      rw [← w85g_aChoice_spec hn6 e α (u * v) σ]
      calc
        w85g_phi e α (u * v) σ = e (α (u * v) (e.symm σ)) := rfl
        _ = e (α u (α v (e.symm σ))) := by rw [map_mul, MulAut.mul_apply]
        _ = w85g_aChoice hn6 e α u * e (α v (e.symm σ)) *
              (w85g_aChoice hn6 e α u)⁻¹ := by
              rw [show e (α u (α v (e.symm σ))) =
                    w85g_phi e α u (e (α v (e.symm σ))) from by simp [w85g_phi]]
              rw [w85g_aChoice_spec hn6 e α u]
        _ = w85g_aChoice hn6 e α u *
              (w85g_aChoice hn6 e α v * σ * (w85g_aChoice hn6 e α v)⁻¹) *
              (w85g_aChoice hn6 e α u)⁻¹ := by
              rw [show e (α v (e.symm σ)) = w85g_phi e α v σ from by simp [w85g_phi]]
              rw [w85g_aChoice_spec hn6 e α v]
        _ = (w85g_aChoice hn6 e α u * w85g_aChoice hn6 e α v) * σ *
              (w85g_aChoice hn6 e α u * w85g_aChoice hn6 e α v)⁻¹ := by group }

theorem gap5Swap_exists_inner_hom {n : ℕ} (hn3 : 3 ≤ n) (hn6 : n ≠ 6) {Y U : Type} [Group Y]
    [Group U] (e : Y ≃* Perm (Fin n)) (α : U →* MulAut Y) :
    ∃ a : U →* Perm (Fin n), ∀ (u : U) (y : Y), e (α u y) = a u * e y * (a u)⁻¹ := by
  refine ⟨w85g_aHom hn3 hn6 e α, fun u y => ?_⟩
  have h := w85g_aChoice_spec hn6 e α u (e y)
  simpa [w85g_aHom, w85g_phi] using h

theorem gap5Swap_false_of_inner_hom {n : ℕ} (hn : 7 ≤ n) {Y U : Type} [Group Y] [Group U]
    (e : Y ≃* Perm (Fin n)) (α : U →* MulAut Y) (a : U →* Perm (Fin n))
    (ha : ∀ (u : U) (y : Y), e (α u y) = a u * e y * (a u)⁻¹) (hα : Function.Injective α)
    (hU2 : ∀ u : U, u * u = 1) (hU : ∃ u v : U, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v)
    (hS : ∀ u : U, u ≠ 1 → ∀ τ : Y, (e τ).IsSwap → α u τ = τ → ∀ u' : U, α u' τ = τ) :
    False := by
  obtain ⟨u, v, hu, hv, huv_ne⟩ := hU
  have hnn6 : n ≠ 6 := by omega
  let x : Perm (Fin n) := a u
  let y : Perm (Fin n) := a v
  have hx : x * x = 1 := by
    dsimp [x]
    rw [← map_mul, hU2 u, map_one]
  have hy : y * y = 1 := by
    dsimp [y]
    rw [← map_mul, hU2 v, map_one]
  have hxy : x * y = y * x := by
    dsimp [x, y]
    have huv : u * v = v * u := by
      have h2 : u * v = (u * v)⁻¹ := eq_inv_of_mul_eq_one_right (hU2 (u * v))
      rw [h2, mul_inv_rev, inv_eq_of_mul_eq_one_right (hU2 u),
        inv_eq_of_mul_eq_one_right (hU2 v)]
    rw [← map_mul, ← map_mul, huv]
  have hx1 : x ≠ 1 := by
    dsimp [x]
    intro hx1
    have hαu1 : α u = 1 := by
      ext y
      have h := ha u y
      rw [hx1] at h
      simp at h
      exact h
    exact hu (hα (by rw [hαu1, map_one]))
  have hy1 : y ≠ 1 := by
    dsimp [y]
    intro hy1
    have hαv1 : α v = 1 := by
      ext y
      have h := ha v y
      rw [hy1] at h
      simp at h
      exact h
    exact hv (hα (by rw [hαv1, map_one]))
  have hne : x ≠ y := by
    dsimp [x, y]
    intro hxy_eq
    have hαuv : α u = α v := by
      ext y
      have h1 := ha u y
      have h2 := ha v y
      rw [hxy_eq] at h1
      exact e.injective (by rw [h1, h2])
    exact huv_ne (hα hαuv)
  have huv_prod_ne : u * v ≠ 1 := by
    intro h
    have h1 : u⁻¹ = v := inv_eq_of_mul_eq_one_right h
    have h2 : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hU2 u)
    exact huv_ne (by rw [← h2, h1])
  have hdich : ∀ i j : Fin n, i ≠ j →
      (x * swap i j = swap i j * x ∧ y * swap i j = swap i j * y) ∨
      (x * swap i j ≠ swap i j * x ∧ y * swap i j ≠ swap i j * y ∧
        x * y * swap i j ≠ swap i j * (x * y)) := by
    intro i j hij
    let s : Perm (Fin n) := swap i j
    let τ : Y := e.symm s
    have hτ : e τ = s := by simp [τ]
    have hτ_swap : (e τ).IsSwap := by rw [hτ]; exact ⟨i, j, hij, rfl⟩
    have h_comm (w : U) : α w τ = τ ↔ a w * s = s * a w := by
      constructor
      · intro h
        have h1 := ha w τ
        rw [h, hτ] at h1
        have h2 : s * a w = a w * s := by
          conv_lhs => rw [h1]
          group
        exact h2.symm
      · intro h
        have h1 := ha w τ
        rw [hτ] at h1
        apply e.injective
        rw [h1, hτ, h]
        group
    by_cases hx_comm : x * s = s * x
    · by_cases hy_comm : y * s = s * y
      · exact Or.inl ⟨hx_comm, hy_comm⟩
      · exfalso
        have hx_tau : α u τ = τ := (h_comm u).2 hx_comm
        have h_all := hS u hu τ hτ_swap hx_tau
        exact hy_comm ((h_comm v).1 (h_all v))
    · by_cases hy_comm : y * s = s * y
      · exfalso
        have hy_tau : α v τ = τ := (h_comm v).2 hy_comm
        have h_all := hS v hv τ hτ_swap hy_tau
        exact hx_comm ((h_comm u).1 (h_all u))
      · refine Or.inr ⟨hx_comm, hy_comm, ?_⟩
        intro hxy_comm
        have hxy_tau : α (u * v) τ = τ := by
          apply (h_comm (u * v)).2
          rw [map_mul]
          simpa [x, y, s] using hxy_comm
        have h_all := hS (u * v) huv_prod_ne τ hτ_swap hxy_tau
        exact hx_comm ((h_comm u).1 (h_all u))
  have hcard := gap5Perm_card_le_six_of_klein_dichotomy hx hy hxy hx1 hy1 hne hdich
  simp at hcard
  omega

theorem gap5_false_of_swap_dichotomy {n : ℕ} (hn : 7 ≤ n) {Y U : Type} [Group Y] [Group U]
    (e : Y ≃* Perm (Fin n)) (α : U →* MulAut Y) (hα : Function.Injective α)
    (hU2 : ∀ u : U, u * u = 1) (hU : ∃ u v : U, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v)
    (hS : ∀ u : U, u ≠ 1 → ∀ τ : Y, (e τ).IsSwap → α u τ = τ → ∀ u' : U, α u' τ = τ) :
    False := by
  obtain ⟨a, ha⟩ := gap5Swap_exists_inner_hom (by omega) (by omega) e α
  exact gap5Swap_false_of_inner_hom hn e α a ha hα hU2 hU hS

end CFSG.LocalAnalysis.WeakClosure81

end
