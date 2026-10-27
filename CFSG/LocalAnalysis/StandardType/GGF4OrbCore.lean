module

public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreRep
public import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.F4Model

@[expose] def adjB (i j : Fin 4) : List (Fin 4) :=
  if i = 3 ∨ j = 3 then (if i = 1 ∨ j = 1 then [3, 2, 1, 0] else [3, 2]) else []

@[expose] def adjC (i j : Fin 4) : List (Fin 4) :=
  if i = 0 ∨ j = 0 then (if i = 2 ∨ j = 2 then [0, 1, 2, 3] else [0, 1]) else []

theorem adjB_spec : ∀ i j : Fin 4, ¬ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) →
    ∃ i' j' : Fin 4, i' ≠ 3 ∧ j' ≠ 3 ∧ conjW (adjB i j) (Sm i) = Sm i' ∧
      conjW (adjB i j) (Sm j) = Sm j' := by
  decide +kernel

theorem adjC_spec : ∀ i j : Fin 4, ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
    ∃ i' j' : Fin 4, i' ≠ 0 ∧ j' ≠ 0 ∧ conjW (adjC i j) (Sm i) = Sm i' ∧
      conjW (adjC i j) (Sm j) = Sm j' := by
  decide +kernel

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

theorem conj_mem_closure_of_B {a : Fin 3 → W} {g : W}
    (hg : g * a 0 * g⁻¹ = R.s 0 ∧ g * a 1 * g⁻¹ = R.s 1 ∧ g * a 2 * g⁻¹ = R.s 2) {x : W}
    (hx : x ∈ Subgroup.closure ({R.s 0, R.s 1, R.s 2} : Set W)) :
    g⁻¹ * x * g ∈ Subgroup.closure (Set.range a) := by
  have hle : Subgroup.closure ({R.s 0, R.s 1, R.s 2} : Set W) ≤
      conjSub g⁻¹ (Subgroup.closure (Set.range a)) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, mem_conjSub, inv_inv]
    rcases hy with rfl | rfl | rfl
    · rw [← hg.1, show g⁻¹ * (g * a 0 * g⁻¹) * g = a 0 by group]
      exact Subgroup.subset_closure ⟨0, rfl⟩
    · rw [← hg.2.1, show g⁻¹ * (g * a 1 * g⁻¹) * g = a 1 by group]
      exact Subgroup.subset_closure ⟨1, rfl⟩
    · rw [← hg.2.2, show g⁻¹ * (g * a 2 * g⁻¹) * g = a 2 by group]
      exact Subgroup.subset_closure ⟨2, rfl⟩
  have h := hle hx
  rwa [mem_conjSub, inv_inv] at h

theorem conj_mem_closure_of_C {a : Fin 3 → W} {g : W}
    (hg : g * a 0 * g⁻¹ = R.s 3 ∧ g * a 1 * g⁻¹ = R.s 2 ∧ g * a 2 * g⁻¹ = R.s 1) {x : W}
    (hx : x ∈ Subgroup.closure ({R.s 3, R.s 2, R.s 1} : Set W)) :
    g⁻¹ * x * g ∈ Subgroup.closure (Set.range a) := by
  have hle : Subgroup.closure ({R.s 3, R.s 2, R.s 1} : Set W) ≤
      conjSub g⁻¹ (Subgroup.closure (Set.range a)) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, mem_conjSub, inv_inv]
    rcases hy with rfl | rfl | rfl
    · rw [← hg.1, show g⁻¹ * (g * a 0 * g⁻¹) * g = a 0 by group]
      exact Subgroup.subset_closure ⟨0, rfl⟩
    · rw [← hg.2.1, show g⁻¹ * (g * a 1 * g⁻¹) * g = a 1 by group]
      exact Subgroup.subset_closure ⟨1, rfl⟩
    · rw [← hg.2.2, show g⁻¹ * (g * a 2 * g⁻¹) * g = a 2 by group]
      exact Subgroup.subset_closure ⟨2, rfl⟩
  have h := hle hx
  rwa [mem_conjSub, inv_inv] at h

theorem wd_mem_closure_of_ne {l : List (Fin 4)} {k : Fin 4} (hl : ∀ i ∈ l, i ≠ k)
    {S : Set W} (hS : ∀ i, i ≠ k → R.s i ∈ S) : R.wd l ∈ Subgroup.closure S := by
  unfold wd
  apply list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure (hS i (hl i hi))

theorem exists_conj_of_B {a : Fin 3 → W} {g : W}
    (hg : g * a 0 * g⁻¹ = R.s 0 ∧ g * a 1 * g⁻¹ = R.s 1 ∧ g * a 2 * g⁻¹ = R.s 2) {i j : Fin 4}
    (hij : ¬ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2))) :
    ∃ w : W, w * R.s i * w⁻¹ ∈ Subgroup.closure (Set.range a) ∧
      w * R.s j * w⁻¹ ∈ Subgroup.closure (Set.range a) := by
  obtain ⟨i', j', hi', hj', ci, cj⟩ := adjB_spec i j hij
  have hmem : ∀ k : Fin 4, k ≠ 3 → R.s k ∈ Subgroup.closure ({R.s 0, R.s 1, R.s 2} : Set W) := by
    intro k hk
    apply Subgroup.subset_closure
    fin_cases k <;> simp_all
  refine ⟨g⁻¹ * R.wd (adjB i j), ?_, ?_⟩
  · rw [show g⁻¹ * R.wd (adjB i j) * R.s i * (g⁻¹ * R.wd (adjB i j))⁻¹ =
        g⁻¹ * (R.wd (adjB i j) * R.s i * (R.wd (adjB i j))⁻¹) * g by group,
      R.conj_wd_eq (R.hs i) (R.hs i') ci]
    exact R.conj_mem_closure_of_B hg (hmem i' hi')
  · rw [show g⁻¹ * R.wd (adjB i j) * R.s j * (g⁻¹ * R.wd (adjB i j))⁻¹ =
        g⁻¹ * (R.wd (adjB i j) * R.s j * (R.wd (adjB i j))⁻¹) * g by group,
      R.conj_wd_eq (R.hs j) (R.hs j') cj]
    exact R.conj_mem_closure_of_B hg (hmem j' hj')

theorem exists_conj_of_C {a : Fin 3 → W} {g : W}
    (hg : g * a 0 * g⁻¹ = R.s 3 ∧ g * a 1 * g⁻¹ = R.s 2 ∧ g * a 2 * g⁻¹ = R.s 1) {i j : Fin 4}
    (hij : ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))) :
    ∃ w : W, w * R.s i * w⁻¹ ∈ Subgroup.closure (Set.range a) ∧
      w * R.s j * w⁻¹ ∈ Subgroup.closure (Set.range a) := by
  obtain ⟨i', j', hi', hj', ci, cj⟩ := adjC_spec i j hij
  have hmem : ∀ k : Fin 4, k ≠ 0 → R.s k ∈ Subgroup.closure ({R.s 3, R.s 2, R.s 1} : Set W) := by
    intro k hk
    apply Subgroup.subset_closure
    fin_cases k <;> simp_all
  refine ⟨g⁻¹ * R.wd (adjC i j), ?_, ?_⟩
  · rw [show g⁻¹ * R.wd (adjC i j) * R.s i * (g⁻¹ * R.wd (adjC i j))⁻¹ =
        g⁻¹ * (R.wd (adjC i j) * R.s i * (R.wd (adjC i j))⁻¹) * g by group,
      R.conj_wd_eq (R.hs i) (R.hs i') ci]
    exact R.conj_mem_closure_of_C hg (hmem i' hi')
  · rw [show g⁻¹ * R.wd (adjC i j) * R.s j * (g⁻¹ * R.wd (adjC i j))⁻¹ =
        g⁻¹ * (R.wd (adjC i j) * R.s j * (R.wd (adjC i j))⁻¹) * g by group,
      R.conj_wd_eq (R.hs j) (R.hs j') cj]
    exact R.conj_mem_closure_of_C hg (hmem j' hj')

theorem exists_cross_of_B {a b : Fin 3 → W} {g : W}
    (hg : g * a 0 * g⁻¹ = R.s 0 ∧ g * a 1 * g⁻¹ = R.s 1 ∧ g * a 2 * g⁻¹ = R.s 2)
    (hb : ∀ k, R.IsRefl (b k))
    (hgen : Subgroup.closure (Set.range a) ⊔ Subgroup.closure (Set.range b) = ⊤) :
    ∃ w : W, w * R.s 2 * w⁻¹ ∈ Subgroup.closure (Set.range a) ∧
      w * R.s 3 * w⁻¹ ∈ Subgroup.closure (Set.range b) := by
  have hNtop : Subgroup.normalizer (R.ClSet ClB) ≠ ⊤ := by
    intro htop
    have h3 : R.s 3 ∈ Subgroup.normalizer (R.ClSet ClB) := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_set_normalizer_iff] at h3
    obtain ⟨c, hc, hcm⟩ := stdB_mem
    have hs2 : R.s 2 ∈ R.ClSet ClB := (R.mem_ClSet).2 ⟨c, hc, by rw [R.hs 2, hcm]⟩
    obtain ⟨c', hc', hρ⟩ := (R.mem_ClSet).1 ((h3 (R.s 2)).1 hs2)
    rw [R.s_inv 3, R.rho_mul3 (R.hs 3) (R.hs 2) (R.hs 3)] at hρ
    exact stdB_notnorm c' hc' (M4.toMat_injective hρ)
  have hk : ∃ k, g * b k * g⁻¹ ∉ Subgroup.normalizer (R.ClSet ClB) := by
    by_contra! h
    apply hNtop
    rw [eq_top_iff]
    intro z _
    have hle : Subgroup.closure (Set.range a) ⊔ Subgroup.closure (Set.range b) ≤
        conjSub g (Subgroup.normalizer (R.ClSet ClB)) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.closure_le]
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, mem_conjSub]
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 by revert k; decide) with rfl | rfl | rfl
        · rw [hg.1]; exact R.mem_normalizer (R.hs 0) (Sm_sq 0) stdB_norm.1
        · rw [hg.2.1]; exact R.mem_normalizer (R.hs 1) (Sm_sq 1) stdB_norm.2.1
        · rw [hg.2.2]; exact R.mem_normalizer (R.hs 2) (Sm_sq 2) stdB_norm.2.2
      · rw [Subgroup.closure_le]
        rintro _ ⟨k, rfl⟩
        exact h k
    have hz : g⁻¹ * z * g ∈ conjSub g (Subgroup.normalizer (R.ClSet ClB)) :=
      hle (by rw [hgen]; exact Subgroup.mem_top _)
    rwa [mem_conjSub, show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at hz
  obtain ⟨k, hk⟩ := hk
  obtain ⟨y, hy, ρy⟩ := R.refl_rep ((hb k).conj g)
  rcases dichB y hy with hn | ⟨hc, hlet⟩
  · exact absurd (R.mem_normalizer ρy (Rm_sq y hy) hn) hk
  · have heq : R.wd (WB y) * R.s 3 * (R.wd (WB y))⁻¹ = g * b k * g⁻¹ :=
      R.conj_wd_eq (R.hs 3) ρy hc
    have hu : R.wd (WB y) ∈ Subgroup.closure ({R.s 0, R.s 1, R.s 2} : Set W) :=
      R.wd_mem_closure_of_ne hlet (fun i hi => by fin_cases i <;> simp_all)
    refine ⟨g⁻¹ * R.wd (WB y), ?_, ?_⟩
    · rw [show g⁻¹ * R.wd (WB y) * R.s 2 * (g⁻¹ * R.wd (WB y))⁻¹ =
          g⁻¹ * (R.wd (WB y) * R.s 2 * (R.wd (WB y))⁻¹) * g by group]
      exact R.conj_mem_closure_of_B hg
        (mul_mem (mul_mem hu (Subgroup.subset_closure (by simp))) (inv_mem hu))
    · rw [show g⁻¹ * R.wd (WB y) * R.s 3 * (g⁻¹ * R.wd (WB y))⁻¹ =
          g⁻¹ * (R.wd (WB y) * R.s 3 * (R.wd (WB y))⁻¹) * g by group, heq,
        show g⁻¹ * (g * b k * g⁻¹) * g = b k by group]
      exact Subgroup.subset_closure ⟨k, rfl⟩

theorem exists_cross_of_C {a b : Fin 3 → W} {g : W}
    (hg : g * a 0 * g⁻¹ = R.s 3 ∧ g * a 1 * g⁻¹ = R.s 2 ∧ g * a 2 * g⁻¹ = R.s 1)
    (hb : ∀ k, R.IsRefl (b k))
    (hgen : Subgroup.closure (Set.range a) ⊔ Subgroup.closure (Set.range b) = ⊤) :
    ∃ w : W, w * R.s 1 * w⁻¹ ∈ Subgroup.closure (Set.range a) ∧
      w * R.s 0 * w⁻¹ ∈ Subgroup.closure (Set.range b) := by
  have hNtop : Subgroup.normalizer (R.ClSet ClC) ≠ ⊤ := by
    intro htop
    have h0 : R.s 0 ∈ Subgroup.normalizer (R.ClSet ClC) := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_set_normalizer_iff] at h0
    obtain ⟨c, hc, hcm⟩ := stdC_mem
    have hs1 : R.s 1 ∈ R.ClSet ClC := (R.mem_ClSet).2 ⟨c, hc, by rw [R.hs 1, hcm]⟩
    obtain ⟨c', hc', hρ⟩ := (R.mem_ClSet).1 ((h0 (R.s 1)).1 hs1)
    rw [R.s_inv 0, R.rho_mul3 (R.hs 0) (R.hs 1) (R.hs 0)] at hρ
    exact stdC_notnorm c' hc' (M4.toMat_injective hρ)
  have hk : ∃ k, g * b k * g⁻¹ ∉ Subgroup.normalizer (R.ClSet ClC) := by
    by_contra! h
    apply hNtop
    rw [eq_top_iff]
    intro z _
    have hle : Subgroup.closure (Set.range a) ⊔ Subgroup.closure (Set.range b) ≤
        conjSub g (Subgroup.normalizer (R.ClSet ClC)) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.closure_le]
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, mem_conjSub]
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 by revert k; decide) with rfl | rfl | rfl
        · rw [hg.1]; exact R.mem_normalizer (R.hs 3) (Sm_sq 3) stdC_norm.1
        · rw [hg.2.1]; exact R.mem_normalizer (R.hs 2) (Sm_sq 2) stdC_norm.2.1
        · rw [hg.2.2]; exact R.mem_normalizer (R.hs 1) (Sm_sq 1) stdC_norm.2.2
      · rw [Subgroup.closure_le]
        rintro _ ⟨k, rfl⟩
        exact h k
    have hz : g⁻¹ * z * g ∈ conjSub g (Subgroup.normalizer (R.ClSet ClC)) :=
      hle (by rw [hgen]; exact Subgroup.mem_top _)
    rwa [mem_conjSub, show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at hz
  obtain ⟨k, hk⟩ := hk
  obtain ⟨y, hy, ρy⟩ := R.refl_rep ((hb k).conj g)
  rcases dichC y hy with hn | ⟨hc, hlet⟩
  · exact absurd (R.mem_normalizer ρy (Rm_sq y hy) hn) hk
  · have heq : R.wd (WC y) * R.s 0 * (R.wd (WC y))⁻¹ = g * b k * g⁻¹ :=
      R.conj_wd_eq (R.hs 0) ρy hc
    have hu : R.wd (WC y) ∈ Subgroup.closure ({R.s 3, R.s 2, R.s 1} : Set W) :=
      R.wd_mem_closure_of_ne hlet (fun i hi => by fin_cases i <;> simp_all)
    refine ⟨g⁻¹ * R.wd (WC y), ?_, ?_⟩
    · rw [show g⁻¹ * R.wd (WC y) * R.s 1 * (g⁻¹ * R.wd (WC y))⁻¹ =
          g⁻¹ * (R.wd (WC y) * R.s 1 * (R.wd (WC y))⁻¹) * g by group]
      exact R.conj_mem_closure_of_C hg
        (mul_mem (mul_mem hu (Subgroup.subset_closure (by simp))) (inv_mem hu))
    · rw [show g⁻¹ * R.wd (WC y) * R.s 0 * (g⁻¹ * R.wd (WC y))⁻¹ =
          g⁻¹ * (R.wd (WC y) * R.s 0 * (R.wd (WC y))⁻¹) * g by group, heq,
        show g⁻¹ * (g * b k * g⁻¹) * g = b k by group]
      exact Subgroup.subset_closure ⟨k, rfl⟩

theorem orb_core {a b : Fin 3 → W} (ha : ∀ k, R.IsRefl (a k)) (hb : ∀ k, R.IsRefl (b k))
    (ha01 : orderOf (a 0 * a 1) = 3) (ha12 : orderOf (a 1 * a 2) = 4)
    (ha02 : orderOf (a 0 * a 2) = 2) (hb01 : orderOf (b 0 * b 1) = 3)
    (hb12 : orderOf (b 1 * b 2) = 4) (hb02 : orderOf (b 0 * b 2) = 2)
    (hgen : Subgroup.closure (Set.range a) ⊔ Subgroup.closure (Set.range b) = ⊤) (i j : Fin 4) :
    ∃ (w : W) (X Y : Subgroup W),
      (X = Subgroup.closure (Set.range a) ∨ X = Subgroup.closure (Set.range b)) ∧
      (Y = Subgroup.closure (Set.range a) ∨ Y = Subgroup.closure (Set.range b)) ∧
      (X = Y ∨ CoxeterMatrix.F₄ i j = 3) ∧ w * R.s i * w⁻¹ ∈ X ∧ w * R.s j * w⁻¹ ∈ Y := by
  have hgen' : Subgroup.closure (Set.range b) ⊔ Subgroup.closure (Set.range a) = ⊤ := by
    rwa [sup_comm]
  obtain ⟨ga, hga | hga⟩ := R.classify (ha 0) (ha 1) (ha 2) ha01 ha12 ha02 <;>
    obtain ⟨gb, hgb | hgb⟩ := R.classify (hb 0) (hb 1) (hb 2) hb01 hb12 hb02
  ·
    by_cases hij : (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
    · obtain ⟨w, h2, h3⟩ := R.exists_cross_of_B hga hb hgen
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨w, _, _, Or.inl rfl, Or.inr rfl, Or.inr (by decide), h2, h3⟩
      · exact ⟨w, _, _, Or.inr rfl, Or.inl rfl, Or.inr (by decide), h3, h2⟩
    · obtain ⟨w, h1, h2⟩ := R.exists_conj_of_B hga hij
      exact ⟨w, _, _, Or.inl rfl, Or.inl rfl, Or.inl rfl, h1, h2⟩
  ·
    by_cases hij : (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
    · have hij' : ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) := by
        rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      obtain ⟨w, h1, h2⟩ := R.exists_conj_of_C hgb hij'
      exact ⟨w, _, _, Or.inr rfl, Or.inr rfl, Or.inl rfl, h1, h2⟩
    · obtain ⟨w, h1, h2⟩ := R.exists_conj_of_B hga hij
      exact ⟨w, _, _, Or.inl rfl, Or.inl rfl, Or.inl rfl, h1, h2⟩
  ·
    by_cases hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
    · have hij' : ¬ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) := by
        rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      obtain ⟨w, h1, h2⟩ := R.exists_conj_of_B hgb hij'
      exact ⟨w, _, _, Or.inr rfl, Or.inr rfl, Or.inl rfl, h1, h2⟩
    · obtain ⟨w, h1, h2⟩ := R.exists_conj_of_C hga hij
      exact ⟨w, _, _, Or.inl rfl, Or.inl rfl, Or.inl rfl, h1, h2⟩
  ·
    by_cases hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
    · obtain ⟨w, h1, h0⟩ := R.exists_cross_of_C hga hb hgen
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨w, _, _, Or.inr rfl, Or.inl rfl, Or.inr (by decide), h0, h1⟩
      · exact ⟨w, _, _, Or.inl rfl, Or.inr rfl, Or.inr (by decide), h1, h0⟩
    · obtain ⟨w, h1, h2⟩ := R.exists_conj_of_C hga hij
      exact ⟨w, _, _, Or.inl rfl, Or.inl rfl, Or.inl rfl, h1, h2⟩

end F4Rep

end CFSG.StandardType.F4Model
