module

public import CFSG.Timmesfeld.RankTwo.GradedPresentation

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.Timmesfeld.GradedPresentation
open scoped commutatorElement

@[expose] def hexRoot : Fin 6 → Fin 2 → ℤ :=
  ![![0, 1], ![1, 3], ![1, 2], ![2, 3], ![1, 1], ![1, 0]]

@[expose] def hexHt : Fin 6 → ℕ := ![1, 4, 3, 5, 2, 1]

section Complete

variable {ι : Type*} [LinearOrder ι] {F : ι → Type*}

@[expose] def hexCm (w : ∀ i (_ : F i) j (_ : F j), FreeGroup (Σ γ, F γ)) :
    ∀ i (_ : F i) j (_ : F j), FreeGroup (Σ γ, F γ) :=
  fun i s j t => if i < j then w i s j t else if j < i then (w j t i s)⁻¹ else 1

variable [∀ γ, AddCommGroup (F γ)] {w : ∀ i (_ : F i) j (_ : F j), FreeGroup (Σ γ, F γ)}

theorem rels_hexCm_of {H : Type*} [Group H] {φ : (Σ γ, F γ) → H}
    (hadd : ∀ γ (c d : F γ), φ ⟨γ, c + d⟩ = φ ⟨γ, c⟩ * φ ⟨γ, d⟩)
    (hlt : ∀ i j, i < j → ∀ (s : F i) (t : F j),
      ⁅φ ⟨i, s⟩, φ ⟨j, t⟩⁆ = FreeGroup.lift φ (w i s j t)) :
    ∀ r ∈ rels (hexCm w), FreeGroup.lift φ r = 1 := by
  rintro r (⟨γ, c, d, rfl⟩ | ⟨i, s, j, t, rfl⟩)
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, hadd, mul_inv_cancel]
  · rw [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, mul_inv_eq_one, hexCm]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [ite_eq_left h, hlt i j h]
    · rw [ite_eq_right (lt_irrefl i), ite_eq_right (lt_irrefl i), map_one,
        commutatorElement_eq_one_iff_mul_comm, ← hadd, ← hadd, add_comm]
    · rw [ite_eq_right (lt_asymm h), ite_eq_left h, map_inv, ← hlt j i h, commutatorElement_inv]

variable {ht : ι → ℕ}

omit [∀ γ, AddCommGroup (F γ)] in
theorem hexCm_mem_above (hw : ∀ i j, i < j → ∀ (s : F i) (t : F j),
      w i s j t ∈ above ht (max (ht i) (ht j))) :
    ∀ i (s : F i) j (t : F j), hexCm w i s j t ∈ above ht (max (ht i) (ht j)) := by
  intro i s j t
  rw [hexCm]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [ite_eq_left h]
    exact hw i j h s t
  · rw [ite_eq_right (lt_irrefl i), ite_eq_right (lt_irrefl i)]
    exact one_mem _
  · rw [ite_eq_right (lt_asymm h), ite_eq_left h, max_comm]
    exact inv_mem (hw j i h t s)

end Complete

section G2

variable {K : Type*} [CommRing K]

@[expose] def g2WordLt : Fin 6 → K → Fin 6 → K → FreeGroup (Σ _ : Fin 6, K)
  | 0, s, 2, t => .of ⟨1, s * t⟩
  | 2, s, 4, t => .of ⟨3, s * t⟩
  | 1, s, 5, t => .of ⟨3, s * t⟩
  | 0, s, 4, t => .of ⟨1, s ^ 2 * t⟩ * .of ⟨3, s * t ^ 2⟩
  | 0, s, 5, t =>
    .of ⟨1, t * s ^ 3⟩ * .of ⟨2, t * s ^ 2⟩ * .of ⟨3, t ^ 2 * s ^ 3⟩ * .of ⟨4, t * s⟩
  | _, _, _, _ => 1

@[expose] def g2Cm : Fin 6 → K → Fin 6 → K → FreeGroup (Σ _ : Fin 6, K) :=
  hexCm (F := fun _ => K) g2WordLt

theorem rels_g2Cm_of {H : Type*} [Group H] {φ : (Σ _ : Fin 6, K) → H}
    (hadd : ∀ i (c d : K), φ ⟨i, c + d⟩ = φ ⟨i, c⟩ * φ ⟨i, d⟩)
    (h02 : ∀ s t, ⁅φ ⟨0, s⟩, φ ⟨2, t⟩⁆ = φ ⟨1, s * t⟩)
    (h24 : ∀ s t, ⁅φ ⟨2, s⟩, φ ⟨4, t⟩⁆ = φ ⟨3, s * t⟩)
    (h15 : ∀ s t, ⁅φ ⟨1, s⟩, φ ⟨5, t⟩⁆ = φ ⟨3, s * t⟩)
    (h04 : ∀ s t, ⁅φ ⟨0, s⟩, φ ⟨4, t⟩⁆ = φ ⟨1, s ^ 2 * t⟩ * φ ⟨3, s * t ^ 2⟩)
    (h05 : ∀ s t, ⁅φ ⟨0, s⟩, φ ⟨5, t⟩⁆ =
      φ ⟨1, t * s ^ 3⟩ * φ ⟨2, t * s ^ 2⟩ * φ ⟨3, t ^ 2 * s ^ 3⟩ * φ ⟨4, t * s⟩)
    (h01 : ∀ s t, Commute (φ ⟨0, s⟩) (φ ⟨1, t⟩)) (h03 : ∀ s t, Commute (φ ⟨0, s⟩) (φ ⟨3, t⟩))
    (h12 : ∀ s t, Commute (φ ⟨1, s⟩) (φ ⟨2, t⟩)) (h13 : ∀ s t, Commute (φ ⟨1, s⟩) (φ ⟨3, t⟩))
    (h14 : ∀ s t, Commute (φ ⟨1, s⟩) (φ ⟨4, t⟩)) (h23 : ∀ s t, Commute (φ ⟨2, s⟩) (φ ⟨3, t⟩))
    (h25 : ∀ s t, Commute (φ ⟨2, s⟩) (φ ⟨5, t⟩)) (h34 : ∀ s t, Commute (φ ⟨3, s⟩) (φ ⟨4, t⟩))
    (h35 : ∀ s t, Commute (φ ⟨3, s⟩) (φ ⟨5, t⟩)) (h45 : ∀ s t, Commute (φ ⟨4, s⟩) (φ ⟨5, t⟩)) :
    ∀ r ∈ rels (g2Cm (K := K)), FreeGroup.lift φ r = 1 := by
  refine rels_hexCm_of hadd fun i j hij s t => ?_
  have hc : ∀ {a b : H}, Commute a b → ⁅a, b⁆ = FreeGroup.lift φ 1 := fun h => by
    rw [map_one, commutatorElement_eq_one_iff_commute]
    exact h
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact hc (h01 s t) | exact hc (h03 s t) | exact hc (h12 s t) | exact hc (h13 s t)
    | exact hc (h14 s t) | exact hc (h23 s t) | exact hc (h25 s t) | exact hc (h34 s t)
    | exact hc (h35 s t) | exact hc (h45 s t)
    | (rw [h02]; simp [g2WordLt]) | (rw [h24]; simp [g2WordLt]) | (rw [h15]; simp [g2WordLt])
    | (rw [h04]; simp [g2WordLt]) | (rw [h05]; simp [g2WordLt])

theorem g2Cm_mem_above (i : Fin 6) (s : K) (j : Fin 6) (t : K) :
    g2Cm i s j t ∈ above hexHt (max (hexHt i) (hexHt j)) := by
  refine hexCm_mem_above (F := fun _ => K) (fun i j hij s t => ?_) i s j t
  have hg : ∀ (k : Fin 6) (c : K) (m : ℕ), m < hexHt k →
      (FreeGroup.of ⟨k, c⟩ : FreeGroup (Σ _ : Fin 6, K)) ∈ above hexHt m :=
    fun k c m hm => Subgroup.subset_closure ⟨⟨k, c⟩, hm, rfl⟩
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact one_mem _
    | exact hg _ _ _ (by decide)
    | exact mul_mem (hg _ _ _ (by decide)) (hg _ _ _ (by decide))
    | exact mul_mem (mul_mem (mul_mem (hg _ _ _ (by decide)) (hg _ _ _ (by decide)))
        (hg _ _ _ (by decide))) (hg _ _ _ (by decide))

end G2

end CFSG.Timmesfeld.RankTwo
