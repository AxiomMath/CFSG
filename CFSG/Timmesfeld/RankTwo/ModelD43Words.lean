module

public import CFSG.Timmesfeld.RankTwo.ModelG2Words
public import CFSG.LieType.Steinberg.TwistedD4.RankOne

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.Timmesfeld.GradedPresentation CFSG.LieType.Steinberg.TwistedD4
open scoped commutatorElement

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] def d43Par : Fin 6 → Type
  | 0 => K
  | 1 => fixedField σ
  | 2 => K
  | 3 => fixedField σ
  | 4 => K
  | 5 => fixedField σ

instance instAddCommGroupD43Par : ∀ i, AddCommGroup (d43Par σ i)
  | 0 => inferInstanceAs (AddCommGroup K)
  | 1 => inferInstanceAs (AddCommGroup (fixedField σ))
  | 2 => inferInstanceAs (AddCommGroup K)
  | 3 => inferInstanceAs (AddCommGroup (fixedField σ))
  | 4 => inferInstanceAs (AddCommGroup K)
  | 5 => inferInstanceAs (AddCommGroup (fixedField σ))

variable {σ}

theorem mem_fixedField_iff {c : K} : c ∈ fixedField σ ↔ σ c = c :=
  Iff.rfl

@[expose] def d43Tr (hσ : ∀ c, σ (σ (σ c)) = c) (c : K) : fixedField σ :=
  ⟨c + σ c + σ (σ c), by
    rw [mem_fixedField_iff, _root_.map_add, _root_.map_add, hσ]
    ring⟩

@[expose] def d43Norm (hσ : ∀ c, σ (σ (σ c)) = c) (c : K) : fixedField σ :=
  ⟨c * σ c * σ (σ c), by
    rw [mem_fixedField_iff, _root_.map_mul, _root_.map_mul, hσ]
    ring⟩

variable (σ) in
@[expose] def d43Sharp (c : K) : K := σ c * σ (σ c)

variable (σ) in
@[expose] def d43Cross (c d : K) : K := σ c * σ (σ d) + σ (σ c) * σ d

variable (hσ : ∀ c, σ (σ (σ c)) = c)

theorem coe_d43Tr (c : K) : (d43Tr hσ c : K) = c + σ c + σ (σ c) := rfl

theorem coe_d43Norm (c : K) : (d43Norm hσ c : K) = c * σ c * σ (σ c) := rfl

@[expose] def d43W02 (s t : K) : FreeGroup (Σ γ, d43Par σ γ) := .of ⟨1, d43Tr hσ (s * t)⟩

@[expose] def d43W24 (s t : K) : FreeGroup (Σ γ, d43Par σ γ) := .of ⟨3, d43Tr hσ (s * t)⟩

variable (σ) in
@[expose] def d43W15 (s t : fixedField σ) : FreeGroup (Σ γ, d43Par σ γ) :=
  .of ⟨3, (s * t : fixedField σ)⟩

@[expose] def d43W04 (s t : K) : FreeGroup (Σ γ, d43Par σ γ) :=
  .of ⟨1, d43Tr hσ (d43Sharp σ s * t)⟩ * .of ⟨2, (d43Cross σ s t : K)⟩ *
    .of ⟨3, d43Tr hσ (s * d43Sharp σ t)⟩

@[expose] def d43W05 (s : K) (t : fixedField σ) : FreeGroup (Σ γ, d43Par σ γ) :=
  .of ⟨1, (t * d43Norm hσ s : fixedField σ)⟩ * .of ⟨2, ((t : K) * d43Sharp σ s : K)⟩ *
    .of ⟨3, (t ^ 2 * d43Norm hσ s : fixedField σ)⟩ * .of ⟨4, ((t : K) * s : K)⟩

@[expose] def d43WordLt :
    ∀ (i : Fin 6) (_ : d43Par σ i) (j : Fin 6) (_ : d43Par σ j), FreeGroup (Σ γ, d43Par σ γ)
  | 0, s, 2, t => d43W02 hσ s t
  | 2, s, 4, t => d43W24 hσ s t
  | 1, s, 5, t => d43W15 σ s t
  | 0, s, 4, t => d43W04 hσ s t
  | 0, s, 5, t => d43W05 hσ s t
  | _, _, _, _ => 1

@[expose] def d43Cm :
    ∀ (i : Fin 6) (_ : d43Par σ i) (j : Fin 6) (_ : d43Par σ j), FreeGroup (Σ γ, d43Par σ γ) :=
  hexCm (d43WordLt hσ)

theorem d43_add_of {H : Type*} [Group H] {φ : (Σ γ, d43Par σ γ) → H}
    (h0 : ∀ c d : K, φ ⟨0, c + d⟩ = φ ⟨0, c⟩ * φ ⟨0, d⟩)
    (h1 : ∀ c d : fixedField σ, φ ⟨1, c + d⟩ = φ ⟨1, c⟩ * φ ⟨1, d⟩)
    (h2 : ∀ c d : K, φ ⟨2, c + d⟩ = φ ⟨2, c⟩ * φ ⟨2, d⟩)
    (h3 : ∀ c d : fixedField σ, φ ⟨3, c + d⟩ = φ ⟨3, c⟩ * φ ⟨3, d⟩)
    (h4 : ∀ c d : K, φ ⟨4, c + d⟩ = φ ⟨4, c⟩ * φ ⟨4, d⟩)
    (h5 : ∀ c d : fixedField σ, φ ⟨5, c + d⟩ = φ ⟨5, c⟩ * φ ⟨5, d⟩) :
    ∀ i (c d : d43Par σ i), φ ⟨i, c + d⟩ = φ ⟨i, c⟩ * φ ⟨i, d⟩ := by
  intro i c d
  fin_cases i
  exacts [h0 c d, h1 c d, h2 c d, h3 c d, h4 c d, h5 c d]

theorem rels_d43Cm_of {H : Type*} [Group H] {φ : (Σ γ, d43Par σ γ) → H}
    (hadd : ∀ i (c d : d43Par σ i), φ ⟨i, c + d⟩ = φ ⟨i, c⟩ * φ ⟨i, d⟩)
    (h02 : ∀ s t : K, ⁅φ ⟨0, s⟩, φ ⟨2, t⟩⁆ = φ ⟨1, d43Tr hσ (s * t)⟩)
    (h24 : ∀ s t : K, ⁅φ ⟨2, s⟩, φ ⟨4, t⟩⁆ = φ ⟨3, d43Tr hσ (s * t)⟩)
    (h15 : ∀ s t : fixedField σ, ⁅φ ⟨1, s⟩, φ ⟨5, t⟩⁆ = φ ⟨3, (s * t : fixedField σ)⟩)
    (h04 : ∀ s t : K, ⁅φ ⟨0, s⟩, φ ⟨4, t⟩⁆ = φ ⟨1, d43Tr hσ (d43Sharp σ s * t)⟩ *
      φ ⟨2, (d43Cross σ s t : K)⟩ * φ ⟨3, d43Tr hσ (s * d43Sharp σ t)⟩)
    (h05 : ∀ (s : K) (t : fixedField σ), ⁅φ ⟨0, s⟩, φ ⟨5, t⟩⁆ =
      φ ⟨1, (t * d43Norm hσ s : fixedField σ)⟩ * φ ⟨2, ((t : K) * d43Sharp σ s : K)⟩ *
        φ ⟨3, (t ^ 2 * d43Norm hσ s : fixedField σ)⟩ * φ ⟨4, ((t : K) * s : K)⟩)
    (h01 : ∀ (s : K) (t : fixedField σ), Commute (φ ⟨0, s⟩) (φ ⟨1, t⟩))
    (h03 : ∀ (s : K) (t : fixedField σ), Commute (φ ⟨0, s⟩) (φ ⟨3, t⟩))
    (h12 : ∀ (s : fixedField σ) (t : K), Commute (φ ⟨1, s⟩) (φ ⟨2, t⟩))
    (h13 : ∀ s t : fixedField σ, Commute (φ ⟨1, s⟩) (φ ⟨3, t⟩))
    (h14 : ∀ (s : fixedField σ) (t : K), Commute (φ ⟨1, s⟩) (φ ⟨4, t⟩))
    (h23 : ∀ (s : K) (t : fixedField σ), Commute (φ ⟨2, s⟩) (φ ⟨3, t⟩))
    (h25 : ∀ (s : K) (t : fixedField σ), Commute (φ ⟨2, s⟩) (φ ⟨5, t⟩))
    (h34 : ∀ (s : fixedField σ) (t : K), Commute (φ ⟨3, s⟩) (φ ⟨4, t⟩))
    (h35 : ∀ s t : fixedField σ, Commute (φ ⟨3, s⟩) (φ ⟨5, t⟩))
    (h45 : ∀ (s : K) (t : fixedField σ), Commute (φ ⟨4, s⟩) (φ ⟨5, t⟩)) :
    ∀ r ∈ rels (d43Cm hσ), FreeGroup.lift φ r = 1 := by
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
    | exact (h02 s t).trans (by simp [d43WordLt, d43W02])
    | exact (h24 s t).trans (by simp [d43WordLt, d43W24])
    | exact (h15 s t).trans (by simp [d43WordLt, d43W15])
    | exact (h04 s t).trans (by simp [d43WordLt, d43W04])
    | exact (h05 s t).trans (by simp [d43WordLt, d43W05])

theorem d43Cm_mem_above (i : Fin 6) (s : d43Par σ i) (j : Fin 6) (t : d43Par σ j) :
    d43Cm hσ i s j t ∈ above hexHt (max (hexHt i) (hexHt j)) := by
  refine hexCm_mem_above (fun i j hij s t => ?_) i s j t
  have hg : ∀ (k : Fin 6) (c : d43Par σ k) (m : ℕ), m < hexHt k →
      (FreeGroup.of ⟨k, c⟩ : FreeGroup (Σ γ, d43Par σ γ)) ∈ above hexHt m :=
    fun k c m hm => Subgroup.subset_closure ⟨⟨k, c⟩, hm, rfl⟩
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact one_mem _
    | exact hg _ _ _ (by decide)
    | exact mul_mem (mul_mem (hg _ _ _ (by decide)) (hg _ _ _ (by decide))) (hg _ _ _ (by decide))
    | exact mul_mem (mul_mem (mul_mem (hg _ _ _ (by decide)) (hg _ _ _ (by decide)))
        (hg _ _ _ (by decide))) (hg _ _ _ (by decide))

end CFSG.Timmesfeld.RankTwo
