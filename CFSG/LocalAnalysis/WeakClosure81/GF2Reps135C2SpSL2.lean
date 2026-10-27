module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups Matrix

variable {K : Type} [Field K] {n : ℕ}

private def spKey : Fin n ⊕ Fin n → ℕ
  | .inl i => i
  | .inr i => 2 * n - 1 - i

private theorem spKey_injective : Function.Injective (spKey (n := n)) := by
  intro a b h
  rcases a with i | i <;> rcases b with j | j
  · exact congrArg Sum.inl (Fin.ext (by simpa [spKey] using h))
  · exfalso; simp only [spKey] at h; omega
  · exfalso; simp only [spKey] at h; omega
  · exact congrArg Sum.inr (Fin.ext (by simp only [spKey] at h; omega))

private theorem spKey_swap_lt_swap (γ δ : Fin n ⊕ Fin n) :
    spKey (γ.swap) < spKey (δ.swap) ↔ spKey δ < spKey γ := by
  rcases γ with i | i <;> rcases δ with j | j <;>
    simp only [Sum.swap_inl, Sum.swap_inr, spKey] <;> omega

private abbrev first (σ : Equiv.Perm (Fin n ⊕ Fin n)) (α : Fin n ⊕ Fin n) : Prop :=
  spKey α < spKey (σ α)

private theorem sigma_apply_apply {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1)
    (α : Fin n ⊕ Fin n) : σ (σ α) = α := by
  have h := congrFun (congrArg (fun e : Equiv.Perm (Fin n ⊕ Fin n) => (e : _ → _)) hσ) α
  simpa [Equiv.Perm.mul_apply] using h

private theorem not_first_and_first {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1)
    (α : Fin n ⊕ Fin n) : ¬ (first σ α ∧ first σ (σ α)) := by
  rw [first, first, sigma_apply_apply hσ α]
  exact fun h => lt_asymm h.1 h.2

private theorem first_ne_self {σ : Equiv.Perm (Fin n ⊕ Fin n)}
    {α : Fin n ⊕ Fin n} (h : first σ α) : σ α ≠ α := by
  intro hfix
  rw [first, hfix] at h
  exact lt_irrefl _ h

private theorem first_apply_ne_self {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1)
    {α : Fin n ⊕ Fin n} (h : first σ (σ α)) : σ α ≠ α := by
  intro hfix
  rw [first, sigma_apply_apply hσ α] at h
  exact lt_irrefl _ (hfix ▸ h)

private theorem eq_or_first_or_first {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1)
    (α : Fin n ⊕ Fin n) : σ α = α ∨ first σ α ∨ first σ (σ α) := by
  by_cases h : σ α = α
  · exact Or.inl h
  · have hne : spKey α ≠ spKey (σ α) := fun e => h (spKey_injective e).symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inr (Or.inl hlt)
    · exact Or.inr (Or.inr (by rw [first, sigma_apply_apply hσ α]; exact hgt))

private theorem first_or_first_or_fixed {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1)
    (α : Fin n ⊕ Fin n) : (first σ α ∨ first σ (σ α)) ∨ σ α = α := by
  rcases eq_or_first_or_first hσ α with h | h | h
  · exact Or.inr h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)

private theorem first_swap_iff {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1)
    (hτ : ∀ x, σ x.swap = (σ x).swap) (α : Fin n ⊕ Fin n) :
    first σ (α.swap) ↔ first σ (σ α) := by
  rw [first, hτ α, first, sigma_apply_apply hσ α]
  exact spKey_swap_lt_swap α (σ α)

private theorem first_sigma_swap_iff {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1)
    (hτ : ∀ x, σ x.swap = (σ x).swap) (α : Fin n ⊕ Fin n) :
    first σ ((σ α).swap) ↔ first σ α := by
  rw [first_swap_iff hσ hτ (σ α), sigma_apply_apply hσ α]

private theorem swap_eq_swap_iff {x y : Fin n ⊕ Fin n} : x.swap = y.swap ↔ x = y :=
  ⟨fun h => by simpa using congrArg Sum.swap h, fun h => by rw [h]⟩

private def sp (K : Type) [Semiring K] {ι : Type} [DecidableEq ι]
    (f : ι → ι) (p : ι → Prop) [DecidablePred p] : Matrix ι ι K :=
  Matrix.of fun β α => if β = f α ∧ p α then (1 : K) else 0

private theorem sp_apply {ι : Type} [DecidableEq ι] (K : Type) [Semiring K]
    (f : ι → ι) (p : ι → Prop) [DecidablePred p] (β α : ι) :
    sp K f p β α = if β = f α ∧ p α then (1 : K) else 0 := rfl

private theorem sp_mul {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Semiring K]
    (f g : ι → ι) (p q : ι → Prop) [DecidablePred p] [DecidablePred q] :
    sp K f p * sp K g q = sp K (f ∘ g) (fun α => q α ∧ p (g α)) := by
  ext β α
  rw [Matrix.mul_apply]
  calc ∑ b, sp K f p β b * sp K g q b α
      = sp K f p β (g α) * sp K g q (g α) α := by
        refine Fintype.sum_eq_single (g α) ?_
        intro b hb
        have hb' : ¬ (b = g α ∧ q α) := fun hc => hb hc.1
        rw [sp_apply, sp_apply, if_neg hb', mul_zero]
    _ = sp K (f ∘ g) (fun α => q α ∧ p (g α)) β α := by
        rw [sp_apply, sp_apply, sp_apply]
        by_cases hq : q α <;> by_cases hp : p (g α) <;>
          simp [hq, hp, Function.comp_apply]

private theorem sp_transpose_id {ι : Type} [DecidableEq ι] (K : Type) [Semiring K]
    {p : ι → Prop} [DecidablePred p] : (sp K id p)ᵀ = sp K id p := by
  ext β α
  rw [Matrix.transpose_apply, sp_apply, sp_apply]
  by_cases h : β = α
  · rw [h]
  · have h' : α ≠ β := fun e => h e.symm
    rw [if_neg (fun hc => h' hc.1), if_neg (fun hc => h hc.1)]

private theorem sp_transpose_sigma {ι : Type} [DecidableEq ι] (K : Type) [Semiring K]
    {σ : ι → ι} (hσ : ∀ α, σ (σ α) = α) {p : ι → Prop} [DecidablePred p] :
    (sp K σ p)ᵀ = sp K σ (fun α => p (σ α)) := by
  ext β α
  rw [Matrix.transpose_apply, sp_apply, sp_apply]
  by_cases h : β = σ α
  · rw [h, hσ α]
    simp
  · have h' : α ≠ σ β := by
      intro hc
      exact h (by rw [hc]; exact (hσ β).symm)
    rw [if_neg (fun hc => h' hc.1), if_neg (fun hc => h hc.1)]

private theorem sp_zero {ι : Type} [DecidableEq ι] (K : Type) [Semiring K]
    {f : ι → ι} {p : ι → Prop} [DecidablePred p] (h : ∀ α, ¬ p α) : sp K f p = 0 := by
  ext β α
  rw [sp_apply, Matrix.zero_apply]
  exact if_neg (fun hc => h α hc.2)

private theorem sp_one {ι : Type} [DecidableEq ι] (K : Type) [Semiring K]
    {f : ι → ι} (h : ∀ α, f α = α) : sp K f (fun _ => True) = 1 := by
  ext β α
  rw [sp_apply, Matrix.one_apply]
  by_cases hβα : β = α
  · rw [if_pos ⟨hβα.trans (h α).symm, trivial⟩, if_pos hβα]
  · rw [if_neg (fun hc => hβα (hc.1.trans (h α))), if_neg hβα]

private theorem sp_add {ι : Type} [DecidableEq ι] (K : Type) [Semiring K]
    {f : ι → ι} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ α, ¬ (p α ∧ q α)) :
    sp K f p + sp K f q = sp K f (fun α => p α ∨ q α) := by
  ext β α
  simp only [Matrix.add_apply, sp_apply]
  by_cases hbf : β = f α
  · subst hbf
    by_cases hp : p α <;> by_cases hq : q α
    · exact absurd ⟨hp, hq⟩ (h α)
    · simp [hp, hq]
    · simp [hp, hq]
    · simp [hp, hq]
  · by_cases hp : p α <;> by_cases hq : q α <;> simp [hbf, hp, hq]

private theorem sp_congr {ι : Type} [DecidableEq ι] (K : Type) [Semiring K]
    {f f' : ι → ι} {p p' : ι → Prop} [DecidablePred p] [DecidablePred p']
    (hf : ∀ α, f α = f' α) (h : ∀ α, p α ↔ p' α) : sp K f p = sp K f' p' := by
  ext β α
  rw [sp_apply, sp_apply, hf α]
  by_cases hβ : β = f' α
  · by_cases hp : p α
    · rw [if_pos ⟨hβ, hp⟩, if_pos ⟨hβ, (h α).1 hp⟩]
    · have hp' : ¬ p' α := fun h' => hp ((h α).2 h')
      rw [if_neg (fun hc => hp hc.2), if_neg (fun hc => hp' hc.2)]
  · rw [if_neg (fun hc => hβ hc.1), if_neg (fun hc => hβ hc.1)]

private theorem sp_congr_of {ι : Type} [DecidableEq ι] (K : Type) [Semiring K]
    {f f' : ι → ι} {p p' : ι → Prop} [DecidablePred p] [DecidablePred p']
    (hf : ∀ α, p α → f α = f' α) (h : ∀ α, p α ↔ p' α) : sp K f p = sp K f' p' := by
  ext β α
  rw [sp_apply, sp_apply]
  by_cases hp : p α
  · have hfα := hf α hp
    have hp' : p' α := (h α).1 hp
    by_cases hβ : β = f α
    · rw [if_pos ⟨hβ, hp⟩, if_pos ⟨by rw [← hfα]; exact hβ, hp'⟩]
    · rw [if_neg (fun hc => hβ hc.1),
        if_neg (fun hc => hβ (by rw [hfα]; exact hc.1))]
  · have hp' : ¬ p' α := fun h' => hp ((h α).2 h')
    rw [if_neg (fun hc => hp hc.2), if_neg (fun hc => hp' hc.2)]

private theorem gram_eq_sp [CharP K 2] : gram K n = sp K Sum.swap (fun _ => True) := by
  ext β α
  rw [sp_apply, gram_apply]
  by_cases h : β = Sum.swap α
  · have h' : α = par β := by
      rw [show par β = Sum.swap β from rfl, h, Sum.swap_swap]
    rw [if_pos h', if_pos ⟨h, trivial⟩]
    cases β <;> simp [sgn, CharTwo.neg_eq]
  · have h' : ¬ (α = par β) := by
      intro hc
      rw [show par β = Sum.swap β from rfl] at hc
      exact h (by rw [hc, Sum.swap_swap])
    rw [if_neg h', if_neg (fun hc => h hc.1)]

private def E11 (σ : Equiv.Perm (Fin n ⊕ Fin n)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  sp K id (first σ)

private def E12 (σ : Equiv.Perm (Fin n ⊕ Fin n)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  sp K σ (fun α => first σ (σ α))

private def E21 (σ : Equiv.Perm (Fin n ⊕ Fin n)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  sp K σ (first σ)

private def E22 (σ : Equiv.Perm (Fin n ⊕ Fin n)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  sp K id (fun α => first σ (σ α))

private def R (σ : Equiv.Perm (Fin n ⊕ Fin n)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  sp K id (fun α => σ α = α)

private theorem E11_transpose {σ : Equiv.Perm (Fin n ⊕ Fin n)} :
    (E11 (K := K) σ)ᵀ = E11 (K := K) σ := by
  rw [E11, sp_transpose_id]

private theorem E22_transpose {σ : Equiv.Perm (Fin n ⊕ Fin n)} :
    (E22 (K := K) σ)ᵀ = E22 (K := K) σ := by
  rw [E22, sp_transpose_id]

private theorem R_transpose {σ : Equiv.Perm (Fin n ⊕ Fin n)} : (R (K := K) σ)ᵀ = R (K := K) σ := by
  rw [R, sp_transpose_id]

private theorem E12_transpose {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    (E12 (K := K) σ)ᵀ = E21 (K := K) σ := by
  rw [E12, E21, sp_transpose_sigma K (sigma_apply_apply hσ)]
  apply sp_congr <;> intro α <;> simp [sigma_apply_apply hσ α]

private theorem E21_transpose {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    (E21 (K := K) σ)ᵀ = E12 (K := K) σ := by
  rw [E21, E12, sp_transpose_sigma K (sigma_apply_apply hσ)]

private theorem E11_mul_E11 {σ : Equiv.Perm (Fin n ⊕ Fin n)} :
    E11 (K := K) σ * E11 (K := K) σ = E11 (K := K) σ := by
  rw [E11, sp_mul]
  apply sp_congr <;> intro α <;> simp [Function.comp_apply]

private theorem E11_mul_E12 {σ : Equiv.Perm (Fin n ⊕ Fin n)} :
    E11 (K := K) σ * E12 (K := K) σ = E12 (K := K) σ := by
  rw [E11, E12, sp_mul]
  apply sp_congr <;> intro α <;> simp [Function.comp_apply]

private theorem E12_mul_E21 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E12 (K := K) σ * E21 (K := K) σ = E11 (K := K) σ := by
  rw [E12, E21, E11, sp_mul]
  apply sp_congr <;> intro α <;> simp [Function.comp_apply, sigma_apply_apply hσ α]

private theorem E12_mul_E22 {σ : Equiv.Perm (Fin n ⊕ Fin n)} :
    E12 (K := K) σ * E22 (K := K) σ = E12 (K := K) σ := by
  rw [E12, E22, sp_mul]
  apply sp_congr <;> intro α <;> simp [Function.comp_apply]

private theorem E21_mul_E11 {σ : Equiv.Perm (Fin n ⊕ Fin n)} :
    E21 (K := K) σ * E11 (K := K) σ = E21 (K := K) σ := by
  rw [E21, E11, sp_mul]
  apply sp_congr <;> intro α <;> simp [Function.comp_apply]

private theorem E21_mul_E12 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E21 (K := K) σ * E12 (K := K) σ = E22 (K := K) σ := by
  rw [E21, E12, E22, sp_mul]
  apply sp_congr <;> intro α <;> simp [Function.comp_apply, sigma_apply_apply hσ α]

private theorem E22_mul_E21 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E22 (K := K) σ * E21 (K := K) σ = E21 (K := K) σ := by
  rw [E22, E21, sp_mul]
  apply sp_congr <;> intro α <;> simp [Function.comp_apply, sigma_apply_apply hσ α]

private theorem E22_mul_E22 {σ : Equiv.Perm (Fin n ⊕ Fin n)} :
    E22 (K := K) σ * E22 (K := K) σ = E22 (K := K) σ := by
  rw [E22, sp_mul]
  apply sp_congr <;> intro α <;> simp [Function.comp_apply]

private theorem R_mul_R {σ : Equiv.Perm (Fin n ⊕ Fin n)} :
    R (K := K) σ * R (K := K) σ = R (K := K) σ := by
  rw [R, sp_mul]
  apply sp_congr <;> intro α <;> simp

private theorem E11_mul_E21 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E11 (K := K) σ * E21 (K := K) σ = 0 := by
  rw [E11, E21, sp_mul]
  exact sp_zero K (fun α h => not_first_and_first hσ α h)

private theorem E11_mul_E22 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E11 (K := K) σ * E22 (K := K) σ = 0 := by
  rw [E11, E22, sp_mul]
  exact sp_zero K (fun α h => not_first_and_first hσ α ⟨h.2, h.1⟩)

private theorem E11_mul_R {σ : Equiv.Perm (Fin n ⊕ Fin n)} :
    E11 (K := K) σ * R (K := K) σ = 0 := by
  rw [E11, R, sp_mul]
  exact sp_zero K (fun α h => first_ne_self h.2 h.1)

private theorem E12_mul_E11 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E12 (K := K) σ * E11 (K := K) σ = 0 := by
  rw [E12, E11, sp_mul]
  exact sp_zero K (fun α h => not_first_and_first hσ α h)

private theorem E12_mul_E12 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E12 (K := K) σ * E12 (K := K) σ = 0 := by
  rw [E12, sp_mul]
  exact sp_zero K (fun α h => by
    have h2 : first σ α := by simpa [sigma_apply_apply hσ α] using h.2
    exact not_first_and_first hσ α ⟨h2, h.1⟩)

private theorem E12_mul_R {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E12 (K := K) σ * R (K := K) σ = 0 := by
  rw [E12, R, sp_mul]
  exact sp_zero K (fun α h => first_apply_ne_self hσ h.2 h.1)

private theorem E21_mul_E21 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E21 (K := K) σ * E21 (K := K) σ = 0 := by
  rw [E21, sp_mul]
  exact sp_zero K (fun α h => not_first_and_first hσ α h)

private theorem E21_mul_E22 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E21 (K := K) σ * E22 (K := K) σ = 0 := by
  rw [E21, E22, sp_mul]
  exact sp_zero K (fun α h => not_first_and_first hσ α ⟨h.2, h.1⟩)

private theorem E21_mul_R {σ : Equiv.Perm (Fin n ⊕ Fin n)} :
    E21 (K := K) σ * R (K := K) σ = 0 := by
  rw [E21, R, sp_mul]
  exact sp_zero K (fun α h => first_ne_self h.2 h.1)

private theorem E22_mul_E11 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E22 (K := K) σ * E11 (K := K) σ = 0 := by
  rw [E22, E11, sp_mul]
  exact sp_zero K (fun α h => not_first_and_first hσ α h)

private theorem E22_mul_E12 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E22 (K := K) σ * E12 (K := K) σ = 0 := by
  rw [E22, E12, sp_mul]
  exact sp_zero K (fun α h => by
    have h2 : first σ α := by simpa [sigma_apply_apply hσ α] using h.2
    exact not_first_and_first hσ α ⟨h2, h.1⟩)

private theorem E22_mul_R {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E22 (K := K) σ * R (K := K) σ = 0 := by
  rw [E22, R, sp_mul]
  exact sp_zero K (fun α h => first_apply_ne_self hσ h.2 h.1)

private theorem R_mul_E11 {σ : Equiv.Perm (Fin n ⊕ Fin n)} :
    R (K := K) σ * E11 (K := K) σ = 0 := by
  rw [R, E11, sp_mul]
  exact sp_zero K (fun α h => first_ne_self h.1 h.2)

private theorem R_mul_E12 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    R (K := K) σ * E12 (K := K) σ = 0 := by
  rw [R, E12, sp_mul]
  exact sp_zero K (fun α h => by
    have h2 : α = σ α := by simpa [sigma_apply_apply hσ α] using h.2
    exact first_apply_ne_self hσ h.1 h2.symm)

private theorem R_mul_E21 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    R (K := K) σ * E21 (K := K) σ = 0 := by
  rw [R, E21, sp_mul]
  exact sp_zero K (fun α h => by
    have h2 : α = σ α := by simpa [sigma_apply_apply hσ α] using h.2
    exact first_ne_self h.1 h2.symm)

private theorem R_mul_E22 {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    R (K := K) σ * E22 (K := K) σ = 0 := by
  rw [R, E22, sp_mul]
  exact sp_zero K (fun α h => first_apply_ne_self hσ h.1 h.2)

private theorem E11_add_E22_add_R {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E11 (K := K) σ + E22 (K := K) σ + R (K := K) σ = 1 := by
  rw [E11, E22, R]
  rw [sp_add K (fun α h => not_first_and_first hσ α h)]
  rw [sp_add K (fun α h => by
    rcases h.1 with h1 | h1
    · exact first_ne_self h1 h.2
    · exact first_apply_ne_self hσ h1 h.2)]
  rw [show sp K id (fun α => (first σ α ∨ first σ (σ α)) ∨ σ α = α) =
      sp K id (fun _ => True) from
    sp_congr K (fun α => rfl) (fun α => by
      constructor
      · intro _; trivial
      · intro _; exact first_or_first_or_fixed hσ α)]
  exact sp_one K (fun α => rfl)

private def spPhi (σ : Equiv.Perm (Fin n ⊕ Fin n)) (g : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  g 0 0 • E11 (K := K) σ + g 0 1 • E12 (K := K) σ + g 1 0 • E21 (K := K) σ +
    g 1 1 • E22 (K := K) σ + R (K := K) σ

private theorem spPhi_one {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    spPhi (K := K) σ 1 = 1 := by
  rw [spPhi]
  have h00 : (1 : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by simp
  have h01 : (1 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by simp
  have h10 : (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simp
  have h11 : (1 : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by simp
  rw [h00, h01, h10, h11]
  simp only [one_smul, zero_smul, add_zero]
  exact E11_add_E22_add_R hσ

private theorem spPhi_mul {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1)
    (g h : Matrix (Fin 2) (Fin 2) K) :
    spPhi (K := K) σ (g * h) = spPhi (K := K) σ g * spPhi (K := K) σ h := by
  simp only [spPhi]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    E11_mul_E11, E11_mul_E12, E12_mul_E21 hσ, E12_mul_E22, E21_mul_E11, E21_mul_E12 hσ,
    E22_mul_E21 hσ, E22_mul_E22, R_mul_R,
    E11_mul_E21 hσ, E11_mul_E22 hσ, E11_mul_R, E12_mul_E11 hσ, E12_mul_E12 hσ,
    E12_mul_R hσ, E21_mul_E21 hσ, E21_mul_E22 hσ, E21_mul_R, E22_mul_E11 hσ,
    E22_mul_E12 hσ, E22_mul_R hσ, R_mul_E11, R_mul_E12 hσ, R_mul_E21 hσ, R_mul_E22 hσ,
    smul_zero, add_zero, zero_add]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  module

private def partnerMat (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  !![g 1 1, g 0 1; g 1 0, g 0 0]

omit [Field K] in
@[simp] private theorem partnerMat_00 (g : Matrix (Fin 2) (Fin 2) K) :
    partnerMat g 0 0 = g 1 1 := by simp [partnerMat]

omit [Field K] in
@[simp] private theorem partnerMat_01 (g : Matrix (Fin 2) (Fin 2) K) :
    partnerMat g 0 1 = g 0 1 := by simp [partnerMat]

omit [Field K] in
@[simp] private theorem partnerMat_10 (g : Matrix (Fin 2) (Fin 2) K) :
    partnerMat g 1 0 = g 1 0 := by simp [partnerMat]

omit [Field K] in
@[simp] private theorem partnerMat_11 (g : Matrix (Fin 2) (Fin 2) K) :
    partnerMat g 1 1 = g 0 0 := by simp [partnerMat]

private theorem partner_mul_self [CharP K 2] (g : Matrix (Fin 2) (Fin 2) K) :
    partnerMat g * g = g.det • 1 := by
  have h : partnerMat g = g.adjugate := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [partnerMat, Matrix.adjugate_fin_two, CharTwo.neg_eq]
  rw [h, Matrix.adjugate_mul]

private theorem E11_transpose_mul_gram {σ : Equiv.Perm (Fin n ⊕ Fin n)} [CharP K 2] (hσ : σ * σ = 1)
    (hτ : ∀ x, σ x.swap = (σ x).swap) :
    (E11 (K := K) σ)ᵀ * gram K n = gram K n * E22 (K := K) σ := by
  rw [E11_transpose, E11, E22, gram_eq_sp, sp_mul, sp_mul]
  apply sp_congr
  · intro α; rfl
  · intro α; simpa using first_swap_iff hσ hτ α

private theorem E22_transpose_mul_gram {σ : Equiv.Perm (Fin n ⊕ Fin n)} [CharP K 2] (hσ : σ * σ = 1)
    (hτ : ∀ x, σ x.swap = (σ x).swap) :
    (E22 (K := K) σ)ᵀ * gram K n = gram K n * E11 (K := K) σ := by
  rw [E22_transpose, E22, E11, gram_eq_sp, sp_mul, sp_mul]
  apply sp_congr
  · intro α; rfl
  · intro α
    simp only [true_and, and_true, hτ α]
    exact first_sigma_swap_iff hσ hτ α

private theorem E12_transpose_mul_gram {σ : Equiv.Perm (Fin n ⊕ Fin n)} [CharP K 2] (hσ : σ * σ = 1)
    (hτ : ∀ x, σ x.swap = (σ x).swap) :
    (E12 (K := K) σ)ᵀ * gram K n = gram K n * E12 (K := K) σ := by
  rw [E12_transpose hσ, E12, E21, gram_eq_sp, sp_mul, sp_mul]
  apply sp_congr
  · intro α; exact hτ α
  · intro α; simpa [Function.comp_apply] using first_swap_iff hσ hτ α

private theorem E21_transpose_mul_gram {σ : Equiv.Perm (Fin n ⊕ Fin n)} [CharP K 2] (hσ : σ * σ = 1)
    (hτ : ∀ x, σ x.swap = (σ x).swap) :
    (E21 (K := K) σ)ᵀ * gram K n = gram K n * E21 (K := K) σ := by
  rw [E21_transpose hσ, E21, E12, gram_eq_sp, sp_mul, sp_mul]
  apply sp_congr
  · intro α; exact hτ α
  · intro α
    simp only [true_and, and_true, hτ α]
    exact first_sigma_swap_iff hσ hτ α

private theorem R_transpose_mul_gram {σ : Equiv.Perm (Fin n ⊕ Fin n)} [CharP K 2]
    (hτ : ∀ x, σ x.swap = (σ x).swap) :
    (R (K := K) σ)ᵀ * gram K n = gram K n * R (K := K) σ := by
  rw [R_transpose, R, gram_eq_sp, sp_mul, sp_mul]
  apply sp_congr
  · intro α; rfl
  · intro α
    simp only [true_and, and_true, hτ α]
    exact swap_eq_swap_iff

private theorem spPhi_transpose_mul_gram {σ : Equiv.Perm (Fin n ⊕ Fin n)} [CharP K 2]
    (hσ : σ * σ = 1)
    (hτ : ∀ x, σ x.swap = (σ x).swap) (g : Matrix (Fin 2) (Fin 2) K) :
    (spPhi (K := K) σ g)ᵀ * gram K n = gram K n * spPhi (K := K) σ (partnerMat g) := by
  simp only [spPhi]
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.smul_mul,
    E11_transpose_mul_gram hσ hτ, E12_transpose_mul_gram hσ hτ,
    E21_transpose_mul_gram hσ hτ, E22_transpose_mul_gram hσ hτ, R_transpose_mul_gram hτ]
  simp only [Matrix.mul_add, Matrix.mul_smul, partnerMat_00, partnerMat_01, partnerMat_10,
    partnerMat_11]
  module

private theorem spPhi_symplectic {σ : Equiv.Perm (Fin n ⊕ Fin n)} [CharP K 2] (hσ : σ * σ = 1)
    (hτ : ∀ x, σ x.swap = (σ x).swap) {g : Matrix (Fin 2) (Fin 2) K} (hg : g.det = 1) :
    (spPhi (K := K) σ g)ᵀ * gram K n * spPhi (K := K) σ g = gram K n := by
  rw [spPhi_transpose_mul_gram hσ hτ g, Matrix.mul_assoc, ← spPhi_mul hσ, partner_mul_self,
    hg, one_smul, spPhi_one hσ, Matrix.mul_one]

private noncomputable def spHom {σ : Equiv.Perm (Fin n ⊕ Fin n)} [CharP K 2] (hσ : σ * σ = 1)
    (hτ : ∀ x, σ x.swap = (σ x).swap) : SL(2, K) →* StatedSp n K where
  toFun X := ofSymplecticMat (spPhi (K := K) σ (X : Matrix (Fin 2) (Fin 2) K))
    (spPhi_symplectic hσ hτ X.2)
  map_one' := mat_injective (by
    rw [mat_ofSymplecticMat, map_one]
    exact spPhi_one hσ)
  map_mul' X Y := mat_injective (by
    rw [mat_ofSymplecticMat, map_mul, mat_ofSymplecticMat, mat_ofSymplecticMat]
    exact spPhi_mul hσ _ _)

private theorem permMatrix_apply {ι : Type} [DecidableEq ι] (σ : Equiv.Perm ι) (i j : ι) :
    Equiv.Perm.permMatrix K σ i j = if σ i = j then (1 : K) else 0 := by
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_some_iff]

private theorem permMatrix_eq_sp {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    sp K σ (fun _ => True) = Equiv.Perm.permMatrix K σ := by
  ext β α
  rw [sp_apply, permMatrix_apply]
  by_cases h : β = σ α
  · have h' : σ β = α := by rw [h, sigma_apply_apply hσ α]
    rw [if_pos ⟨h, trivial⟩, if_pos h']
  · rw [if_neg (fun hc => h hc.1),
      if_neg (fun hc => h ((sigma_apply_apply hσ β).symm.trans (congrArg σ hc)))]

private theorem E12_add_E21_add_R {σ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ * σ = 1) :
    E12 (K := K) σ + E21 (K := K) σ + R (K := K) σ = sp K σ (fun _ => True) := by
  rw [E12, E21, R]
  rw [show sp K id (fun α => σ α = α) = sp K σ (fun α => σ α = α) from
    sp_congr_of K (fun α h => h.symm) (fun α => Iff.rfl)]
  rw [sp_add K (fun α h => not_first_and_first hσ α ⟨h.2, h.1⟩)]
  rw [sp_add K (fun α h => by
    rcases h.1 with h1 | h1
    · exact first_apply_ne_self hσ h1 h.2
    · exact first_ne_self h1 h.2)]
  rw [show sp K σ (fun α => (first σ (σ α) ∨ first σ α) ∨ σ α = α) =
      sp K σ (fun _ => True) from
    sp_congr K (fun α => rfl) (fun α => by
      constructor
      · intro _; trivial
      · intro _
        rcases first_or_first_or_fixed hσ α with (h1 | h1) | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inl (Or.inl h1)
        · exact Or.inr h1)]

private def swapMat (K : Type) [Zero K] [One K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

@[simp] private theorem swapMat_00 : swapMat K 0 0 = 0 := by simp [swapMat]

@[simp] private theorem swapMat_01 : swapMat K 0 1 = 1 := by simp [swapMat]

@[simp] private theorem swapMat_10 : swapMat K 1 0 = 1 := by simp [swapMat]

@[simp] private theorem swapMat_11 : swapMat K 1 1 = 0 := by simp [swapMat]

private theorem swapMat_det [CharP K 2] : (swapMat K).det = 1 := by
  rw [swapMat, Matrix.det_fin_two_of]
  simp [CharTwo.neg_eq]

theorem exists_sl2Hom_mat_eq_permMatrix {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (σ : Equiv.Perm (Fin n ⊕ Fin n)) (hσ : σ * σ = 1) (hτ : ∀ x, σ x.swap = (σ x).swap) :
    ∃ (φ : SL(2, K) →* StatedSp n K) (t : SL(2, K)), t ≠ 1 ∧ t * t = 1 ∧
      mat n K (φ t) = Equiv.Perm.permMatrix K σ := by
  refine ⟨spHom hσ hτ, ⟨swapMat K, swapMat_det⟩, ?_, ?_, ?_⟩
  · intro h
    have h' : swapMat K 0 0 = (1 : Matrix (Fin 2) (Fin 2) K) 0 0 :=
      congrFun (congrFun (congrArg Subtype.val h) 0) 0
    simp [swapMat] at h'
  · apply Subtype.ext
    show swapMat K * swapMat K = (1 : Matrix (Fin 2) (Fin 2) K)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two]
  · have hφ : mat n K (spHom hσ hτ ⟨swapMat K, swapMat_det⟩) = spPhi (K := K) σ (swapMat K) := rfl
    rw [hφ, spPhi]
    rw [swapMat_00, swapMat_01, swapMat_10, swapMat_11]
    simp only [zero_smul, one_smul, zero_add, add_zero]
    rw [E12_add_E21_add_R hσ, permMatrix_eq_sp hσ]

end CFSG.LocalAnalysis.WeakClosure81
