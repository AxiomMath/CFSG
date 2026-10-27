module

public import CFSG.Quasithin.EmptyFaithful.S1417Quad
public import CFSG.Quasithin.EmptyFaithful.S1417Blocks

public section

namespace CFSG.Quasithin

namespace S1417

section Orth

variable {W : Type*} [CommGroup W] {U₁ U₂ : Subgroup W}

theorem mul_self_eq_one_of_mem (φ : ↥U₁ ≃* F2sq) {x : W} (hx : x ∈ U₁) : x * x = 1 := by
  have h : ∀ a : F2sq, a * a = 1 := by decide
  have h1 : φ (⟨x, hx⟩ * ⟨x, hx⟩) = 1 := by rw [map_mul]; exact h _
  have h2 : (⟨x, hx⟩ * ⟨x, hx⟩ : U₁) = 1 := φ.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem quadOf_apply_of_stab (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) {g : MulAut W} (h₁ : ∀ u ∈ U₁, g u ∈ U₁) (h₂ : ∀ u ∈ U₂, g u ∈ U₂)
    (w : W) : quadOf hinf hsup φ₁ φ₂ (g w) = quadOf hinf hsup φ₁ φ₂ w := by
  classical
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq hsup w
  rw [map_mul, quadOf_mul hinf hsup φ₁ φ₂ (h₁ y hy) (h₂ z hz),
    quadOf_mul hinf hsup φ₁ φ₂ hy hz]
  have e1 : g y = 1 ↔ y = 1 := g.map_eq_one_iff
  have e2 : g z = 1 ↔ z = 1 := g.map_eq_one_iff
  simp only [e1, e2]

theorem quadOf_apply_of_swap (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) {g : MulAut W} (h₁ : ∀ u ∈ U₁, g u ∈ U₂) (h₂ : ∀ u ∈ U₂, g u ∈ U₁)
    (w : W) : quadOf hinf hsup φ₁ φ₂ (g w) = quadOf hinf hsup φ₁ φ₂ w := by
  classical
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq hsup w
  rw [map_mul, mul_comm, quadOf_mul hinf hsup φ₁ φ₂ (h₂ z hz) (h₁ y hy),
    quadOf_mul hinf hsup φ₁ φ₂ hy hz]
  have e1 : g y = 1 ↔ y = 1 := g.map_eq_one_iff
  have e2 : g z = 1 ↔ z = 1 := g.map_eq_one_iff
  simp only [e1, e2]
  exact add_comm _ _

theorem perm_of_mem_orthogonal (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq)
    (φ₂ : ↥U₂ ≃* F2sq) (hex : ∃ a ∈ U₁, a ≠ 1) {g : MulAut W}
    (hg : ∀ w, quadOf hinf hsup φ₁ φ₂ (g w) = quadOf hinf hsup φ₁ φ₂ w) :
    ((∀ u ∈ U₁, g u ∈ U₁) ∧ (∀ u ∈ U₂, g u ∈ U₂)) ∨
      ((∀ u ∈ U₁, g u ∈ U₂) ∧ (∀ u ∈ U₂, g u ∈ U₁)) := by
  classical
  set q := quadOf hinf hsup φ₁ φ₂ with hq
  have hN : ∀ x, q x = 1 ↔ (x ∈ U₁ ∨ x ∈ U₂) ∧ x ≠ 1 := fun x =>
    quadOf_eq_one_iff hinf hsup φ₁ φ₂
  have hdisj : ∀ x, x ∈ U₁ → x ∈ U₂ → x = 1 := fun x => mem_inf_eq_one hinf
  have hNg : ∀ x, ((x ∈ U₁ ∨ x ∈ U₂) ∧ x ≠ 1) → ((g x ∈ U₁ ∨ g x ∈ U₂) ∧ g x ≠ 1) := by
    intro x hx
    exact (hN _).mp (by rw [hg]; exact (hN x).mpr hx)
  have hpol : ∀ x y, quadPolar q (g x) (g y) = quadPolar q x y := by
    intro x y
    simp only [quadPolar, ← map_mul, hg]
  have hsq₁ : ∀ x ∈ U₁, x * x = 1 := fun x hx => mul_self_eq_one_of_mem φ₁ hx
  have hsq₂ : ∀ x ∈ U₂, x * x = 1 := fun x hx => mul_self_eq_one_of_mem φ₂ hx
  have hq1 : ∀ x ∈ U₁, x ≠ 1 → q x = 1 := fun x hx hx1 => (hN x).mpr ⟨Or.inl hx, hx1⟩
  have hq2 : ∀ x ∈ U₂, x ≠ 1 → q x = 1 := fun x hx hx1 => (hN x).mpr ⟨Or.inr hx, hx1⟩
  have hpol11 : ∀ x ∈ U₁, ∀ y ∈ U₁, x ≠ 1 → y ≠ 1 → x ≠ y → quadPolar q x y = 1 := by
    intro x hx y hy hx1 hy1 hxy
    have hxy1 : x * y ≠ 1 := by
      intro h
      apply hxy
      have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact eq_inv_of_mul_eq_one_left (hsq₁ x hx)
    simp only [quadPolar, hq1 _ (U₁.mul_mem hx hy) hxy1, hq1 x hx hx1, hq1 y hy hy1]
    decide
  have hpol22 : ∀ x ∈ U₂, ∀ y ∈ U₂, x ≠ 1 → y ≠ 1 → x ≠ y → quadPolar q x y = 1 := by
    intro x hx y hy hx1 hy1 hxy
    have hxy1 : x * y ≠ 1 := by
      intro h
      apply hxy
      have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact eq_inv_of_mul_eq_one_left (hsq₂ x hx)
    simp only [quadPolar, hq2 _ (U₂.mul_mem hx hy) hxy1, hq2 x hx hx1, hq2 y hy hy1]
    decide
  have hpol12 : ∀ x ∈ U₁, ∀ y ∈ U₂, x ≠ 1 → y ≠ 1 → quadPolar q x y = 0 := by
    intro x hx y hy hx1 hy1
    have : q (x * y) = 0 := by
      rw [hq, quadOf_mul hinf hsup φ₁ φ₂ hx hy]
      simp only [hx1, hy1, ↓reduceIte]
      decide
    simp only [quadPolar, this, hq1 x hx hx1, hq2 y hy hy1]
    decide
  have hpol21 : ∀ x ∈ U₂, ∀ y ∈ U₁, x ≠ 1 → y ≠ 1 → quadPolar q x y = 0 := by
    intro x hx y hy hx1 hy1
    have h := hpol12 y hy x hx hy1 hx1
    have e : quadPolar q x y = quadPolar q y x := by
      simp only [quadPolar, mul_comm x y]
      ring
    rw [e]
    exact h
  have hsame : ∀ x y, ((x ∈ U₁ ∨ x ∈ U₂) ∧ x ≠ 1) → ((y ∈ U₁ ∨ y ∈ U₂) ∧ y ≠ 1) →
      ((x = y ∨ quadPolar q x y = 1) ↔ ((x ∈ U₁ ∧ y ∈ U₁) ∨ (x ∈ U₂ ∧ y ∈ U₂))) := by
    rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · by_cases hxy : x = y
      · simp [hxy, hy]
      · simp only [hxy, false_or, hpol11 x hx y hy hx1 hy1 hxy, true_iff]
        exact Or.inl ⟨hx, hy⟩
    · have hxy : x ≠ y := fun h => hx1 (hdisj x hx (h ▸ hy))
      have hy' : y ∉ U₁ := fun h => hy1 (hdisj y h hy)
      have hx' : x ∉ U₂ := fun h => hx1 (hdisj x hx h)
      simp only [hxy, false_or, hpol12 x hx y hy hx1 hy1, zero_ne_one, false_iff]
      rintro (h | h)
      · exact hy' h.2
      · exact hx' h.1
    · have hxy : x ≠ y := fun h => hx1 (hdisj x (h ▸ hy) hx)
      have hy' : y ∉ U₂ := fun h => hy1 (hdisj y hy h)
      have hx' : x ∉ U₁ := fun h => hx1 (hdisj x h hx)
      simp only [hxy, false_or, hpol21 x hx y hy hx1 hy1, zero_ne_one, false_iff]
      rintro (h | h)
      · exact hx' h.1
      · exact hy' h.2
    · by_cases hxy : x = y
      · simp [hxy, hy]
      · simp only [hxy, false_or, hpol22 x hx y hy hx1 hy1 hxy, true_iff]
        exact Or.inr ⟨hx, hy⟩
  obtain ⟨a, ha, ha1⟩ := hex
  have hkey : ∀ x, ((x ∈ U₁ ∨ x ∈ U₂) ∧ x ≠ 1) →
      (((x ∈ U₁ ∧ a ∈ U₁) ∨ (x ∈ U₂ ∧ a ∈ U₂)) ↔
        ((g x ∈ U₁ ∧ g a ∈ U₁) ∨ (g x ∈ U₂ ∧ g a ∈ U₂))) := by
    intro x hx
    rw [← hsame x a hx ⟨Or.inl ha, ha1⟩, ← hsame (g x) (g a) (hNg x hx) (hNg a ⟨Or.inl ha, ha1⟩),
      hpol, g.injective.eq_iff]
  have hgaN := hNg a ⟨Or.inl ha, ha1⟩
  rcases hgaN.1 with hga | hga
  · left
    constructor
    · intro u hu
      by_cases hu1 : u = 1
      · rw [hu1, map_one]; exact U₁.one_mem
      · have h := (hkey u ⟨Or.inl hu, hu1⟩).mp (Or.inl ⟨hu, ha⟩)
        rcases h with h | h
        · exact h.1
        · exact absurd (hdisj _ hga h.2) hgaN.2
    · intro u hu
      by_cases hu1 : u = 1
      · rw [hu1, map_one]; exact U₂.one_mem
      · have hn := hNg u ⟨Or.inr hu, hu1⟩
        rcases hn.1 with h | h
        · exfalso
          have := (hkey u ⟨Or.inr hu, hu1⟩).mpr (Or.inl ⟨h, hga⟩)
          rcases this with h' | h'
          · exact hu1 (hdisj u h'.1 hu)
          · exact ha1 (hdisj a ha h'.2)
        · exact h
  · right
    constructor
    · intro u hu
      by_cases hu1 : u = 1
      · rw [hu1, map_one]; exact U₂.one_mem
      · have h := (hkey u ⟨Or.inl hu, hu1⟩).mp (Or.inl ⟨hu, ha⟩)
        rcases h with h | h
        · exact absurd (hdisj _ h.2 hga) hgaN.2
        · exact h.1
    · intro u hu
      by_cases hu1 : u = 1
      · rw [hu1, map_one]; exact U₁.one_mem
      · have hn := hNg u ⟨Or.inr hu, hu1⟩
        rcases hn.1 with h | h
        · exact h
        · exfalso
          have := (hkey u ⟨Or.inr hu, hu1⟩).mpr (Or.inr ⟨h, hga⟩)
          rcases this with h' | h'
          · exact hu1 (hdisj u h'.1 hu)
          · exact ha1 (hdisj a ha h'.2)

end Orth


section Main

variable {W : Type*} [CommGroup W] [Finite W] {L₁ L₂ : Subgroup (MulAut W)}

theorem mem_stabSub_of_forall_le {U : Subgroup W} {g : MulAut W} (h : ∀ u ∈ U, g u ∈ U) :
    g ∈ stabSub U := by
  have hle : U.map g.toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  have hcard : Nat.card U ≤ Nat.card (U.map g.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective g.injective]
  exact mem_stabSub_of_map_eq (Subgroup.eq_of_le_of_card_ge hle hcard)

theorem exists_quad_orthogonal (hN₁ : ActsAsNaturalL2 L₁ (commV L₁))
    (hN₂ : ActsAsNaturalL2 L₂ (commV L₂)) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hinf : commV L₁ ⊓ commV L₂ = ⊥) (hUtop : commV L₁ ⊔ commV L₂ = ⊤) {t : MulAut W}
    (ht₁ : ∀ u ∈ commV L₁, t u ∈ commV L₂) (ht₂ : ∀ u ∈ commV L₂, t u ∈ commV L₁) :
    Nat.card W = 16 ∧ ∃ q : W → ZMod 2, IsQuadraticFormOn q ∧ IsNondegQuadratic q ∧
      IsPlusType q ∧ (L₁ ⊔ L₂) ⊔ Subgroup.zpowers t = orthogonalGroupOf q := by
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hinf' : commV L₂ ⊓ commV L₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hN₁' := hN₁
  have hN₂' := hN₂
  obtain ⟨-, φ₁, -⟩ := hN₁'
  obtain ⟨-, φ₂, -⟩ := hN₂'
  have hex : ∃ a ∈ commV L₁, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h4 := (card_of_actsAsNaturalL2 hN₁).2
    have : commV L₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at h4
    omega
  refine ⟨card_eq_sixteen hinf hUtop φ₁ φ₂, quadOf hinf hUtop φ₁ φ₂,
    quadOf_isQuadratic hinf hUtop φ₁ φ₂, quadOf_nondeg hinf hUtop φ₁ φ₂,
    quadOf_plus hinf hUtop φ₁ φ₂, ?_⟩
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) ?_
    · intro l hl v
      exact quadOf_apply_of_stab hinf hUtop φ₁ φ₂ (fun u hu => commV_stable L₁ hl hu)
        (fun u hu => by rw [apply_eq_of_mem_commV_of_commute hc hinf hl hu]; exact hu) v
    · intro l hl v
      exact quadOf_apply_of_stab hinf hUtop φ₁ φ₂
        (fun u hu => by rw [apply_eq_of_mem_commV_of_commute hc' hinf' hl hu]; exact hu)
        (fun u hu => commV_stable L₂ hl hu) v
    · rw [Subgroup.zpowers_le]
      intro v
      exact quadOf_apply_of_swap hinf hUtop φ₁ φ₂ ht₁ ht₂ v
  · intro g hg
    have hg' : ∀ w, quadOf hinf hUtop φ₁ φ₂ (g w) = quadOf hinf hUtop φ₁ φ₂ w := hg
    have key : ∀ g : MulAut W, (∀ u ∈ commV L₁, g u ∈ commV L₁) →
        (∀ u ∈ commV L₂, g u ∈ commV L₂) → g ∈ L₁ ⊔ L₂ := by
      intro g h₁ h₂
      obtain ⟨y, hy, hgy⟩ := exists_mem_sup_apply_eq hN₁ hN₂ hc hinf (mem_stabSub_of_forall_le h₁)
        (mem_stabSub_of_forall_le h₂)
      have : g = y := MulEquiv.ext fun w => hgy w (by rw [hUtop]; exact Subgroup.mem_top w)
      rw [this]
      exact hy
    rcases perm_of_mem_orthogonal hinf hUtop φ₁ φ₂ hex hg' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Subgroup.mem_sup_left (key g h₁ h₂)
    · have hgt : g * t ∈ L₁ ⊔ L₂ := key _ (fun u hu => h₂ _ (ht₁ u hu))
        (fun u hu => h₁ _ (ht₂ u hu))
      have : g = (g * t) * t⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgt)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)))

end Main

end S1417

end CFSG.Quasithin
