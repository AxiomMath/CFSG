module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartOne.K159

open scoped Pointwise

variable {G : Type*} [Group G]

theorem inner_sup {E Y₁ Y₂ : Subgroup G} (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (h₁ : ∀ x ∈ E, ∃ y ∈ Y₁, ∃ c ∈ Subgroup.centralizer (Y₁ : Set G), x = y * c)
    (h₂ : ∀ x ∈ E, ∃ y ∈ Y₂, ∃ c ∈ Subgroup.centralizer (Y₂ : Set G), x = y * c) :
    ∀ x ∈ E, ∃ y ∈ Y₁ ⊔ Y₂, ∃ c ∈ Subgroup.centralizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G),
      x = y * c := by
  intro x hx
  obtain ⟨y₁, hy₁, c₁, hc₁, hx₁⟩ := h₁ x hx
  obtain ⟨y₂, hy₂, c₂, hc₂, hx₂⟩ := h₂ x hx
  have hc12 : Commute y₁ y₂ := hcomm y₁ hy₁ y₂ hy₂
  have key : y₂⁻¹ * c₁ = y₁⁻¹ * c₂ := by
    have h1 : y₁ * c₁ = y₂ * c₂ := hx₁.symm.trans hx₂
    have h2 : y₁ * (y₂⁻¹ * c₁) = c₂ := by
      calc y₁ * (y₂⁻¹ * c₁) = (y₁ * y₂⁻¹) * c₁ := by group
        _ = (y₂⁻¹ * y₁) * c₁ := by rw [hc12.inv_right.eq]
        _ = y₂⁻¹ * (y₁ * c₁) := by group
        _ = y₂⁻¹ * (y₂ * c₂) := by rw [h1]
        _ = c₂ := by group
    calc y₂⁻¹ * c₁ = y₁⁻¹ * (y₁ * (y₂⁻¹ * c₁)) := by group
      _ = y₁⁻¹ * c₂ := by rw [h2]
  refine ⟨y₁ * y₂, Subgroup.mul_mem_sup hy₁ hy₂, y₂⁻¹ * c₁, ?_, ?_⟩
  · have hle : Y₁ ⊔ Y₂ ≤ Subgroup.centralizer ({y₂⁻¹ * c₁} : Set G) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        symm
        have h1 : w * y₂⁻¹ = y₂⁻¹ * w := by
          have h := hcomm w hw y₂ hy₂
          calc w * y₂⁻¹ = y₂⁻¹ * (y₂ * w) * y₂⁻¹ := by group
            _ = y₂⁻¹ * (w * y₂) * y₂⁻¹ := by rw [← h]
            _ = y₂⁻¹ * w := by group
        have h2 : w * c₁ = c₁ * w := Subgroup.mem_centralizer_iff.1 hc₁ w hw
        calc y₂⁻¹ * c₁ * w = y₂⁻¹ * (c₁ * w) := by group
          _ = y₂⁻¹ * (w * c₁) := by rw [h2]
          _ = (y₂⁻¹ * w) * c₁ := by group
          _ = (w * y₂⁻¹) * c₁ := by rw [h1]
          _ = w * (y₂⁻¹ * c₁) := by group
      · rw [Subgroup.mem_centralizer_singleton_iff, key]
        symm
        have h1 : w * y₁⁻¹ = y₁⁻¹ * w := by
          have h := hcomm y₁ hy₁ w hw
          calc w * y₁⁻¹ = y₁⁻¹ * (y₁ * w) * y₁⁻¹ := by group
            _ = y₁⁻¹ * (w * y₁) * y₁⁻¹ := by rw [h]
            _ = y₁⁻¹ * w := by group
        have h2 : w * c₂ = c₂ * w := Subgroup.mem_centralizer_iff.1 hc₂ w hw
        calc y₁⁻¹ * c₂ * w = y₁⁻¹ * (c₂ * w) := by group
          _ = y₁⁻¹ * (w * c₂) := by rw [h2]
          _ = (y₁⁻¹ * w) * c₂ := by group
          _ = (w * y₁⁻¹) * c₂ := by rw [h1]
          _ = w * (y₁⁻¹ * c₂) := by group
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  · calc x = y₁ * c₁ := hx₁
      _ = (y₁ * y₂) * (y₂⁻¹ * c₁) := by group

theorem le_normalizer_of_commute {Y₁ Y₂ : Subgroup G} (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) :
    Y₂ ≤ Subgroup.normalizer (Y₁ : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have h := hcomm g hg b hb
    have : b * g * b⁻¹ = g := by rw [← h]; group
    rw [this]
    exact hg
  · intro hg
    have h := hcomm (b * g * b⁻¹) hg b hb
    have : g = b * g * b⁻¹ := by
      calc g = b⁻¹ * (b * g * b⁻¹ * b) := by group
        _ = b⁻¹ * (b * (b * g * b⁻¹)) := by rw [h]
        _ = b * g * b⁻¹ := by group
    rw [this]
    exact hg

theorem noP_sup {p : ℕ} (hp : p.Prime) {Y₁ Y₂ : Subgroup G}
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (h₁ : ∀ z ∈ Y₁ ⊓ Subgroup.centralizer (Y₁ : Set G), ¬ p ∣ orderOf z)
    (h₂ : ∀ z ∈ Y₂ ⊓ Subgroup.centralizer (Y₂ : Set G), ¬ p ∣ orderOf z) :
    ∀ z ∈ (Y₁ ⊔ Y₂) ⊓ Subgroup.centralizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G),
      ¬ p ∣ orderOf z := by
  rintro z ⟨hzY, hzC⟩
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left Y₁ Y₂ (le_normalizer_of_commute hcomm)
  have hz' : z ∈ ((Y₁ : Set G) * (Y₂ : Set G)) := by
    rw [← hset]
    exact hzY
  obtain ⟨a, ha, b, hb, rfl⟩ := hz'
  have hzc := Subgroup.mem_centralizer_iff.1 hzC
  have hab : Commute a b := hcomm a ha b hb
  have haC : a ∈ Subgroup.centralizer (Y₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := hzc u (Subgroup.mem_sup_left hu)
    have h2 : u * b = b * u := hcomm u hu b hb
    have h3 : u * a * b = a * u * b := by
      calc u * a * b = u * (a * b) := by group
        _ = a * b * u := h1
        _ = a * (b * u) := by group
        _ = a * (u * b) := by rw [h2]
        _ = a * u * b := by group
    exact mul_right_cancel h3
  have hbC : b ∈ Subgroup.centralizer (Y₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := hzc v (Subgroup.mem_sup_right hv)
    have h2 : a * v = v * a := hcomm a ha v hv
    have h3 : a * (v * b) = a * (b * v) := by
      calc a * (v * b) = (a * v) * b := by group
        _ = (v * a) * b := by rw [h2]
        _ = v * (a * b) := by group
        _ = a * b * v := h1
        _ = a * (b * v) := by group
    exact mul_left_cancel h3
  intro hdvd
  have h1 : orderOf (a * b) ∣ Nat.lcm (orderOf a) (orderOf b) := hab.orderOf_mul_dvd_lcm
  have h2 : p ∣ orderOf a * orderOf b := (hdvd.trans h1).trans (Nat.lcm_dvd_mul _ _)
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h | h
  · exact h₁ a ⟨ha, haC⟩ h
  · exact h₂ b ⟨hb, hbC⟩ h

theorem inner_finset_sup {E : Subgroup G} (s : Finset (Subgroup G))
    (hcomm : ∀ Y ∈ s, ∀ Y' ∈ s, Y ≠ Y' → ∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a)
    (hin : ∀ Y ∈ s, ∀ x ∈ E, ∃ y ∈ Y, ∃ c ∈ Subgroup.centralizer (Y : Set G), x = y * c) :
    ∀ x ∈ E, ∃ y ∈ s.sup id, ∃ c ∈ Subgroup.centralizer ((s.sup id : Subgroup G) : Set G),
      x = y * c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x hx
    refine ⟨1, one_mem _, x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have : h = 1 := by simpa using hh
    rw [this]
    simp
  | insert a t hat ih =>
    intro x hx
    rw [Finset.sup_insert]
    have hcommt : ∀ u ∈ a, ∀ v ∈ t.sup id, u * v = v * u := by
      intro u hu v hv
      have hle : t.sup id ≤ Subgroup.centralizer (a : Set G) := by
        refine Finset.sup_le fun Y hY => ?_
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact hcomm a (Finset.mem_insert_self _ _) Y (Finset.mem_insert_of_mem hY)
          (fun h => hat (h ▸ hY)) w hw y hy
      exact (Subgroup.mem_centralizer_iff.1 (hle hv) u hu)
    exact inner_sup (E := E) (Y₁ := a) (Y₂ := t.sup id) hcommt (hin a (Finset.mem_insert_self _ _))
      (ih (fun Y hY Y' hY' hne => hcomm Y (Finset.mem_insert_of_mem hY) Y'
        (Finset.mem_insert_of_mem hY') hne)
        (fun Y hY => hin Y (Finset.mem_insert_of_mem hY))) x hx

theorem noP_finset_sup {p : ℕ} (hp : p.Prime) (s : Finset (Subgroup G))
    (hcomm : ∀ Y ∈ s, ∀ Y' ∈ s, Y ≠ Y' → ∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a)
    (hz : ∀ Y ∈ s, ∀ z ∈ Y ⊓ Subgroup.centralizer (Y : Set G), ¬ p ∣ orderOf z) :
    ∀ z ∈ s.sup id ⊓ Subgroup.centralizer ((s.sup id : Subgroup G) : Set G), ¬ p ∣ orderOf z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rintro z ⟨hz1, -⟩
    have : z = 1 := by simpa using hz1
    rw [this, orderOf_one]
    exact hp.not_dvd_one
  | insert a t hat ih =>
    rw [Finset.sup_insert]
    have hcommt : ∀ u ∈ a, ∀ v ∈ t.sup id, u * v = v * u := by
      intro u hu v hv
      have hle : t.sup id ≤ Subgroup.centralizer (a : Set G) := by
        refine Finset.sup_le fun Y hY => ?_
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact hcomm a (Finset.mem_insert_self _ _) Y (Finset.mem_insert_of_mem hY)
          (fun h => hat (h ▸ hY)) w hw y hy
      exact (Subgroup.mem_centralizer_iff.1 (hle hv) u hu)
    exact noP_sup hp hcommt (hz a (Finset.mem_insert_self _ _))
      (ih (fun Y hY Y' hY' hne => hcomm Y (Finset.mem_insert_of_mem hY) Y'
        (Finset.mem_insert_of_mem hY') hne) (fun Y hY => hz Y (Finset.mem_insert_of_mem hY)))

end CFSG.RankThree.PartOne.K159
