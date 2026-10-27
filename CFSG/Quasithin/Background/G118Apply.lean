module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.SourceBinaryGolayCode

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped Pointwise

namespace G11

namespace G118

variable {G : Type*} [Group G]

theorem mem_sup_of_commute' {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hN : A ≤ Subgroup.normalizer (B : Set G) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : a * h * a⁻¹ = h := by rw [hAB a ha h hh]; group
      rw [this]
      exact hh
    · intro hh
      have h1 : a⁻¹ * (a * h * a⁻¹) = (a * h * a⁻¹) * a⁻¹ := hAB a⁻¹ (A.inv_mem ha) _ hh
      have h2 : h * a⁻¹ = a * h * a⁻¹ * a⁻¹ := by
        have : a⁻¹ * (a * h * a⁻¹) = h * a⁻¹ := by group
        rw [← this]
        exact h1
      have : h = a * h * a⁻¹ := by
        calc h = (h * a⁻¹) * a := by group
          _ = (a * h * a⁻¹ * a⁻¹) * a := by rw [h2]
          _ = a * h * a⁻¹ := by group
      rw [this]
      exact hh
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hN] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem exists_max_card_subgroup [Finite G] (P : Subgroup G → Prop) (hP : P ⊥) :
    ∃ A : Subgroup G, P A ∧ ∀ B : Subgroup G, P B → Nat.card B ≤ Nat.card A := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P)
    (fun A : Subgroup G => Nat.card A) ⟨⊥, by simp [hP]⟩
  exact ⟨A, (Finset.mem_filter.mp hA).2, fun B hB => hmax B (by simp [hB])⟩

theorem exists_complement_of_isElemTwo [Finite G] {E F : Subgroup G}
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1) (hFE : F ≤ E) :
    ∃ C : Subgroup G, C ≤ E ∧ C ⊓ F = ⊥ ∧ C ⊔ F = E := by
  obtain ⟨C, ⟨hCE, hCF⟩, hmax⟩ :=
    exists_max_card_subgroup (fun C : Subgroup G => C ≤ E ∧ C ⊓ F = ⊥) ⟨bot_le, bot_inf_eq F⟩
  refine ⟨C, hCE, hCF, ?_⟩
  by_contra hne
  obtain ⟨e, heE, heCF⟩ : ∃ e ∈ E, e ∉ C ⊔ F := by
    by_contra h
    push Not at h
    exact hne (le_antisymm (sup_le hCE hFE) h)
  have he2 : e * e = 1 := hsq e heE
  have hZE : Subgroup.zpowers e ≤ E := Subgroup.zpowers_le.mpr heE
  have hcomm' : ∀ a ∈ C, ∀ b ∈ Subgroup.zpowers e, a * b = b * a := fun a ha b hb =>
    hcomm a (hCE ha) b (hZE hb)
  have hC'E : C ⊔ Subgroup.zpowers e ≤ E := sup_le hCE hZE
  have hC'F : (C ⊔ Subgroup.zpowers e) ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨c, hc, b, hb, rfl⟩ := mem_sup_of_commute' hcomm' hx1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
    · have h1 : e ^ (2 * n) = 1 := by
        rw [zpow_mul]
        have : e ^ (2 : ℤ) = 1 := by simpa [pow_two] using he2
        rw [this, one_zpow]
      rw [h1, mul_one] at hx2 ⊢
      have : c ∈ C ⊓ F := ⟨hc, hx2⟩
      rw [hCF] at this
      exact this
    · exfalso
      have h1 : e ^ (2 * n + 1) = e := by
        rw [zpow_add_one, zpow_mul]
        have : e ^ (2 : ℤ) = 1 := by simpa [pow_two] using he2
        rw [this, one_zpow, one_mul]
      rw [h1] at hx2
      apply heCF
      have : e = c⁻¹ * (c * e) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hc))
        (Subgroup.mem_sup_right hx2)
  have hcard : Nat.card (C ⊔ Subgroup.zpowers e : Subgroup G) ≤ Nat.card C :=
    hmax _ ⟨hC'E, hC'F⟩
  have hEq : C = C ⊔ Subgroup.zpowers e := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  apply heCF
  have hmem : e ∈ C ⊔ Subgroup.zpowers e := Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  rw [← hEq] at hmem
  exact Subgroup.mem_sup_left hmem

end G118

end G11

end CFSG.Quasithin
