module

public import CFSG.RankThree.PartTwo.Sec4.Item413Eigen

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223RankResProof

section Exponent

variable {G : Type*} [CommGroup G]

theorem ne_inv_of_pow_three {g : G} (h3 : g ^ 3 = 1) (hg : g ≠ 1) : g ≠ g⁻¹ := by
  intro h
  apply hg
  have h2 : g ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h]
    exact mul_inv_cancel g
  calc g = g ^ 3 * (g ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

theorem mem_zpowers_of_sq_mem {g h : G} (h3 : g ^ 3 = 1) (hsq : g ^ 2 ∈ Subgroup.zpowers h) :
    g ∈ Subgroup.zpowers h := by
  have : g = (g ^ 2) ^ 2 * (g ^ 3)⁻¹ := by group
  rw [this, h3, inv_one, mul_one]
  exact pow_mem hsq 2

end Exponent

section Combinatorics

variable {G : Type*} [CommGroup G] [DecidableEq G]

theorem exists_closure_pair (S : Finset G) (hG : ∀ g ∈ S, g ^ 3 = 1) (h1 : (1 : G) ∉ S)
    (hcard : S.card ≤ 7) (hinv : ∀ χ ∈ S, χ⁻¹ ∈ S)
    (hprod : ∀ χ ∈ S, ∀ ψ ∈ S, ψ ≠ χ → ψ ≠ χ⁻¹ → χ * ψ ∈ S ∨ χ⁻¹ * ψ ∈ S) :
    ∃ χ₁ χ₂ : G, (χ₁ = 1 ∨ χ₁ ∈ S) ∧ (χ₂ = 1 ∨ χ₂ ∈ S) ∧
      ∀ χ ∈ S, χ ∈ Subgroup.closure ({χ₁, χ₂} : Set G) := by
  by_cases hS : S = ∅
  · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by simp [hS]⟩
  obtain ⟨χ₁, hχ₁⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  have hzp : ∀ χ₂ : G, Subgroup.zpowers χ₁ ≤ Subgroup.closure ({χ₁, χ₂} : Set G) := by
    intro χ₂
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_mono (by simp)
  by_cases hA : ∀ χ ∈ S, χ ∈ Subgroup.zpowers χ₁
  · exact ⟨χ₁, χ₁, Or.inr hχ₁, Or.inr hχ₁, fun χ hχ => hzp χ₁ (hA χ hχ)⟩
  push Not at hA
  obtain ⟨χ₂, hχ₂, hχ₂A⟩ := hA
  refine ⟨χ₁, χ₂, Or.inr hχ₁, Or.inr hχ₂, fun ψ hψ => ?_⟩
  by_contra hψH
  set A := Subgroup.zpowers χ₁ with hAdef
  set H := Subgroup.closure ({χ₁, χ₂} : Set G) with hHdef
  have hAH : A ≤ H := hzp χ₂
  have hχ₁A : χ₁ ∈ A := Subgroup.mem_zpowers χ₁
  have hχ₂H : χ₂ ∈ H := Subgroup.subset_closure (by simp)
  have hne1 : ∀ χ ∈ S, χ ≠ 1 := fun χ hχ h => h1 (h ▸ hχ)
  have hχ₂ne : χ₂ ≠ χ₁ := fun h => hχ₂A (h ▸ hχ₁A)
  have hχ₂ne' : χ₂ ≠ χ₁⁻¹ := fun h => hχ₂A (h ▸ inv_mem hχ₁A)
  obtain ⟨χ₃, hχ₃S, hχ₃H, hχ₃A, hχ₃ne, hχ₃ne'⟩ :
      ∃ χ₃ ∈ S, χ₃ ∈ H ∧ χ₃ ∉ A ∧ χ₃ ≠ χ₂ ∧ χ₃ ≠ χ₂⁻¹ := by
    rcases hprod χ₁ hχ₁ χ₂ hχ₂ hχ₂ne hχ₂ne' with h | h
    · refine ⟨χ₁ * χ₂, h, mul_mem (hAH hχ₁A) hχ₂H, fun hA' => hχ₂A ?_, fun he => ?_,
        fun he => hχ₂A ?_⟩
      · have := mul_mem (inv_mem hχ₁A) hA'
        rwa [inv_mul_cancel_left] at this
      · exact hne1 χ₁ hχ₁ (by simpa using he)
      · refine mem_zpowers_of_sq_mem (hG χ₂ hχ₂) ?_
        have : χ₂ ^ 2 = χ₁⁻¹ := by
          rw [sq]
          calc χ₂ * χ₂ = χ₁⁻¹ * (χ₁ * χ₂) * χ₂ := by group
            _ = χ₁⁻¹ * χ₂⁻¹ * χ₂ := by rw [he]
            _ = χ₁⁻¹ := by group
        rw [this]
        exact inv_mem hχ₁A
    · refine ⟨χ₁⁻¹ * χ₂, h, mul_mem (inv_mem (hAH hχ₁A)) hχ₂H, fun hA' => hχ₂A ?_,
        fun he => ?_, fun he => hχ₂A ?_⟩
      · have := mul_mem hχ₁A hA'
        rwa [mul_inv_cancel_left] at this
      · exact hne1 χ₁ hχ₁ (by simpa using he)
      · refine mem_zpowers_of_sq_mem (hG χ₂ hχ₂) ?_
        have : χ₂ ^ 2 = χ₁ := by
          rw [sq]
          calc χ₂ * χ₂ = χ₁ * (χ₁⁻¹ * χ₂) * χ₂ := by group
            _ = χ₁ * χ₂⁻¹ * χ₂ := by rw [he]
            _ = χ₁ := by group
        rw [this]
        exact hχ₁A
  have hχ₂ne1 := hne1 χ₂ hχ₂
  have hχ₃ne1 := hne1 χ₃ hχ₃S
  have hψne1 := hne1 ψ hψ
  set T₁ : Finset G := {χ₁, χ₁⁻¹} with hT₁
  set T₂ : Finset G := {χ₂, χ₂⁻¹, χ₃, χ₃⁻¹} with hT₂
  set T₃ : Finset G := {ψ, ψ⁻¹} with hT₃
  have hT₁c : T₁.card = 2 := Finset.card_pair (ne_inv_of_pow_three (hG χ₁ hχ₁) (hne1 χ₁ hχ₁))
  have hT₂c : T₂.card = 4 := by
    have hinvne : χ₂⁻¹ ≠ χ₃⁻¹ := fun h => hχ₃ne (inv_injective h).symm
    have hinvne' : χ₂⁻¹ ≠ χ₃ := fun h => hχ₃ne' h.symm
    rw [hT₂, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair (ne_inv_of_pow_three (hG χ₃ hχ₃S) hχ₃ne1)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hinvne', hinvne⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨ne_inv_of_pow_three (hG χ₂ hχ₂) hχ₂ne1, fun h => hχ₃ne h.symm, ?_⟩
      intro h
      exact hχ₃ne' (by rw [h, inv_inv])
  have hT₃c : T₃.card = 2 := Finset.card_pair (ne_inv_of_pow_three (hG ψ hψ) hψne1)
  have hT₁A : ∀ g ∈ T₁, g ∈ A := by
    intro g hg
    simp only [hT₁, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact hχ₁A
    · exact inv_mem hχ₁A
  have hT₂H : ∀ g ∈ T₂, g ∈ H ∧ g ∉ A := by
    intro g hg
    simp only [hT₂, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨hχ₂H, hχ₂A⟩
    · exact ⟨inv_mem hχ₂H, fun h => hχ₂A (by simpa using inv_mem h)⟩
    · exact ⟨hχ₃H, hχ₃A⟩
    · exact ⟨inv_mem hχ₃H, fun h => hχ₃A (by simpa using inv_mem h)⟩
  have hT₃H : ∀ g ∈ T₃, g ∉ H := by
    intro g hg
    simp only [hT₃, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact hψH
    · exact fun h => hψH (by simpa using inv_mem h)
  have hd12 : Disjoint T₁ T₂ := Finset.disjoint_left.mpr fun g h1 h2 =>
    (hT₂H g h2).2 (hT₁A g h1)
  have hd3 : Disjoint (T₁ ∪ T₂) T₃ := Finset.disjoint_left.mpr fun g h12 h3 => by
    rcases Finset.mem_union.mp h12 with h | h
    · exact hT₃H g h3 (hAH (hT₁A g h))
    · exact hT₃H g h3 (hT₂H g h).1
  have hsub : T₁ ∪ T₂ ∪ T₃ ⊆ S := by
    intro g hg
    simp only [hT₁, hT₂, hT₃, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with ((rfl | rfl) | (rfl | rfl | rfl | rfl)) | (rfl | rfl)
    · exact hχ₁
    · exact hinv _ hχ₁
    · exact hχ₂
    · exact hinv _ hχ₂
    · exact hχ₃S
    · exact hinv _ hχ₃S
    · exact hψ
    · exact hinv _ hψ
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd12, hT₁c, hT₂c,
    hT₃c] at this
  omega

end Combinatorics

section Characters

variable {E : Type*} [Group E] {L : Type*} [Field L]

theorem char_pow_three (hexp : ∀ x : E, x ^ 3 = 1) {χ : E → Lˣ}
    (hmul : ∀ x y, χ (x * y) = χ x * χ y) : χ ^ 3 = 1 := by
  have h1 : χ 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  funext x
  have : χ (x ^ 3) = χ x ^ 3 := by
    rw [pow_three, pow_three, hmul, hmul]
  rw [Pi.pow_apply, ← this, hexp x, h1, Pi.one_apply]

theorem card_le_nine_of_characters [Finite E] {ι : Type*} [Fintype ι] (χ : ι → E → Lˣ)
    (hmul : ∀ a x y, χ a (x * y) = χ a x * χ a y)
    (hexp : ∀ x : E, x ^ 3 = 1) (hfaith : ∀ x : E, (∀ a, χ a x = 1) → x = 1)
    (hcount : Nat.card {a // χ a ≠ 1} ≤ 7)
    (hpair : ∀ a, ∃ a', χ a' = (χ a)⁻¹)
    (hprod : ∀ a e, χ a ≠ 1 → χ e ≠ χ a → χ e ≠ (χ a)⁻¹ →
      ∃ e', χ e' = χ a * χ e ∨ χ e' = (χ a)⁻¹ * χ e) :
    Nat.card E ≤ 9 := by
  classical
  have hcount' : (Finset.univ.filter fun a => χ a ≠ 1).card ≤ 7 := by
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at hcount
  set S : Finset (E → Lˣ) := (Finset.univ.filter fun a => χ a ≠ 1).image χ with hSdef
  have hmemS : ∀ ψ, ψ ∈ S ↔ ψ ≠ 1 ∧ ∃ a, χ a = ψ := by
    intro ψ
    simp only [hSdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, a, rfl⟩
    · rintro ⟨hψ, a, rfl⟩
      exact ⟨a, hψ, rfl⟩
  have hS3 : ∀ ψ ∈ S, ψ ^ 3 = 1 := by
    intro ψ hψ
    obtain ⟨-, a, rfl⟩ := (hmemS ψ).mp hψ
    exact char_pow_three hexp (hmul a)
  have hS1 : (1 : E → Lˣ) ∉ S := fun h => ((hmemS 1).mp h).1 rfl
  have hScard : S.card ≤ 7 := Finset.card_image_le.trans hcount'
  have hSinv : ∀ ψ ∈ S, ψ⁻¹ ∈ S := by
    intro ψ hψ
    obtain ⟨hψ1, a, rfl⟩ := (hmemS ψ).mp hψ
    obtain ⟨a', ha'⟩ := hpair a
    refine (hmemS _).mpr ⟨fun h => hψ1 ?_, a', ha'⟩
    simpa using h
  have hSprod : ∀ φ ∈ S, ∀ ψ ∈ S, ψ ≠ φ → ψ ≠ φ⁻¹ → φ * ψ ∈ S ∨ φ⁻¹ * ψ ∈ S := by
    intro φ hφ ψ hψ hne hne'
    obtain ⟨hφ1, a, rfl⟩ := (hmemS φ).mp hφ
    obtain ⟨-, e, rfl⟩ := (hmemS ψ).mp hψ
    obtain ⟨e', he' | he'⟩ := hprod a e hφ1 hne hne'
    · refine Or.inl ((hmemS _).mpr ⟨fun h => hne' ?_, e', he'⟩)
      exact (mul_eq_one_iff_inv_eq.mp h).symm
    · refine Or.inr ((hmemS _).mpr ⟨fun h => hne ?_, e', he'⟩)
      exact (inv_mul_eq_one.mp h).symm
  obtain ⟨χ₁, χ₂, hχ₁, hχ₂, hgen⟩ := exists_closure_pair S hS3 hS1 hScard hSinv hSprod
  have hcube : ∀ ψ : E → Lˣ, (ψ = 1 ∨ ψ ∈ S) → ∀ x, ((ψ x : Lˣ) : L) ^ 3 = 1 := by
    rintro ψ (rfl | hψ) x
    · simp
    · rw [← Units.val_pow_eq_pow_val, ← Pi.pow_apply, hS3 ψ hψ, Pi.one_apply, Units.val_one]
  have hinj : Function.Injective fun (x : E) (i : Fin 2) => (((![χ₁, χ₂] i) x : Lˣ) : L) := by
    intro x y hxy
    have h0 : χ₁ x = χ₁ y := Units.ext (congrFun hxy 0)
    have h1 : χ₂ x = χ₂ y := Units.ext (congrFun hxy 1)
    have key : ∀ ψ ∈ Subgroup.closure ({χ₁, χ₂} : Set (E → Lˣ)), ψ x = ψ y := by
      intro ψ hψ
      induction hψ using Subgroup.closure_induction with
      | mem ψ hψ =>
        rcases hψ with rfl | rfl
        · exact h0
        · exact h1
      | one => rfl
      | mul ψ ψ' _ _ hψ hψ' => rw [Pi.mul_apply, Pi.mul_apply, hψ, hψ']
      | inv ψ _ hψ => rw [Pi.inv_apply, Pi.inv_apply, hψ]
    have hall : ∀ a, χ a x = χ a y := by
      intro a
      by_cases ha : χ a = 1
      · rw [ha]
        rfl
      · exact key (χ a) (hgen _ ((hmemS _).mpr ⟨ha, a, rfl⟩))
    have hxy1 : x * y⁻¹ = 1 := by
      apply hfaith
      intro a
      have hy : χ a y * χ a y⁻¹ = 1 := by
        rw [← hmul, mul_inv_cancel]
        have h := hmul a 1 1
        rw [mul_one] at h
        exact left_eq_mul.mp h
      rw [hmul, hall a, hy]
    exact mul_inv_eq_one.mp hxy1
  have h3 : ∀ (x : E) (i : Fin 2), (((![χ₁, χ₂] i) x : Lˣ) : L) ^ 3 = 1 := by
    intro x i
    fin_cases i
    · exact hcube χ₁ hχ₁ x
    · exact hcube χ₂ hχ₂ x
  have := Sec4.card_le_three_pow_of_injective _ hinj h3
  simpa using this

end Characters

end CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
