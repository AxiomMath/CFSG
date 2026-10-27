module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Quasithin
open scoped Pointwise

variable {X : Type*} [Group X]

theorem le_normalizer_of_commute {A B : Subgroup X} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (B : Set X) := fun a ha =>
  Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm)

theorem exists_mul_of_mem_sup {A B : Subgroup X} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : X}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hcoe : (↑(A ⊔ B) : Set X) = (A : Set X) * (B : Set X) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B (le_normalizer_of_commute hc)
  have hx' : x ∈ (A : Set X) * (B : Set X) := by rw [← hcoe]; exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem oTwoUpper_sup_le {K₁ K₂ : Subgroup X} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hi : K₁ ⊓ K₂ = ⊥) : oTwoUpper (K₁ ⊔ K₂) ≤ oTwoUpper K₁ ⊔ oTwoUpper K₂ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hx, ho⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hx
  have hab : Commute a b := hc a ha b hb
  have hn : (a * b) ^ orderOf (a * b) = 1 := pow_orderOf_eq_one _
  rw [hab.mul_pow] at hn
  have han : a ^ orderOf (a * b) = 1 := by
    have heq : a ^ orderOf (a * b) = (b ^ orderOf (a * b))⁻¹ := eq_inv_of_mul_eq_one_left hn
    have hmem : a ^ orderOf (a * b) ∈ K₁ ⊓ K₂ :=
      ⟨K₁.pow_mem ha _, heq ▸ K₂.inv_mem (K₂.pow_mem hb _)⟩
    rw [hi] at hmem
    exact hmem
  have hbn : b ^ orderOf (a * b) = 1 := by rwa [han, one_mul] at hn
  have hoa : Odd (orderOf a) := ho.of_dvd_nat (orderOf_dvd_of_pow_eq_one han)
  have hob : Odd (orderOf b) := ho.of_dvd_nat (orderOf_dvd_of_pow_eq_one hbn)
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_oTwoUpper_of_odd ha hoa))
    (Subgroup.mem_sup_right (mem_oTwoUpper_of_odd hb hob))

theorem inf_eq_bot_or_le {C O : Subgroup X} (hC : IsSimpleGroup ↥C)
    (hCO : C ≤ Subgroup.normalizer (O : Set X)) : C ⊓ O = ⊥ ∨ C ≤ O := by
  have hn : (O.subgroupOf C).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hCO g.2) n).mp hn⟩
  have := hC
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.subgroupOf C) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_iff.mp h.symm
  · right
    exact Subgroup.subgroupOf_eq_top.mp h

theorem commute_of_inf_eq_bot {C O : Subgroup X} (hi : C ⊓ O = ⊥)
    (hCO : C ≤ Subgroup.normalizer (O : Set X)) (hOC : O ≤ Subgroup.normalizer (C : Set X)) :
    ∀ c ∈ C, ∀ o ∈ O, c * o = o * c := by
  intro c hc o ho
  have h1 : c * (o * c⁻¹ * o⁻¹) ∈ C :=
    C.mul_mem hc ((Subgroup.mem_normalizer_iff.mp (hOC ho) c⁻¹).mp (C.inv_mem hc))
  have h2 : c * o * c⁻¹ * o⁻¹ ∈ O :=
    O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCO hc) o).mp ho) (O.inv_mem ho)
  have h3 : c * o * c⁻¹ * o⁻¹ ∈ C ⊓ O := ⟨by simpa [mul_assoc] using h1, h2⟩
  rw [hi, Subgroup.mem_bot] at h3
  calc c * o = c * o * c⁻¹ * o⁻¹ * (o * c) := by group
    _ = o * c := by rw [h3, one_mul]

theorem commute_of_le_sup {C O₁ O₂ : Subgroup X} (hC : C ≤ O₁ ⊔ O₂)
    (h₁ : ∀ c ∈ C, ∀ o ∈ O₁, c * o = o * c) (h₂ : ∀ c ∈ C, ∀ o ∈ O₂, c * o = o * c) :
    ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c := by
  intro c hc c' hc'
  have hle : O₁ ⊔ O₂ ≤ Subgroup.centralizer ({c} : Set X) :=
    sup_le (fun o ho => Subgroup.mem_centralizer_singleton_iff.mpr (h₁ c hc o ho).symm)
      fun o ho => Subgroup.mem_centralizer_singleton_iff.mpr (h₂ c hc o ho).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (hC hc'))).symm

theorem sup_le_normalizer_left {A B : Subgroup X} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ⊔ B ≤ Subgroup.normalizer (A : Set X) :=
  sup_le Subgroup.le_normalizer
    (le_normalizer_of_commute fun b hb a ha => (hc a ha b hb).symm)

theorem eq_oTwoUpper_or_eq_oTwoUpper {K₁ K₂ A B : Subgroup X}
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hi : K₁ ⊓ K₂ = ⊥)
    (hO₁ : oTwoUpper K₁ ≠ ⊥) (hO₂ : oTwoUpper K₂ ≠ ⊥)
    (hAs : IsSimpleGroup ↥A) (hBs : IsSimpleGroup ↥B)
    (hAn : ∃ a ∈ A, ∃ a' ∈ A, a * a' ≠ a' * a) (hBn : ∃ b ∈ B, ∃ b' ∈ B, b * b' ≠ b' * b)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (h₁ : oTwoUpper K₁ ≤ A ⊔ B) (h₂ : oTwoUpper K₂ ≤ A ⊔ B)
    (hN : A ⊔ B ≤ oTwoUpper K₁ ⊔ oTwoUpper K₂) :
    (A = oTwoUpper K₁ ∧ B = oTwoUpper K₂) ∨ (A = oTwoUpper K₂ ∧ B = oTwoUpper K₁) := by
  set O₁ := oTwoUpper K₁
  set O₂ := oTwoUpper K₂
  have hcO : ∀ a ∈ O₁, ∀ b ∈ O₂, a * b = b * a := fun a ha b hb =>
    hc a (oTwoUpper_le K₁ ha) b (oTwoUpper_le K₂ hb)
  have hiO : O₁ ⊓ O₂ = ⊥ :=
    le_bot_iff.mp (hi ▸ inf_le_inf (oTwoUpper_le K₁) (oTwoUpper_le K₂))
  have hN₁ : O₁ ⊔ O₂ ≤ Subgroup.normalizer (O₁ : Set X) := sup_le_normalizer_left hcO
  have hN₂ : O₁ ⊔ O₂ ≤ Subgroup.normalizer (O₂ : Set X) := by
    rw [sup_comm]; exact sup_le_normalizer_left fun b hb a ha => (hcO a ha b hb).symm
  have hNA : A ⊔ B ≤ Subgroup.normalizer (A : Set X) := sup_le_normalizer_left hAB
  have hNB : A ⊔ B ≤ Subgroup.normalizer (B : Set X) := by
    rw [sup_comm]; exact sup_le_normalizer_left fun b hb a ha => (hAB a ha b hb).symm
  have hAle : A ≤ A ⊔ B := le_sup_left
  have hBle : B ≤ A ⊔ B := le_sup_right
  have key : ∀ C : Subgroup X, IsSimpleGroup ↥C → (∃ c ∈ C, ∃ c' ∈ C, c * c' ≠ c' * c) →
      C ≤ A ⊔ B → A ⊔ B ≤ Subgroup.normalizer (C : Set X) → C ≤ O₁ ∨ C ≤ O₂ := by
    intro C hCs hCn hCle hNC
    have hC₁ : C ≤ Subgroup.normalizer (O₁ : Set X) := (hCle.trans hN).trans hN₁
    have hC₂ : C ≤ Subgroup.normalizer (O₂ : Set X) := (hCle.trans hN).trans hN₂
    rcases inf_eq_bot_or_le hCs hC₁ with e₁ | e₁
    · rcases inf_eq_bot_or_le hCs hC₂ with e₂ | e₂
      · exfalso
        obtain ⟨c, hc', c', hc'', hne⟩ := hCn
        exact hne (commute_of_le_sup (hCle.trans hN)
          (commute_of_inf_eq_bot e₁ hC₁ (h₁.trans hNC))
          (commute_of_inf_eq_bot e₂ hC₂ (h₂.trans hNC)) c hc' c' hc'')
      · exact Or.inr e₂
    · exact Or.inl e₁
  have fill : ∀ {P Q : Subgroup X}, P ⊓ Q = ⊥ → P ≤ A ⊔ B → A ≤ P → B ≤ Q → P ≤ A := by
    intro P Q hPQ hP hAP hBQ x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hAB (hP hx)
    have hbP : b ∈ P := by
      have : b = a⁻¹ * (a * b) := by group
      rw [this]; exact P.mul_mem (P.inv_mem (hAP ha)) hx
    have hb1 : b ∈ P ⊓ Q := ⟨hbP, hBQ hb⟩
    rw [hPQ, Subgroup.mem_bot] at hb1
    rw [hb1, mul_one]; exact ha
  have fill' : ∀ {P Q : Subgroup X}, P ⊓ Q = ⊥ → Q ≤ A ⊔ B → A ≤ P → B ≤ Q → Q ≤ B := by
    intro P Q hPQ hQ hAP hBQ x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hAB (hQ hx)
    have haQ : a ∈ Q := by
      have : a = (a * b) * b⁻¹ := by group
      rw [this]; exact Q.mul_mem hx (Q.inv_mem (hBQ hb))
    have ha1 : a ∈ P ⊓ Q := ⟨hAP ha, haQ⟩
    rw [hPQ, Subgroup.mem_bot] at ha1
    rw [ha1, one_mul]; exact hb
  rcases key A hAs hAn hAle hNA with hA₁ | hA₂ <;> rcases key B hBs hBn hBle hNB with hB₁ | hB₂
  · exact absurd (le_bot_iff.mp (hiO ▸ le_inf (h₂.trans (sup_le hA₁ hB₁)) le_rfl)) hO₂
  · exact Or.inl ⟨le_antisymm hA₁ (fill hiO h₁ hA₁ hB₂), le_antisymm hB₂ (fill' hiO h₂ hA₁ hB₂)⟩
  · have hiO' : O₂ ⊓ O₁ = ⊥ := by rw [inf_comm]; exact hiO
    exact Or.inr ⟨le_antisymm hA₂ (fill hiO' h₂ hA₂ hB₁),
      le_antisymm hB₁ (fill' hiO' h₁ hA₂ hB₁)⟩
  · exact absurd (le_bot_iff.mp (hiO ▸ le_inf le_rfl (h₁.trans (sup_le hA₂ hB₂)))) hO₁

theorem false_of_isSimpleGroup {O A B : Subgroup X} (hO : IsSimpleGroup ↥O)
    (hAn : ∃ a ∈ A, ∃ a' ∈ A, a * a' ≠ a' * a) (hBn : ∃ b ∈ B, ∃ b' ∈ B, b * b' ≠ b' * b)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hle : A ⊔ B ≤ O) (hge : O ≤ A ⊔ B) : False := by
  have hOA : O ≤ Subgroup.normalizer (A : Set X) := hge.trans (sup_le_normalizer_left hAB)
  rcases inf_eq_bot_or_le hO hOA with h | h
  · obtain ⟨a, ha, a', ha', hne⟩ := hAn
    have h1 : a ∈ O ⊓ A := ⟨hle (Subgroup.mem_sup_left ha), ha⟩
    have h2 : a' ∈ O ⊓ A := ⟨hle (Subgroup.mem_sup_left ha'), ha'⟩
    rw [h, Subgroup.mem_bot] at h1 h2
    exact hne (by rw [h1, h2])
  · obtain ⟨b, hb, b', hb', hne⟩ := hBn
    exact hne (hAB b (h (hle (Subgroup.mem_sup_right hb))) b' hb')

end CFSG.Quasithin.Vol2.Ch10.SecE
