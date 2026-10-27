module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Basic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_card_eq_pow_of_le (h : Counterexample p A θ) {B : Subgroup G} (hB : B ≤ A) :
    ∃ j ≤ 3, Nat.card B = p ^ j := by
  have hdvd : Nat.card B ∣ p ^ 3 := h.card ▸ Subgroup.card_dvd_of_le hB
  exact (Nat.dvd_prime_pow h.prime).1 hdvd

theorem ne_bot_of_mem_E1 (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) : F ≠ ⊥ := by
  rintro rfl
  have h1 := hF.2
  rw [Subgroup.card_bot, pow_one] at h1
  exact h.prime.one_lt.ne h1

theorem zpowers_mem_E1 (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Subgroup.zpowers a ∈ signalizerFunctorEk p 1 A :=
  zpowers_mem_signalizerFunctorEk_one h.prime h.elemAbelian ha ha1

theorem line_eq_zpowers (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) {f : G} (hf : f ∈ F) (hf1 : f ≠ 1) :
    F = Subgroup.zpowers f := by
  have hcard := (h.zpowers_mem_E1 (hF.1 hf) hf1).2
  have hle : Subgroup.zpowers f ≤ F := Subgroup.zpowers_le.mpr hf
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hF.2, hcard])).symm

theorem exists_ne_one_of_mem_E1 (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) : ∃ f ∈ F, f ≠ 1 := by
  obtain ⟨a, -, ha1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF
  exact ⟨a, Subgroup.mem_zpowers a, ha1⟩

theorem thetaOf_line (h : Counterexample p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) {f : G} (hf : f ∈ F) (hf1 : f ≠ 1) :
    thetaOf θ F = θ f := by
  rw [h.line_eq_zpowers hF hf hf1]
  exact h.isFunctor.thetaOf_zpowers (hF.1 hf) hf1

theorem inf_eq_bot_of_ne_E1 (h : Counterexample p A θ) {E F : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hF : F ∈ signalizerFunctorEk p 1 A) (hne : E ≠ F) :
    E ⊓ F = ⊥ := by
  refine inf_eq_bot_of_not_le h.prime (by rw [hF.2, pow_one]) fun hFE => hne ?_
  exact (Subgroup.eq_of_le_of_card_ge hFE (by rw [hE.2, hF.2])).symm

theorem sup_mem_E2_of_ne (h : Counterexample p A θ) {E F : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hF : F ∈ signalizerFunctorEk p 1 A) (hne : E ≠ F) :
    E ⊔ F ∈ signalizerFunctorEk p 2 A := by
  have := sup_mem_Ek_succ h.elemAbelian hE hF (h.inf_eq_bot_of_ne_E1 hE hF hne)
  simpa using this

theorem card_sup_mul_card_inf (h : Counterexample p A θ) {H K : Subgroup G} (hH : H ≤ A)
    (hK : K ≤ A) : Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have hKel : IsElemAbelian p K := h.isElemAbelian_of_le hK
  obtain ⟨F, hFK, -, hEF, hsup⟩ := exists_complement_containing h.prime hKel
    (E := H ⊓ K) (R := ⊥) inf_le_right bot_le (inf_bot_eq _)
  have hcardK : Nat.card ↥(H ⊓ K) * Nat.card F = Nat.card K :=
    card_mul_card_complement hKel inf_le_right hFK hEF hsup
  have hdisj : H ⊓ F = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ (H ⊓ K) ⊓ F := ⟨⟨hx.1, hFK hx.2⟩, hx.2⟩
    rwa [hEF] at this
  have hsup' : H ⊔ K = H ⊔ F := by
    calc H ⊔ K = H ⊔ ((H ⊓ K) ⊔ F) := by rw [hsup]
      _ = (H ⊔ (H ⊓ K)) ⊔ F := by rw [sup_assoc]
      _ = H ⊔ F := by rw [sup_inf_self]
  rw [hsup', card_sup_of_le_elemAbelian h.elemAbelian hH (hFK.trans hK) hdisj, ← hcardK]
  ring

theorem inf_mem_E1_of_ne_E2 (h : Counterexample p A θ) {H K : Subgroup G}
    (hH : H ∈ signalizerFunctorEk p 2 A) (hK : K ∈ signalizerFunctorEk p 2 A) (hne : H ≠ K) :
    H ⊓ K ∈ signalizerFunctorEk p 1 A := by
  have hprod := h.card_sup_mul_card_inf hH.1 hK.1
  rw [hH.2, hK.2] at hprod
  have hsupA : Nat.card ↥(H ⊔ K) ≤ p ^ 3 := h.card ▸ Subgroup.card_le_of_le (sup_le hH.1 hK.1)
  have hHle : Nat.card H ≤ Nat.card ↥(H ⊔ K) := Subgroup.card_le_of_le le_sup_left
  have hne' : Nat.card ↥(H ⊔ K) ≠ p ^ 2 := by
    intro heq
    have hHK : H = H ⊔ K := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hH.2, heq])
    have hKH : K ≤ H := by rw [hHK]; exact le_sup_right
    exact hne (Subgroup.eq_of_le_of_card_ge hKH (by rw [hH.2, hK.2])).symm
  have hdvd : Nat.card ↥(H ⊔ K) ∣ p ^ 3 := h.card ▸ Subgroup.card_dvd_of_le (sup_le hH.1 hK.1)
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow h.prime).1 hdvd
  have hj2 : j ≠ 2 := fun h2 => hne' (by rw [hjeq, h2])
  have hj3 : 2 ≤ j := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(H ⊔ K) ≤ p := by
      rw [hjeq]
      calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right h.prime.pos (by omega)
        _ = p := pow_one p
    have h1 : p ^ 2 ≤ p := le_trans (by rw [← hH.2]; exact hHle) this
    have : p < p ^ 2 := by nlinarith [h.prime.one_lt]
    omega
  have hj3' : j = 3 := by omega
  rw [hjeq, hj3'] at hprod
  refine ⟨inf_le_left.trans hH.1, ?_⟩
  have hp0 : 0 < p ^ 3 := pow_pos h.prime.pos 3
  have : Nat.card ↥(H ⊓ K) = p := by
    have h2 : p ^ 3 * Nat.card ↥(H ⊓ K) = p ^ 3 * p := by rw [hprod]; ring
    rw [Nat.eq_of_mul_eq_mul_left hp0 h2]
  rw [this, pow_one]

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
