module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Counterexample

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S33

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

section Geom

variable (h : Counterexample p A θ)

include h

theorem isElemAbelian_of_le {B : Subgroup G} (hB : B ≤ A) : IsElemAbelian p B :=
  CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p h.hyp.elemAbelian hB

theorem exists_card_eq_pow_of_le {B : Subgroup G} (hB : B ≤ A) : ∃ j ≤ 3, Nat.card B = p ^ j := by
  have hdvd : Nat.card B ∣ p ^ 3 := h.hyp.card ▸ Subgroup.card_dvd_of_le hB
  exact (Nat.dvd_prime_pow h.hyp.prime).1 hdvd

theorem zpowers_mem_E1 {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Subgroup.zpowers a ∈ signalizerFunctorEk p 1 A :=
  zpowers_mem_signalizerFunctorEk_one h.hyp.prime h.hyp.elemAbelian ha ha1

theorem eq_zpowers_of_mem {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) {f : G}
    (hf : f ∈ F) (hf1 : f ≠ 1) : F = Subgroup.zpowers f := by
  have hcard := (zpowers_mem_E1 h (hF.1 hf) hf1).2
  have hle : Subgroup.zpowers f ≤ F := Subgroup.zpowers_le.mpr hf
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hF.2, hcard])).symm

theorem inf_eq_bot_of_ne_E1 {E F : Subgroup G} (hE : E ∈ signalizerFunctorEk p 1 A)
    (hF : F ∈ signalizerFunctorEk p 1 A) (hne : E ≠ F) : E ⊓ F = ⊥ := by
  refine inf_eq_bot_of_not_le h.hyp.prime (by rw [hF.2, pow_one]) fun hFE => hne ?_
  exact (Subgroup.eq_of_le_of_card_ge hFE (by rw [hE.2, hF.2])).symm

theorem sup_mem_E2_of_ne {E F : Subgroup G} (hE : E ∈ signalizerFunctorEk p 1 A)
    (hF : F ∈ signalizerFunctorEk p 1 A) (hne : E ≠ F) : E ⊔ F ∈ signalizerFunctorEk p 2 A := by
  have := sup_mem_Ek_succ h.hyp.elemAbelian hE hF (inf_eq_bot_of_ne_E1 h hE hF hne)
  simpa using this

theorem card_sup_mul_card_inf {H K : Subgroup G} (hH : H ≤ A) (hK : K ≤ A) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have hKel : IsElemAbelian p K := isElemAbelian_of_le h hK
  obtain ⟨F, hFK, -, hEF, hsup⟩ := exists_complement_containing h.hyp.prime hKel
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
  rw [hsup', card_sup_of_le_elemAbelian h.hyp.elemAbelian hH (hFK.trans hK) hdisj, ← hcardK]
  ring

theorem inf_mem_E1_of_ne_E2 {H K : Subgroup G} (hH : H ∈ signalizerFunctorEk p 2 A)
    (hK : K ∈ signalizerFunctorEk p 2 A) (hne : H ≠ K) :
    H ⊓ K ∈ signalizerFunctorEk p 1 A := by
  have hprod := card_sup_mul_card_inf h hH.1 hK.1
  rw [hH.2, hK.2] at hprod
  have hsupA : Nat.card ↥(H ⊔ K) ≤ p ^ 3 :=
    h.hyp.card ▸ Subgroup.card_le_of_le (sup_le hH.1 hK.1)
  have hHle : Nat.card H ≤ Nat.card ↥(H ⊔ K) := Subgroup.card_le_of_le le_sup_left
  have hne' : Nat.card ↥(H ⊔ K) ≠ p ^ 2 := by
    intro heq
    have hHK : H = H ⊔ K := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hH.2, heq])
    have hKH : K ≤ H := by rw [hHK]; exact le_sup_right
    exact hne (Subgroup.eq_of_le_of_card_ge hKH (by rw [hH.2, hK.2])).symm
  have hdvd : Nat.card ↥(H ⊔ K) ∣ p ^ 3 :=
    h.hyp.card ▸ Subgroup.card_dvd_of_le (sup_le hH.1 hK.1)
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow h.hyp.prime).1 hdvd
  have hj2 : j ≠ 2 := fun h2 => hne' (by rw [hjeq, h2])
  have hj3 : 2 ≤ j := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(H ⊔ K) ≤ p := by
      rw [hjeq]
      calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right h.hyp.prime.pos (by omega)
        _ = p := pow_one p
    have h1 : p ^ 2 ≤ p := le_trans (by rw [← hH.2]; exact hHle) this
    have : p < p ^ 2 := by nlinarith [h.hyp.prime.one_lt]
    omega
  have hj3' : j = 3 := by omega
  rw [hjeq, hj3'] at hprod
  refine ⟨inf_le_left.trans hH.1, ?_⟩
  have hp0 : 0 < p ^ 3 := pow_pos h.hyp.prime.pos 3
  have : Nat.card ↥(H ⊓ K) = p := by
    have h2 : p ^ 3 * Nat.card ↥(H ⊓ K) = p ^ 3 * p := by rw [hprod]; ring
    rw [Nat.eq_of_mul_eq_mul_left hp0 h2]
  rw [this, pow_one]

theorem eq_of_le_of_ne_top {B Q : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) (hQ : Q ≤ A)
    (hBQ : B ≤ Q) (hQA : Q ≠ A) : Q = B := by
  obtain ⟨j, hj, hjeq⟩ := exists_card_eq_pow_of_le h hQ
  have hle : Nat.card B ≤ Nat.card Q := Subgroup.card_le_of_le hBQ
  rw [hB.2, hjeq] at hle
  have h2 : 2 ≤ j := (Nat.pow_le_pow_iff_right h.hyp.prime.one_lt).mp hle
  have hj3 : j ≠ 3 := by
    intro hj3
    apply hQA
    exact Subgroup.eq_of_le_of_card_ge hQ (by rw [h.hyp.card, hjeq, hj3])
  have : j = 2 := by omega
  exact (Subgroup.eq_of_le_of_card_ge hBQ (by rw [hB.2, hjeq, this])).symm

theorem sup_zpowers_eq_top_of_not_mem {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A)
    {b : G} (hb : b ∈ A) (hbB : b ∉ B) : B ⊔ Subgroup.zpowers b = A := by
  by_contra hne
  have hbne : b ≠ 1 := fun h1 => hbB (h1 ▸ one_mem _)
  have hsupA : B ⊔ Subgroup.zpowers b ≤ A := sup_le hB.1 (Subgroup.zpowers_le.mpr hb)
  have heq := eq_of_le_of_ne_top h hB hsupA le_sup_left hne
  exact hbB (heq ▸ (le_sup_right (a := B) (Subgroup.mem_zpowers b)))

theorem exists_mem_not_mem_zpowers {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) {u : G}
    (hu : u ∈ A) : ∃ b ∈ B, b ∉ Subgroup.zpowers u := by
  by_contra hcon
  push Not at hcon
  have hle : B ≤ Subgroup.zpowers u := fun b hb => hcon b hb
  have h1 := Subgroup.card_le_of_le hle
  have hord : orderOf u ≤ p :=
    Nat.le_of_dvd h.hyp.prime.pos (orderOf_dvd_of_pow_eq_one (h.hyp.elemAbelian.2 u hu))
  rw [hB.2, Nat.card_zpowers] at h1
  have : p < p ^ 2 := by nlinarith [h.hyp.prime.one_lt]
  omega

end Geom

end Sec6S33

end CFSG.SignalizerFunctorTheorem.McBride.Near
