module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S153LComp
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

section Count

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem card_sup_mul_card_inf_of_le_normalizer' {A B : Subgroup Γ}
    (hB : B ≤ Subgroup.normalizer (A : Set Γ)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := B2F.relIndex_sup_eq_of_le_normalizer' hB
  have h2 := Subgroup.relIndex_mul_card A (B ⊔ A)
  have h3 := Subgroup.relIndex_mul_card A B
  have h4 : A ⊓ (B ⊔ A) = A := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [sup_comm] at h2
  rw [← h2, ← h3, inf_comm]
  ring

omit [Finite Γ] in
theorem card_sup_eq_mul_of_commute {A B : Subgroup Γ} (hinf : A ⊓ B = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have h := B2F.card_sup_mul_card_inf_of_commute hc
  rwa [hinf, Subgroup.card_bot, mul_one] at h

theorem card_sylow_eq_two_pow {S H : Subgroup Γ} (hS : IsSylowTwoOf S H) :
    Nat.card S = 2 ^ (Nat.card H).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsSylowIn.card_eq ⟨hS.1, hS.2.1, hS.2.2⟩

omit [Finite Γ] in
theorem normal_left_of_commute {G₁ G₂ J : Subgroup Γ} (hsup : G₁ ⊔ G₂ = J)
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) :
    J ≤ Subgroup.normalizer (G₁ : Set Γ) := by
  rw [← hsup]
  refine sup_le Subgroup.le_normalizer fun b hb => ?_
  refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
  · rw [← hc x hx b hb, mul_inv_cancel_right]
    exact hx
  · have h := hc x hx b hb
    have e : b⁻¹ * x * b = x := by rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]
    exact hx

theorem card_sylow_eq_mul {G₁ G₂ J S : Subgroup Γ} (hsup : G₁ ⊔ G₂ = J) (hinf : G₁ ⊓ G₂ = ⊥)
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hS : IsSylowTwoOf S J) :
    Nat.card S = Nat.card ↥(S ⊓ G₁) * Nat.card ↥(S ⊓ G₂) := by
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
  have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
  have hS₁ := A4.isSylowTwoOf_inf_normal hS hG₁J (normal_left_of_commute hsup hc)
  have hS₂ := A4.isSylowTwoOf_inf_normal hS hG₂J
    (normal_left_of_commute (by rw [sup_comm]; exact hsup) hc')
  rw [card_sylow_eq_two_pow hS, card_sylow_eq_two_pow hS₁, card_sylow_eq_two_pow hS₂,
    ← hsup, card_sup_eq_mul_of_commute hinf hc, Nat.factorization_mul Nat.card_pos.ne'
      Nat.card_pos.ne', Finsupp.add_apply, pow_add]

theorem exists_order_three_normalizer_of_swap {G₁ G₂ J S L : Subgroup Γ} {t : Γ}
    (hsup : G₁ ⊔ G₂ = J) (hinf : G₁ ⊓ G₂ = ⊥) (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hS : IsSylowTwoOf S J) (hLJ : L ≤ J) (hSL : S ≤ Subgroup.normalizer (L : Set Γ))
    (hLidx : Nat.card ↥L ≤ 3 * Nat.card ↥(L ⊓ S))
    (htS : t ∈ Subgroup.normalizer (S : Set Γ)) (htL : t ∈ Subgroup.normalizer (L : Set Γ))
    (ht : G₁.map (MulAut.conj t).toMonoidHom = G₂) {l : Γ} (hl : l ∈ L)
    (hl3 : orderOf l = 3) :
    ∃ g ∈ G₁, orderOf g = 3 ∧ g ∈ Subgroup.normalizer ((S ⊓ G₁ : Subgroup Γ) : Set Γ) := by
  have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
  have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hJ₁ := normal_left_of_commute hsup hc
  set P : Subgroup Γ := L ⊔ S with hP
  have hPJ : P ≤ J := sup_le hLJ hS.1
  have hcardP : Nat.card ↥P ≤ 3 * Nat.card S := by
    have h := card_sup_mul_card_inf_of_le_normalizer' hSL
    have hpos : 0 < Nat.card ↥(L ⊓ S) := Nat.card_pos
    have h' : Nat.card ↥P * Nat.card ↥(L ⊓ S) ≤ (3 * Nat.card S) * Nat.card ↥(L ⊓ S) := by
      rw [h]
      calc Nat.card ↥L * Nat.card ↥S ≤ (3 * Nat.card ↥(L ⊓ S)) * Nat.card ↥S :=
            Nat.mul_le_mul_right _ hLidx
        _ = (3 * Nat.card S) * Nat.card ↥(L ⊓ S) := by ring
    exact Nat.le_of_mul_le_mul_right h' hpos
  have htmap : ∀ X : Subgroup Γ, t ∈ Subgroup.normalizer (X : Set Γ) →
      X.map (MulAut.conj t).toMonoidHom = X := fun X hX =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hX
  have htP : P.map (MulAut.conj t).toMonoidHom = P := by
    rw [hP, Subgroup.map_sup, htmap L htL, htmap S htS]
  have hinj : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
  have hA : (P ⊓ G₁).map (MulAut.conj t).toMonoidHom = P ⊓ G₂ := by
    rw [Subgroup.map_inf_eq _ _ _ hinj, htP, ht]
  have hS₁₂ : (S ⊓ G₁).map (MulAut.conj t).toMonoidHom = S ⊓ G₂ := by
    rw [Subgroup.map_inf_eq _ _ _ hinj, htmap S htS, ht]
  have hcardA : Nat.card ↥(P ⊓ G₁) = Nat.card ↥(P ⊓ G₂) := by
    rw [← hA]
    exact (Nat.card_congr ((P ⊓ G₁).equivMapOfInjective _ hinj).toEquiv)
  have hcardS : Nat.card ↥(S ⊓ G₁) = Nat.card ↥(S ⊓ G₂) := by
    rw [← hS₁₂]
    exact (Nat.card_congr ((S ⊓ G₁).equivMapOfInjective _ hinj).toEquiv)
  have hS₁A : S ⊓ G₁ ≤ P ⊓ G₁ := inf_le_inf_right _ le_sup_right
  have hS₂B : S ⊓ G₂ ≤ P ⊓ G₂ := inf_le_inf_right _ le_sup_right
  obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le hS₁A
  obtain ⟨b, hb⟩ := Subgroup.card_dvd_of_le hS₂B
  have hab : a = b := by
    have hpos : 0 < Nat.card ↥(S ⊓ G₁) := Nat.card_pos
    rw [hcardA, hb, ← hcardS] at ha
    exact (Nat.eq_of_mul_eq_mul_left hpos ha).symm
  have hle : Nat.card ↥(P ⊓ G₁) * Nat.card ↥(P ⊓ G₂) ≤ Nat.card ↥P := by
    have h1 : (P ⊓ G₁) ⊓ (P ⊓ G₂) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [← hinf]
      exact ⟨hx.1.2, hx.2.2⟩
    have h2 := card_sup_eq_mul_of_commute h1 fun x hx y hy => hc x hx.2 y hy.2
    rw [← h2]
    exact Subgroup.card_le_of_le (sup_le inf_le_left inf_le_left)
  have hSS := card_sylow_eq_mul hsup hinf hc hS
  have ha1 : a = 1 := by
    have hle' := hle.trans hcardP
    rw [ha, hb, hSS, ← hab] at hle'
    replace hle := hle'
    have hpos₁ : 0 < Nat.card ↥(S ⊓ G₁) := Nat.card_pos
    have hpos₂ : 0 < Nat.card ↥(S ⊓ G₂) := Nat.card_pos
    have h3 : a * a ≤ 3 := by
      have : Nat.card ↥(S ⊓ G₁) * a * (Nat.card ↥(S ⊓ G₂) * a) =
          (a * a) * (Nat.card ↥(S ⊓ G₁) * Nat.card ↥(S ⊓ G₂)) := by ring
      rw [this] at hle
      exact Nat.le_of_mul_le_mul_right hle (Nat.mul_pos hpos₁ hpos₂)
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [mul_zero] at ha
      exact Nat.card_pos.ne' ha
    rcases Nat.lt_or_ge a 2 with h | h
    · omega
    · nlinarith
  have hA₁ : P ⊓ G₁ = S ⊓ G₁ :=
    (Subgroup.eq_of_le_of_card_ge hS₁A (by rw [ha, ha1, mul_one])).symm
  have hB₂ : P ⊓ G₂ = S ⊓ G₂ :=
    (Subgroup.eq_of_le_of_card_ge hS₂B (by rw [hb, ← hab, ha1, mul_one])).symm
  obtain ⟨g₁, hg₁, g₂, hg₂, hl12⟩ := S153L.comp_exists_mul hc (hsup ▸ hLJ hl)
  have hlP : l ∈ P := le_sup_left (a := L) hl
  have hlN : l ∈ Subgroup.normalizer ((S ⊓ G₁ : Subgroup Γ) : Set Γ) := by
    rw [← hA₁]
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · exact ⟨P.mul_mem (P.mul_mem hlP hx.1) (P.inv_mem hlP),
        (Subgroup.mem_normalizer_iff.mp (hJ₁ (hPJ hlP)) x).mp hx.2⟩
    · have hli : l⁻¹ ∈ J := J.inv_mem (hPJ hlP)
      have := (Subgroup.mem_normalizer_iff.mp (hJ₁ hli) x).mp hx.2
      rw [inv_inv] at this
      exact ⟨P.mul_mem (P.mul_mem (P.inv_mem hlP) hx.1) hlP, this⟩
  have hconj : ∀ x ∈ G₁, l * x * l⁻¹ = g₁ * x * g₁⁻¹ := by
    intro x hx
    rw [hl12]
    have h := hc x hx g₂ hg₂
    calc g₁ * g₂ * x * (g₁ * g₂)⁻¹ = g₁ * (g₂ * x) * g₂⁻¹ * g₁⁻¹ := by group
      _ = g₁ * (x * g₂) * g₂⁻¹ * g₁⁻¹ := by rw [h]
      _ = g₁ * x * g₁⁻¹ := by group
  have hg₁N : g₁ ∈ Subgroup.normalizer ((S ⊓ G₁ : Subgroup Γ) : Set Γ) := by
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · rw [← hconj x hx.2]
      exact (Subgroup.mem_normalizer_iff.mp hlN x).mp hx
    · have hconj' : l⁻¹ * x * l = g₁⁻¹ * x * g₁ := by
        have h1 := hconj (g₁⁻¹ * x * g₁) (G₁.mul_mem (G₁.mul_mem (G₁.inv_mem hg₁) hx.2) hg₁)
        have e : g₁ * (g₁⁻¹ * x * g₁) * g₁⁻¹ = x := by group
        rw [e] at h1
        calc l⁻¹ * x * l = l⁻¹ * (l * (g₁⁻¹ * x * g₁) * l⁻¹) * l := by rw [h1]
          _ = g₁⁻¹ * x * g₁ := by group
      rw [← hconj']
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlN) x).mp hx
      rwa [inv_inv] at this
  have hg₁3 : g₁ ^ 3 = 1 := by
    have h1 : l ^ 3 = 1 := by rw [← hl3]; exact pow_orderOf_eq_one l
    have hcomm : Commute g₁ g₂ := hc g₁ hg₁ g₂ hg₂
    rw [hl12, hcomm.mul_pow] at h1
    have h2 : g₁ ^ 3 = (g₂ ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : g₁ ^ 3 ∈ G₁ ⊓ G₂ := ⟨G₁.pow_mem hg₁ 3, h2 ▸ G₂.inv_mem (G₂.pow_mem hg₂ 3)⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact h3
  have hg₁1 : g₁ ≠ 1 := by
    rintro rfl
    rw [one_mul] at hl12
    have hlS : l ∈ S ⊓ G₂ := by
      rw [← hB₂]
      exact ⟨hlP, hl12 ▸ hg₂⟩
    obtain ⟨k, hk⟩ := hS.2.1 ⟨l, hlS.1⟩
    have h1 : l ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : 3 ∣ 2 ^ k := hl3 ▸ orderOf_dvd_of_pow_eq_one h1
    have h3 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h2
    omega
  exact ⟨g₁, hg₁, orderOf_eq_prime hg₁3 hg₁1, hg₁N⟩

end Count

end CFSG.Quasithin.H13.A5
