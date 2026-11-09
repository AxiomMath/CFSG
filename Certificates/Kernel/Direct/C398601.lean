module

public import Certificates.Data.TwinPerpV3A6dNoFive
import all Certificates.Data.TwinPerpV3A6dNoFive
import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CertificateChecks.KernelDirect.C398601

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d CFSG.ClassicalInvolution.Q3.AE

theorem supp_card_five {n : ℕ} (hn : n < 10) (σ : Equiv.Perm (Fin n)) (h5 : σ ^ 5 = 1)
    (h1 : σ ≠ 1) : σ.support.card = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have ho : orderOf σ = 5 := orderOf_eq_prime h5 h1
  have hc : σ.IsCycle := Equiv.Perm.isCycle_of_prime_order' (by rw [ho]; exact Nat.prime_five)
    (by rw [ho, Fintype.card_fin]; omega)
  rw [← hc.orderOf, ho]

theorem fix_card_add {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun y => σ y = y).card + σ.support.card = n := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun y : Fin n => σ y = y)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hs : σ.support = Finset.univ.filter fun y => ¬ σ y = y := by
    ext y
    simp
  rw [hs]
  exact h

theorem false_of_fix {n : ℕ} (P : List (Finset (Fin n))) (σ : Equiv.Perm (Fin n))
    (hp : ∀ s ∈ P, s.map σ.toEmbedding ∈ P) (Fx : Fin n → Prop) (hF : ∀ y, σ y = y ↔ Fx y)
    (s : Finset (Fin n)) (hs : s ∈ P) (hFs : ∀ y, Fx y → y ∈ s) (x : Fin n) (hx : x ∈ s)
    (hxF : ¬ Fx x) (huniq : ∀ t ∈ P, (∀ y, Fx y → y ∈ t) → t = s)
    (hcov : ∀ y ∈ s, Fx y ∨ y = x) : False := by
  have h1 : s.map σ.toEmbedding = s :=
    huniq _ (hp s hs) fun f hf => Finset.mem_map.2 ⟨f, hFs f hf, (hF f).2 hf⟩
  have h2 : σ x ∈ s := by
    rw [← h1]
    exact Finset.mem_map.2 ⟨x, hx, rfl⟩
  rcases hcov _ h2 with h | h
  · exact hxF ((hF x).1 (σ.injective ((hF _).2 h)))
  · exact hxF ((hF x).1 h)

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
theorem planes_three : ∀ p q r : Fin 8, p ≠ q → p ≠ r → q ≠ r → ∃ s ∈ affinePlanes,
    p ∈ s ∧ q ∈ s ∧ r ∈ s ∧ ∃ x ∈ s, x ≠ p ∧ x ≠ q ∧ x ≠ r ∧
      (∀ t ∈ affinePlanes, p ∈ t → q ∈ t → r ∈ t → t = s) ∧
      ∀ y ∈ s, (y = p ∨ y = q ∨ y = r) ∨ y = x := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
theorem lines_two : ∀ p q : Fin 7, p ≠ q → ∃ s ∈ fanoLines,
    p ∈ s ∧ q ∈ s ∧ ∃ x ∈ s, x ≠ p ∧ x ≠ q ∧
      (∀ t ∈ fanoLines, p ∈ t → q ∈ t → t = s) ∧ ∀ y ∈ s, (y = p ∨ y = q) ∨ y = x := by
  decide +kernel

theorem noFiveCheck_eq_true : noFiveCheck () = true := by
  simp only [noFiveCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun σ h5 h1 hpres => ?_, fun σ h5 h1 hpres => ?_⟩
  · have hc := fix_card_add σ
    rw [supp_card_five (by norm_num) σ h5 h1] at hc
    obtain ⟨p, q, r, hpq, hpr, hqr, he⟩ :=
      (Finset.card_eq_three (s := Finset.univ.filter fun y => σ y = y)).1 (by omega)
    have hF : ∀ y, σ y = y ↔ (y = p ∨ y = q ∨ y = r) := fun y => by
      simpa using Finset.ext_iff.1 he y
    obtain ⟨s, hs, hp', hq', hr', x, hx, hxp, hxq, hxr, hu, hcov⟩ := planes_three p q r hpq hpr hqr
    refine false_of_fix affinePlanes σ (fun s hs => (hpres s hs).1) _ hF s hs ?_ x hx ?_ ?_ hcov
    · rintro y (rfl | rfl | rfl) <;> assumption
    · rintro (h | h | h) <;> contradiction
    · exact fun t ht h => hu t ht (h _ (Or.inl rfl)) (h _ (Or.inr (Or.inl rfl)))
        (h _ (Or.inr (Or.inr rfl)))
  · have hc := fix_card_add σ
    rw [supp_card_five (by norm_num) σ h5 h1] at hc
    obtain ⟨p, q, hpq, he⟩ :=
      (Finset.card_eq_two (s := Finset.univ.filter fun y => σ y = y)).1 (by omega)
    have hF : ∀ y, σ y = y ↔ (y = p ∨ y = q) := fun y => by
      simpa using Finset.ext_iff.1 he y
    obtain ⟨s, hs, hp', hq', x, hx, hxp, hxq, hu, hcov⟩ := lines_two p q hpq
    refine false_of_fix fanoLines σ (fun s hs => (hpres s hs).1) _ hF s hs ?_ x hx ?_ ?_ hcov
    · rintro y (rfl | rfl) <;> assumption
    · rintro (h | h) <;> contradiction
    · exact fun t ht h => hu t ht (h _ (Or.inl rfl)) (h _ (Or.inr rfl))

end CertificateChecks.KernelDirect.C398601
