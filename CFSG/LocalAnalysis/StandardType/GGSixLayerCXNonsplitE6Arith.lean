module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Cover
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule

namespace E6Nonsplit

section Row

theorem not_dvd_card_field_of_ne_two {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

theorem exists_dvd_phi_of_dvd_ordE6 {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) (hq : 1 ≤ q)
    (hdvd : p ∣ CFSG.Open.ordE6 q) :
    ∃ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 8 ∨ m = 9 ∨ m = 12) ∧
      (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) := by
  have h1 : p ∣ CFSG.SeitzReduction.E6Pilot.numE6 q :=
    hdvd.trans (CFSG.SeitzReduction.E6Pilot.ordE6_dvd_numE6 q)
  unfold CFSG.SeitzReduction.E6Pilot.numE6 at h1
  have hD : ∃ d ∈ ([2, 5, 6, 8, 9, 12] : List ℕ), p ∣ q ^ d - 1 := by
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
            · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
              · exact absurd (hp.dvd_of_dvd_pow h) hpq
              · exact ⟨12, by simp, h⟩
            · exact ⟨9, by simp, h⟩
          · exact ⟨8, by simp, h⟩
        · exact ⟨6, by simp, h⟩
      · exact ⟨5, by simp, h⟩
    · exact ⟨2, by simp, h⟩
  obtain ⟨m, hm, hpm⟩ := exists_mem_row_of_dvd_pow_sub_one hp hq
    (D := [2, 5, 6, 8, 9, 12]) (by decide)
    (row := ({1, 2, 3, 4, 5, 6, 8, 9, 12} : Finset ℕ)) (by decide) hD
  exact ⟨m, by simpa using hm, hpm⟩

theorem dvd_sub_one_of_dvd_phiOne {p q : ℕ} (hq : 1 ≤ q)
    (h : (p : ℤ) ∣ (exhaustionPhi 1).eval (q : ℤ)) : p ∣ q - 1 := by
  have e : (exhaustionPhi 1).eval (q : ℤ) = ((q - 1 : ℕ) : ℤ) := by
    simp [exhaustionPhi, Nat.cast_sub hq]
  rw [e] at h
  exact Int.natCast_dvd_natCast.1 h

theorem dvd_add_one_of_dvd_phiTwo {p q : ℕ}
    (h : (p : ℤ) ∣ (exhaustionPhi 2).eval (q : ℤ)) : p ∣ q + 1 := by
  have e : (exhaustionPhi 2).eval (q : ℤ) = ((q + 1 : ℕ) : ℤ) := by
    simp [exhaustionPhi]
  rw [e] at h
  exact Int.natCast_dvd_natCast.1 h

theorem dvd_phiThree_nat {p q : ℕ} (h : (p : ℤ) ∣ (exhaustionPhi 3).eval (q : ℤ)) :
    p ∣ q ^ 2 + q + 1 := by
  have e : (exhaustionPhi 3).eval (q : ℤ) = ((q ^ 2 + q + 1 : ℕ) : ℤ) := by
    simp [exhaustionPhi]
  rw [e] at h
  exact Int.natCast_dvd_natCast.1 h

theorem dvd_phiFive_nat {p q : ℕ} (h : (p : ℤ) ∣ (exhaustionPhi 5).eval (q : ℤ)) :
    p ∣ q ^ 4 + q ^ 3 + q ^ 2 + q + 1 := by
  have e : (exhaustionPhi 5).eval (q : ℤ) = ((q ^ 4 + q ^ 3 + q ^ 2 + q + 1 : ℕ) : ℤ) := by
    simp [exhaustionPhi]
  rw [e] at h
  exact Int.natCast_dvd_natCast.1 h

end Row

section Group

theorem exists_dvd_phi_of_dvd_card_E6 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K) (hdvd : p ∣ Nat.card (adjointGroup .E6 K)) :
    ∃ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 8 ∨ m = 9 ∨ m = 12) ∧
      (p : ℤ) ∣ (exhaustionPhi m).eval (Nat.card K : ℤ) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6] at hdvd
  exact exists_dvd_phi_of_dvd_ordE6 hp hpK Nat.card_pos hdvd

end Group

end E6Nonsplit

end CFSG.StandardType
