module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsCube

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem cube_mod_three (r : ℕ) : r ^ 3 % 3 = r % 3 := by
  rw [Nat.pow_mod]
  have h : r % 3 < 3 := Nat.mod_lt r (by norm_num)
  interval_cases (r % 3) <;> rfl

theorem isTypeEpsCube_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    (h : IsTypeEpsCube Y) : IsTypeEpsCube X := by
  obtain ⟨p, f, hp, hp3, hf, h3, ⟨hq, ⟨ψ⟩⟩ | ⟨hq, hq2, ⟨ψ⟩⟩⟩ := h
  · exact ⟨p, f, hp, hp3, hf, h3, Or.inl ⟨hq, ⟨φ.trans ψ⟩⟩⟩
  · exact ⟨p, f, hp, hp3, hf, h3, Or.inr ⟨hq, hq2, ⟨φ.trans ψ⟩⟩⟩

theorem card_of_isTypeEpsCube {X : Type} [Group X] (h : IsTypeEpsCube X) :
    ∃ r : ℕ, 2 ≤ r ∧ ((r % 3 = 2 ∧ Nat.card X = r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 - 1))) ∨
      (r % 3 = 1 ∧ Nat.card X = r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 + 1)))) := by
  obtain ⟨p, f, hp, -, hf, ⟨g, rfl⟩, ⟨hq, ⟨ψ⟩⟩ | ⟨hq, -, ⟨ψ⟩⟩⟩ := h
  · have hpp : p.Prime := hp.out
    have hg : 1 ≤ g := by omega
    have hr2 : 2 ≤ p ^ g := hpp.two_le.trans (Nat.le_self_pow (by omega) p)
    have hqr : p ^ (3 * g) = (p ^ g) ^ 3 := by rw [← pow_mul, mul_comm]
    have hr3 : (p ^ g) % 3 = 2 := by rw [← cube_mod_three, ← hqr, hq]
    have hc := KS14.card_projSL_three_mul_gcd (GaloisField p (3 * g))
    rw [GaloisField.card p (3 * g) (by omega), ← Nat.card_congr ψ.toEquiv, hqr] at hc
    have hgcd : Nat.gcd 3 ((p ^ g) ^ 3 - 1) = 1 := by
      have h1 : 1 ≤ (p ^ g) ^ 3 := Nat.one_le_pow _ _ (by omega)
      have h2 : ((p ^ g) ^ 3 - 1) % 3 = 1 := by
        have := cube_mod_three (p ^ g)
        omega
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
    rw [hgcd, mul_one] at hc
    refine ⟨p ^ g, hr2, Or.inl ⟨hr3, ?_⟩⟩
    rw [hc]
    ring_nf
  · have hpp : p.Prime := hp.out
    have hg : 1 ≤ g := by omega
    have hr2 : 2 ≤ p ^ g := hpp.two_le.trans (Nat.le_self_pow (by omega) p)
    have hqr : p ^ (3 * g) = (p ^ g) ^ 3 := by rw [← pow_mul, mul_comm]
    have hr3 : (p ^ g) % 3 = 1 := by rw [← cube_mod_three, ← hqr, hq]
    have hc := KS14.card_projSU_three_mul_gcd p (3 * g) hf
    rw [← Nat.card_congr ψ.toEquiv, hqr] at hc
    have hgcd : Nat.gcd 3 ((p ^ g) ^ 3 + 1) = 1 := by
      have h2 : ((p ^ g) ^ 3 + 1) % 3 = 2 := by
        have := cube_mod_three (p ^ g)
        omega
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
    rw [hgcd, mul_one] at hc
    refine ⟨p ^ g, hr2, Or.inr ⟨hr3, ?_⟩⟩
    rw [hc]
    ring_nf

theorem ordCube_mono {r s : ℕ} (h : r ≤ s) :
    r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 - 1)) ≤ s ^ 9 * ((s ^ 6 - 1) * (s ^ 9 - 1)) := by
  have h6 : r ^ 6 ≤ s ^ 6 := Nat.pow_le_pow_left h 6
  have h9 : r ^ 9 ≤ s ^ 9 := Nat.pow_le_pow_left h 9
  exact Nat.mul_le_mul h9 (Nat.mul_le_mul (by omega) (by omega))

theorem le_card_of_isTypeEpsCube {X : Type} [Group X] (h : IsTypeEpsCube X) :
    16482816 ≤ Nat.card X := by
  obtain ⟨r, hr, ⟨-, hc⟩ | ⟨-, hc⟩⟩ := card_of_isTypeEpsCube h
  · rw [hc]
    exact (show 16482816 = 2 ^ 9 * ((2 ^ 6 - 1) * (2 ^ 9 - 1)) by norm_num) ▸ ordCube_mono hr
  · rw [hc]
    refine le_trans ((show 16482816 = 2 ^ 9 * ((2 ^ 6 - 1) * (2 ^ 9 - 1)) by norm_num) ▸
      ordCube_mono hr) ?_
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))

theorem not_isTypeEpsCube_of_dvd {X : Type} [Group X] {N B : ℕ} (hN : 0 < N)
    (hd : Nat.card X ∣ N) (hB : N < B ^ 9 * ((B ^ 6 - 1) * (B ^ 9 - 1)))
    (hL : ∀ r < B, 2 ≤ r → r % 3 = 2 → ¬ r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 - 1)) ∣ N)
    (hU : ∀ r < B, 2 ≤ r → r % 3 = 1 → ¬ r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 + 1)) ∣ N) :
    ¬ IsTypeEpsCube X := by
  intro h
  obtain ⟨r, hr, ⟨hr3, hc⟩ | ⟨hr3, hc⟩⟩ := card_of_isTypeEpsCube h
  · rw [hc] at hd
    have hrB : r < B := by
      by_contra hrB
      have h1 := Nat.le_of_dvd hN hd
      have h2 := ordCube_mono (not_lt.mp hrB)
      omega
    exact hL r hrB hr hr3 hd
  · rw [hc] at hd
    have hrB : r < B := by
      by_contra hrB
      have h1 := Nat.le_of_dvd hN hd
      have h2 := ordCube_mono (not_lt.mp hrB)
      have h3 : r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 - 1)) ≤ r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      omega
    exact hU r hrB hr hr3 hd

section NoCfg

variable {S : Type} [Group S] [Finite S]

theorem noCfgSEps_of_dvd
    (h : ∀ (X : Type) [Group X], Nat.card X ∣ Nat.card S → ¬ IsTypeEpsCube X) :
    NoCfgSEps S := fun _ _ K hc =>
  h (K ⧸ CFSG.pCore 2 K) ((Subgroup.card_quotient_dvd_card _).trans
    (Subgroup.card_subgroup_dvd_card K)) (isTypeEpsCube_of_cfgSEps hc)

theorem noCfgSEps_of_card {N B : ℕ} (hS : Nat.card S ∣ N) (hN : 0 < N)
    (hB : N < B ^ 9 * ((B ^ 6 - 1) * (B ^ 9 - 1)))
    (hL : ∀ r < B, 2 ≤ r → r % 3 = 2 → ¬ r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 - 1)) ∣ N)
    (hU : ∀ r < B, 2 ≤ r → r % 3 = 1 → ¬ r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 + 1)) ∣ N) :
    NoCfgSEps S :=
  noCfgSEps_of_dvd fun _ _ hd => not_isTypeEpsCube_of_dvd hN (hd.trans hS) hB hL hU

theorem noCfgSEps_of_card_lt (h : Nat.card S < 16482816) : NoCfgSEps S :=
  noCfgSEps_of_dvd fun _ _ hd hX => by
    have h1 := le_card_of_isTypeEpsCube hX
    have h2 := Nat.le_of_dvd Nat.card_pos hd
    omega

end NoCfg

end CFSG.RankThree.PartTwo.Sec4.RonanEps
