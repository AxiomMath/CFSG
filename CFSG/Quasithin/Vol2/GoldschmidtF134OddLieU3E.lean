module

public import CFSG.Quasithin.Vol2.F134LieU3
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieBridge

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin.F134.LieU3 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem not_dvd_pow_mul_cube {q p a : ℕ} (hq : 4 ≤ q) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ q ^ 3 + 1 ∣ p ^ a * q ^ 3 := by
  intro hdvd
  have hcop : (q ^ 3 + 1).Coprime (q ^ 3) := Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have h1 : q ^ 3 + 1 ∣ p ^ a := hcop.dvd_of_dvd_mul_right hdvd
  have hf : q ^ 3 + 1 = (q + 1) * ((q + 1) * (q - 2) + 3) := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hd1 : q + 1 ∣ p ^ a := (hf ▸ Dvd.intro _ rfl : q + 1 ∣ q ^ 3 + 1).trans h1
  have hd2 : (q + 1) * (q - 2) + 3 ∣ p ^ a :=
    (hf ▸ Dvd.intro_left _ rfl : (q + 1) * (q - 2) + 3 ∣ q ^ 3 + 1).trans h1
  have hpd : ∀ d : ℕ, 1 < d → d ∣ p ^ a → p ∣ d := by
    intro d hd hdp
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdp
    exact dvd_pow_self p (fun h0 => by simp [h0] at hd)
  have hpq := hpd (q + 1) (by omega) hd1
  have hpr := hpd _ (by nlinarith) hd2
  have h3 : p ∣ 3 := (Nat.dvd_add_right (hpq.mul_right (q - 2))).mp hpr
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
  omega

theorem psu3Even_noPExt (n : ℕ) :
    NoPExt fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 n := by
  intro X _ _ hX p a hp hp5 ha S H Q hS2 hSi hSH hQH hH hQ hQe
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hq : 4 ≤ 2 ^ n := by
    obtain ⟨-, hn1, -, hne⟩ := hX.1
    have hn : 2 ≤ n := by
      by_contra hlt
      obtain rfl : n = 1 := by omega
      exact hne rfl
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨K, _, h, Φ, hΦ, hrange, hTU⟩ := exists_perm_comap_rkOneUStar_eq hX (hS2.toSylow hSi)
  replace hTU : (rkOneUStar h).comap Φ = S := hTU
  have hcardS : Nat.card S = (2 ^ n) ^ 3 := by
    rw [← hTU, ← Subgroup.card_map_of_injective hΦ, Subgroup.map_comap_eq, hrange,
      inf_eq_right.2 (rkOneUStar_le_rkOneG h), card_rkOneUStar h]
  have hUH : rkOneUStar h ≤ H.map Φ := by
    intro x hx
    have hx' : x ∈ Φ.range := by
      rw [hrange]
      exact rkOneUStar_le_rkOneG h hx
    obtain ⟨y, rfl⟩ := hx'
    have hy : y ∈ (rkOneUStar h).comap Φ := hx
    rw [hTU] at hy
    exact ⟨y, hSH hy, rfl⟩
  have hcardH : Nat.card (H.map Φ) = p ^ a * (2 ^ n) ^ 3 := by
    rw [Subgroup.card_map_of_injective hΦ, hH, hcardS]
  have hfix := le_stabilizer_infL_of_not_dvd h hUH (by
    rw [hcardH]
    exact not_dvd_pow_mul_cube hq hp hp5)
  have hQinf : Q.map Φ ≤ rkOneGInf h := fun x hx =>
    ⟨hrange ▸ Subgroup.map_le_range Φ _ hx, hfix (Subgroup.map_mono hQH hx)⟩
  have hQcard : Nat.card (Q.map Φ) = p ^ a := by
    rw [Subgroup.card_map_of_injective hΦ, hQ]
  have hcyc : IsCyclic (Q.map Φ) := isCyclic_of_le_rkOneGInf h hQinf (by
    rw [hQcard]
    intro h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)
    omega)
  have hcycQ : IsCyclic Q :=
    isCyclic_of_surjective (Q.equivMapOfInjective Φ hΦ).symm.toMonoidHom
      (Q.equivMapOfInjective Φ hΦ).symm.surjective
  exact not_isCyclic_of_card_pow (by omega) hQ hQe hcycQ

theorem psu3Even_simple (n : ℕ) :
    NoOddCfg fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 n :=
  noOddCfg_of_noPExt (psu3Even_noPExt n)

theorem liePsu3Even : LiePsu3Even := fun n =>
  noOddConfigQ_of_noOddCfg (isoInvariant_stated .PSU 3 2 n) (psu3Even_simple n)

end CFSG.Quasithin.H13.NQCore
