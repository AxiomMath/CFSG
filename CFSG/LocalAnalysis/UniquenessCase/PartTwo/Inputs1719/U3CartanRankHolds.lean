module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixAFull
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientBridge
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXU3P
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem k_U3CartanRank_holds :
    S17.K_U3CartanRank := by
  intro X _ _ n p hX hp hpdvd hcond S hS
  have hn2 : 2 ≤ n := s13_two_le_of_isU3 hX.2
  have hperf : Group.IsPerfect (↥(⊤ : Subgroup X)) := by
    rw [Group.IsPerfect.top_iff]
    exact Group.isPerfect_def.mpr hX.1.1
  let eTop : ↥(⊤ : Subgroup X) ≃* X := Subgroup.topEquiv
  let eQ : (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) ≃*
      (X ⧸ Subgroup.center X) :=
    QuotientGroup.congr _ _ eTop (Subgroup.map_center_eq eTop)
  have hXPSU : CFSG.Quasithin.IsPSU 3 2 n (X ⧸ Subgroup.center X) :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hX.2
  have hPSU : CFSG.Quasithin.IsPSU 3 2 n
      (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) :=
    CFSG.Quasithin.IsPSU.of_mulEquiv eQ.symm hXPSU
  obtain ⟨-, hcard, -, -, -⟩ :=
    CFSG.Quasithin.H13.P31X.u3BorelFacts_holds n hn2 X (⊤ : Subgroup X) S hperf hPSU hS
  rw [top_inf_eq] at hcard
  have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
    have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hodd hpdvd
  have h4 : p ∣ 4 ^ n - 1 := by
    have hsq : 4 ^ n - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h2 : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
        rw [← mul_pow]
        norm_num
      rw [h2]
      zify [h1, Nat.one_le_iff_ne_zero.mpr (by positivity : 2 ^ n * 2 ^ n ≠ 0)]
      ring
    rw [hsq]
    exact Dvd.dvd.mul_left hpdvd _
  have hpN : p ∣ Nat.card ↥(Subgroup.normalizer (S : Set X)) := by
    have hdvd : p ∣ Nat.card ↥(Subgroup.normalizer (S : Set X)) * Nat.gcd 3 (2 ^ n + 1) := by
      rw [hcard]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h4 _) _
    rcases hcond with h3 | rfl
    · have hcop : Nat.Coprime p (Nat.gcd 3 (2 ^ n + 1)) := by
        apply Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _)
        exact (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
      exact hcop.dvd_of_dvd_mul_right hdvd
    · have hp3 : p = 3 := by
        have h9 : p ∣ 3 ^ 2 := by norm_num at hpdvd ⊢; exact hpdvd
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h9)
      subst hp3
      norm_num at hcard
      have : 3 * Nat.card ↥(Subgroup.normalizer (S : Set X)) =
          3 * (21 * (Nat.card ↥S * Nat.card ↥(Subgroup.center ↥(⊤ : Subgroup X)))) := by
        rw [mul_comm 3, hcard]
        ring
      have h' := Nat.eq_of_mul_eq_mul_left (by norm_num) this
      rw [h']
      exact Dvd.dvd.mul_right (by norm_num) _
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.normalizer (S : Set X))) p hpN
  have hxo : orderOf (x : X) = p := by
    rw [Subgroup.orderOf_coe, hx]
  obtain ⟨hE, hEc⟩ := CFSG.RankThree.OddKernel.isElemAbelian_zpowers_of_orderOf hxo
  have hFN : Subgroup.zpowers (x : X) ≤ Subgroup.normalizer (S : Set X) :=
    (Subgroup.zpowers_le).mpr x.2
  exact (le_pRank_normalizerQuotient_of_le_normalizer hp hp2 hS.2.1 hFN hE hEc).1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
