module

public import Certificates.Kernel.BalanceSC.Syl8
public import Certificates.Kernel.BalanceSC.Syl9
public import Certificates.Kernel.BalanceSC.Syl10
public import Certificates.Kernel.BalanceSC.Syl11
public import Certificates.Kernel.BalanceSC.Check8
public import Certificates.Kernel.BalanceSC.Check9
public import Certificates.Kernel.BalanceSC.Check10
public import Certificates.Kernel.BalanceSC.Check11
public import Certificates.Kernel.BalanceSC.SylGen
public import CFSG.Certificates.Kernel.BalanceSC.BalSound

public section

open CFSG.KC.BalanceSC CFSG.KC.BalanceSC.TableSound CFSG.KC.BalanceSC.BalSound
open CFSG.OddStandard.Solomon75.AhatData (P0 SylowGood BalanceGood)

namespace CFSG.KD.BalSC8

theorem checks : Checks 8 64 (getL 0 G) (tab64 PB) (fun i k => getL 0 (getL [] E i) k)
    (getL 0 PAR) (getL 0 LAB) PS :=
  ⟨sz, gsize, gen, sq, tabHead, tabPoints, tabKeys⟩

theorem card_sylow : Nat.card (P0 8) = 64 ∧ SylowGood 8 (P0 8) :=
  sylow_of_checks checks (by norm_num) (by norm_num) isoI nbr conn rank eight half

theorem balance : BalanceGood 8 3 (P0 8) := by
  have hT := tabIn_of_checks (by norm_num) (by norm_num) checks
  intro e he r hr hrmin her
  have key : ∀ r k : ℕ, r.Prime → 3 ≤ r → 1 ≤ k → k * r ≤ 8 →
      (r = 3 ∧ k = 1) ∨ (r = 3 ∧ k = 2) ∨ (r = 5 ∧ k = 1) ∨ (r = 7 ∧ k = 1) := by
    intro r k hr h3 hk1 hkr
    have : r ≤ 8 := by nlinarith
    have : k ≤ 2 := by nlinarith
    interval_cases r <;> interval_cases k <;> first | omega | norm_num at hr
  rcases key r _ hr hrmin (one_le_card_cycParts he) (card_cycParts_mul_le hr her) with
    ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩
  · exact wit_of_partsOK (by norm_num) sz hT s3 parts3_1 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s3 parts3_2 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s5 parts5_1 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s7 parts7_1 hr her hk (by norm_num)

end CFSG.KD.BalSC8

namespace CFSG.KD.BalSC9

theorem checks : Checks 9 64 (getL 0 G) (tab64 PB) (fun i k => getL 0 (getL [] E i) k)
    (getL 0 PAR) (getL 0 LAB) PS :=
  ⟨sz, gsize, gen, sq, tabHead, tabPoints, tabKeys⟩

theorem card_sylow : Nat.card (P0 9) = 64 ∧ SylowGood 9 (P0 9) :=
  sylow_of_checks checks (by norm_num) (by norm_num) isoI nbr conn rank eight half

theorem balance : BalanceGood 9 3 (P0 9) := by
  have hT := tabIn_of_checks (by norm_num) (by norm_num) checks
  intro e he r hr hrmin her
  have key : ∀ r k : ℕ, r.Prime → 3 ≤ r → 1 ≤ k → k * r ≤ 9 →
      (r = 3 ∧ k = 1) ∨ (r = 3 ∧ k = 2) ∨ (r = 3 ∧ k = 3) ∨ (r = 5 ∧ k = 1) ∨
        (r = 7 ∧ k = 1) := by
    intro r k hr h3 hk1 hkr
    have : r ≤ 9 := by nlinarith
    have : k ≤ 3 := by nlinarith
    interval_cases r <;> interval_cases k <;> first | omega | norm_num at hr
  rcases key r _ hr hrmin (one_le_card_cycParts he) (card_cycParts_mul_le hr her) with
    ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩
  · exact wit_of_partsOK (by norm_num) sz hT s3 parts3_1 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s3 parts3_2 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s3 parts3_3 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s5 parts5_1 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s7 parts7_1 hr her hk (by norm_num)

end CFSG.KD.BalSC9

namespace CFSG.KD.BalSC10

theorem checks : Checks 10 128 (getL 0 G) (tab64 PB) (fun i k => getL 0 (getL [] E i) k)
    (getL 0 PAR) (getL 0 LAB) PS :=
  ⟨sz, gsize, gen, sq, tabHead, tabPoints, tabKeys⟩

theorem card_sylow : Nat.card (P0 10) = 128 ∧ SylowGood 10 (P0 10) :=
  sylow_of_checks checks (by norm_num) (by norm_num) isoI nbr conn rank eight half

theorem balance : BalanceGood 10 3 (P0 10) := by
  have hT := tabIn_of_checks (by norm_num) (by norm_num) checks
  intro e he r hr hrmin her
  have key : ∀ r k : ℕ, r.Prime → 3 ≤ r → 1 ≤ k → k * r ≤ 10 →
      (r = 3 ∧ k = 1) ∨ (r = 3 ∧ k = 2) ∨ (r = 3 ∧ k = 3) ∨ (r = 5 ∧ k = 1) ∨
        (r = 5 ∧ k = 2) ∨ (r = 7 ∧ k = 1) := by
    intro r k hr h3 hk1 hkr
    have : r ≤ 10 := by nlinarith
    have : k ≤ 3 := by nlinarith
    interval_cases r <;> interval_cases k <;> first | omega | norm_num at hr
  rcases key r _ hr hrmin (one_le_card_cycParts he) (card_cycParts_mul_le hr her) with
    ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩
  · exact wit_of_partsOK (by norm_num) sz hT s3 parts3_1 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s3 parts3_2 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s3 parts3_3 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s5 parts5_1 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s5 parts5_2 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s7 parts7_1 hr her hk (by norm_num)

end CFSG.KD.BalSC10

namespace CFSG.KD.BalSC11

theorem checks : Checks 11 128 (getL 0 G) (tab64 PB) (fun i k => getL 0 (getL [] E i) k)
    (getL 0 PAR) (getL 0 LAB) PS :=
  ⟨sz, gsize, gen, sq, tabHead, tabPoints, tabKeys⟩

theorem card_sylow : Nat.card (P0 11) = 128 ∧ SylowGood 11 (P0 11) :=
  sylow_of_checks checks (by norm_num) (by norm_num) isoI nbr conn rank eight half

theorem balance : BalanceGood 11 5 (P0 11) := by
  have hT := tabIn_of_checks (by norm_num) (by norm_num) checks
  intro e he r hr hrmin her
  have key : ∀ r k : ℕ, r.Prime → 5 ≤ r → 1 ≤ k → k * r ≤ 11 →
      (r = 5 ∧ k = 1) ∨ (r = 5 ∧ k = 2) ∨ (r = 7 ∧ k = 1) ∨ (r = 11 ∧ k = 1) := by
    intro r k hr h5 hk1 hkr
    have : r ≤ 11 := by nlinarith
    have : k ≤ 2 := by nlinarith
    interval_cases r <;> interval_cases k <;> first | omega | norm_num at hr
  rcases key r _ hr hrmin (one_le_card_cycParts he) (card_cycParts_mul_le hr her) with
    ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, -⟩
  · exact wit_of_partsOK (by norm_num) sz hT s5 parts5_1 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s5 parts5_2 hr her hk (by norm_num)
  · exact wit_of_partsOK (by norm_num) sz hT s7 parts7_1 hr her hk (by norm_num)
  · have hc := card_sylow.1
    exact balance_of_prime_card (by rw [Fintype.card_fin]; norm_num) he
      (by rw [Fintype.card_fin]; exact her) (P0 11) (by rw [hc, Fintype.card_fin]; norm_num)
      (by rw [hc, Fintype.card_fin]; norm_num)

end CFSG.KD.BalSC11

end
