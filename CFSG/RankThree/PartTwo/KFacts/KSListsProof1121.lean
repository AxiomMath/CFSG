module

public import CFSG.RankThree.PartTwo.Sec11.Item1121ProofSteps
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.RankThree.PartTwo.KFacts.KSListsProofArith
import CFSG.RankThree.PartTwo.Sec19.Step1917StepsOrders
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (ordTrialityD4 ordG2)
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace KSListsProof

theorem mul_sq_sub_one {x : ℕ} (hx : 1 ≤ x) : x * (x ^ 2 - 1) = (x - 1) * x * (x + 1) := by
  have h2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [hx, h2]
  ring

theorem pow_six_dvd_ordG2 (q : ℕ) : q ^ 6 ∣ ordG2 q :=
  ⟨(q ^ 6 - 1) * (q ^ 2 - 1), by unfold ordG2; ring⟩

theorem pow_le_of_dvd_psl2 {s g k x m d : ℕ} (hs : s.Prime) (hx : 3 ≤ x)
    (hd : (Odd x ∧ d = 2) ∨ (Even x ∧ d = 1)) (hdvd : (s ^ g) ^ k ∣ m)
    (h : m * d = x * (x ^ 2 - 1)) : (s ^ g) ^ k ≤ x + 1 := by
  rw [mul_sq_sub_one (by omega)] at h
  rw [← pow_mul]
  rw [← pow_mul] at hdvd
  by_cases hs2 : s = 2
  · subst hs2
    rcases hd with ⟨hxo, rfl⟩ | ⟨hxe, rfl⟩
    · have h2 : 2 ^ (g * k + 1) ∣ (x - 1) * (x + 1) := by
        have h1 : 2 ^ (g * k + 1) ∣ x * ((x - 1) * (x + 1)) := by
          rw [pow_succ, show x * ((x - 1) * (x + 1)) = (x - 1) * x * (x + 1) by ring, ← h]
          exact Nat.mul_dvd_mul_right hdvd 2
        exact (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hxo)).dvd_of_dvd_mul_left h1
      exact two_pow_le_of_dvd_mul_succ hxo (by omega) h2
    · rw [mul_one] at h
      exact pow_le_succ_of_dvd_consecutive Nat.prime_two
        (Or.inr (even_iff_two_dvd.mp hxe)) (by omega) (h ▸ hdvd)
  · exact pow_le_succ_of_dvd_consecutive hs (Or.inl hs2) (by omega)
      (h ▸ Dvd.dvd.mul_right hdvd d)

theorem false_G2_psl2 {s g x d : ℕ} (hs : s.Prime) (hq3 : 3 ≤ s ^ g) (hx : 4 ≤ x)
    (hd : (Odd x ∧ d = 2) ∨ (Even x ∧ d = 1)) (h : ordG2 (s ^ g) * d = x * (x ^ 2 - 1)) :
    False := by
  have hle := pow_le_of_dvd_psl2 hs (by omega) hd (pow_six_dvd_ordG2 _) h
  have := lt_psl2_g2 hq3 hle
  rcases hd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega

theorem false_D4_psl2 {f x d : ℕ} (hf : 1 ≤ f) (hx : 4 ≤ x)
    (hd : (Odd x ∧ d = 2) ∨ (Even x ∧ d = 1))
    (h : ordTrialityD4 (2 ^ f) * d = x * (x ^ 2 - 1)) : False := by
  have hle := pow_le_of_dvd_psl2 Nat.prime_two (by omega) hd (pow_twelve_dvd_ordTrialityD4 _) h
  have := lt_psl2 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)) hle
  rcases hd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega

theorem false_L3_psl2 {s g x d m : ℕ} (hs : s.Prime) (hg : 1 ≤ g) (hy3 : ¬ 3 ∣ s ^ g) (hx : 4 ≤ x)
    (hd : (Odd x ∧ d = 2) ∨ (Even x ∧ d = 1))
    (hm : (s ^ g) ^ 3 * ((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 - 1) = 3 * m ∨
      (s ^ g) ^ 3 * ((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 + 1) = 3 * m)
    (h : m * d = x * (x ^ 2 - 1)) : False := by
  have hy2 : 2 ≤ s ^ g := le_trans hs.two_le (Nat.le_self_pow (by omega) s)
  have hdvd : (s ^ g) ^ 3 ∣ m := by
    have h3 : (s ^ g) ^ 3 ∣ 3 * m := by
      rcases hm with hm | hm <;> rw [← hm, mul_assoc] <;> exact Dvd.intro _ rfl
    refine (Nat.Coprime.pow_left 3 ?_).dvd_of_dvd_mul_left h3
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hy3))
  have hle := pow_le_of_dvd_psl2 hs (by omega) hd hdvd h
  have hlt := lt_psl2_l3 hx hy2 hle
  have hsub : (s ^ g) ^ 3 - 1 ≤ (s ^ g) ^ 3 + 1 := by omega
  have hmle : 3 * m ≤ (s ^ g) ^ 3 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 + 1)) := by
    rcases hm with hm | hm
    · rw [← hm, mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsub)
    · rw [← hm, mul_assoc]
  rcases hd with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · have : 3 * (x * (x ^ 2 - 1)) = 2 * (3 * m) := by rw [← h]; ring
    omega
  · have : 3 * (x * (x ^ 2 - 1)) = 3 * m := by rw [← h, mul_one]
    omega

theorem odd_sl3_part {a : ℕ} (ha : 1 ≤ a) :
    Odd (((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 - 1)) ∧
      Odd (((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 + 1)) :=
  ⟨(CFSG.Timmesfeld.Orders.odd_pow_sub_one ha two_pos).mul
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one ha three_pos),
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one ha two_pos).mul
      (CFSG.Timmesfeld.Orders.odd_pow_add_one ha three_pos)⟩

theorem dvd_cube_of_dvd_sl3 {a k m : ℕ} (ha : 1 ≤ a)
    (hm : m = (2 ^ a) ^ 3 * (((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 - 1)) ∨
      m = (2 ^ a) ^ 3 * (((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 + 1)))
    (h : 2 ^ k ∣ m) : 2 ^ k ∣ (2 ^ a) ^ 3 := by
  obtain ⟨h1, h2⟩ := odd_sl3_part ha
  rcases hm with rfl | rfl
  · exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr h1)).dvd_of_dvd_mul_right h
  · exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr h2)).dvd_of_dvd_mul_right h

theorem sl3_le {x m : ℕ}
    (hm : m = x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) ∨ m = x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1))) :
    x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) ≤ m := by
  rcases hm with rfl | rfl
  · exact le_rfl
  · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))

theorem sl3_le_two_mul {x m : ℕ} (hx : 1 ≤ x)
    (hm : m = x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) ∨ m = x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1))) :
    m ≤ 2 * x ^ 8 := by
  have h2 : x ^ 2 - 1 ≤ x ^ 2 := Nat.sub_le _ _
  have h1 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  have h3 : x ^ 3 + 1 ≤ 2 * x ^ 3 := by omega
  have h3' : x ^ 3 - 1 ≤ 2 * x ^ 3 := by omega
  rcases hm with rfl | rfl
  · calc x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) ≤ x ^ 3 * (x ^ 2 * (2 * x ^ 3)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h3')
      _ = 2 * x ^ 8 := by ring
  · calc x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) ≤ x ^ 3 * (x ^ 2 * (2 * x ^ 3)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h3)
      _ = 2 * x ^ 8 := by ring

theorem two_mul_pow_lt {n : ℕ} (hn : 1 ≤ n) : 2 * (2 ^ (3 * n)) ^ 8 < 2 ^ (3 * (9 * n)) := by
  calc 2 * (2 ^ (3 * n)) ^ 8 = 2 ^ (3 * n * 8 + 1) := by rw [← pow_mul, pow_succ, mul_comm]
    _ < 2 ^ (3 * (9 * n)) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem false_G2_sl3 {s g n : ℕ} (hs : s.Prime) (hq3 : 3 ≤ s ^ g) (hn : 1 ≤ n)
    (h : ordG2 (s ^ g) =
        (2 ^ (3 * n)) ^ 3 * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 - 1)) ∨
      ordG2 (s ^ g) = (2 ^ (3 * n)) ^ 3 * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1))) :
    False := by
  have ha : 1 ≤ 3 * n := by omega
  by_cases hs2 : s = 2
  · subst hs2
    have hdvd := dvd_cube_of_dvd_sl3 ha h (by rw [pow_mul]; exact pow_six_dvd_ordG2 _)
    have hle : ((2 ^ g) ^ 2) ^ 3 ≤ (2 ^ (3 * n)) ^ 3 := Nat.le_of_dvd (by positivity) (by
      rw [show ((2 ^ g) ^ 2) ^ 3 = 2 ^ (g * 6) by rw [← pow_mul, ← pow_mul]]
      exact hdvd)
    have hle2 : (2 ^ g) ^ 2 ≤ 2 ^ (3 * n) := (Nat.pow_le_pow_iff_left (by norm_num)).mp hle
    have := lt_sl3_g2 (by omega) hle2
    have := sl3_le h
    omega
  · have hodd : Odd (s ^ g) := (hs.odd_of_ne_two hs2).pow
    have hdvd : 2 ^ (9 * n) ∣ ordG2 (s ^ g) := by
      rcases h with h | h <;> rw [h, show 9 * n = 3 * n * 3 by ring, pow_mul] <;>
        exact Dvd.intro _ rfl
    exact false_of_odd_g2 hodd hq3 hdvd
      ((sl3_le_two_mul Nat.one_le_two_pow h).trans_lt (two_mul_pow_lt hn)) rfl

theorem false_D4_sl3 {f n : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n)
    (h : ordTrialityD4 (2 ^ f) =
        (2 ^ (3 * n)) ^ 3 * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 - 1)) ∨
      ordTrialityD4 (2 ^ f) =
        (2 ^ (3 * n)) ^ 3 * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1))) :
    False := by
  have hdvd := dvd_cube_of_dvd_sl3 (by omega) h
    (by rw [pow_mul]; exact pow_twelve_dvd_ordTrialityD4 _)
  have hle : ((2 ^ f) ^ 4) ^ 3 ≤ (2 ^ (3 * n)) ^ 3 := Nat.le_of_dvd (by positivity) (by
    rw [show ((2 ^ f) ^ 4) ^ 3 = 2 ^ (f * 12) by rw [← pow_mul, ← pow_mul]]
    exact hdvd)
  have hle4 : (2 ^ f) ^ 4 ≤ 2 ^ (3 * n) := (Nat.pow_le_pow_iff_left (by norm_num)).mp hle
  have := lt_sl3_d4 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)) hle4
  have := sl3_le h
  omega

theorem false_L3_sl3 {s g n m : ℕ} (hs : s.Prime) (hg : 1 ≤ g) (hn : 1 ≤ n)
    (hm : (s ^ g % 3 = 1 ∧ (s ^ g) ^ 3 * ((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 - 1) = 3 * m) ∨
      (s ^ g % 3 = 2 ∧ (s ^ g) ^ 3 * ((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 + 1) = 3 * m))
    (hx : (2 ^ (3 * n) % 3 = 1 ∧
        m = (2 ^ (3 * n)) ^ 3 * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1))) ∨
      (2 ^ (3 * n) % 3 = 2 ∧
        m = (2 ^ (3 * n)) ^ 3 * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 - 1)))) :
    False := by
  set x := 2 ^ (3 * n) with hxdef
  have hx2 : 2 ≤ x := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega) :
    2 ^ 1 ≤ 2 ^ (3 * n))
  obtain ⟨hl1, hl2⟩ := l3_lt_l3 hx2
  have hmx : m = x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) ∨ m = x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) := by
    rcases hx with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inl h
  by_cases hs2 : s = 2
  · subst hs2
    obtain ⟨ho1, ho2⟩ := odd_sl3_part hg
    obtain ⟨hx1, hx2'⟩ := odd_sl3_part (a := 3 * n) (by omega)
    have h3 : ∃ r, Odd r ∧ 3 * m = 2 ^ (g * 3) * r := by
      rcases hm with ⟨-, h⟩ | ⟨-, h⟩
      · exact ⟨_, ho1, by rw [← h, pow_mul]; ring⟩
      · exact ⟨_, ho2, by rw [← h, pow_mul]; ring⟩
    have h3' : ∃ r, Odd r ∧ 3 * m = 2 ^ (3 * n * 3) * r := by
      rcases hmx with h | h
      · exact ⟨3 * _, (by decide : Odd 3).mul hx1, by rw [h, pow_mul]; ring⟩
      · exact ⟨3 * _, (by decide : Odd 3).mul hx2', by rw [h, pow_mul]; ring⟩
    obtain ⟨r, hr, hr'⟩ := h3
    obtain ⟨r', hr2, hr2'⟩ := h3'
    have hgn : g * 3 = 3 * n * 3 :=
      CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hr2 (hr'.symm.trans hr2')
    have hy : 2 ^ g = x := by rw [hxdef]; congr 1; omega
    rw [hy] at hm
    rcases hx with ⟨hx3, h⟩ | ⟨hx3, h⟩ <;> rcases hm with ⟨hy3, hm⟩ | ⟨hy3, hm⟩
    · rw [h, show x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) = x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) by
        ring] at hm
      omega
    · omega
    · omega
    · rw [h, show x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) = x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) by
        ring] at hm
      omega
  · have hy3 : 3 ≤ s ^ g := le_trans (by have := hs.two_le; omega) (Nat.le_self_pow (by omega) s)
    have hyo : Odd (s ^ g) := (hs.odd_of_ne_two hs2).pow
    have hdvd : 2 ^ (9 * n) ∣ m := by
      rcases hmx with h | h <;> rw [h, hxdef, show 9 * n = 3 * n * 3 by ring, pow_mul] <;>
        exact Dvd.intro _ rfl
    have hdvd3 : 2 ^ (9 * n) ∣ 3 * m := Dvd.dvd.mul_left hdvd 3
    have hle := Sec19.Step1917Steps.two_pow_le_of_dvd_sl3Order (N := 9 * n) hyo hy3 (by omega) (by
      rcases hm with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl (h ▸ hdvd3)
      · exact Or.inr (h ▸ hdvd3))
    have hle' : 2 ^ (4 * n) ≤ s ^ g + 1 :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hle
    have hlt : 3 * (x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1))) <
        (s ^ g) ^ 3 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 - 1)) := lt_l3_l3 hn hle'
    have h1 : 3 * m ≤ 3 * (x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1))) := by
      rcases hmx with h | h <;> rw [h]
      · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega)))
    have h2 : (s ^ g) ^ 3 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 - 1)) ≤ 3 * m := by
      rcases hm with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [← h, mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    omega

theorem card_of_isList1016 {X : Type} [Group X] (hX : Sec9.IsList1016 X) :
    (∃ x d : ℕ, 4 ≤ x ∧ ((Odd x ∧ d = 2) ∨ (Even x ∧ d = 1)) ∧
      Nat.card X * d = x * (x ^ 2 - 1)) ∨
    ∃ n : ℕ, 1 ≤ n ∧
      ((2 ^ (3 * n) % 3 = 1 ∧ Nat.card X =
          (2 ^ (3 * n)) ^ 3 * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1))) ∨
        (2 ^ (3 * n) % 3 = 2 ∧ Nat.card X =
          (2 ^ (3 * n)) ^ 3 * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 - 1)))) := by
  rcases hX with ⟨p, e, hp, hp3, he, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨n, hn, hL⟩
  · left
    have hodd : Odd (p ^ (3 * e)) := (hp.out.odd_of_ne_two (by omega)).pow
    refine ⟨p ^ (3 * e), 2, ?_, Or.inl ⟨hodd, rfl⟩, ?_⟩
    · calc 4 ≤ p := by omega
        _ ≤ p ^ (3 * e) := Nat.le_self_pow (by omega) p
    · have h := card_projSL_two_mul (GaloisField p (3 * e))
      rw [GaloisField.card p (3 * e) (by omega)] at h
      have hg : Nat.gcd 2 (p ^ (3 * e) - 1) = 2 :=
        Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one))
      rwa [hg, ← Nat.card_congr φ.toEquiv] at h
  · left
    refine ⟨2 ^ (3 * n), 1, ?_, Or.inr ⟨(Nat.even_pow' (by omega)).mpr even_two, rfl⟩, ?_⟩
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [mul_one, Nat.card_congr φ.toEquiv, Sec21.card_projSL_two (3 * n) (by omega)]
  · right
    refine ⟨n, hn, ?_⟩
    rcases hL with ⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
    · left
      refine ⟨h1, ?_⟩
      have h := KFacts.KS14.card_projSU_three_mul_gcd 2 (3 * n) (by omega)
      have hg : Nat.gcd 3 (2 ^ (3 * n) + 1) = 1 :=
        Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
          (fun h3 => by omega))
      rwa [hg, mul_one, ← Nat.card_congr φ.toEquiv] at h
    · right
      refine ⟨h2, ?_⟩
      have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 (3 * n))
      rw [GaloisField.card 2 (3 * n) (by omega)] at h
      have h1 : 1 ≤ 2 ^ (3 * n) := Nat.one_le_two_pow
      have hg : Nat.gcd 3 (2 ^ (3 * n) - 1) = 1 :=
        Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
          (fun h3 => by omega))
      rwa [hg, mul_one, ← Nat.card_congr φ.toEquiv] at h

end KSListsProof

open KSListsProof in
theorem kFact1121Lists :
    KFact1121Lists := by
  intro X _ hX hY
  have hL := card_of_isList1016 hX
  rcases hY with ⟨q, hq, ⟨e⟩⟩ | ⟨n', q, hq, hq2, -, ⟨e⟩⟩ | ⟨s, g, hs, hg, hiso⟩
  ·
    have hcard : Nat.card X = ordG2 (q.p ^ q.exponent) := by
      rw [Nat.card_congr e.toEquiv, card_G2_carrier q hq, TauCeti.PrimePower.card_def]
    have hq3 : 3 ≤ q.p ^ q.exponent := by
      rw [← TauCeti.PrimePower.card_def]
      exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hq).1
    rcases hL with ⟨x, d, hx, hd, h⟩ | ⟨n, hn, h⟩
    · exact false_G2_psl2 q.prime_p hq3 hx hd (hcard ▸ h)
    · refine false_G2_sl3 q.prime_p hq3 hn ?_
      rcases h with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inr (hcard ▸ h)
      · exact Or.inl (hcard ▸ h)
  ·
    have hcard : Nat.card X = ordTrialityD4 (2 ^ q.exponent) := by
      rw [Nat.card_congr e.toEquiv, card_trialityD4_carrier q hq, TauCeti.PrimePower.card_def,
        hq2]
    rcases hL with ⟨x, d, hx, hd, h⟩ | ⟨n, hn, h⟩
    · exact false_D4_psl2 q.exponent_pos hx hd (hcard ▸ h)
    · refine false_D4_sl3 q.exponent_pos hn ?_
      rcases h with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inr (hcard ▸ h)
      · exact Or.inl (hcard ▸ h)
  ·
    have hm := Sec19.Step1917Steps.three_mul_card_of_isoLThreePi hg hiso
    have hm' : (s ^ g % 3 = 1 ∧
          (s ^ g) ^ 3 * ((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 - 1) = 3 * Nat.card X) ∨
        (s ^ g % 3 = 2 ∧ (s ^ g) ^ 3 * ((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 + 1) = 3 * Nat.card X) := by
      rcases hm with ⟨h1, h2, -⟩ | h
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr h
    rcases hL with ⟨x, d, hx, hd, h⟩ | ⟨n, hn, h⟩
    · have hy3 : ¬ 3 ∣ s ^ g := by rcases hm' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
      refine false_L3_psl2 hs.out hg hy3 hx hd ?_ h
      rcases hm' with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · exact false_L3_sl3 hs.out hg hn hm' h

end CFSG.RankThree.PartTwo.Sec11
