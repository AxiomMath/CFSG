module

public import CFSG.Quasithin.Vol2.Ch10SecKRRb
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Families
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRR

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem three_dvd_card_alt {n : ℕ} (hn : 3 ≤ n) : 3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h1 := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_perm, Nat.card_fin] at h1
  have h3 : 3 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  rw [← h1] at h3
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)

theorem three_dvd_card_of_isAlt {n : ℕ} {Y : Type} [Group Y] (hn : 3 ≤ n) (h : IsAlt n Y) :
    3 ∣ Nat.card Y := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_alt hn

theorem card_of_isPSL {n p e : ℕ} {Y : Type} [Group Y] (hn : 1 ≤ n) (h : IsPSL n p e Y) :
    Nat.card Y = (p ^ e) ^ (n * (n - 1) / 2) * (∏ j ∈ Finset.Icc 2 n, ((p ^ e) ^ j - 1)) /
      Nat.gcd n (p ^ e - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl hn h

theorem card_of_isPSL_three_two {Y : Type} [Group Y] (h : IsPSL 3 2 1 Y) : Nat.card Y = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_of_isPSL_four_two {Y : Type} [Group Y] (h : IsPSL 4 2 1 Y) :
    Nat.card Y = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

theorem card_of_isPSL_three_four {Y : Type} [Group Y] (h : IsPSL 3 2 2 Y) :
    Nat.card Y = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

theorem card_of_isPSL_two_two {n : ℕ} {Y : Type} [Group Y] (h : IsPSL 2 2 n Y) :
    Nat.card Y = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [card_of_isPSL (by norm_num) h]
  have hodd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have hn : 1 ≤ n := h.1.2.1
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h3 : (2 ^ n - 1) % 2 = 1 := by omega
    rw [Nat.gcd_rec, h3]
    exact Nat.gcd_one_left 2
  rw [hodd, Nat.div_one]
  simp

theorem prime_dvd_card_of_isPSL_two {p : ℕ} {Y : Type} [Group Y] (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsPSL 2 p 1 Y) : p ∣ Nat.card Y := by
  rw [card_of_isPSL (by norm_num) h]
  simp only [pow_one, show 2 * (2 - 1) / 2 = 1 by rfl, Finset.Icc_self, Finset.prod_singleton]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h2 : Nat.gcd 2 (p - 1) = 2 := Nat.gcd_eq_left (by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩)
  rw [h2]
  have h4 : 2 ∣ p ^ 2 - 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨2 * k ^ 2 + 2 * k, by subst hk; ring_nf; omega⟩
  rw [Nat.mul_div_assoc _ h4]
  exact Dvd.intro _ rfl

theorem prime_dvd_card_of_isSL2 {p : ℕ} {Y : Type} [Group Y] (hp : p.Prime) (h : IsSL2 p Y) :
    p ∣ Nat.card Y := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
    (by norm_num), Nat.card_zmod]
  exact Dvd.dvd.mul_right (dvd_pow_self p (by norm_num)) _

theorem three_dvd_card_of_isHat {Y S : Type} [Group Y] [Group S] (h : IsHat Y S) :
    3 ∣ Nat.card Y := by
  rw [← h.2.1]
  exact Subgroup.card_subgroup_dvd_card _

theorem two_le_pRank_three_of_isAlt7 {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (h : IsAlt 7 ↥L) : 2 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨e⟩ := h
  exact two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _)
    (CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_of_alternating (by norm_num) e)

theorem two_le_pRank_three_of_isHat {Y S : Type} [Group Y] [Group S] [Finite Y] [Finite S]
    (h : IsHat Y S) (hS : 2 ≤ CFSG.pRank 3 S) : 2 ≤ CFSG.pRank 3 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  refine two_le_pRank_of_central (by norm_num) (Subgroup.center Y) (fun x hx => hx) hZ ?_
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e,
    ← CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact hS

theorem two_le_pRank_of_isPSL_two_sq {X : Type} [Group X] [Finite X] {L : Subgroup X} {p : ℕ}
    (hp2 : p ≠ 2) (h : IsPSL 2 p 2 ↥L) : 2 ≤ CFSG.Open.pRank p L := by
  obtain ⟨hp, -, hc⟩ := CFSG.SectionRank.classical_model_rank hp2 h
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  rcases hc with ⟨-, ⟨-, h2⟩ | ⟨h3, -⟩ | h4⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h4
  · exact h2
  · omega
  · omega
  · cases h
  · cases h
  · omega

theorem two_le_pRank_of_isPSLEps3 {X : Type} [Group X] [Finite X] {L : Subgroup X} {p : ℕ}
    (hp2 : p ≠ 2) (s : Bool) (h : IsPSLEps3 s p 1 ↥L) : 2 ≤ CFSG.Open.pRank p L := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  cases s with
  | true =>
    obtain ⟨hp, -, hc⟩ := CFSG.SectionRank.classical_model_rank hp2 (h : IsPSL 3 p 1 ↥L)
    rcases hc with ⟨-, ⟨h2, -⟩ | ⟨-, h3⟩ | h4⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h4
    · omega
    · omega
    · omega
    · cases h
    · cases h
    · omega
  | false =>
    obtain ⟨hp, -, hc⟩ := CFSG.SectionRank.classical_model_rank hp2 (h : IsPSU 3 p 1 ↥L)
    rcases hc with ⟨h, -⟩ | ⟨-, ⟨-, h3⟩ | h4⟩ | ⟨h, -⟩ | h4
    · cases h
    · omega
    · omega
    · cases h
    · omega

theorem two_le_pRank_of_isSLEps3 {X : Type} [Group X] [Finite X] {L : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (s : Bool) (h : IsSLEps3 s p ↥L) :
    2 ≤ CFSG.Open.pRank p L := by
  have : Fact p.Prime := ⟨hp⟩
  cases s with
  | true =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := (h : IsSL3 p ↥L)
    exact two_le_open_pRank_of_mulEquiv hp e (two_le_pRank_sl3_odd hp5 hK)
  | false =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := (h : IsSU3 p ↥L)
    exact two_le_open_pRank_of_mulEquiv hp e (two_le_pRank_su3_odd hp5 hK)

theorem two_le_pRank_three_of_isPSL_two_one {X : Type} [Group X] [Finite X] {L : Subgroup X}
    {n : ℕ} (hn : 4 ≤ n) (h : IsPSL n 2 1 ↥L) : 2 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  refine two_le_open_pRank_of_mulEquiv Nat.prime_three e ?_
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psl hn

end CFSG.Quasithin.Vol2.Ch10.SecB.KRR
