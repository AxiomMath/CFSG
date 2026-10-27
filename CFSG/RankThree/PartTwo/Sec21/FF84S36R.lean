module

public import CFSG.RankThree.PartTwo.Sec21.FF84S36RDec
public import CFSG.RankThree.PartTwo.Sec21.FF84S36RCard
public import CFSG.RankThree.PartTwo.Sec21.FF84S36RQ

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

variable {G : Type} [Group G] [Finite G]

theorem F6_r_ne_one_of_A9 (hA9 : A9CentralizerStmt) {b t b₁ b₂ : G} {L B : Subgroup G}
    (hchar : CFSG.Assembly.IsCharTwoType G) (d : F6Data b L B b₁ b₂ t)
    (h31 : FF84_3_1) (h33 : FF84_3_3) (_h34 : FF84_3_4) :
    Nat.card (Op 2 (Cen t)) ≠ 2 ^ 5 := by
  intro hT
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hTL, hdec⟩ := R_decomp hchar d h31 h33 hT
  have hZ : Subgroup.center L = ⊥ := (h31 G b L B b₁ b₂ d.sec).2
  have hb1B : b₁ ∈ B := (Subgroup.mem_inf.1 d.sec.hb₁).1
  have hb1L : b₁ ∈ L := (Subgroup.mem_inf.1 d.sec.hb₁).2
  have htc' : ∀ x ∈ L, t * x = x * t := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 d.htL x hx).symm
  have hLX : L ≤ Cen t := fun x hx => S36_mem_cen_of (htc' x hx)
  have hb1X : b₁ ∈ Cen t := hLX hb1L
  have hXT : Cen t ≤ Subgroup.normalizer ((Op 2 (Cen t) : Subgroup G) : Set G) :=
    fun x hx => S36_nor_op2 hx
  have hb13 : b₁ ^ 3 = 1 := pow3_of_mem_B d.sec hb1B
  have hb1ord : orderOf b₁ = 3 := orderOf_eq_prime hb13 (b₁_ne_one d.sec)
  have hcard := R_card_cen (S36_op2_le (Cen t)) hLX hXT hTL hdec hb1L
  have hL18 : Nat.card ↥(L ⊓ Cen b₁) = 18 := by
    have := d.sec.caseA
    rw [hZ, Subgroup.card_bot] at this
    omega
  obtain ⟨Q, hQle, hQcard⟩ := R_exists_Q32 hA9 d h31
  have h32 : 32 ∣ Nat.card ↥(Cen t ⊓ Cen b₁) := by
    rw [← hQcard]
    exact Subgroup.card_dvd_of_le hQle
  rw [hcard, hL18] at h32
  have h16 : 16 ∣ Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₁) := by omega
  have hmT : Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₁) ∣ 32 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Op 2 (Cen t) ⊓ Cen b₁ ≤ Op 2 (Cen t))
    rwa [hT] at this
  have hmod := R_card_modEq3 (hXT hb1X) hb13
  rw [hT] at hmod
  have hm : Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₁) = 32 := by
    obtain ⟨k, hk⟩ := h16
    have hle : Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₁) ≤ 32 := Nat.le_of_dvd (by norm_num) hmT
    have hpos : 0 < Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₁) := Nat.card_pos
    have hk2 : k ≤ 2 := by omega
    have hk1 : 1 ≤ k := by omega
    interval_cases k
    · exfalso
      rw [hk] at hmod
      revert hmod
      decide
    · omega
  have hTeq : Op 2 (Cen t) ⊓ Cen b₁ = Op 2 (Cen t) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hm, hT]; norm_num)
  have hcs : b₁ ∈ CenS (Op 2 (Cen t)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have : u ∈ Cen b₁ := by
      have : u ∈ Op 2 (Cen t) ⊓ Cen b₁ := by rw [hTeq]; exact hu
      exact (Subgroup.mem_inf.1 this).2
    exact (S36_comm_of_cen this).symm
  have hb1T : b₁ ∈ Op 2 (Cen t) := R_cen_le_op2 hchar d (Subgroup.mem_inf.2 ⟨hb1X, hcs⟩)
  obtain ⟨k, hk⟩ := S36_op2_isPGroup (Cen t) ⟨b₁, hb1T⟩
  have hk' : b₁ ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : 3 ∣ 2 ^ k := by
    rw [← hb1ord]
    exact orderOf_dvd_of_pow_eq_one hk'
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow hdvd)
  omega

theorem F6_r_ne_one_stmt (hA9 : A9CentralizerStmt) :
    ∀ {b t b₁ b₂ : G} {L B : Subgroup G}, CFSG.Assembly.IsCharTwoType G →
      F6Data b L B b₁ b₂ t → FF84_3_1 → FF84_3_3 → FF84_3_4 →
        Nat.card (Op 2 (Cen t)) ≠ 2 ^ 5 :=
  fun hchar d h31 h33 h34 => F6_r_ne_one_of_A9 hA9 hchar d h31 h33 h34

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
