module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMa
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise
variable {G : Type} [Group G] [Finite G]

theorem s16h_orderOf_eq_three_mul_orderOf_pow_three {H : Type*} [Group H] [Finite H] {x : H}
    (h3 : 3 ∣ orderOf x) : orderOf x = 3 * orderOf (x ^ 3) := by
  rw [orderOf_pow_of_dvd (x := x) (n := 3) (by norm_num) h3]
  exact (Nat.mul_div_cancel' h3).symm

theorem s16h_orderOf_pow_orderOf_pow_three {H : Type*} [Group H] [Finite H] {x : H}
    (h3 : 3 ∣ orderOf x) : orderOf (x ^ orderOf (x ^ 3)) = 3 := by
  have hx : orderOf x = 3 * orderOf (x ^ 3) := s16h_orderOf_eq_three_mul_orderOf_pow_three h3
  have hdvd : Nat.gcd (orderOf x) (orderOf (x ^ 3)) = orderOf (x ^ 3) := by
    rw [hx]
    exact Nat.gcd_eq_right (Nat.dvd_mul_left (orderOf (x ^ 3)) 3)
  rw [orderOf_pow, hdvd, hx, Nat.mul_div_left 3 (orderOf_pos (x ^ 3))]

theorem s16h_zpowers_pow_eq_of_not_three_dvd {H : Type*} [Group H] [Finite H] {y : H}
    (hy : orderOf y = 3) {d : ℕ} (hd : ¬ 3 ∣ d) :
    Subgroup.zpowers (y ^ d) = Subgroup.zpowers y := by
  have hcop : Nat.Coprime (orderOf y) d := by
    rw [hy]
    exact (Nat.prime_three.coprime_iff_not_dvd).2 hd
  have hord : orderOf (y ^ d) = 3 := by
    rw [hcop.orderOf_pow, hy]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · exact Subgroup.zpowers_le.2 ((Subgroup.zpowers y).pow_mem (Subgroup.mem_zpowers y) d)
  · rw [Nat.card_zpowers, Nat.card_zpowers, hord, hy]

theorem s16h_pow_not_mem_of_not_mem {H : Type*} [Group H] [Finite H] {y : H} {L B : Subgroup H}
    (hyL : y ∉ L) (hyB : y ∉ B) (hy : orderOf y = 3) {d : ℕ} (hd : ¬ 3 ∣ d) :
    y ^ d ∉ L ∧ y ^ d ∉ B := by
  have hz : Subgroup.zpowers (y ^ d) = Subgroup.zpowers y :=
    s16h_zpowers_pow_eq_of_not_three_dvd hy hd
  have hyz : y ∈ Subgroup.zpowers (y ^ d) := by
    rw [hz]
    exact Subgroup.mem_zpowers y
  constructor <;> intro h
  · exact hyL (Subgroup.zpowers_le.2 h hyz)
  · exact hyB (Subgroup.zpowers_le.2 h hyz)

theorem s16h_exists_order_three_pow_not_mem {H W : Type*} [Group H] [Finite H] [Group W] [Finite W]
    (φ : H →* W) {L B : Subgroup W}
    (hcomm : ∀ p ∈ L, ∀ q ∈ B, p * q = q * p) (hbot : L ⊓ B = ⊥) {a b : H}
    (haL : φ a ∈ L) (hbB : φ b ∈ B) (ha1 : φ a ≠ 1) (hb1 : φ b ≠ 1)
    (ha3 : (φ a) ^ 3 = 1) (hb3 : (φ b) ^ 3 = 1)
    (hker3 : ¬ 3 ∣ Nat.card ↥(MonoidHom.ker φ)) :
    ∃ s : H, orderOf s = 3 ∧ φ s ∉ L ∧ φ s ∉ B := by
  have hφx : φ (a * b) = φ a * φ b := map_mul φ a b
  have hcommφ : Commute (φ a) (φ b) := hcomm (φ a) haL (φ b) hbB
  have hφx3 : (φ (a * b)) ^ 3 = 1 := by
    rw [hφx, hcommφ.mul_pow, ha3, hb3, mul_one]
  have hφx1 : φ (a * b) ≠ 1 := by
    intro h1
    rw [hφx] at h1
    have hb_eq : φ b = (φ a)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hbL : φ b ∈ L := by rw [hb_eq]; exact L.inv_mem haL
    have hmem : φ b ∈ L ⊓ B := ⟨hbL, hbB⟩
    rw [hbot] at hmem
    exact hb1 (Subgroup.mem_bot.1 hmem)
  have hφxL : φ (a * b) ∉ L := by
    intro h
    have hbL : φ b ∈ L := by
      have h1 : (φ a)⁻¹ * (φ a * φ b) ∈ L := by
        rw [← hφx]
        exact L.mul_mem (L.inv_mem haL) h
      simpa using h1
    have hmem : φ b ∈ L ⊓ B := ⟨hbL, hbB⟩
    rw [hbot] at hmem
    exact hb1 (Subgroup.mem_bot.1 hmem)
  have hφxB : φ (a * b) ∉ B := by
    intro h
    rw [hφx] at h
    have haB : φ a ∈ B := by
      have h1 : φ a * φ b * (φ b)⁻¹ ∈ B := B.mul_mem h (B.inv_mem hbB)
      simpa using h1
    have hmem : φ a ∈ L ⊓ B := ⟨haL, haB⟩
    rw [hbot] at hmem
    exact ha1 (Subgroup.mem_bot.1 hmem)
  have hφx_ord : orderOf (φ (a * b)) = 3 := by
    have hdvd : orderOf (φ (a * b)) ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hφx3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hφx1
    · exact h
  have hx3ker : (a * b) ^ 3 ∈ MonoidHom.ker φ := by
    rw [MonoidHom.mem_ker, map_pow, hφx3]
  have hd3 : ¬ 3 ∣ orderOf ((a * b) ^ 3) := fun h =>
    hker3 (h.trans (Subgroup.orderOf_dvd_natCard (MonoidHom.ker φ) hx3ker))
  have h3dvd : 3 ∣ orderOf (a * b) := by
    by_contra h3
    have hcop : Nat.Coprime (orderOf (a * b)) 3 :=
      ((Nat.prime_three.coprime_iff_not_dvd).2 h3).symm
    have hord : orderOf ((a * b) ^ 3) = orderOf (a * b) := by
      rw [orderOf_pow, hcop.gcd_eq_one, Nat.div_one]
    have hzpe : Subgroup.zpowers ((a * b) ^ 3) = Subgroup.zpowers (a * b) := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · exact Subgroup.zpowers_le.2
          ((Subgroup.zpowers (a * b)).pow_mem (Subgroup.mem_zpowers (a * b)) 3)
      · rw [Nat.card_zpowers, Nat.card_zpowers, hord]
    have hxmem : a * b ∈ Subgroup.zpowers ((a * b) ^ 3) := by
      rw [hzpe]
      exact Subgroup.mem_zpowers (a * b)
    have hmem : a * b ∈ MonoidHom.ker φ := (Subgroup.zpowers_le.2 hx3ker) hxmem
    exact hφx1 (MonoidHom.mem_ker.1 hmem)
  refine ⟨(a * b) ^ orderOf ((a * b) ^ 3),
    s16h_orderOf_pow_orderOf_pow_three h3dvd, ?_, ?_⟩
  · have hpow := s16h_pow_not_mem_of_not_mem (L := L) (B := B) hφxL hφxB hφx_ord hd3
    simpa [map_pow] using hpow.1
  · have hpow := s16h_pow_not_mem_of_not_mem (L := L) (B := B) hφxL hφxB hφx_ord hd3
    simpa [map_pow] using hpow.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
