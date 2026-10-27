module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XB
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeCovers
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.Quasithin.EmptyFaithful.S146D1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3h_three_mem_piSet {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n)
    (hpow : IsPowTwo c.n) : 3 ∈ piSet c.B0 := by
  obtain ⟨k, hk⟩ := hpow
  have h2 : 2 ∣ c.n := by
    rcases k with _ | k
    · rw [hk] at hn3
      norm_num at hn3
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _
  rw [c.hpi]
  exact ⟨Nat.prime_three, by simpa using Nat.pow_sub_one_dvd_pow_sub_one 2 h2⟩

theorem uc22r3h_not_three_dvd_card {D : Data G} {Ch : Choice2011 G} (h82 : F08.R82 D)
    (he : CFSG.Open.evenRank G = 3) (h1930 : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n)
    (hpow : IsPowTwo c.n) {L K L' : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (hne : K ≠ L) (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hL2 : IsL2 (Bar2 L) n)
    (hL' : L' ∈ calC D.M) (h₁ : L' ≠ L) (h₂ : L' ≠ K) : ¬ 3 ∣ Nat.card L' := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : (1 : ℕ) < 3 := by norm_num
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥L') 3 h3
  have h1 : 1 ≤ CFSG.Open.pRank 3 L' := by
    have hcard : Nat.card (zpowers (g : G)) = 3 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg]
    exact CFSG.SectionRank.le_pRank hp3 (zpowers_le.2 g.2)
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hcard) (by rw [hcard, pow_one])
  obtain ⟨eK⟩ := u4x_bar2_equiv (M := D.M) (L := L) (K := K) (by rw [hset]; simp)
  have hK2 : IsL2 (Bar2 K) n := CFSG.Blueprint.LieModel.of_mulEquiv eK hL2
  have eL := PartTwo.S17.pRank_three_eq_one_of_isL2 hL2
  have eK' := PartTwo.S17.pRank_three_eq_one_of_isL2 hK2
  by_cases hr1 : CFSG.Open.pRank 3 L' ≤ 1
  ·
    have hsp := h82 _ (PartTwo.s16h_hyp81_of_three_pRank_one hL hK hL' hne.symm h₁.symm h₂.symm
      eL eK' (le_antisymm hr1 h1))
    obtain ⟨b, hb, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet (uc22r3h_three_mem_piSet c hn3 hpow)
    exact uc22s217v_not_sp D Ch h1930 c hb Nat.prime_three hbo hsp
  obtain ⟨hcomm, hLK, -, -, -, -, hXc⟩ := u4x_bar_structure hL hK hne hset (Or.inl hL2)
  have hcY : ∀ x ∈ barImage D.M L ⊔ barImage D.M K, ∀ y ∈ barImage D.M L', x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := u4x_mem_sup hcomm hx
    have e1 := uc22p22l_barImage_commute hL hL' h₁.symm a ha y hy
    have e2 := uc22p22l_barImage_commute hK hL' h₂.symm b hb y hy
    rw [mul_assoc, e2, ← mul_assoc, e1, mul_assoc]
  have hXY : (barImage D.M L ⊔ barImage D.M K) ⊓ barImage D.M L' = ⊥ := by
    rw [eq_bot_iff, ← hXc]
    intro y hy
    exact ⟨hy.1, mem_centralizer_iff.2 fun x hx => hcY x hx y hy.2⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  rw [← PartTwo.s13_pRank_barImage Nat.prime_three hp2 (PartTwo.s13_le_of_mem_calC hL)] at eL
  rw [← PartTwo.s13_pRank_barImage Nat.prime_three hp2 (PartTwo.s13_le_of_mem_calC hK)] at eK'
  have hL'r : 2 ≤ CFSG.Open.pRank 3 (barImage D.M L') := by
    rw [PartTwo.s13_pRank_barImage Nat.prime_three hp2 (PartTwo.s13_le_of_mem_calC hL')]
    omega
  have s1 := CFSG.Quasithin.pRank_add_le_pRank_sup Nat.prime_three hcomm hLK
  have s2 := CFSG.Quasithin.pRank_add_le_pRank_sup Nat.prime_three hcY hXY
  have s3 := CFSG.SectionRank.pRank_mono hp3
    (le_top : barImage D.M L ⊔ barImage D.M K ⊔ barImage D.M L' ≤ ⊤)
  rw [pRank_bar2_eq_of_odd Nat.prime_three hp2] at s3
  have s4 := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three hp2
    D.M D.maxLocal.1
  omega

theorem uc22r3h_isSz_of_not_three_dvd {D : Data G} {Ch : Choice2011 G} (h16 : S21_16 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (h3 : ¬ 3 ∣ Nat.card L) : ∃ a : ℕ, IsSz (Bar2 L) a := by
  have hq : Nat.card (Bar2 L) ∣ Nat.card L := Subgroup.card_quotient_dvd_card _
  rcases h16 h1930 c L hL with ⟨n, -, hSp⟩ | ⟨n, hSU⟩ | ⟨n, hL2⟩ | hSz | ⟨p, -, -, hO⟩ | hJ
  · exact (h3 ((uc22p2214_three_dvd_card_sp4 hSp).trans hq)).elim
  · exact (h3 (((CFSG.LocalAnalysis.EvenBN.GMSK.three_dvd_card_of_lieModel_PSU3 hSU.2).trans
      (Subgroup.card_quotient_dvd_card _)).trans hq)).elim
  · exact (h3 ((three_dvd_card_of_isL2 hL2).trans hq)).elim
  · exact hSz
  · have h5 := (PartTwo.s13_five_le_of_isL2Odd hO).2.2
    exact (h3 ((three_dvd_card_of_isL2Odd (by omega) hO).trans hq)).elim
  · exact (h3 ((three_dvd_card_of_isJ1 hJ).trans hq)).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
