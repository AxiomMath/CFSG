module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Uh
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Sz
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS5
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214R5
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2214_two_le_pRank_use (D : Data G)
    (Ch : Choice2011 G) (h2115 : S21_15C D Ch) (h17 : S21_17 D Ch) (hn : SpU3NotList D)
    (hJ : J1NotSp4SU3) (hV : S22_V D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch) {p : ℕ}
    (hp : p ∈ D.sig) {K : Subgroup G} (hKC : K ∈ calC D.M) {n : ℕ}
    (hpre : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∨
      (IsSz ↥(mbarImage D.M c.V K) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)]))
    (hcl : (IsSp4 ↥(mbarImage D.M c.V K) n ∧ Odd n) ∨
      (IsSU3 ↥(mbarImage D.M c.V K) n ∧ n ≡ 1 [MOD 6]) ∨
      ((IsL2 ↥(mbarImage D.M c.V K) n ∨ IsSz ↥(mbarImage D.M c.V K) n) ∧
        (conjSetOf D.M K).ncard = 2)) :
    2 ≤ CFSG.Open.pRank p (conjClosure D.M K) := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hKC.1
  obtain ⟨-, hq, -, -, -⟩ := uc22p2214_case_data D Ch h17 hn hV h1930 c hKC hcl
  rcases hcl with ⟨hsp, -⟩ | ⟨hsu, hmod⟩ | ⟨hL | hSz, hc2⟩
  ·
    have hN : (K.subgroupOf D.M).Normal :=
      uc22p21j_normal_of_s21_17 D Ch h17 hn h1930 c.toCtx22.toCtx21 K hKC
        (Or.inl ⟨n, uc22p22a_shape_sp4 D c hKC hsp⟩)
    rw [uc22p2214_conjClosure_eq_of_normal hKM hN]
    rcases hpre with h | ⟨hSz, -⟩
    · exact P2214R.two_le_pRank_of_sp4 D.M c.V hKM hsp hpp hp2
        (P2214R.dvd_sq_sub_one (P2214R.dvd_of_cong h))
    · exact absurd (uc22p2214_three_dvd_card_sp4 hsp)
        (CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz)
  ·
    have hN : (K.subgroupOf D.M).Normal :=
      uc22p21j_normal_of_s21_17 D Ch h17 hn h1930 c.toCtx22.toCtx21 K hKC
        (Or.inr ⟨n, uc22p22a_shape_su3 D c hKC hsu⟩)
    have hodd : Odd n := by
      have h2 : n % 6 = 1 := hmod
      exact Nat.odd_iff.2 (by omega)
    rw [uc22p2214_conjClosure_eq_of_normal hKM hN]
    rcases hpre with h | ⟨hSz, -⟩
    · exact P2214R.two_le_pRank_of_su3 D.M c.V hKM hsu hodd hpp hp2 (P2214R.dvd_of_cong h)
    · exact absurd
        ((P2214R.three_dvd_card_u3 hsu.2 hodd).trans (Subgroup.card_quotient_dvd_card _))
        (CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz)
  ·
    haveI := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
    rcases hpre with h | ⟨hSz, -⟩
    · refine P2214R.two_le_pRank_pair hKC hc2 hpp hp2
        (P2214R.dvd_index_center_bar2 D c hKC hq ?_)
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
        (CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide))]
      exact (P2214R.dvd_sq_sub_one (P2214R.dvd_of_cong h)).mul_left _
    · exact (P2214S.false_of_isSz_of_isL2 hSz hL).elim
  ·
    haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
    rcases hpre with h | ⟨-, h⟩
    · exact (P2214S.false_of_weak D Ch h2115 h17 hJ h1930 c hKC hSz hc2 hp h).elim
    · refine P2214R.two_le_pRank_pair hKC hc2 hpp hp2
        (P2214R.dvd_index_center_bar2 D c hKC hq ?_)
      rw [CFSG.LocalAnalysis.EvenBN.GMSK.card_of_lieModel_twistedB2 hSz]
      have h1 : p ∣ (2 ^ n) ^ 2 + 1 := by
        rw [← pow_mul, mul_comm]
        exact P2214R.dvd_of_cong h
      exact (h1.mul_left _).mul_right _

theorem uc22p2214_pre_of_not_j1 (D : Data G) {Ch : Choice2011 G} (c : Ctx22b D Ch)
    (hJ : J1NotSp4SU3) (hJL : J1NotL2Sz) {p : ℕ} {K : Subgroup G} {n : ℕ}
    (hpre : (IsJ1 ↥(mbarImage D.M c.V K) ∧ n = 3 ∧ p ∣ Nat.card ↥(mbarImage D.M c.V K) ∧
        ¬ IsL2 ↥(mbarImage D.M c.V K) n) ∨ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∨
      (IsSz ↥(mbarImage D.M c.V K) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)]))
    (hcl : (IsSp4 ↥(mbarImage D.M c.V K) n ∧ Odd n) ∨
      (IsSU3 ↥(mbarImage D.M c.V K) n ∧ n ≡ 1 [MOD 6]) ∨
      ((IsL2 ↥(mbarImage D.M c.V K) n ∨ IsSz ↥(mbarImage D.M c.V K) n) ∧
        (conjSetOf D.M K).ncard = 2)) :
    (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∨
      (IsSz ↥(mbarImage D.M c.V K) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)]) := by
  rcases hpre with ⟨hJK, -⟩ | h | h
  · exfalso
    rcases hcl with ⟨hsp, -⟩ | ⟨hsu, -⟩ | ⟨hL | hS, -⟩
    · exact (hJ _ hJK).2.1 n hsp
    · exact (hJ _ hJK).2.2 n hsu
    · exact (hJL _ hJK).1 n hL
    · exact (hJL _ hJK).2 n hS
  · exact Or.inl h
  · exact Or.inr h

theorem uc22p2214_s22_14_main_faith (D : Data G)
    (Ch : Choice2011 G) (h17 : S21_17 D Ch) (hn : SpU3NotList D) (hJ : J1NotSp4SU3)
    (hJL : J1NotL2Sz) (h8 : S22_8 D Ch) (hSg : UC6S846.SigmaStd D) (hV : S22_V D Ch)
    (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n) (h846 : F08.R846 D) (h1930 : H1930 D) (c : Ctx22b D Ch)
    {p : ℕ} (hp : p ∈ D.sig) {K : Subgroup G} (hKC : K ∈ calC D.M) {n : ℕ}
    (hpre : (IsJ1 ↥(mbarImage D.M c.V K) ∧ n = 3 ∧ p ∣ Nat.card ↥(mbarImage D.M c.V K) ∧
        ¬ IsL2 ↥(mbarImage D.M c.V K) n) ∨ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∨
      (IsSz ↥(mbarImage D.M c.V K) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)]))
    (hcl : (IsSp4 ↥(mbarImage D.M c.V K) n ∧ Odd n) ∨
      (IsSU3 ↥(mbarImage D.M c.V K) n ∧ n ≡ 1 [MOD 6]) ∨
      ((IsL2 ↥(mbarImage D.M c.V K) n ∨ IsSz ↥(mbarImage D.M c.V K) n) ∧
        (conjSetOf D.M K).ncard = 2))
    (hfaith : ∀ b ∈ c.B0, b ≠ 1 →
      ∃ K' ∈ conjSetOf D.M K, ∃ k ∈ K', b * k * b⁻¹ * k⁻¹ ∉ centralizer (c.V : Set G)) :
    c.n ≤ n := by
  have hpre' := uc22p2214_pre_of_not_j1 D c hJ hJL hpre hcl
  by_cases hm6 : c.n = 6
  · exact uc22p2214_six_faith D Ch h17 hn hV h8 hSg h1930 c hm6 hp hKC hpre' hcl hfaith
  · exact uc22p2214_main_faith D Ch h17 hn hV h846 h1930 c (hn3 c) hm6 hKC hcl hfaith

theorem uc22p2214_s22_14_of_faith (D : Data G) (Ch : Choice2011 G)
    (h17 : S21_17 D Ch) (hn : SpU3NotList D) (hJ : J1NotSp4SU3) (hJL : J1NotL2Sz)
    (hJ1 : uc22p22d_J1Nontrivial) (h8 : S22_8 D Ch) (hSg : UC6S846.SigmaStd D)
    (hV : S22_V D Ch) (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n) (h846 : F08.R846 D)
    (h2121 : S21_21Used D Ch)
    (hfaith : ∀ (h1930 : H1930 D) (c : Ctx22b D Ch) (p : ℕ), p ∈ D.sig →
      ∀ (K : Subgroup G) (n : ℕ), K ∈ calC D.M →
      ((2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∨
        (IsSz ↥(mbarImage D.M c.V K) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) →
      ((IsSp4 ↥(mbarImage D.M c.V K) n ∧ Odd n) ∨
        (IsSU3 ↥(mbarImage D.M c.V K) n ∧ n ≡ 1 [MOD 6]) ∨
        ((2 < n ∧ (IsL2 ↥(mbarImage D.M c.V K) n ∨ IsSz ↥(mbarImage D.M c.V K) n)) ∧
          (conjSetOf D.M K).ncard = 2)) →
      ∀ b ∈ c.B0, b ≠ 1 →
        ∃ K' ∈ conjSetOf D.M K, ∃ k ∈ K', b * k * b⁻¹ * k⁻¹ ∉ centralizer (c.V : Set G)) :
    S22_14 D Ch := by
  intro h1930 c p hp K n hK
  obtain ⟨hKC, hpre, hcl⟩ := hK
  have hmain : ((IsSp4 ↥(mbarImage D.M c.V K) n ∧ Odd n) ∨
      (IsSU3 ↥(mbarImage D.M c.V K) n ∧ n ≡ 1 [MOD 6]) ∨
      ((2 < n ∧ (IsL2 ↥(mbarImage D.M c.V K) n ∨ IsSz ↥(mbarImage D.M c.V K) n)) ∧
        (conjSetOf D.M K).ncard = 2)) → c.n ≤ n := fun hcl' => by
    have hcl'' := hcl'.imp_right (Or.imp_right (And.imp_left And.right))
    exact uc22p2214_s22_14_main_faith D Ch h17 hn hJ hJL h8 hSg hV hn3 h846 h1930 c hp hKC hpre
      hcl'' (hfaith h1930 c p hp K n hKC (uc22p2214_pre_of_not_j1 D c hJ hJL hpre hcl'') hcl')
  rcases hcl with ⟨hsp, hodd, -⟩ | ⟨hsu, hmod⟩ | ⟨hLS | ⟨hJK, hn3'⟩, hc2⟩ | ⟨hH, -, hpow⟩
  · exact hmain (Or.inl ⟨hsp, hodd⟩)
  · exact hmain (Or.inr (Or.inl ⟨hsu, hmod⟩))
  · exact hmain (Or.inr (Or.inr ⟨hLS, hc2⟩))
  · exact uc22p2214_j1 D Ch h17 hJ hJL hV h1930 c hKC hJK hJ1 hn3' hc2
  · have hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] := by
      rcases hpre with ⟨-, rfl, -, -⟩ | h | ⟨hSz, -⟩
      · exact absurd hpow (uc22p22a_not_isPowTwo_of_odd (by decide) (by decide))
      · exact h
      · obtain ⟨-, -, -, -, hodd', h3⟩ := CFSG.Blueprint.LieModel.admissible hSz
        exact absurd hpow (uc22p22a_not_isPowTwo_of_odd hodd' (by omega))
    exact uc22p2214_clause4 D Ch h2121 h1930 c hp hH hpow hpn

theorem uc22p2214_s22_14_of_use5 (D : Data G) (Ch : Choice2011 G)
    (h869 : F08.R869NS5 D) (h2115 : S21_15C D Ch) (h17 : S21_17 D Ch) (hn : SpU3NotList D)
    (hJ : J1NotSp4SU3) (hJL : J1NotL2Sz) (hJ1 : uc22p22d_J1Nontrivial) (h8 : S22_8 D Ch)
    (hSg : UC6S846.SigmaStd D) (hV : S22_V D Ch) (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n)
    (h846 : F08.R846 D) (h2121 : S21_21Used D Ch) : S22_14 D Ch :=
  uc22p2214_s22_14_of_faith D Ch h17 hn hJ hJL hJ1 h8 hSg hV hn3 h846 h2121
    fun h1930 c p hp K n hKC hpre hcl => by
      have hcl' := hcl.imp_right (Or.imp_right (And.imp_left And.right))
      obtain ⟨hKV, hq, -, hfix, -⟩ := uc22p2214_case_data D Ch h17 hn hV h1930 c hKC hcl'
      have h5 : p = 5 → 2 ^ 12 ∣ Nat.card (Bar2 (conjClosure D.M K)) := by
        rintro rfl
        have hodd5 : Odd n → ¬ (2 : ℤ) ^ n ≡ -1 [ZMOD ((5 : ℕ) : ℤ)] := fun ⟨k, hk⟩ h => by
          have := CFSG.RankThree.PartTwo.Census.mod_four_of_five_dvd_two_pow_add_one
            (P2214R.dvd_of_cong h)
          omega
        rcases hcl with ⟨hsp, hodd⟩ | ⟨hsu, hmod⟩ | ⟨⟨hn2, hL | hSz⟩, hc2⟩
        · rcases hpre with h | ⟨hSz, -⟩
          · exact absurd h (hodd5 hodd)
          · exact absurd (uc22p2214_three_dvd_card_sp4 hsp)
              (CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz)
        · have hodd : Odd n := by
            have h6 : n % 6 = 1 := hmod
            exact Nat.odd_iff.2 (by omega)
          rcases hpre with h | ⟨hSz, -⟩
          · exact absurd h (hodd5 hodd)
          · exact absurd
              ((P2214R.three_dvd_card_u3 hsu.2 hodd).trans (Subgroup.card_quotient_dvd_card _))
              (CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz)
        · rcases hpre with h | ⟨hSz, -⟩
          · exact P2214R.two_pow_twelve_dvd_pair D hV h1930 c hKC hq
              (Or.inl ⟨hn2, hL, P2214R.dvd_of_cong h⟩) hc2
          · exact (P2214S.false_of_isSz_of_isL2 hSz hL).elim
        · exact P2214R.two_pow_twelve_dvd_pair D hV h1930 c hKC hq (Or.inr hSz) hc2
      exact fun b hb hb1 => uc22p2214_faith_of_R869NS5 D Ch h869 hV h1930 c hKC hKV
        ⟨p, hp, uc22p2214_two_le_pRank_use D Ch h2115 h17 hn hJ hV h1930 c hp hKC hpre hcl', h5⟩
        hfix hb hb1

end CFSG.LocalAnalysis.UniquenessCase.UC22
