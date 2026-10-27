module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G2CartanRank
import CFSG.HardMathSupport.Lang.Coordinator.TrialityNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_two_le_pRank_of_barInf {L : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (BarInf L))) : 2 ≤ CFSG.Open.pRank r L := by
  have h3 := CFSG.GroupTheory.two_le_pRank_of_quotient (CFSG.solvableRadical ↥L) hr hr2 h
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h3

section NotThin


theorem uc22s2114_not_thin {L : Subgroup G} {f : ℕ} (hX : LieRankTwoEven (BarInf L) f)
    (hf : IsPowTwo f) (hL32 : ¬ IsL3 (BarInf L) 1) : ¬ F08.Thin8 L := by
  suffices h : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.Open.pRank r L by
    obtain ⟨r, hr, hr2, h2⟩ := h
    intro hthin
    have := hthin r hr hr2
    omega
  have h3f : f ≠ 1 → 3 ∣ 2 ^ f - 1 := by
    obtain ⟨k, rfl⟩ := hf
    intro hf1
    exact Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_pow_self 2 fun hk => hf1 (by rw [hk, pow_zero]))
  have h3 : (3 : ℕ) ≠ 2 := by norm_num
  rcases hX with hX | hX | hX | hX | hX | hX | hX
  · obtain ⟨A, hA, hcard⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_nine_of_psl
      (LieModel.statedClassicalModel hX (by decide)) (dvd_refl 3)
      (h3f fun hf1 => hL32 (hf1 ▸ hX))
    exact ⟨3, Nat.prime_three, h3, uc22s2114_two_le_pRank_of_barInf Nat.prime_three h3
      (CFSG.SectionRank.le_pRank (by norm_num) le_top hA hcard)⟩
  · exact ⟨3, Nat.prime_three, h3, uc22s2114_two_le_pRank_of_barInf Nat.prime_three h3
      (uc22p2214_two_le_pRank_sp4 hX)⟩
  · obtain ⟨-, -, -, h32⟩ := LieModel.admissible hX
    have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) h32
    have hf1 : f ≠ 1 := by
      rintro rfl
      norm_num at hq
    obtain ⟨S, hS⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf (⊤ : Subgroup (BarInf L))
    obtain ⟨h2, -⟩ := PartTwo.Inputs1719.k_G2CartanRank_holds (BarInf L) f hX hq S hS 3
      Nat.prime_three h3 (h3f hf1)
    have h4 := h2.ge
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h4
    have h5 := CFSG.GroupTheory.two_le_pRank_of_quotient
      (S.subgroupOf (normalizer (S : Set (BarInf L)))) Nat.prime_three h3 h4
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h5
    exact ⟨3, Nat.prime_three, h3, uc22s2114_two_le_pRank_of_barInf Nat.prime_three h3
      (h5.trans (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_top))⟩
  · obtain ⟨A, hA, hcard⟩ := CFSG.HardMathSupport.Lang.Coordinator.exists_nine_of_trialityD4
      (LieModel.chevalleyExceptionalModel hX (by decide))
    exact ⟨3, Nat.prime_three, h3, uc22s2114_two_le_pRank_of_barInf Nat.prime_three h3
      (CFSG.SectionRank.le_pRank (by norm_num) le_top hA hcard)⟩
  · exfalso
    obtain ⟨-, -, -, -, hodd, hf3⟩ := LieModel.admissible hX
    obtain ⟨k, rfl⟩ := hf
    rcases k with _ | k
    · norm_num at hf3
    · exact Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, k.succ_ne_zero⟩) hodd
  · obtain ⟨r, hr, hr2, h2⟩ := PartTwo.S17.exists_two_le_pRank_of_isU (n := 4) hX (by norm_num)
    exact ⟨r, hr, hr2, uc22s2114_two_le_pRank_of_barInf hr hr2 h2⟩
  · obtain ⟨r, hr, hr2, h2⟩ := PartTwo.S17.exists_two_le_pRank_of_isU (n := 5) hX (by norm_num)
    exact ⟨r, hr, hr2, uc22s2114_two_le_pRank_of_barInf hr hr2 h2⟩

end NotThin

theorem uc22s2114_B0_le_normalizer {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) :
    c.B0 ≤ normalizer (L : Set G) :=
  h5 hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } L hL

theorem uc22s2114_faithful {D : Data G} {Ch : Choice2011 G} (h3 : S21_3 D Ch) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) (hthin : ¬ F08.Thin8 L) :
    ∀ b ∈ c.B0, CentralizesBar b L → b = 1 := by
  intro b hb hcb
  by_contra hb1
  exact hthin (h3 hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } L hL ⟨b, hb, hb1, hcb⟩)

theorem uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one {M L B : Subgroup G} (hL : L ∈ calC M)
    (hBL : B ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ B, CentralizesBar b L → b = 1) {b : G}
    (hb : b ∈ B) (h1 : inducedBarInfAutHom L ⟨b, hBL hb⟩ = 1) : b = 1 :=
  hfaith b hb (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 (hBL hb) h1)

theorem uc22s2114_card_dvd_aut {M L B : Subgroup G} (hL : L ∈ calC M)
    (hBL : B ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ B, CentralizesBar b L → b = 1) :
    Nat.card B ∣ Nat.card (MulAut (BarInf L)) := by
  refine Subgroup.card_dvd_of_injective ((inducedBarInfAutHom L).comp (inclusion hBL)) ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  exact (mem_bot).2 (Subtype.ext (uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith
    x.2 hx))

end CFSG.LocalAnalysis.UniquenessCase.UC22
