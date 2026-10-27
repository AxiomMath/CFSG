module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90E2Core
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90S5
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Main
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgForward
import CFSG.Goldschmidt75.Sec45

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC22

theorem cfg890_normalizer_ne_top {G : Type} [Group G] [Finite G] {D : Data G}
    {L P J Y : Subgroup G} {n : ℕ} (cfg : Cfg890 D L P J Y n) :
    Subgroup.normalizer (Y : Set G) ≠ ⊤ := by
  have hY3 : Nat.card Y = 3 := cfg.card_Y
  intro hNt
  have hnormal : Y.Normal := Subgroup.normalizer_eq_top_iff.mp hNt
  have hsimple : IsSimpleGroup G := D.standing.simple
  have hYnorm : Y.Normal := hnormal
  rcases Subgroup.Normal.eq_bot_or_eq_top Y with hb | ht
  · rw [hb, Subgroup.card_bot] at hY3
    omega
  · have hG3 : Nat.card G = 3 := by
      have h : Nat.card (⊤ : Subgroup G) = 3 := ht ▸ hY3
      rwa [Subgroup.card_top] at h
    have hprime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc : IsCyclic G := isCyclic_of_prime_card hG3
    have hcomm : IsMulCommutative G := IsCyclic.isMulCommutative
    obtain ⟨a, b, hab⟩ := D.standing.nonab
    exact hab (mul_comm' a b)

theorem cfg890_rank_five {G : Type} [Group G] [Finite G] {D : Data G}
    {L P J Y : Subgroup G} {n : ℕ} (cfg : Cfg890 D L P J Y n) (h885 : R885 D) :
    ∀ s : ↥(normalizer (Y : Set G)), orderOf s = 2 →
      CFSG.Open.pRank 5 (centralizer ({s} : Set ↥(normalizer (Y : Set G)))) ≤ 3 := by
  intro s hs
  have hse : orderOf ((s : G)) = 2 := by rw [Subgroup.orderOf_coe, hs]
  have hcard : Nat.card (Subgroup.zpowers (s : G)) = 2 := by
    rw [Nat.card_zpowers, hse]
  have hPne : Subgroup.zpowers (s : G) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcard
    omega
  have hp2 : IsPGroup 2 (Subgroup.zpowers (s : G)) :=
    IsPGroup.of_card (p := 2) (n := 1) (by rw [hcard]; norm_num)
  have hlocal : IsTwoLocal (normalizer (Subgroup.zpowers (s : G) : Set G)) :=
    ⟨Subgroup.zpowers (s : G), hPne, hp2, rfl⟩
  have hbound := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank
    (G := G) 5 Nat.prime_five (by norm_num)
    (normalizer (Subgroup.zpowers (s : G) : Set G)) hlocal
  have he : evenRank G = 3 := (h885 L P cfg.set880).2.2
  have hmap : (centralizer ({s} : Set ↥(normalizer (Y : Set G)))).map
      (normalizer (Y : Set G)).subtype ≤
      normalizer (Subgroup.zpowers (s : G) : Set G) := by
    rw [CFSG.Goldschmidt75.normalizer_zpowers_eq hse]
    rintro x ⟨y, hy, rfl⟩
    have hy' : y * s = s * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg (fun z : ↥(normalizer (Y : Set G)) => (z : G)) hy'
  calc CFSG.Open.pRank 5 (centralizer ({s} : Set ↥(normalizer (Y : Set G))))
      ≤ CFSG.Open.pRank 5 ((centralizer ({s} : Set ↥(normalizer (Y : Set G)))).map
          (normalizer (Y : Set G)).subtype) :=
        CFSG.SectionRank.pRank_le_map (by norm_num) _
          (normalizer (Y : Set G)).subtype_injective _
    _ ≤ CFSG.Open.pRank 5 (normalizer (Subgroup.zpowers (s : G))) :=
        CFSG.SectionRank.pRank_mono (by norm_num) hmap
    _ ≤ evenRank G := hbound
    _ = 3 := he

theorem cfg5e2_of_cfg890 {G : Type} [Group G] [Finite G] {D : Data G}
    {L P J Y : Subgroup G} {n : ℕ} (cfg : Cfg890 D L P J Y n) (h885 : R885 D)
    (h3 : (Nat.card (normalizer (Y : Set G))).factorization 3 = 2)
    (hP : CFSG.pCore 2 ↥(normalizer (Y : Set G)) = ⊥)
    (hF : Fstar (perfInter890 J (centralizer (Y : Set G))) =
      pCoreOf 2 (perfInter890 J (centralizer (Y : Set G))))
    (hSz : IsSz (Bar2 (perfInter890 J (centralizer (Y : Set G)))) n)
    (hO : ⁅perfInter890 J (centralizer (Y : Set G)),
      oddCore890 (normalizer (Y : Set G))⁆ = ⊥) :
    Cfg5e2 ↥(normalizer (Y : Set G)) (Y.subgroupOf (normalizer (Y : Set G)))
      ((perfInter890 J (centralizer (Y : Set G))).subgroupOf
        (normalizer (Y : Set G))) n := by
  set N : Subgroup G := normalizer (Y : Set G) with hN
  set K : Subgroup G := perfInter890 J (centralizer (Y : Set G)) with hK
  have hY3 : Nat.card Y = 3 := cfg.card_Y
  have hYN : Y ≤ N := Subgroup.le_normalizer
  have hKN : K ≤ N := (r890_perfInter_le_right J (centralizer (Y : Set G))).trans
    (Subgroup.centralizer_le_normalizer _)
  refine ⟨D.standing.kProper.isKGroup N (cfg890_normalizer_ne_top cfg), ?_, ?_, h3, hP, ?_, ?_,
    ?_, ?_, cfg890_rank_five cfg h885⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hYN).mpr le_rfl
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv, hY3]
  · apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKN]
    exact r890_perfInter_perfect J (centralizer (Y : Set G))
  · intro hbot
    have hKne : pCoreOf 2 K ≠ ⊥ := r890_fstarNeBot G K n hSz hF
    have hmap := CFSG.GroupTheory.map_pCoreOf_subgroupOf (p := 2) (Y := K) (K := N) hKN
    rw [hbot, Subgroup.map_bot] at hmap
    exact hKne hmap.symm
  · have hbar : Bar2 K ≃* Bar2 (K.subgroupOf N) :=
      (CFSG.RankThree.PartTwo.Sec4.RonanK429.quotPCoreTwoCongr
        (Subgroup.subgroupOfEquivOfLe hKN)).symm
    exact CFSG.Blueprint.LieModel.of_mulEquiv hbar hSz
  · apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKN]
    change ⁅K, oddCore890 N⁆ = (⊥ : Subgroup ↥N).map N.subtype
    rw [hO, Subgroup.map_bot]

theorem lemma5e2_890_of_noSz (hNo : NoSzSectionAutRankOne) : Lemma5e2_890 := by
  intro hKSch hK3 _ G _ _ D L P J Y n cfg h885 h3 hF hSz hO
  set N : Subgroup G := normalizer (Y : Set G) with hN
  by_cases hP : CFSG.pCore 2 ↥N = ⊥
  · exact (false_of_cfg5e2 hKSch hK3 hNo (cfg5e2_of_cfg890 cfg h885 h3 hP hF hSz hO)).elim
  · refine ⟨(CFSG.pCore 2 ↥N).map N.subtype, ?_, ?_, ?_⟩
    · intro hbot
      have h1 : CFSG.pCore 2 ↥N ≤ (N.subtype : ↥N →* G).ker :=
        (Subgroup.map_eq_bot_iff (CFSG.pCore 2 ↥N)).mp hbot
      rw [Subgroup.ker_subtype] at h1
      exact hP (le_bot_iff.mp h1)
    · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
    · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
