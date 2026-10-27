module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.CharacterTheory.Burnside
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
import CFSG.Quasithin.Background.A3FactsClassical
import CFSG.Open.StatedZModTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKRank3Omega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.BorelTits (orthGroup statedOmega_le_orthGroup)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
  (card_orthGroup_quadPlus_two)

variable {W : Type} [CommGroup W]

private theorem s16h_not_isSolvable_of_isQuasisimple {Q : Type} [Group Q]
    (hq : CFSG.Open.IsQuasisimple Q) : ¬ Group.IsSolvable Q := by
  intro hs
  haveI := hs
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hq.2.toNontrivial
  haveI : Nontrivial Q := (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  have h := Group.IsSolvable.commutator_lt_top_of_nontrivial Q
  rw [hq.1] at h
  exact lt_irrefl _ h

private theorem s16h_card_GL_fin_le_six {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) {d : ℕ} (hd : d ≤ 2) : Nat.card (GL (Fin d) K) < 60 := by
  rw [Matrix.card_GL_field]
  interval_cases d <;> simp_all <;> norm_num

private theorem s16h_card_GL_le_six {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Fintype K] (hK : Fintype.card K = 2) (hι : Fintype.card ι ≤ 2) :
    Nat.card (GL ι K) < 60 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have h := Nat.card_congr (Units.mapEquiv (Matrix.reindexRingEquiv K e).toMulEquiv).toEquiv
  rw [h]
  exact s16h_card_GL_fin_le_six hK hι

private theorem s16h_isSolvable_GL_of_card_le_two {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (hι : Fintype.card ι ≤ 2) :
    Group.IsSolvable (GL ι K) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  exact CFSG.GroupTheory.groups_order_below_sixty_solvable (s16h_card_GL_le_six hK' hι)

private theorem s16h_isSolvable_subgroup_GL {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (hι : Fintype.card ι ≤ 2)
    (H : Subgroup (GL ι K)) : Group.IsSolvable ↥H :=
  haveI := s16h_isSolvable_GL_of_card_le_two hK hι
  Group.isSolvable_of_isSolvable_injective (f := H.subtype) H.subtype_injective

private theorem s16h_isSolvable_statedProj {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (hι : Fintype.card ι ≤ 2)
    (H : Subgroup (GL ι K)) : Group.IsSolvable (StatedProj H) :=
  haveI := s16h_isSolvable_subgroup_GL hK hι H
  Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective ((StatedScalars ι K).subgroupOf H))

private theorem s16h_isSolvable_orthGroup_quadPlus_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Group.IsSolvable ↥(orthGroup (StatedQuadPlus 2 K)) := by
  have hcard : Nat.card ↥(orthGroup (StatedQuadPlus 2 K)) = 2 ^ 3 * 3 ^ 2 := by
    rw [card_orthGroup_quadPlus_two, hK]
    norm_num
  haveI : Fintype ↥(orthGroup (StatedQuadPlus 2 K)) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])

private theorem s16h_isSolvable_statedOmega_quadPlus_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 K)) :=
  haveI := s16h_isSolvable_orthGroup_quadPlus_two hK
  Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (statedOmega_le_orthGroup (StatedQuadPlus 2 K)))
    (Subgroup.inclusion_injective _)

private theorem s16h_isSolvable_statedProj_statedOmega_quadPlus_two {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) :
    Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus 2 K))) :=
  haveI := s16h_isSolvable_statedOmega_quadPlus_two hK
  Group.isSolvable_of_surjective
    (QuotientGroup.mk'_surjective ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadPlus 2 K))))

private theorem s16h_three_le_of_isSLn {X : Type} [Group X] {n : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (h : IsSLn X n 1) : 3 ≤ n := by
  by_contra hlt
  have hn : n ≤ 2 := by omega
  obtain ⟨K, hF, hfin, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by simpa using hcard
  haveI : Group.IsSolvable ↥(StatedSL n K) :=
    s16h_isSolvable_subgroup_GL hK (by simpa using hn) (StatedSL n K)
  haveI : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact (s16h_not_isSolvable_of_isQuasisimple hq) inferInstance

private theorem s16h_six_le_of_isSpn {X : Type} [Group X] {n : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (h : IsSpn X n 1) : 6 ≤ n := by
  by_contra hlt
  have hn : n ≤ 5 := by omega
  obtain ⟨hev, K, hF, hfin, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by simpa using hcard
  obtain ⟨r, hr⟩ := hev
  have hn' : n = 0 ∨ n = 2 ∨ n = 4 := by omega
  rcases hn' with rfl | rfl | rfl
  · haveI : Group.IsSolvable ↥(StatedSp (0 / 2) K) :=
      s16h_isSolvable_subgroup_GL hK
        (by simp only [Fintype.card_sum, Fintype.card_fin]; norm_num) (StatedSp (0 / 2) K)
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16h_not_isSolvable_of_isQuasisimple hq) inferInstance
  · haveI : Group.IsSolvable ↥(StatedSp (2 / 2) K) :=
      s16h_isSolvable_subgroup_GL hK
        (by simp only [Fintype.card_sum, Fintype.card_fin]; norm_num) (StatedSp (2 / 2) K)
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16h_not_isSolvable_of_isQuasisimple hq) inferInstance
  · haveI : Fintype K := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
    obtain ⟨f⟩ :=
      CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm (k := K) hK'
    haveI : Group.IsPerfect X := by rw [Group.isPerfect_def]; exact hq.1
    haveI : Group.IsPerfect (Equiv.Perm (Fin 6)) :=
      Group.IsPerfect.ofSurjective (f := (e.trans f).toMonoidHom) (e.trans f).surjective
    have htop : (alternatingGroup (Fin 6) : Subgroup (Equiv.Perm (Fin 6))) = ⊤ := by
      have hc := alternatingGroup.commutator_perm_eq (α := Fin 6) (by simp)
      rw [Group.IsPerfect.commutator_eq_top] at hc
      exact hc.symm
    have hswap : Equiv.swap (0 : Fin 6) 1 ∈
        (alternatingGroup (Fin 6) : Subgroup (Equiv.Perm (Fin 6))) := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at hswap
    exact absurd hswap (by decide)

private theorem s16h_six_le_of_isOmegaPlus {X : Type} [Group X] {n : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (h : IsOmegaPlus X n 1) : 6 ≤ n := by
  by_contra hlt
  have hn : n ≤ 5 := by omega
  obtain ⟨hev, K, hF, hfin, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by simpa using hcard
  obtain ⟨r, hr⟩ := hev
  have hn' : n = 0 ∨ n = 2 ∨ n = 4 := by omega
  rcases hn' with rfl | rfl | rfl
  · haveI : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus (0 / 2) K))) :=
      s16h_isSolvable_statedProj hK
        (by simp only [Fintype.card_sum, Fintype.card_fin]; norm_num)
        (StatedOmega (StatedQuadPlus (0 / 2) K))
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16h_not_isSolvable_of_isQuasisimple hq) inferInstance
  · haveI : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus (2 / 2) K))) :=
      s16h_isSolvable_statedProj hK
        (by simp only [Fintype.card_sum, Fintype.card_fin]; norm_num)
        (StatedOmega (StatedQuadPlus (2 / 2) K))
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16h_not_isSolvable_of_isQuasisimple hq) inferInstance
  · haveI : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus 2 K))) :=
      s16h_isSolvable_statedProj_statedOmega_quadPlus_two hK
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16h_not_isSolvable_of_isQuasisimple hq) inferInstance

private theorem s16h_four_le_of_isOmegaMinus {X : Type} [Group X] {n : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (h : IsOmegaMinus X n 1) : 4 ≤ n := by
  by_contra hlt
  have hn : n ≤ 3 := by omega
  obtain ⟨hev, K, hF, hfin, b, c, hcard, hpoly, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by simpa using hcard
  obtain ⟨r, hr⟩ := hev
  have hn' : n = 0 ∨ n = 2 := by omega
  rcases hn' with rfl | rfl
  · haveI : Group.IsSolvable
        (StatedProj (StatedOmega (StatedQuadMinus (0 / 2) K b c))) :=
      s16h_isSolvable_statedProj hK
        (by simp only [Fintype.card_sum, Fintype.card_fin]; norm_num)
        (StatedOmega (StatedQuadMinus (0 / 2) K b c))
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16h_not_isSolvable_of_isQuasisimple hq) inferInstance
  · haveI : Group.IsSolvable
        (StatedProj (StatedOmega (StatedQuadMinus (2 / 2) K b c))) :=
      s16h_isSolvable_statedProj hK
        (by simp only [Fintype.card_sum, Fintype.card_fin]; norm_num)
        (StatedOmega (StatedQuadMinus (2 / 2) K b c))
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16h_not_isSolvable_of_isQuasisimple hq) inferInstance

private theorem s16h_five_le_of_isAlt {X : Type} [Group X] {n : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (h : IsAlt X n) : 5 ≤ n := by
  by_contra hlt
  have hn : n ≤ 4 := by omega
  obtain ⟨e⟩ := h
  haveI : Group.IsSolvable (alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by simpa using hn)
  haveI : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact (s16h_not_isSolvable_of_isQuasisimple hq) inferInstance

private noncomputable def s16h_statedProjMulEquivSelf {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (hK : Nat.card K = 2) (H : Subgroup (GL ι K)) :
    StatedProj H ≃* H := by
  have hbot : (StatedScalars ι K).subgroupOf H = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK ι, Subgroup.bot_subgroupOf]
  exact (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot

private theorem s16h_pRank_eq_top_of_mulEquiv {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {X : Type} [Group X] [Finite X] (e : ↥L ≃* X) :
    CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L).trans
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e)

private theorem s16h_charP_two_of_card_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime (p := 2) (by rw [← Nat.card_eq_fintype_card]; exact hK)

private theorem s16h_two_le_pRank_statedSL {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSL n K)) := by
  have h2 := CFSG.Quasithin.A3Facts.psl_two_le_pRank_three (K := K) hn
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
    (s16h_statedProjMulEquivSelf hK (StatedSL n K))] at h2
  exact h2

private theorem s16h_two_le_pRank_statedSp {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSp m K)) := by
  haveI : CharP K 2 := s16h_charP_two_of_card_two hK
  have h3 := CFSG.SectionRank.ClassicalEven.psp_three_le_pRank_three (K := K) (n := m) hm
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
    (s16h_statedProjMulEquivSelf hK (StatedSp m K))] at h3
  exact (by norm_num : 2 ≤ 3).trans h3

private theorem s16h_two_le_pRank_alternating {n : ℕ} (hn : 6 ≤ n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) :=
  CFSG.Quasithin.A3Facts.two_le_pRank_alternating hn

private theorem s16h_false_of_two_le_pRank {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hc : s16h_H5Cfg A L t)
    (h2 : 2 ≤ CFSG.Open.pRank 3 L) : False := by
  have h1 := hc.thin 3 Nat.prime_three (by norm_num)
  omega

theorem s16h_H5_thin_sum [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : SumOfAtMostThreeNat L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∨
      s16h_H5RowA5 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) := by
  have hq : CFSG.Open.IsQuasisimple ↥L := hc.comp.2.2
  obtain ⟨k, hk, n, hSL | hSp | hOP | hOM | hAlt⟩ := h
  ·
    obtain ⟨hSL, hsum⟩ := hSL
    have hn3 : 3 ≤ n := s16h_three_le_of_isSLn hq hSL
    rcases eq_or_lt_of_le hn3 with hn | hn
    · subst n
      exact Or.inl ⟨k, hk, hSL, hsum⟩
    · obtain ⟨K, hF, hfin, hcard, ⟨e⟩⟩ := hSL
      letI := hF
      letI := hfin
      have hK : Nat.card K = 2 := by simpa using hcard
      have h2 : 2 ≤ CFSG.Open.pRank 3 L := by
        rw [s16h_pRank_eq_top_of_mulEquiv e]
        exact s16h_two_le_pRank_statedSL hK (by omega)
      exact (s16h_false_of_two_le_pRank hc h2).elim
  ·
    obtain ⟨hSp, hsum⟩ := hSp
    have hn6 : 6 ≤ n := s16h_six_le_of_isSpn hq hSp
    obtain ⟨hev, K, hF, hfin, hcard, ⟨e⟩⟩ := hSp
    letI := hF
    letI := hfin
    have hK : Nat.card K = 2 := by simpa using hcard
    obtain ⟨r, hr⟩ := hev
    have h2 : 2 ≤ CFSG.Open.pRank 3 L := by
      rw [s16h_pRank_eq_top_of_mulEquiv e]
      exact s16h_two_le_pRank_statedSp hK (m := n / 2) (by omega)
    exact (s16h_false_of_two_le_pRank hc h2).elim
  ·
    obtain ⟨hOP, hsum⟩ := hOP
    have hn6 : 6 ≤ n := s16h_six_le_of_isOmegaPlus hq hOP
    have h2 : 2 ≤ CFSG.Open.pRank 3 L := by
      by_cases h6 : n = 6
      · subst n
        obtain ⟨e8⟩ := s15k_omp6_isAlt8 (X := ↥L) hOP
        rw [s16h_pRank_eq_top_of_mulEquiv e8]
        exact s16h_two_le_pRank_alternating (n := 8) (by norm_num)
      · obtain ⟨hev, K, hF, hfin, hcard, ⟨e⟩⟩ := hOP
        letI := hF
        letI := hfin
        have hK : Nat.card K = 2 := by simpa using hcard
        obtain ⟨r, hr⟩ := hev
        have hm : 4 ≤ n / 2 := by omega
        haveI : CharP K 2 := s16h_charP_two_of_card_two hK
        rw [s16h_pRank_eq_top_of_mulEquiv e]
        exact (by norm_num : 2 ≤ 3).trans
          (CFSG.SectionRank.ClassicalEven.omegaPlus_three_le_pRank_three
            (K := K) (n := n / 2) hm)
    exact (s16h_false_of_two_le_pRank hc h2).elim
  ·
    obtain ⟨hOM, hsum⟩ := hOM
    have hn4 : 4 ≤ n := s16h_four_le_of_isOmegaMinus hq hOM
    rcases eq_or_lt_of_le hn4 with hn | hn
    · subst n
      exact Or.inr ⟨k, hk, Or.inl ⟨hOM, hsum⟩⟩
    · have h2 : 2 ≤ CFSG.Open.pRank 3 L := by
        by_cases h6 : n = 6
        · subst n
          obtain ⟨E, hEel, hEcard⟩ := s15k_om6_exists_e27 hOM
          have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
            CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hEel
              (by rw [hEcard]; norm_num)
          rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L]
          exact (by norm_num : 2 ≤ 3).trans h3
        · obtain ⟨hev, K, hF, hfin, b, c, hcard, hpoly, ⟨e⟩⟩ := hOM
          letI := hF
          letI := hfin
          have hK : Nat.card K = 2 := by simpa using hcard
          obtain ⟨r, hr⟩ := hev
          have hm : 4 ≤ n / 2 := by omega
          haveI : CharP K 2 := s16h_charP_two_of_card_two hK
          rw [s16h_pRank_eq_top_of_mulEquiv e]
          exact (by norm_num : 2 ≤ 3).trans
            (CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three
              (K := K) (n := n / 2) hm b c)
      exact (s16h_false_of_two_le_pRank hc h2).elim
  ·
    obtain ⟨hAlt, hsum⟩ := hAlt
    have hn5 : 5 ≤ n := s16h_five_le_of_isAlt hq hAlt
    rcases eq_or_lt_of_le hn5 with hn | hn
    · subst n
      exact Or.inr ⟨k, hk, Or.inr ⟨hAlt, hsum⟩⟩
    · have hn6 : 6 ≤ n := by omega
      obtain ⟨e⟩ := hAlt
      have h2 : 2 ≤ CFSG.Open.pRank 3 L := by
        rw [s16h_pRank_eq_top_of_mulEquiv e]
        exact s16h_two_le_pRank_alternating (n := n) hn6
      exact (s16h_false_of_two_le_pRank hc h2).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
