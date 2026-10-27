module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213RestNN
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableQ
import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7UseThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S217L2Three
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeK
import CFSG.GroupTheory.SurjectiveRangeFactor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedSolvableQ StronglyEmbeddedFive StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213t_normalizer_le_of_sig {D : Data G} (hσ : UC6S846.SigmaStd D) (hKF : KF7Use D)
    (huniq : ∀ p ∈ D.sig, ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup 2 X →
      2 ≤ CFSG.Open.pRank p (normalizer (X : Set G) ⊓ D.M) → normalizer (X : Set G) ≤ D.M)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hthin : ¬ F08.Thin8 L) {p : ℕ} (hp : p ∈ D.sig)
    {A : Subgroup G} (hAM : A ≤ D.M) {r : ℕ} (hr : r.Prime) (hAr : Nat.card A = r)
    (hY : (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L)
    (h2 : 2 ≤ CFSG.Open.pRank p (normalizer (A : Set G) ⊓ D.M)) :
    normalizer (A : Set G) ≤ D.M := by
  classical
  by_contra hHM
  have : IsSimpleGroup G := D.standing.simple
  have htop : normalizer (A : Set G) ≠ ⊤ := by
    intro htop
    have : A.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A with hbot | hAtop
    · subst hbot
      rw [Subgroup.card_bot] at hAr
      exact hr.ne_one hAr.symm
    · exact hHM fun x _ => hAM (hAtop ▸ Subgroup.mem_top x)
  have hpr := D.sig_prime p hp
  have hsp : IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hp
  have hsec : F07.Sec7Hyp D p (normalizer (A : Set G)) :=
    ⟨hpr.1, hpr.2, hsp, htop, hHM, h2⟩
  have hodd : Odd (Nat.card (CFSG.pPrimeCore p ↥(normalizer (A : Set G)))) :=
    PartOne.Section7.odd_card_pPrimeCore hsp hpr.1 (huniq p hp) hHM h2
  obtain ⟨f, hf⟩ := uc22s213_exists_surj_center_quotient hL hY
  have hsimple : IsSimpleGroup (Bar2 L ⧸ center (Bar2 L)) := hL.2.2.2
  have : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hL.2.2.1
  have hnab : ∃ x y : Bar2 L ⧸ center (Bar2 L), x * y ≠ y * x := by
    by_contra hcomm
    push Not at hcomm
    exact Group.IsPerfect.not_isSolvable _ (isSolvable_of_comm hcomm)
  obtain ⟨-, x, hx⟩ :=
    CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have hx2 : x ^ 2 ^ 1 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa using h
  have hD0Y := CFSG.Quasithin.perfectCore_le (L ⊓ centralizer (A : Set G))
  have hD0H : CFSG.Quasithin.perfectCore (L ⊓ centralizer (A : Set G)) ≤
      normalizer (A : Set G) :=
    hD0Y.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hD0M : CFSG.Quasithin.perfectCore (L ⊓ centralizer (A : Set G)) ≤ D.M :=
    hD0Y.trans (inf_le_left.trans hL.1.le)
  let g := (QuotientGroup.mk' (CFSG.pPrimeCore p ↥(normalizer (A : Set G)))).comp
    (Subgroup.inclusion hD0H)
  have hker : g.ker ≤ f.ker := by
    refine CFSG.AGLEmbedding.le_ker_of_isSimpleGroup f hf g.ker (p := 2) (fun n hn => ?_) hx1 hx2
    have hnK : Subgroup.inclusion hD0H n ∈ CFSG.pPrimeCore p ↥(normalizer (A : Set G)) :=
      (QuotientGroup.eq_one_iff _).mp hn
    have hord : orderOf n = orderOf (⟨_, hnK⟩ : ↥(CFSG.pPrimeCore p ↥(normalizer (A : Set G)))) :=
      (orderOf_injective _ (Subgroup.inclusion_injective hD0H) n).symm.trans
        (Subgroup.orderOf_mk _ hnK).symm
    rw [hord, Nat.coprime_two_left]
    exact hodd.of_dvd_nat (orderOf_dvd_natCard _)
  obtain ⟨ψ, hψ⟩ := CFSG.exists_surjective_range_of_ker_le g f hf hker
  have hle : g.range ≤ ((normalizer (A : Set G) ⊓ D.M).subgroupOf (normalizer (A : Set G))).map
      (QuotientGroup.mk' (CFSG.pPrimeCore p ↥(normalizer (A : Set G)))) := by
    rintro _ ⟨d, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hD0H d.2, hD0M d.2⟩)
  have hperf : ⁅g.range, g.range⁆ = g.range := by
    have : Group.IsPerfect ↥(CFSG.Quasithin.perfectCore (L ⊓ centralizer (A : Set G))) :=
      Subgroup.isPerfect_iff.mpr (CFSG.Quasithin.perfectCore_perfect _)
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective g.rangeRestrict_surjective)
  rcases hKF p hp (normalizer (A : Set G)) hsec with hsol | ⟨-, hA5⟩
  ·
    have : Group.IsSolvable ↥(((normalizer (A : Set G) ⊓ D.M).subgroupOf
        (normalizer (A : Set G))).map
          (QuotientGroup.mk' (CFSG.pPrimeCore p ↥(normalizer (A : Set G))))) := hsol
    have : Group.IsSolvable ↥g.range :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have hbot : g.range = ⊥ := by
      rw [← CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf]
      exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot _).mp inferInstance
    obtain ⟨y, rfl⟩ := hψ x
    have hy : y = 1 := Subtype.ext (by simpa [hbot] using y.2)
    exact hx1 (by rw [hy, map_one])
  ·
    exact hthin (uc22s213_thin8_of_isAlt_five hL.2.1 (hA5 g.range hle hperf _ hsimple ψ hψ))

theorem s21_3_of_rest {D : Data G} (hσ : UC6S846.SigmaStd D) (hKF : KF7Use D)
    (huniq : ∀ p ∈ D.sig, ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup 2 X →
      2 ≤ CFSG.Open.pRank p (normalizer (X : Set G) ⊓ D.M) → normalizer (X : Set G) ≤ D.M)
    (hK3 : StronglyEmbeddedThree) (h82 : F08.R82 D) (Ch : Choice2011 G)
    (hRest : S21_3Rest D Ch) : S21_3 D Ch := by
  intro h1930 c L hL ⟨b, hbB, hb1, hbL⟩
  by_contra hthin
  have hodd : Odd (orderOf b) := uc22p21d_odd_orderOf_of_mem_calB1 c.hB hbB
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (orderOf_eq_one_iff.not.mpr hb1)
  obtain ⟨a, haB, haL, hord⟩ : ∃ a ∈ c.B, CentralizesBar a L ∧ orderOf a = r :=
    ⟨b ^ (orderOf b / r), c.B.pow_mem hbB _, uc22p21d_centralizesBar_pow hbL _,
      orderOf_pow_orderOf_div (orderOf_pos b).ne' hrd⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact Nat.not_odd_iff_even.mpr even_two (hodd.of_dvd_nat hrd)
  have hAr : Nat.card (zpowers a) = r := by rw [Nat.card_zpowers, hord]
  have hAB : zpowers a ≤ c.B := zpowers_le.mpr haB
  have hAM : zpowers a ≤ D.M := hAB.trans (c.hle.trans c.hBM)
  have hY : (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G)) ⊔ pCoreOf 2 L = L :=
    uc22p21d_sup_pCore_eq hr hr2 hAr fun g hg => uc22p21d_centralizesBar_of_mem_zpowers haL hg
  refine s21_2 D Ch h1930 c _ hAB ?_
  by_cases hp : ∃ p ∈ D.sig,
      2 ≤ CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M)
  · obtain ⟨p, hp, h2⟩ := hp
    exact uc22s213t_normalizer_le_of_sig hσ hKF huniq hL hthin hp hAM hr hAr hY h2
  by_cases h3 : IsStronglyPEmbedded 3 D.M ∧ 2 ≤ CFSG.Open.pRank 3 L
  · exact uc22s217l2t_normalizer_le_of_strongThree D.standing.simple D.standing.kProper hK3 h3.1
      hL.1.le hL.2.1 h3.2 hr hAM hAr hY
  have hm3 : CFSG.Open.pRank 3 L ≤ 2 := by
    by_contra h
    exact h3 ⟨h82 L ⟨hL.1, hL.2.1, by omega,
      Or.inl (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.2.2)⟩, by omega⟩
  have hk1 : IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1 := fun hM => by
    by_contra h
    exact h3 ⟨hM, by omega⟩
  push Not at hp
  exact absurd haL (hRest h1930 c L hL hthin hm3 hk1 a haB (hord ▸ hr)
    fun p hp' => Nat.le_of_lt_succ (hp p hp'))

theorem s21_3_of_restNN {D : Data G} (hσ : UC6S846.SigmaStd D) (hKF : KF7Use D)
    (huniq : ∀ p ∈ D.sig, ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup 2 X →
      2 ≤ CFSG.Open.pRank p (normalizer (X : Set G) ⊓ D.M) → normalizer (X : Set G) ≤ D.M)
    (hK3 : StronglyEmbeddedThree) (h82 : F08.R82 D) (h869N : F08.R869N D) (Ch : Choice2011 G)
    (hRest : S21_3RestNN D Ch) : S21_3 D Ch :=
  s21_3_of_rest hσ hKF huniq hK3 h82 Ch (s21_3Rest_of_restNN hσ h869N hRest)

theorem s21_3_dataOfSetup_of_restNN (hSQ : StronglyEmbeddedSolvableQ)
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree) (hS : RankThreeUC.Standing G)
    (S : RankThreeUC.Setup G) (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h869N : F08.R869N (PartTwo.Three.dataOfSetup hS S)) (Ch : Choice2011 G)
    (hRest : S21_3RestNN (PartTwo.Three.dataOfSetup hS S) Ch) :
    S21_3 (PartTwo.Three.dataOfSetup hS S) Ch :=
  s21_3_of_restNN (UC6S846.sigmaStd_dataOfSetup hS S) (kf7Use_dataOfSetup hSQ hSE hK3 hS S)
    (fun _ hq => PartTwo.Three.normalizer_le_of_mem_sigmaOf S hq) hK3 h82 h869N Ch hRest

end CFSG.LocalAnalysis.UniquenessCase.UC22
