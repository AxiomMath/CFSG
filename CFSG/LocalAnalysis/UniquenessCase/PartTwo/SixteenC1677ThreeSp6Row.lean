module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenStarRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6QuotientModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSimpleComponentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SchurSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSig
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s168e3_sp6_pRank_top
    {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {H : Subgroup (MulAut (Vtil V₀ V hV))} (hSp : IsSpn H 6 1) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) := by
  obtain ⟨-, K', hKf, hKfin, hKcard, ⟨e⟩⟩ := hSp
  letI : Field K' := hKf
  letI : Finite K' := hKfin
  have hcardK : Nat.card K' = 2 := by simpa using hKcard
  have hle : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSp 3 K')) :=
    CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedSp
      (K := K') (n := 3) Nat.prime_three (by rw [hcardK]; norm_num)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  exact hle

omit [Finite G] in
private theorem s168e3_sp6_center_two
    {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {H : Subgroup (MulAut (Vtil V₀ V hV))} (hSp : IsSpn H 6 1)
    (Q : Type) [Group Q] [Finite Q] (hq : CFSG.Open.IsQuasisimple Q)
    (he : Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥H)) :
    IsPGroup 2 ↥(Subgroup.center Q) := by
  classical
  obtain ⟨e⟩ := he
  let q : Q →* ↥H := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hqsurj : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker_eq : q.ker = Subgroup.center Q := by
    rw [show q = e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q)) from rfl,
      MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center Q))
        e.toMonoidHom e.injective, QuotientGroup.ker_mk']
  have hperf : Group.IsPerfect Q := Group.isPerfect_def.mpr hq.1
  have hdvd : Nat.card (Subgroup.center Q) ∣ 2 := by
    have h := c8SchurSp6_holds H Q hSp hperf q hqsurj hqker_eq.le
    rwa [hqker_eq] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exact IsPGroup.of_card (n := 0) (by rw [h1]; norm_num)
  · exact IsPGroup.of_card (n := 1) (by rw [h1]; norm_num)

theorem s15_eq_one_of_sp6_component_at_three
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSp : IsSpn (lBar V₀ V hV L) 6 1) :
    s15 D.M V₀ V hV L = 1 :=
  s15_eq_one_of_simple_component_of_three_rank (D := D) (V₀ := V₀) (V := V) (hV := hV)
    c hcomp (c8_isSimpleGroup_of_isSpn hSp).1 (r := 3) (by norm_num)
    (s168e3_sp6_pRank_top (V₀ := V₀) (V := V) (hV := hV) hSp)
    (fun Q _ _ hq he =>
      s168e3_sp6_center_two (V₀ := V₀) (V := V) (hV := hV) hSp Q hq he)

theorem case162_9_of_sp6_quotient_rank_eight
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSp : IsSpn (lBar V₀ V hV L) 6 1)
    (hirr : commSub ⊤ (lBar V₀ V hV L) ∈ irrSet (lBar V₀ V hV L))
    (hdim : E3.mQuot (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) = 8) :
    Case162_9 D V₀ V hV L := by
  have hs : s15 D.M V₀ V hV L = 1 := s15_eq_one_of_sp6_component_at_three c hcomp hSp
  have hgamma : gamma15 D.M V₀ V hV L = 8 := by
    have hstar : S16kStar D V₀ V L hV := c.toS16kStar hs
    exact hstar.gamma15_eq_mQuot.trans hdim
  have hcomm : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) = ⊤ := by
    simpa only [wTil, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hdimtop : E3.mQuot (⊤ : Subgroup (Vtil V₀ V hV))
      (fixV (lBar V₀ V hV L)) = 8 := by
    have := hdim
    rw [hcomm, top_inf_eq] at this
    exact this
  have hAnorm : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs hg)
  have hsig : D.sig = {3} := by
    refine c.sig_eq_singleton_of_pRank_lt_two 3 ?_
    intro q hq hq2 hq3
    have hrank := pRank_le_one_of_normalizes_sp6_quotient_rank_eight
      (W := Vtil V₀ V hV) (H := lBar V₀ V hV L) (A := Mbar D.M V₀ V hV)
      (s15_Infra_vtil_sq_eq_one V₀ V hV) hSp hcomm hirr hdimtop hAnorm hq hq2 hq3
    omega
  refine ⟨hSp, hgamma, hs, hsig, ?_⟩
  exact c.std.pRank_eq_three (p := 3) (by rw [hsig]; exact Set.mem_singleton 3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
