module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2s
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2t
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeZ3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallSigBig
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Small

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

theorem s15Small_case_one (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (hSimple : RSimple153)
    (h127 : R127 D) (h115 : F11.R115 D) (h119 : F11.R119 D) (h82 : F08.R82 D)
    (h880 : F08.R880 D) (h1217 : R1217 D) (hT : RTable137) (hTor : RTorus3_153)
    (hAut : RAutRank153) (hAbs : RAbsIrr153) (hCov : RCover3Rank153) (hOm : RRank3Omega153)
    (hSchur : RSchur153) (hIso : RIso153) (hNotJ2 : RNotJ2) (hPerfT : RPerfType153)
    (hne : D.sig.Nonempty) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hV0 : mSub V₀ ≤ 2)
    (hL : barSub V₀ V hV L ≠ ⊥) (hshape : s15Shape D V₀ V hV L K₀)
    (hrs : s15Rs D V₀ V hV L K₀ = 1)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL4 : s15ListFour ↥(lBar V₀ V hV L)) : Case153_1 D V₀ V hV L := by
  have hs : s15 D.M V₀ V hV L = 1 := ((s15_Three_rs_eq_one_iff D V₀ V hV L K₀).1 hrs).2
  have hperf' := s15_Three_perf_star h1217 h hV hshape hrs hperf
  obtain ⟨K, hK⟩ := s15_Three_cover_K hSimple h127 h119 h1217 h hV hshape hperf
  have hk := s15_Three_k_one h82 h880 hCov hOm hSchur hIso hNotJ2 hV hshape hrs hK hL4
  have hsig := s15_Three_sig_three hAut hAbs h127 h115 h1217 h hV hL hs hperf' hL4 hne hV0
  have hnot : ¬ s15O1a D V := s15_Three_not_O1a_of_unique h61 h63 h127 h.hyp125 (Or.inr hk)
  have hΩ : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1 := by
    rcases hL4 with hΩ | h6 | h7 | h4
    · exact hΩ
    · exact absurd (s15_Three_O1a_of_alt hAut hAbs hT hTor h127 h115 h1217 h hV hL hs hperf'
        (Or.inl h6) hsig hV0) hnot
    · exact absurd (s15_Three_O1a_of_alt hAut hAbs hT hTor h127 h115 h1217 h hV hL hs hperf'
        (Or.inr (Or.inl h7)) hsig hV0) hnot
    · exact absurd (s15_Three_O1a_of_alt hAut hAbs hT hTor h127 h115 h1217 h hV hL hs hperf'
        (Or.inr (Or.inr h4)) hsig hV0) hnot
  exact ⟨hΩ, (hPerfT _ _ _ _ hperf').2.2.2.2 hΩ, hsig,
    s15_Three_rank_three hAut hAbs hT hTor h127 h115 h1217 h hV hL hs hperf' hΩ hsig hV0 hnot,
    hs, hV0⟩

theorem s15Small_case_two_big (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (hSimple : RSimple153)
    (hS2 : RSchur2_153) (h127 : R127 D) (h119 : F11.R119 D) (h1217 : R1217 D)
    (h82 : F08.R82 D) (h880 : F08.R880 D) (h1111 : R1111_153 D) (hRk : RRank3List153)
    (hCov : RCover3Rank153) (hSchur : RSchur153) (hIso : RIso153) (hNotJ2 : RNotJ2)
    (hPerfT : RPerfType153) (hAut : RAutRank153) (hAbs : RAbsIrr153) (hne : D.sig.Nonempty)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hsmall : mSub V₀ ≤ 2)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hO1 : s15O1a D V) (hbig : ¬ (s15Rs D V₀ V hV L K₀ = 1 ∧ s15ExcList ↥(lBar V₀ V hV L))) :
    Case153_2 D V₀ V hV L := by
  obtain ⟨hns, h3⟩ := s15_Three_unique_of_O1a h61 h63 h127 h.hyp125 hO1
  obtain ⟨K, hK⟩ := s15_Three_cover_K hSimple h127 h119 h1217 h hV hshape hperf
  have hL2 := s15_Three_K_two h82 h880 hRk hCov hSchur hIso hNotJ2 hV hK hperf hns
  have hle2 := s15_Three_rs_le_two h82 hS2 hSimple h127 h119 h1217 h hV hshape hperf hL2 hns
  have hrs1 : s15Rs D V₀ V hV L K₀ ≠ 1 := by
    intro hrs
    have hLK := s15_Three_lBar_eq hshape hrs
    apply hbig
    refine ⟨hrs, ?_⟩
    rw [hLK]
    rcases hL2 with h3' | h5'
    · exact Or.inl h3'
    · exact Or.inr (Or.inr (Or.inl h5'))
  have hge := s15_Three_one_le_rs D V₀ V hV L K₀
  have hrs2 : s15Rs D V₀ V hV L K₀ = 2 := by omega
  obtain ⟨p, hp, hsigp, hrk⟩ :=
    s15Small_sig_big hAut hAbs hSimple h61 h127 h1111 h1217 h hV hsmall hshape hperf hL2 hrs2
      hne h3
  refine s15_Three_case_two_of p hshape.1 ?_ hshape.2.2.1 hsigp hrk hle2 (fun h1 => absurd h1 hrs1)
  rcases hp with ⟨rfl, hA5⟩ | ⟨rfl, hL3⟩
  · exact Or.inl ⟨rfl, hA5, (hPerfT _ _ _ _ hperf).2.1 hA5⟩
  · exact Or.inr ⟨rfl, hL3, (hPerfT _ _ _ _ hperf).1 hL3⟩

end Small

section Final

private theorem s15Small_not_perf_of_cyclic (hSimple : RSimple153) {V : Type} [CommGroup V]
    {X : Type} [Group X] [Finite X] {K : Subgroup (MulAut V)} {Z : Subgroup V}
    (hp : s15KNatPerf X K Z) (hc : IsCyclic X) : False := by
  have hq : IsSimpleGroup (X ⧸ Subgroup.center X) := (hSimple V X K Z hp).1.2
  have hcomm : ∀ a b : X, a * b = b * a := fun a b => by
    obtain ⟨g, hg⟩ := hc.exists_generator
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
    rw [← zpow_add, ← zpow_add, add_comm]
  haveI : Subsingleton (X ⧸ Subgroup.center X) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    refine QuotientGroup.eq.2 ?_
    rw [Subgroup.mem_center_iff]
    intro g
    exact hcomm g _
  exact (not_nontrivial_iff_subsingleton.2 ‹_›) hq.toNontrivial

theorem fifteen_three_small (D : Data G) (hx : DataExt D)
    (hMcL : RMcLaughlin) (hDer : RJPrime153) (hNorm : RNormNat153)
    (hT : RTable137) (hTor : RTorus3_153) (hRk : RRank3List153) (hAbs : RAbsIrr153)
    (hSimple : RSimple153)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (hS2 : RSchur2_153) (h127 : R127 D) (h115 : F11.R115 D) (h119 : F11.R119 D)
    (h1217 : R1217 D) (h1214 : F12.R1214 D) (h82 : F08.R82 D) (h880 : F08.R880 D)
    (h1111 : R1111_153 D) (hAut : RAutRank153)
    (hCov : RCover3Rank153) (hOm : RRank3Omega153) (hSchur : RSchur153) (hIso : RIso153)
    (hNotJ2 : RNotJ2) (hPerfT : RPerfType153) :
    R15_3Small D := by
  intro V₀ V L h hsmall htr
  have hne : D.sig.Nonempty := hx.sig_nonempty
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hL : barSub V₀ V hV L ≠ ⊥ := by
    obtain ⟨φ, -, hφ⟩ := htr
    exact s15_Three_barSub_ne_bot h hφ
  have hsemi := s15_Three_semisimple_AW_of_sSup_irr h (s15_semiBot_sSup_irr_star h1217 h hL htr)
  obtain ⟨K₀, hshape⟩ := s15_Three_shape hMcL hDer hNorm h1217 h hL hsemi
    (fun I I' hI hI' => s15_Three_trans_AW hx h61 h127 h1214 h1217 h hL hsemi I I' hI hI') htr
  by_cases hZ : IsCyclicOrd ↥(barSub V₀ V hV K₀) 3
  · have hZ3 := hshape.2.2.2.1.resolve_left
      (fun hp => s15Small_not_perf_of_cyclic hSimple hp hZ.1)
    exact Or.inr (Or.inr ⟨⟨K₀, hshape.1, hZ3.1, hshape.2.2.1,
      s15_Three_Z3_natural h1217 h hV hshape hZ3.1 hZ3.2⟩, Or.inl hsmall⟩)
  · have hperf := hshape.2.2.2.1.resolve_right (fun hz => hZ hz.1)
    by_cases hexc : s15Rs D V₀ V hV L K₀ = 1 ∧ s15ExcList ↥(lBar V₀ V hV L)
    · obtain ⟨hrs, hex⟩ := hexc
      by_cases hL2 : s15ListTwo ↥(lBar V₀ V hV L)
      · have hs : s15 D.M V₀ V hV L = 1 := ((s15_Three_rs_eq_one_iff D V₀ V hV L K₀).1 hrs).2
        have hperf' := s15_Three_perf_star h1217 h hV hshape hrs hperf
        exact absurd (s15_Three_V0_large hAut hAbs h127 h115 h1217 h hV hL hs hperf' hL2 hne)
          (by omega)
      · have hL4 : s15ListFour ↥(lBar V₀ V hV L) := by
          rcases hex with h1 | h2 | h3 | h4 | h5 | h6
          · exact absurd (Or.inl h1) hL2
          · exact Or.inr (Or.inr (Or.inr h2))
          · exact absurd (Or.inr h3) hL2
          · exact Or.inr (Or.inl h4)
          · exact Or.inr (Or.inr (Or.inl h5))
          · exact Or.inl h6
        exact Or.inl (s15Small_case_one h61 h63 hSimple h127 h115 h119 h82 h880 h1217 hT hTor hAut
          hAbs hCov hOm hSchur hIso hNotJ2 hPerfT hne h hV hsmall hL hshape hrs hperf hL4)
    · have hO1 : s15O1a D V := by
        rcases s15_Three_trich hT hRk hAbs hSimple h127 h119 h1217 h hV hL hshape with
          hO | hz | hb
        · exact hO
        · exact absurd hz hZ
        · exact absurd hb hexc
      exact Or.inr (Or.inl (s15Small_case_two_big h61 h63 hSimple hS2 h127 h119 h1217 h82 h880
        h1111 hRk hCov hSchur hIso hNotJ2 hPerfT hAut hAbs hne h hV hsmall hshape hperf hO1 hexc))

end Final

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
