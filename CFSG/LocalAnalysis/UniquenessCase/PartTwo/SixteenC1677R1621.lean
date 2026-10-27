module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21CasesA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21CasesB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21SU4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Sp6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677Glue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Sixteen21

theorem card_mbar_dvd_of_realizes {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {A : Subgroup (MulAut (Vtil V₀ V hV))}
    (hT : (tensorPairModel SL32 SL32).RealizesMod A)
    (hnorm : Mbar D.M V₀ V hV ≤ normalizer (A : Set (MulAut (Vtil V₀ V hV)))) :
    Nat.card (Mbar D.M V₀ V hV) ∣ 2 * 168 ^ 2 := by
  obtain ⟨e, he⟩ := CFSG.Quasithin.H.L3Wr.exists_model hT
  have h2 : (Mbar D.M V₀ V hV).map (CFSG.Quasithin.H.congrHom e) ≤
      CFSG.Quasithin.H.L3Wr.norm := by
    have h3 : (Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV)))).map
        (CFSG.Quasithin.H.congrHom e) =
        Subgroup.normalizer (A.map (CFSG.Quasithin.H.congrHom e)) :=
      Subgroup.map_equiv_normalizer_eq A (MulAut.congr e)
    have h4 := (Subgroup.map_mono (f := CFSG.Quasithin.H.congrHom e) hnorm).trans
      (le_of_eq h3)
    have h5 := congrArg (fun P : Subgroup (MulAut CFSG.Quasithin.H.L3Wr.WMod) =>
      Subgroup.normalizer (P : Set (MulAut CFSG.Quasithin.H.L3Wr.WMod))) he
    exact h4.trans (le_of_eq h5)
  have hd : Nat.card (Mbar D.M V₀ V hV) ∣ Nat.card CFSG.Quasithin.H.L3Wr.norm := by
    rw [← CFSG.Quasithin.H.card_map_congrHom e (Mbar D.M V₀ V hV)]
    exact Subgroup.card_dvd_of_le h2
  rwa [CFSG.Quasithin.H.L3Wr.card_norm] at hd

theorem card_mbar_dvd_of_case7F {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Case167_7F D V₀ V hV) : Nat.card (Mbar D.M V₀ V hV) ∣ 2 * 168 ^ 2 :=
  card_mbar_dvd_of_realizes hc.tensor_realizes (mbar_le_normalizer_fstarBar D.M V₀ V hV)

theorem one_le_pRank_of_case7F {D : Data G} (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V} (hH : Hyp16 D V₀ V) (hc : Case167_7F D V₀ V hV) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank 7 (D.M ⊓ centralizer ({v} : Set G)) := by
  have h7 : 7 ∈ D.sig := by rw [hc.2.2]; exact Set.mem_singleton 7
  refine one_le_pRank_of_not_dvd_mbar hV hH (p := 7) (k := 3) (by norm_num)
    (by norm_num) (D.sig_rank 7 h7) (hSg.three_le 7 h7) ?_
  intro hdiv
  exact absurd (hdiv.trans (card_mbar_dvd_of_case7F hc)) (by norm_num)

theorem r1621_holds_F {D : Data G} (h7 : R16_7F D) (h165 : R16_5 D) (h136 : R4_136 D)
    (h1217 : R1217 D) (hSg : UC6S846.SigmaStd D) (hSU : RSU4NatFix)
    (hSp : RSp6SmallIndex) : R1621 D := by
  intro V₀ V h16
  obtain ⟨L₀, hS₀, hne₀, hConc₀⟩ := h136 V₀ V h16
  obtain ⟨L, hS, hne, hConc, h7L⟩ := h7 V₀ V L₀ h16.hyp125.isElemAbelian hS₀ hne₀ hConc₀
  have hSect : Sect16 D V₀ V L h16.hyp125.isElemAbelian := ⟨hS, hne, hConc⟩
  rcases h7L with hc | hc | hc | hc | hc | hc | hc | hc
  · exact ⟨3, hc.2.2.1, one_le_pRank_of_case1 _ h16 hS.hyp151 hc⟩
  · exact ⟨7, hc.2.2.2, one_le_pRank_of_case2 h1217 hSg hSect hc⟩
  · exact ⟨3, hc.2.2.2, one_le_pRank_of_case3 h1217 hSg hSect hc⟩
  · exact ⟨3, hc.2.2, one_le_pRank_of_case4 hSU _ h16 hS.hyp151 hc⟩
  · exact ⟨5, hc.2.2, one_le_pRank_of_case5 hSg _ h16 hc⟩
  · exact ⟨3, hc.2.2, one_le_pRank_of_case6 h165 hSect hc⟩
  · exact ⟨7, hc.2.2, one_le_pRank_of_case7F hSg h16 hc⟩
  · exact ⟨3, hc.2.2.1, one_le_pRank_of_case8 hSp h1217 _ h16 hS.hyp151 hc⟩

end Sixteen21

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
