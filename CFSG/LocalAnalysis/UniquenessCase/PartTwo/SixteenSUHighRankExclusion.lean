module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCentralThreeCover
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wb
public import CFSG.Quasithin.EmptyFaithful.R3cBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_false_of_su_component_ge_five
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn : 5 ≤ n)
    (hSU : IsSUn ↥(lBar V₀ V hV L) n 1) : False := by
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  have hcompH : IsComponentOf H A := by simpa [H, A] using hcomp
  obtain ⟨K, hK, hbarK⟩ :=
    exists_calC_cover_of_component c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcompH
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  let C : Subgroup (Bar2 D.M) := barImage D.M K
  have hCmap : C.map ψ = H := by
    simpa [C, H] using
      barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hK hbarK ψ hψ
  have hCcomp : CFSG.IsComponent C := uc22p22l_barImage_isComponent hK
  have hCcompTop : IsComponentOf C ⊤ :=
    CFSG.Quasithin.A3.isComponentOf_top_iff.mpr hCcomp
  obtain ⟨eC, -⟩ := uc22p22l_barImage_equiv (L := D.M) hK
  have hoddC : Odd (Nat.card (Subgroup.center ↥C)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr eC).toEquiv]
    exact uc22p20p_odd_center_bar2 ↥K
  let f : ↥C →* ↥H := (ψ.comp C.subtype).codRestrict H (by
    intro x
    rw [← hCmap]
    exact Subgroup.mem_map_of_mem ψ x.2)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : MulAut (Vtil V₀ V hV)) ∈ C.map ψ := by
      rw [hCmap]
      exact y.2
    obtain ⟨x, hxC, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hxC⟩, Subtype.ext hxy⟩
  obtain ⟨Kf, hField, hFinite, hKcard, ⟨eH⟩⟩ := hSU
  let _field : Field Kf := hField
  let _finite : Finite Kf := hFinite
  have hqH : CFSG.Open.IsQuasisimple ↥H := hcompH.2.2
  have hqSU : CFSG.Open.IsQuasisimple ↥(StatedSU n (2 ^ 1) Kf) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eH.symm hqH
  let g : ↥C →* ↥(StatedSU n (2 ^ 1) Kf) := eH.toMonoidHom.comp f
  have hg : Function.Surjective g := eH.surjective.comp hf
  have hqC : CFSG.Open.IsQuasisimple ↥C :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hCcomp.1
  obtain ⟨eZ⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.quotCenter_equiv hqC hqSU g hg
  have hcenter : Subgroup.center ↥(StatedSU n (2 ^ 1) Kf) =
      (StatedScalars (Fin n) Kf).subgroupOf (StatedSU n (2 ^ 1) Kf) :=
    le_antisymm
      (CFSG.StandardType.center_statedSU_le_scalars (n := 1) (d := n) (F := Kf)
        hKcard (by omega))
      (CFSG.StandardType.scalars_le_center_statedSU (n := 1) (d := n) (F := Kf))
  let eproj : ↥C ⧸ Subgroup.center ↥C ≃*
      StatedProj (StatedSU n (2 ^ 1) Kf) :=
    eZ.trans (QuotientGroup.quotientMulEquivOfEq hcenter)
  have _fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have _charP : CharP Kf 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) hKcard
  obtain ⟨ρ, -, hρker, -⟩ :=
    CFSG.AGLEmbedding.kFactCoverUnitary (Y := Bar2 D.M) C hCcompTop hoddC n (2 ^ 1) Kf hKcard
      (by omega) (by
        rw [show (2 : ℕ) ^ 1 = 2 by norm_num]
        intro h
        injection h with hn3 _
        omega) eproj
  have h4Ctop : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.CentralThree.four_le_pRank_of_uniCover
      (K := Kf) (f := 1) (n := n) hKcard hn (by norm_num) ρ hρker
  have h4C : 4 ≤ CFSG.Open.pRank 3 C := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup C]
    exact h4Ctop
  have hmono : CFSG.Open.pRank 3 C ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
  have hquot : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) = CFSG.Open.pRank 3 D.M :=
    (CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient D.M).symm
  have h4M : 4 ≤ CFSG.Open.pRank 3 D.M := h4C.trans (hmono.trans (le_of_eq hquot))
  have hle : CFSG.Open.pRank 3 D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) D.M D.maxLocal.1
  have h3 : CFSG.Open.evenRank G = 3 := c.std.h3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
