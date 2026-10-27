module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Two
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Nat
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Proof
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem lBar_conj_eq_of_s15_eq_one {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : s15 D.M V₀ V hV L = 1) {g : MulAut (Vtil V₀ V hV)} (hg : g ∈ Mbar D.M V₀ V hV) :
    (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom = lBar V₀ V hV L := by
  have h1 : (conjSet (lBar V₀ V hV L) (Mbar D.M V₀ V hV)).ncard = 1 := h
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
  have hmem : lBar V₀ V hV L ∈ conjSet (lBar V₀ V hV L) (Mbar D.M V₀ V hV) :=
    s15_T7_mem_conjSet_self _ _
  have hmem' : (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom ∈
      conjSet (lBar V₀ V hV L) (Mbar D.M V₀ V hV) := ⟨g, hg, rfl⟩
  rw [ha, Set.mem_singleton_iff] at hmem hmem'
  rw [hmem', hmem]

theorem wTil_eq_top_of_case163_2 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Conc4_136 D V₀ V hV L) (h : s15 D.M V₀ V hV L = 1) : wTil V₀ V hV L = ⊤ := by
  obtain ⟨t, -, -, -, -, hsup, -⟩ := hc
  rw [← hsup]
  apply le_antisymm
  · exact le_iSup₂_of_le (wTil V₀ V hV L) ⟨1, (Mbar D.M V₀ V hV).one_mem, by
      ext x
      simp [wTil, lBar, Subgroup.mem_map]⟩ le_rfl
  · refine iSup₂_le fun X hX => ?_
    obtain ⟨g, hg, rfl⟩ := hX
    have h2 := Asc81c.commSub_map_conj (lBar V₀ V hV L) g
    rw [lBar_conj_eq_of_s15_eq_one h hg] at h2
    exact h2.symm.le

theorem exists_omegaModel_of_omegaPlus_eight {D : Data G} (h3 : R16_3_2 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hΩ : IsOmegaPlus ↥(lBar V₀ V hV L) 4 3) :
    ∃ S : OmegaModel (Vtil V₀ V hV), S.omega = lBar V₀ V hV L ∧ Nat.card S.K = 8 := by
  have h2 : Case163_2 D V₀ V hV L := h3 V₀ V L hV hS.setting hS.ne_bot hS.conc hΩ
  obtain ⟨-, hnat, hs⟩ := h2
  rw [wTil_eq_top_of_case163_2 hS.conc hs] at hnat
  obtain ⟨S, hS1, hS2⟩ := exists_omegaModel_of_natOmegaPlus (by norm_num : 2 ≤ 3) hnat
  exact ⟨S, hS1, by rw [hS2]; norm_num⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
