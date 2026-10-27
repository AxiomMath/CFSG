module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFourN
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.FourInputN.OnlyL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.FourInputN.Orbit
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.FourInputN.RootLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TIFusion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s23_4_inputN_of (D : Data G) (Ch : Choice2011 G) (h208 : S20_8 D)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch)
    (hTL : H1930 D → ∀ c : Ctx23L D Ch, D.T ⊓ c.L ≤ centralizer (D.U : Set G)) :
    S23_4_inputN D Ch := by
  intro h1930 c
  obtain ⟨hV, n, hcard, hnat⟩ := h2 h1930 c
  have hcardU : Nat.card D.U = 2 ^ n := by
    rw [← h3 h1930 c]
    exact hcard
  have hUV : D.U ≤ c.V := by
    rw [← h3 h1930 c, Ctx23L.U0, Ctx23L.V]
    exact uc22p22v_conjClosure_mono inf_le_left D.Z
  have hU := c.eq_infCentralizer_of_card hV hnat hUV (hTL h1930 c) hcardU
  rw [c.X23_4_eq_L h208 h1930 hU]
  constructor
  · refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have haN : a ∈ normalizer (c.infCentralizer : Set G) := by
      have h : a ∈ normalizer (D.U : Set G) := by
        rw [Data.normalizer_U_eq D]
        exact ha.2
      rwa [hU] at h
    have hbN : b ∈ normalizer (c.infCentralizer : Set G) := by
      have h : b ∈ normalizer (D.U : Set G) := by
        rw [Data.normalizer_U_eq D]
        exact hb.2
      rwa [hU] at h
    have h1 := c.commutator_mem_centralizer_infCentralizer hV hnat ha.1 hb.1 haN hbN
    rwa [← hU] at h1
  · obtain ⟨y, hyL, hyN, htr⟩ := c.exists_zpowers_transitive hV hnat
    have hyM : y ∈ D.M := by
      rw [← Data.normalizer_U_eq D, hU]
      exact hyN
    exact irrOn_of_zpowers_transitive (A := c.L ⊓ D.M) (U := D.U) (y := y)
      ⟨hyL, hyM⟩ (by rw [hU]; exact htr)

end CFSG.LocalAnalysis.UniquenessCase.UC22
