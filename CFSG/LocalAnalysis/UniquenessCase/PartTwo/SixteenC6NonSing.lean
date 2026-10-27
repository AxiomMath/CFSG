module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Elem9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c6_nonsing_rank
    (D : Data G) (hstd : S168e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case163_6 D V₀ V hV L)
    (c : S16c6Coords V₀ V L hV) {w : G} (hw : w ∈ V) (hns : c.NonSingular w hw) :
    2 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨K, E, hK, hKM, hEK, hE, hcard, hfix⟩ := s16c6_exists_elem9 D hstd hS hc c hw hns
  have hodd : Odd (Nat.card E) := by rw [hcard]; decide
  have hEC : E ≤ centralizer ({w} : Set G) :=
    s16c6_le_centralizer_of_fix D hS hKM hK.2.1 hEK hw hfix (Or.inr hodd)
  exact CFSG.SectionRank.le_pRank (by norm_num) (le_inf (hEK.trans hKM) hEC) hE
    (k := 2) (by rw [hcard]; norm_num)
