module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs

import CFSG.LocalAnalysis.StandardType.GGHdRo7LNC

public section

namespace CFSG.StandardType.HdRo7KNC

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem knc_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
      (GGResRowAt ggRowCorank2C p J K ∨ GGResRowAt ggRowSUCorank2 p J K) →
      ∃ S : Subgroup G, S ≤ K ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  intro G _ _ p B Bs x L D J y K hH hp hrow
  rcases hrow with hrowC | hrowU
  · obtain ⟨labJ, labK, hJlam, hKlam, hJlab, hKlab, hr⟩ := hrowC
    obtain ⟨rfl, hJtag, hJn, hKtag, hKn, hrk⟩ := hr
    have hJrank : 2 ≤ labJ.rank := by
      obtain ⟨t, l, n⟩ := labJ
      simp only at hJtag
      rcases hJtag with rfl | rfl
      · dsimp only [CFSG.Assembly.LargeEvenInLambda2] at hJlam
        exact hJlam.2.1
      · dsimp only [CFSG.Assembly.LargeEvenInLambda2] at hJlam
        exact hJlam.2.1
    have hl2 : 2 ≤ labK.rank := by omega
    exact CFSG.StandardType.HdRo7LNC.hdRo7LNCAux_sp_noncyclic hKtag hKn hl2 hKlab
  · obtain ⟨labJ, labK, hJlam, hKlam, hJlab, hKlab, hr⟩ := hrowU
    obtain ⟨rfl, hJtag, hJn, hKtag, hKn, hrk, hl6, hndvd⟩ := hr
    exact CFSG.StandardType.HdRo7LNC.hdRo7LNCAux_su_noncyclic hKtag hKn hl6 hKlab

end CFSG.StandardType.HdRo7KNC
