module

public import CFSG.Sporadic.SuzI301Cover.Elements
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301CoverSplit

public section

namespace CFSG.Sporadic.SuzI301Cover

open CFSG.Open CFSG.Monster.B.Co2 CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzI301
  CFSG.Sporadic.SuzI301Cover.Native CFSG.LocalAnalysis.GLTheoremA.H301


theorem suzh_split (hd : dP ∈ suzM) (E : Type) [Group E] [Finite E] (π : E →* ↥suzM)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center E) (hk3 : Nat.card π.ker = 3) :
    ∃ Bh : Subgroup E, IsElemAbelian 3 Bh ∧ Bh ⊓ Subgroup.center E = ⊥ ∧
      Bh.map π = B1.subgroupOf suzM ∧ ∃ dh ∈ Bh, π dh = ⟨dP, hd⟩ := by
  obtain ⟨Bh, hBh, hBhk, hBhmap, hlift⟩ := exists_elemAbelian_complement_of_noForms π hπ hker.le
    hk3 bM bM_comm bM_pow_three nM nMat nM_conj noAltForm noLinForm bM_indep
  obtain ⟨dh, hdh, hdhπ⟩ := hlift 0
  refine ⟨Bh, hBh, by rw [← hker]; exact hBhk, by rw [hBhmap, closure_range_bM], dh, hdh, ?_⟩
  rw [hdhπ]
  exact Subtype.ext bP_zero

end CFSG.Sporadic.SuzI301Cover
