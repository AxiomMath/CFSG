module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGammaInvolution
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGammaBounds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem commSub_sup_fixV_eq_top_of_conc4_136W {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hconc : Conc4_136W A t L) :
    commSub ⊤ L ⊔ fixV L = ⊤ := by
  refine le_antisymm le_top ?_
  calc ⊤ = (⨆ X ∈ conjSubs A (commSub ⊤ L), X) := hconc.1.symm
    _ ≤ commSub ⊤ L ⊔ fixV L := by
        refine iSup_le fun X => iSup_le fun hX => ?_
        obtain ⟨g, hgA, rfl⟩ := hX
        by_cases hgn : g ∈ Subgroup.normalizer (L : Set (MulAut W))
        · have hHg : L.map (MulAut.conj g).toMonoidHom = L := by
            simpa only [MulEquiv.coe_toMonoidHom] using!
              Subgroup.mem_normalizer_iff_map_conj_eq.mp hgn
          have hmap := Asc81c.commSub_map_conj L g
          rw [hHg] at hmap
          exact hmap.ge.trans le_sup_left
        · obtain ⟨hcomm, hcommW⟩ := hconc.2.1 g hgA hgn
          have hswap := commSub_le_fixV_of_commutator_eq_bot hcomm (commSub_eq_bot_iff.mp hcommW)
          rw [Asc81c.commSub_map_conj L g] at hswap
          exact hswap.trans le_sup_right

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
