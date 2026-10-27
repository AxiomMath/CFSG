module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Norm
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private lemma s16h_e3_CycThreeCentAAAB_map_eq_of_mem_stabSub {W : Type*} [CommGroup W]
    {U : Subgroup W} {φ : MulAut W} (hφ : φ ∈ stabSub U) : U.map φ.toMonoidHom = U := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    exact (mem_stabSub.mp hφ u).2 hu
  · intro u hu
    refine Subgroup.mem_map.mpr ⟨φ⁻¹ u, ?_, ?_⟩
    · exact (mem_stabSub.mp hφ (φ⁻¹ u)).1 (by simpa using hu)
    · simp

theorem s16h_e3_cyc_stab_wTil_le_normalizer
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    {φ : MulAut (Vtil V₀ V hV)} (hφ : φ ∈ Mbar D.M V₀ V hV)
    (hφW : φ ∈ stabSub (wTil V₀ V hV L)) :
    φ ∈ Subgroup.normalizer ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) :
      Set (MulAut (Vtil V₀ V hV))) := by
  obtain ⟨t, htM, ht2, ht1, htr, hW⟩ := hc
  have hLbar_ne_bot : lBar V₀ V hV L ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥(lBar V₀ V hV L) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    exact hp.ne_one (hLp.2.symm.trans hcard)
  have hWt_ne_bot : wTil V₀ V hV L ≠ ⊥ := c8_wTil_ne_bot hV hLbar_ne_bot
  have hcommWt : commSub (wTil V₀ V hV L) (lBar V₀ V hV L) = wTil V₀ V hV L :=
    c8_commSub_wTil h.hyp151 hV
  have hWt_map : (wTil V₀ V hV L).map φ.toMonoidHom = wTil V₀ V hV L :=
    s16h_e3_CycThreeCentAAAB_map_eq_of_mem_stabSub hφW
  by_contra hφN
  have hbot : commSub (wTil V₀ V hV L)
      ((lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom) = ⊥ := (hW.2.1 φ hφ hφN).2
  have heq : commSub (wTil V₀ V hV L)
      ((lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom) = wTil V₀ V hV L := by
    calc
      commSub (wTil V₀ V hV L) ((lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom)
          = commSub ((wTil V₀ V hV L).map φ.toMonoidHom)
              ((lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom) := by rw [hWt_map]
      _ = (commSub (wTil V₀ V hV L) (lBar V₀ V hV L)).map φ.toMonoidHom :=
            s15_Core_commSub_map_conj _ _ _
      _ = (wTil V₀ V hV L).map φ.toMonoidHom := by rw [hcommWt]
      _ = wTil V₀ V hV L := hWt_map
  exact hWt_ne_bot (by rw [← heq]; exact hbot)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
