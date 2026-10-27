module

public import CFSG.RankThree.GF2n.Smith81.S81VDefs
public import CFSG.RankThree.GF2n.Smith81.S81VFrameMat

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

theorem map_map_gLin (g h : SUid σ 6) (W : Submodule F (Fin 6 → F)) :
    (W.map (gLin h)).map (gLin g) = W.map (gLin (g * h)) := by
  have hl : gLin (g * h) = (gLin g).comp (gLin h) := LinearMap.ext fun v => gLin_mul g h v
  rw [hl, Submodule.map_comp]

theorem map_gLin_inf (g : SUid σ 6) (x y : Submodule F (Fin 6 → F)) :
    (x ⊓ y).map (gLin g) = x.map (gLin g) ⊓ y.map (gLin g) := by
  exact Submodule.map_inf (gLin g) (gLin_injective g)

theorem finrank_map_gLin (g : SUid σ 6) (W : Submodule F (Fin 6 → F)) :
    finrank F ↥(W.map (gLin g)) = finrank F ↥W := by
  exact (Submodule.equivMapOfInjective (gLin g) (gLin_injective g) W).finrank_eq.symm

theorem isPt_map (g : SUid σ 6) {W : Submodule F (Fin 6 → F)} (hW : IsPt σ W) :
    IsPt σ (W.map (gLin g)) := by
  have hT : IsTotIso σ W := hW.1
  have hd : finrank F ↥W = 3 := hW.2
  refine And.intro ?_ ?_
  · intro x hx y hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hy
    rw [herm_gLin]
    exact hT w hw w' hw'
  · rw [finrank_map_gLin]
    exact hd

end CFSG.RankThree.GF2n.Smith81.S81V
