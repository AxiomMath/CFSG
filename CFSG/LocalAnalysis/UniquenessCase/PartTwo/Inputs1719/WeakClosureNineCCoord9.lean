module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordDataPGL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6PGL

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoordA6.PGLCoord

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6
  CFSG.LocalAnalysis.WeakClosure81.NFA6.Core CFSG.LocalAnalysis.WeakClosure81.CoordA6.Core

theorem Hs_gens : ∀ D ∈ PGLCData.Hs, ∀ c ∈ D.K.gc,
    ∃ x ∈ (A6Models.psl29 : Set P10), code x = c := fun D hD c hc => by
  obtain ⟨x, hx, hxc⟩ := exists_psl29_of_code (List.contains_iff_mem.mp
    (List.all_eq_true.mp ((List.all_eq_true.mp PGLCData.Hs_gens) D hD) c hc))
  exact ⟨x, hx, hxc⟩

theorem Ks_gens : ∀ D ∈ PGLCData.Ks, ∀ c ∈ D.K.gc,
    ∃ x ∈ (A6Models.pgl29 : Set P10), code x = c := fun D hD c hc =>
  PGLModel.decode_gens c (List.contains_iff_mem.mp
    (List.all_eq_true.mp ((List.all_eq_true.mp PGLCData.Ks_gens) D hD) c hc))

theorem coordModel : Coord.CoordModel A6Models.pgl29 A6Models.psl29 PGLModel.T₀ ⊥ where
  base := Coord.modelBase_of_modelFacts PGLModel.modelFacts
  sq := sq_spec PGLModel.desc_T (fun _ hc => exists_psl29_of_code hc) PGLCData.sq_ok
  mov := mov_model PGLModel.desc_T PGLModel.isPGroup_T PGLData.seed_ok
    (entries_sub PGLData.entries_ok) PGLCData.Hs_ok Hs_gens PGLCData.mov_ok
  fix := fix_model PGLModel.desc_T PGLModel.isPGroup_T PGLData.seed_ok
    (entries_sub PGLData.entries_ok) PGLCData.Ks_ok Ks_gens
    (fun x => by rw [mem_bot, List.mem_singleton, code_eq_cid_iff]) PGLCData.fix_ok
  normal := normal_spec PGLModel.desc_T PGLModel.isPGroup_T (fun _ hc => exists_psl29_of_code hc)
    PGLCData.pc_ok fun _ hFT hTF hFe hF4 => (close_vacuous PGLModel.desc_T PGLData.inv_ok
      PGLData.entries_ok PGLData.seed_ok PGLData.nonNormal_ok hFT hTF hFe hF4).elim
  star := fun h => absurd rfl h

end CFSG.LocalAnalysis.WeakClosure81.CoordA6.PGLCoord

namespace CFSG.LocalAnalysis.WeakClosure81

theorem tcCoord9_holds : TCCoord9 := by
  intro B _ _ L D hD hLn hL1 hLp hB
  obtain ⟨e⟩ := NFA6.nonempty_mulEquiv_pgl29_of_isPGL2 hB
  exact Coord.coordFacts_of_equiv CoordA6.PGLCoord.coordModel e hLn hL1 hLp hD

end CFSG.LocalAnalysis.WeakClosure81
