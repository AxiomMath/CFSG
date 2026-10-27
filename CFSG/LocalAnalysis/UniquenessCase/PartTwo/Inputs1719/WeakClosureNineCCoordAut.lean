module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordDataAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Aut

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoordA6.AutCoord

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6
  CFSG.LocalAnalysis.WeakClosure81.NFA6.Core CFSG.LocalAnalysis.WeakClosure81.CoordA6.Core

theorem Hs_gens : ∀ D ∈ AutCData.Hs, ∀ c ∈ D.K.gc,
    ∃ x ∈ (A6Models.psl29 : Set P10), code x = c := fun D hD c hc => by
  obtain ⟨x, hx, hxc⟩ := exists_psl29_of_code (List.contains_iff_mem.mp
    (List.all_eq_true.mp ((List.all_eq_true.mp AutCData.Hs_gens) D hD) c hc))
  exact ⟨x, hx, hxc⟩

theorem Ks_gens : ∀ D ∈ AutCData.Ks, ∀ c ∈ D.K.gc,
    ∃ x ∈ (A6Models.autA6 : Set P10), code x = c := fun D hD c hc => by
  obtain ⟨x, hx, hxc⟩ := AutModel.decode_autL c (List.contains_iff_mem.mp
    (List.all_eq_true.mp ((List.all_eq_true.mp AutCData.Ks_gens) D hD) c hc))
  exact ⟨x, hx, hxc⟩

theorem coordModel :
    ∃ Es₀ : Subgroup P10, Coord.CoordModel A6Models.autA6 A6Models.psl29 P0 Es₀ := by
  obtain ⟨Es₀, hEst, hET, hTE, hEe, hE4⟩ := exists_estar AutModel.desc_T AutCData.EstS_ok
    AutCData.EstS_gens AutCData.EstS_norm AutCData.EstS_elem AutCData.EstS_len
  refine ⟨Es₀, Coord.modelBase_of_modelFacts AutModel.modelFacts,
    sq_spec AutModel.desc_T (fun _ hc => exists_psl29_of_code hc) AutCData.sq_ok,
    mov_model AutModel.desc_T AutModel.isPGroup_T AutData.seed_ok
      (entries_sub AutData.entries_ok) AutCData.Hs_ok Hs_gens AutCData.mov_ok,
    fix_model AutModel.desc_T AutModel.isPGroup_T AutData.seed_ok
      (entries_sub AutData.entries_ok) AutCData.Ks_ok Ks_gens hEst.mem AutCData.fix_ok,
    normal_spec AutModel.desc_T AutModel.isPGroup_T (fun _ hc => exists_psl29_of_code hc)
      AutCData.pc_ok (normal4_eq AutModel.desc_T AutData.inv_ok AutData.entries_ok
        AutData.seed_ok AutData.nonNormal_ok hEst AutCData.EstS_eq),
    fun _ => ⟨hET, hTE, hEe, hE4, star_model AutModel.desc_T AutModel.isPGroup_T hEst
      AutData.seed_ok (entries_sub AutData.entries_ok) AutCData.Hs_ok Hs_gens
      AutCData.star_ok, AutModel.modelFacts.close Es₀ hET hTE hEe hE4⟩⟩

end CFSG.LocalAnalysis.WeakClosure81.CoordA6.AutCoord

namespace CFSG.LocalAnalysis.WeakClosure81

theorem tcCoordAut_holds : TCCoordAut := by
  intro B _ _ L D hD hLn hL1 hLp hB
  obtain ⟨e⟩ := NFA6.nonempty_mulEquiv_autA6_of_isAutOf hB
  obtain ⟨Es₀, hM⟩ := CoordA6.AutCoord.coordModel
  exact Coord.coordFacts_of_equiv hM e hLn hL1 hLp hD

end CFSG.LocalAnalysis.WeakClosure81
