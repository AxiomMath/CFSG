module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordDataM10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6M10

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoordA6.M10Coord

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6
  CFSG.LocalAnalysis.WeakClosure81.NFA6.Core CFSG.LocalAnalysis.WeakClosure81.CoordA6.Core

theorem Hs_gens : ∀ D ∈ M10CData.Hs, ∀ c ∈ D.K.gc,
    ∃ x ∈ (A6Models.psl29 : Set P10), code x = c := fun D hD c hc => by
  obtain ⟨x, hx, hxc⟩ := exists_psl29_of_code (List.contains_iff_mem.mp
    (List.all_eq_true.mp ((List.all_eq_true.mp M10CData.Hs_gens) D hD) c hc))
  exact ⟨x, hx, hxc⟩

theorem Ks_gens : ∀ D ∈ M10CData.Ks, ∀ c ∈ D.K.gc,
    ∃ x ∈ (A6Models.m10 : Set P10), code x = c := fun D hD c hc =>
  M10Model.decode_gens c (List.contains_iff_mem.mp
    (List.all_eq_true.mp ((List.all_eq_true.mp M10CData.Ks_gens) D hD) c hc))

theorem coordModel : Coord.CoordModel A6Models.m10 A6Models.psl29 M10Model.T₀ ⊥ where
  base := Coord.modelBase_of_modelFacts M10Model.modelFacts
  sq := sq_spec M10Model.desc_T (fun _ hc => exists_psl29_of_code hc) M10CData.sq_ok
  mov := mov_model M10Model.desc_T M10Model.isPGroup_T M10Data.seed_ok
    (entries_sub M10Data.entries_ok) M10CData.Hs_ok Hs_gens M10CData.mov_ok
  fix := fix_model M10Model.desc_T M10Model.isPGroup_T M10Data.seed_ok
    (entries_sub M10Data.entries_ok) M10CData.Ks_ok Ks_gens
    (fun x => by rw [mem_bot, List.mem_singleton, code_eq_cid_iff]) M10CData.fix_ok
  normal := normal_spec M10Model.desc_T M10Model.isPGroup_T (fun _ hc => exists_psl29_of_code hc)
    M10CData.pc_ok fun _ hFT hTF hFe hF4 => (close_vacuous M10Model.desc_T M10Data.inv_ok
      M10Data.entries_ok M10Data.seed_ok M10Data.nonNormal_ok hFT hTF hFe hF4).elim
  star := fun h => absurd rfl h

end CFSG.LocalAnalysis.WeakClosure81.CoordA6.M10Coord

namespace CFSG.LocalAnalysis.WeakClosure81

theorem tcCoordM10_holds : TCCoordM10 := by
  intro B _ _ L D hD hLn hL1 hLp hB
  obtain ⟨e⟩ := NFA6.nonempty_mulEquiv_m10_of_isM10 hB
  exact Coord.coordFacts_of_equiv CoordA6.M10Coord.coordModel e hLn hL1 hLp hD

end CFSG.LocalAnalysis.WeakClosure81
