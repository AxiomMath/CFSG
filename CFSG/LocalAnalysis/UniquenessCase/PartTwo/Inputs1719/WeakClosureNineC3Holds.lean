module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC3Models
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine3CEmbed

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

theorem tcCoord3_holds : TCCoord3 := by
  intro B _ _ L D hD hLn hq hZ3 hC hρ
  have key : ∀ {G T : Subgroup NF3C.Y} {ι : B →* NF3C.Y}, Function.Injective ι → ι.range = G →
      L.map ι = NF3C.ML → D.map ι = T →
      (∃ Es : Subgroup (Equiv.Perm (Fin 46)),
        Coord3.CoordModel914 (G.map NF3C.ι46) (NF3C.ML.map NF3C.ι46) (T.map NF3C.ι46) Es) →
      ∃ Es : Subgroup B, CoordFacts914 L D Es := by
    intro G T ι hι hr hL hDT ⟨Es, hM⟩
    refine ⟨Es.comap (NF3C.ι46.comp ι),
      hM.coordFacts (fun a b h => hι (NF3C.ι46_injective h)) ?_ ?_ ?_⟩
    · rw [MonoidHom.range_comp, hr]
    · rw [← map_map, hL]
    · rw [← map_map, hDT]
  rcases NF3C.exists_embedding hLn hq hZ3 hC hρ hD with
    ⟨ι, hι, hr, hL, hDT⟩ | ⟨ι, hι, hr, hL, hDT⟩ | ⟨ι, hι, hr, hL, hDT⟩
  · exact key hι hr hL hDT NF3C.coordModel_P
  · exact key hι hr hL hDT NF3C.coordModel_A
  · exact key hι hr hL hDT NF3C.coordModel_M

end CFSG.LocalAnalysis.WeakClosure81
