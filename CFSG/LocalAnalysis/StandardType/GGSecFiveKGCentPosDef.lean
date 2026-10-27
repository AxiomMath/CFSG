module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType

theorem ggU_cartan_posDef
    {t : StatedLieTag} {n f : ℕ} (hrank : 3 ≤ bnRank t n)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) :
    ((ggU t n f).D.cartan.map (Int.cast : ℤ → ℚ)).PosDef := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [bnRank] at hrank; omega⟩
    exact TauCeti.posDef_map_intCast_cartanMatrix_A m
  · have hn3 : 3 ≤ n := by simpa only [bnRank] using hrank
    have hU : ggU .POmegaPlus n f =
        ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
          Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
      simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
    rw [hU]
    exact CFSG.Timmesfeld.ARS.CaseE.posDef_D n
  · exact Steinberg.Minuscule.posDef_cartan_E6
  · exact Steinberg.Minuscule.posDef_cartan_E7
  · exact CFSG.Timmesfeld.ARS.CaseE.posDef_E8

end CFSG.StandardType

end
