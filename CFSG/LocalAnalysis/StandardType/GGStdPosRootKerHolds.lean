module

public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerGen
public import CFSG.LocalAnalysis.StandardType.GGRankOneTags
public import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
public import CFSG.LieType.Steinberg.Minuscule.Form
public import CFSG.Timmesfeld.ARS.CaseEFrameOf
public import CFSG.Timmesfeld.ARS.CaseEConfig
public import CFSG.Timmesfeld.ARS.LinearMain
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType

theorem ggRootKerStmt_holds :
    GGRootKerStmt := by
  intro t n f hadm hrank ht p hp hp2 hpf ν hν u i
  obtain ⟨x, C, O, hE, -⟩ := ggRankOneModel_of_tag ht hadm hrank
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GaloisField 2 f)ˣ = 2 ^ f - 1 := by
    rw [Nat.card_units, GaloisField.card 2 f (by have := hadm.2.1; omega)]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 f)ˣ) p (hcard ▸ hpf)
  obtain ⟨hW, hle3⟩ := ggTag_weylMatrix ht hadm
  have h3 : 3 ≤ (ggU t n f).D.rank := by
    rw [lieUniversal_rank_eq_bnRank t n 2 f Nat.prime_two hadm hrank]
    exact hrank
  have hdp : (ggU t n f).D.divisible = ∅ ∧
      ((ggU t n f).D.cartan.map (Int.cast : ℤ → ℚ)).PosDef := by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [bnRank] at hrank; omega⟩
      exact ⟨rfl, TauCeti.posDef_map_intCast_cartanMatrix_A m⟩
    · have hn3 : 3 ≤ n := by simpa only [bnRank] using hrank
      have hU : ggU .POmegaPlus n f =
          ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
            Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
        simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
      rw [hU]
      exact ⟨rfl, CFSG.Timmesfeld.ARS.CaseE.posDef_D n⟩
    · exact ⟨rfl, Steinberg.Minuscule.posDef_cartan_E6⟩
    · exact ⟨rfl, Steinberg.Minuscule.posDef_cartan_E7⟩
    · exact ⟨rfl, CFSG.Timmesfeld.ARS.CaseE.posDef_E8⟩
  exact ggRootKer_of_chevalleyExtras hE hdp.1 hdp.2 (ggSimplyLacedConnected_of_weyl hW hle3) h3
    hp hp2 hζ hν u i

end CFSG.StandardType

end
