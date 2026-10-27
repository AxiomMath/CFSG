module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3FrameNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3SplitCase
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3SL8Model

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Polynomial CoordSL Multiplicative

section Inputs

theorem ggSixLSixSevenA3EntryPSL_holds : GGSixLSixSevenA3EntryPSL := by
  intro G _ _ p B Bs x L D J n f ψ hctx _ _ _ hA
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hctx.2.2.2.1.1.2.2.1; omega⟩
  have : Fact p.Prime := ⟨hctx.prime⟩
  by_cases hpf : p ∣ 2 ^ f - 1
  · exact (false_of_a3Case_of_dvd hctx hpf hA).elim
  obtain ⟨g, hgi, s, r, ε, A₀, hC, hCp, hζ, i, j, k, l, hij, hik, hil, hjk, hjl, hkl, hD, hk, hl,
    hn, he, hs, hr, hK2⟩ := exists_a3_frame_nonsplit hctx hpf hA
  have hCa := rootMat_apply_of_card_two hK2 he
  have hσ : Function.Injective (![i, j, k, l] : Fin 4 → Fin s) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  obtain ⟨Φ, hΦ⟩ := exists_hom_eq_nsSL hn he hs hr ε hC hCa (![i, j, k, l] : Fin 4 → Fin s) hσ
  have hι : ∀ (a : ℕ) (ha : a < 4),
      frameHom ψ A₀ ε hC hCp (ofAdd (Pi.single ((![i, j, k, l] : Fin 4 → Fin s) ⟨a, ha⟩) 1)) =
        ((SLRep.ggFrame ψ A₀).comp Φ) (GGA3.omSL a ha) := by
    intro a ha
    rw [MonoidHom.comp_apply, hΦ a ha]
    refine congrArg (SLRep.ggFrame ψ A₀) (congrArg (SLNS.nsSL ε hC) ?_)
    funext u
    by_cases h : u = (![i, j, k, l] : Fin 4 → Fin s) ⟨a, ha⟩
    · simp [h, ZMod.val_one]
    · simp [h, Pi.single_apply]
  refine ⟨(SLRep.ggFrame ψ A₀).comp Φ, ?_, ?_, ?_⟩
  · calc ((SLRep.ggFrame ψ A₀).comp Φ).range ≤ (SLRep.ggFrame ψ A₀).range := by
          rintro _ ⟨x, rfl⟩
          exact ⟨Φ x, rfl⟩
      _ = ψ.range := SLRep.range_ggFrame ψ A₀
      _ = _ := hctx.range_eq
  · refine hD.trans ?_
    rw [GGA3.slD, MonoidHom.map_closure, Set.image_pair]
    exact le_of_eq (by rw [← hι 0 (by norm_num), ← hι 1 (by norm_num)]; rfl)
  · rw [GGA3.slT, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [← hι 2 (by norm_num)]
      exact hk
    · rw [← hι 3 (by norm_num)]
      exact hl

end Inputs

end CFSG.StandardType
