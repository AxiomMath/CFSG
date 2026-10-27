module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSp4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.RootFree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.RootInH
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.LongRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.TauRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.TauReducible

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Lin2.Five (tauSp)

theorem k_19_19_sp4TorusRed_holds : K_19_19_sp4TorusRed := by
  intro K _ _ _ n p hq hn hodd hp hpd H hHH hT hpr
  change IsTorusReducible H
  have hK : 8 ≤ Nat.card K := by
    rw [hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  by_contra hred
  by_cases hX : IsRootFree (H ⊔ torus 2 K)
  · apply hred
    rw [eq_bot_of_isRootFree hq hn hodd hHH hX]
    exact isTorusReducible_bot
  obtain ⟨a, b, hab, hH⟩ := exists_root_subgroup_le_of_not_isRootFree hT hX
  by_cases hb : b = a.swap
  · subst hb
    obtain ⟨h0, h1⟩ := lam_range_le_of_long_root hK hT (a := a) (fun s => hH s) hred
    have h2 := two_le_pRank_of_lam_range_le hq hp hpd h0 h1
    omega
  · by_cases hτ : IsTorusReducible (H.map tauSp)
    · rcases isTorusReducible_or_two_le_pRank_of_tau hK hq hp hpd hHH hT hτ with h | h
      · exact hred h
      · omega
    · obtain ⟨c, hc⟩ := exists_long_root_le_map_tauSp hab hb hH
      obtain ⟨h0, h1⟩ := lam_range_le_of_long_root hK (torus_le_normalizer_map_tauSp hT) hc hτ
      have h2 := two_le_pRank_of_lam_range_le hq hp hpd h0 h1
      rw [pRank_map_tauSp hp] at h2
      omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
