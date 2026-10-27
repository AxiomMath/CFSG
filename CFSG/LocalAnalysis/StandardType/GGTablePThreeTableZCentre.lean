module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs

import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.WeakClosure81.W16LPU3Cover
import CFSG.ClassicalGroups.UnitaryFlag.PointSylow
import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryGen
import CFSG.LocalAnalysis.WeakClosure81.W16Inputs
import CFSG.LocalAnalysis.WeakClosure81.W16QDefs

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover

theorem card_center_dvd_three_of_twA
    {J : Type} [Group J] [Finite J] {n : ℕ}
    (hJ : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 2 ∧ lab.n = 3 * n)) :
    Nat.card (Subgroup.center J) ∣ 3 := by
  obtain ⟨lab, _hlab, R, _instR, I, F, θ, _hs, _hna, hP, hm⟩ :=
    largeEvenMarking_exists_markedModel hJ
  have hmarked : MarkedModel lab (J ⧸ Subgroup.center J) := MarkedModel.of_mulEquiv θ.symm hm
  have hPSU : CFSG.LocalAnalysis.WeakClosure81.IsPSUGp (J ⧸ Subgroup.center J) 3 (3 * n) := by
    obtain ⟨t, l, nl⟩ := lab
    obtain ⟨ht, hr, hn⟩ := hP
    dsimp only at ht hr hn
    subst ht
    subst hr
    subst hn
    dsimp only [CFSG.LocalAnalysis.WeakClosure81.IsPSUGp, MarkedModel, markTag, markRank,
      markChar, markDeg] at hmarked ⊢
    exact hmarked
  exact (CFSG.LocalAnalysis.WeakClosure81.w16l_isU3Shape_of_perfect hJ.1 hPSU).2.2

end CFSG.StandardType.TablePThreeKG

end
