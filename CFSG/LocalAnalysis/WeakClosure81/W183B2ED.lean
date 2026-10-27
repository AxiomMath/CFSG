module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
import CFSG.LocalAnalysis.WeakClosure81.W183B2EDAux2
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Defs
public import CFSG.LocalAnalysis.WeakClosure81.W18KernPack
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem br2ED (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T)) :
    ∃ ED : Subgroup (LGL 2 M.W) → Submodule (ZMod 2) M.W,
      Br2ED (packFamilyU D V H i M) (packSpaceU D V₀ V H i M) x.mB (packDeltaU D V H i M)
        ED := by
  classical
  refine ⟨x.w183b2ed_ED M, x.w183b2ed_comm_le M, ?_⟩
  intro A hA e he
  obtain ⟨g, hg, himg, hdelta⟩ := x.w183b2ed_exists_attaining M hA
  have hex : ∃ g : G, Gam183 V H (eOmegaZ H D.T) i g ∧ M.img (vInH V H g) = A ∧
      E3.mQuot (conjSubgroup V g) (vInH V H g) = packDeltaU D V H i M A :=
    ⟨g, hg, himg, hdelta⟩
  have hspec := Classical.choose_spec hex
  rw [x.w183b2ed_ED_eq M hex] at he
  obtain ⟨e₀, he₀E, he₀⟩ := M.ι_surj e
  have he₀' : e₀ ∉ x.w183b2ed_EDg (Classical.choose hex) := by
    intro hmem
    exact he (M.mem_sp.2 ⟨e₀, ⟨hmem, he₀E⟩, he₀⟩)
  have hrank := x.w183b2ed_rank_aux (M := M) hspec.1 he₀E he₀'
  rw [he₀, hspec.2.1, hspec.2.2] at hrank
  exact hrank

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
