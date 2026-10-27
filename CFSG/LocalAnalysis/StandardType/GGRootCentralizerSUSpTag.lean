module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUSp
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Tags

theorem ggRootCentralizerCyclicTag_PSp : GGRootCentralizerCyclicTag .PSp := by
  intro G _ _ n f ψ _ hrk hker hC r hr Y hY hYd
  refine ⟨1, Y.one_mem, fun y hy => Subgroup.mem_sup_right ?_⟩
  obtain ⟨g, hg, hcg⟩ := PsiDiag.Symp.exists_mem_centralizer (F := GaloisField 2 f) hrk ψ hker
    (hYd y hy)
  have hcg' : y * g ∈ Subgroup.centralizer (ψ.range : Set G) := hcg
  have hg' : g ∈ ψ.range := hg
  rw [hC, Subgroup.mem_bot] at hcg'
  have hyG : y ∈ ψ.range := by
    rw [eq_inv_of_mul_eq_one_left hcg']
    exact ψ.range.inv_mem hg'
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans
      (CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := GaloisField 2 f) n).le
  have hcx := OTwoGen.centralizer_conj_le_ggOTwoPrime
    (RootCentSp.centralizer_le_ggOTwoPrime_of_mem_rootGroup (F := GaloisField 2 f) hγ hx hx1) u
  have key := OTwoGen.inf_centralizer_le_ggOTwoPrime ψ hinj hcx
  have hyr := (hY hy).2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyr ⊢
  exact key (Subgroup.mem_inf.mpr ⟨hyG, hyr⟩)

end Tags

end CFSG.StandardType
