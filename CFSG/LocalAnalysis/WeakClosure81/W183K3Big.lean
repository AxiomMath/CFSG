module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Leaves
public import CFSG.LocalAnalysis.WeakClosure81.W183K3DispAux
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneC
public import CFSG.LocalAnalysis.WeakClosure81.W183Q
import CFSG.LocalAnalysis.WeakClosure81.W183L31Pair
public import CFSG.LocalAnalysis.WeakClosure81.W183KStar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open W183K3

variable {G : Type} [Group G] [Finite G]

private theorem w183k3big_cj_conjSubgroup {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (y : LGL 2 W) (B : Subgroup (LGL 2 W)) : cj y (conjSubgroup B y) = B := by
  ext x
  rw [mem_cj, mem_conjSubgroup_iff]
  constructor
  · intro h
    rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x from by group] at h
  · intro hx
    rw [show y * (y⁻¹ * x * y) * y⁻¹ = x from by group]
    exact hx

theorem tail1812FourFreeKStar_of_big (hB : ListBNonabelian) (h3 : Tail1812Two_AS G)
    (h4 : Tail1812FourFreeKStarBig G) : Tail1812FourFreeKStar G := by
  intro h162 h172 h5_4 h5_11 h5_12 h5_13 D V₀ V H i c h2 hK g hgT hgK hgi hA
  by_cases hbig : ∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g')
  · exact h4 h162 h172 h5_4 h5_11 h5_12 h5_13 c h2 hK hbig hgT hgK hgi hA
  · obtain ⟨g', hg'not⟩ := not_forall.mp hbig
    obtain ⟨hg'gam, hnot⟩ := not_imp.mp hg'not
    have hlt : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g') < 3 :=
      not_le.mp hnot
    obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ (Hyp183.normalizer_eOmegaZ H D.T)
    have x : Ctx188 D V₀ V H i 3 := c.ctx188_three_AS h162 h5_11 h2
    have hgam : Gam183 V H (eOmegaZ H D.T) i g := w183k3_gam_of_not_le_ker x hgi hgK
    obtain ⟨Kk, F, hsoc, hKk, hperf, hFeq, hle, hcent, hodd⟩ :=
      MinCex183.kernel_182 hB h162 h172 h5_4 h5_11 h5_13 c h2 M hgam hgT
    have hker : KStarData Kk F := ⟨hsoc, hperf, hFeq, hle, hcent, hodd⟩
    have hg'K : ¬ vInH V H g' ≤ kerMV V H := w183k3_not_le_ker_of_gam x M hker hKk hg'gam
    have hrel2 : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g') = 2 := by
      rcases c.relIndex_cases hg'K with h2' | h3'
      · exact h2'
      · omega
    set A' : Subgroup (LGL 2 M.W) := M.img (vInH V H g') with hA'def
    have hA'mem : A' ∈ Ctx188.packFamilyU D V H i M := ⟨g', hg'gam, by rw [hA'def]⟩
    have hcardA' : Nat.card A' = 2 := by
      rw [hA'def, M.card_img (S := vInH V H g') inf_le_right]
      exact hrel2
    have hSyl : IsSylowIn 2 (M.img D.T) (M.img H) :=
      M.isSylowIn_img_of_isSylowIn c.hyp.isSylowIn_T
    have hA'H : A' ≤ M.img H := by
      rw [hA'def]
      exact M.img_mono inf_le_right
    have hab' : IsElemAbelian 2 (vInH V H g') :=
      (E3.isElemAbelian_conjSubgroup c.hyp.setting.isElemAbelian g').mono inf_le_left
    have hA'p : IsPGroup 2 A' := by
      rw [hA'def]
      exact M.isPGroup_img (CFSG.Open.IsElemAbelian.isPGroup hab')
    obtain ⟨y, hyH, hyA⟩ := E3.exists_le_conj_of_isSylowIn hSyl hA'H hA'p
    have hcyle : cj y A' ≤ M.img D.T := by
      calc cj y A' ≤ cj y (conjSubgroup (M.img D.T) y) := cj_mono y hyA
        _ = M.img D.T := w183k3big_cj_conjSubgroup y (M.img D.T)
    have hcymem : cj y A' ∈ Ctx188.packFamilyU D V H i M :=
      (x.assumption131U M).invariant A' hA'mem y hyH
    obtain ⟨g'', hg''gam, hg''T, hg''img⟩ :=
      x.w183l31_exists_member_le_T M hcymem hcyle
    have hrel'' : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g'') = 2 := by
      rw [← M.card_img (S := vInH V H g'') inf_le_right, hg''img, card_cj A' y]
      exact hcardA'
    have hg''K : ¬ vInH V H g'' ≤ kerMV V H :=
      w183k3_not_le_ker_of_gam x M hker hKk hg''gam
    exact h3 h162 h172 h5_4 h5_11 h5_12 h5_13 c h2 hg''T hg''K hg''gam.1 hrel''

end CFSG.LocalAnalysis.WeakClosure81

end
