module

public import CFSG.LocalAnalysis.WeakClosure81.W183L31Pair
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem w183tp_big_member_le_T (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G))
    (hbig : ∃ g' : G, Gam183 V H (eOmegaZ H D.T) i g' ∧
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g')) :
    ∃ g'' : G, vInH V H g'' ≤ D.T ∧ ¬ vInH V H g'' ≤ kerMV V H ∧
      E3.mQuot (conjSubgroup V g'') (vInH V H g'') ≤ i ∧
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g'') := by
  classical
  obtain ⟨g', hg'gam, hg'3⟩ := hbig
  set A' : Subgroup (LGL 2 M.W) := M.img (vInH V H g') with hA'def
  have hA'mem : A' ∈ packFamilyU D V H i M := ⟨g', hg'gam, by rw [hA'def]⟩
  have hSyl : IsSylowIn 2 (M.img D.T) (M.img H) :=
    M.isSylowIn_img_of_isSylowIn x.hyp.isSylowIn_T
  have hA'H : A' ≤ M.img H := by
    rw [hA'def]
    exact M.img_mono inf_le_right
  have hab' : IsElemAbelian 2 (vInH V H g') :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g').mono inf_le_left
  have hA'p : IsPGroup 2 A' := by
    rw [hA'def]
    exact M.isPGroup_img (CFSG.Open.IsElemAbelian.isPGroup hab')
  obtain ⟨y, hyH, hyA⟩ := E3.exists_le_conj_of_isSylowIn hSyl hA'H hA'p
  have hcyle : cj y A' ≤ M.img D.T := by
    have hcj : cj y (conjSubgroup (M.img D.T) y) = M.img D.T := by
      ext z
      rw [mem_cj, mem_conjSubgroup_iff]
      constructor
      · intro h
        rwa [show y * (y⁻¹ * z * y) * y⁻¹ = z from by group] at h
      · intro hz
        rw [show y * (y⁻¹ * z * y) * y⁻¹ = z from by group]
        exact hz
    calc cj y A' ≤ cj y (conjSubgroup (M.img D.T) y) := cj_mono y hyA
      _ = M.img D.T := hcj
  have hcymem : cj y A' ∈ packFamilyU D V H i M :=
    (x.assumption131U M).invariant A' hA'mem y hyH
  obtain ⟨g'', hg''gam, hg''T, hg''img⟩ := w183l31_exists_member_le_T x M hcymem hcyle
  refine ⟨g'', hg''T, fun hle => hg''gam.2 (hle.trans hK), hg''gam.1, ?_⟩
  rw [← M.card_img (S := vInH V H g'') inf_le_right, hg''img, card_cj, hA'def,
    M.card_img (S := vInH V H g') inf_le_right]
  exact hg'3

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
