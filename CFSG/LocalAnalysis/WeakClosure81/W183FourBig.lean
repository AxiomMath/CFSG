module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneC
public import CFSG.LocalAnalysis.WeakClosure81.W18ASCtx
public import CFSG.LocalAnalysis.WeakClosure81.W18ASTail
public import CFSG.LocalAnalysis.WeakClosure81.W18KernPack
import CFSG.LocalAnalysis.WeakClosure81.W183L31Pair
public import CFSG.LocalAnalysis.WeakClosure81.W18Tail

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] def Tail1812FourBig (G : Type) [Group G] [Finite G] : Prop :=
  W3Thm162Gt2 G → W3Thm172Weak G → Asch5_4 → Asch5_11AS → Asch5_12 → Asch5_13AS →
    ∀ {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}, MinCex183 D V₀ V H i →
      ¬ Concl182 D V₀ V H i →
      kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) →
      (∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
        3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g')) →
      ∀ {g : G}, vInH V H g ≤ D.T → ¬ vInH V H g ≤ kerMV V H →
        E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i →
        3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) → False

private theorem w183_fourbig_cj_conjSubgroup {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (y : LGL 2 W) (B : Subgroup (LGL 2 W)) : cj y (conjSubgroup B y) = B := by
  ext x
  rw [mem_cj, mem_conjSubgroup_iff]
  constructor
  · intro h
    rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x from by group] at h
  · intro hx
    rw [show y * (y⁻¹ * x * y) * y⁻¹ = x from by group]
    exact hx

theorem tail1812Four_AS_of_big (h3 : Tail1812Two_AS G) (h4 : Tail1812FourBig G) :
    Tail1812Four_AS G := by
  intro h162 h172 h5_4 h5_11 h5_12 h5_13 D V₀ V H i c h2 hK g hgT hgK hgi hA
  by_cases hbig : ∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g')
  · exact h4 h162 h172 h5_4 h5_11 h5_12 h5_13 c h2 hK hbig hgT hgK hgi hA
  · obtain ⟨g', hg'not⟩ := not_forall.mp hbig
    obtain ⟨hg'gam, hnot⟩ := not_imp.mp hg'not
    have hlt : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g') < 3 :=
      not_le.mp hnot
    have hg'K : ¬ vInH V H g' ≤ kerMV V H := fun hle => hg'gam.2 (hle.trans hK)
    have hrel2 : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g') = 2 := by
      rcases c.relIndex_cases hg'K with h2' | h3'
      · exact h2'
      · omega
    obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ (Hyp183.normalizer_eOmegaZ H D.T)
    have x : Ctx188 D V₀ V H i 3 := c.ctx188_three_AS h162 h5_11 h2
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
        _ = M.img D.T := w183_fourbig_cj_conjSubgroup y (M.img D.T)
    have hcymem : cj y A' ∈ Ctx188.packFamilyU D V H i M :=
      (x.assumption131U M).invariant A' hA'mem y hyH
    obtain ⟨g'', hg''gam, hg''T, hg''img⟩ :=
      x.w183l31_exists_member_le_T M hcymem hcyle
    have hrel'' : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g'') = 2 := by
      rw [← M.card_img (S := vInH V H g'') inf_le_right, hg''img, card_cj A' y]
      exact hcardA'
    have hg''K : ¬ vInH V H g'' ≤ kerMV V H := fun hle => hg''gam.2 (hle.trans hK)
    exact h3 h162 h172 h5_4 h5_11 h5_12 h5_13 c h2 hg''T hg''K hg''gam.1 hrel''

end CFSG.LocalAnalysis.WeakClosure81

end
