module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Defs
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneC
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.W18KernPack

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

private theorem w183_sp_inj {J E : Subgroup G} (M : ModDataE J E) {S S' : Subgroup G}
    (h : M.sp S = M.sp S') : S ⊓ E = S' ⊓ E := by
  apply le_antisymm
  · intro e he
    have hmem : M.ι e ∈ M.sp S' := by rw [← h]; exact ⟨e, he, rfl⟩
    obtain ⟨e', he', he'eq⟩ := M.mem_sp.1 hmem
    have hee : e' = e := M.ι_injOn he'.2 he.2 he'eq
    rwa [hee] at he'
  · intro e he
    have hmem : M.ι e ∈ M.sp S := by rw [h]; exact ⟨e, he, rfl⟩
    obtain ⟨e', he', he'eq⟩ := M.mem_sp.1 hmem
    have hee : e' = e := M.ι_injOn he'.2 he.2 he'eq
    rwa [hee] at he'

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem br1_hmi (x : Ctx188 D V₀ V H i 3) : i + 3 ≤ x.mB := by
  have h := x.bound
  unfold mB
  omega

theorem br1_h131 (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    Assumption131 (M.img H) (packFamilyU D V H i M) (packSpaceU D V₀ V H i M)
      (x.mB - i - 1) :=
  x.assumption131U M

theorem br1_vfix (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ A ∈ packFamilyU D V H i M, packSpaceU D V₀ V H i M A ≤ fixSub A := by
  rintro A ⟨g, hg, rfl⟩
  rw [x.packSpaceU_eq_apply M hg, M.fixSub_img (B := vInH V H g) inf_le_right]
  refine M.sp_mono fun v hv => ?_
  exact Subgroup.mem_centralizer_iff.mpr fun d hd =>
    ((E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).comm
      (E3.conjSubgroup_mono_left g x.hyp.setting.pair.le hv) hd.1).symm

theorem br1_delta_le (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ A ∈ packFamilyU D V H i M, packDeltaU D V H i M A ≤ i := by
  rintro A ⟨g, hg, rfl⟩
  have hmem : E3.mQuot (conjSubgroup V g) (vInH V H g) ∈
      {k | ∃ g' : G, Gam183 V H (eOmegaZ H D.T) i g' ∧
        M.img (vInH V H g') = M.img (vInH V H g) ∧
        E3.mQuot (conjSubgroup V g') (vInH V H g') = k} := ⟨g, hg, rfl, rfl⟩
  exact (Nat.sInf_le hmem).trans hg.1

theorem br1_comm_le (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ A ∈ packFamilyU D V H i M, ∀ B : Subgroup (LGL 2 M.W), B ≤ A →
      mOf A B + packDeltaU D V H i M A < x.mB →
      CFSG.Quasithin.G11.commSpace A (fixSub B) ≤ packSpaceU D V₀ V H i M A := by
  rintro A ⟨g₀, hg₀, rfl⟩ B hBA hlt
  have hmem : packDeltaU D V H i M (M.img (vInH V H g₀)) ∈
      {k | ∃ g : G, Gam183 V H (eOmegaZ H D.T) i g ∧
        M.img (vInH V H g) = M.img (vInH V H g₀) ∧
        E3.mQuot (conjSubgroup V g) (vInH V H g) = k} :=
    Nat.sInf_mem ⟨_, g₀, hg₀, rfl, rfl⟩
  obtain ⟨g, hg, himg, hδ⟩ := hmem
  have hlt' : mOf (M.img (vInH V H g₀)) B +
      E3.mQuot (conjSubgroup V g) (vInH V H g) <
      mBar D.M V₀ V x.hyp.setting.isElemAbelian := by
    rw [← hδ] at hlt
    exact hlt
  rw [← himg] at hBA
  obtain ⟨B₀, hB₀D, hB₀C, hB₀img⟩ := M.exists_preimage (A := vInH V H g) inf_le_right hBA
  have hB₀H : B₀ ≤ H := hB₀D.trans inf_le_right
  have hDab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left
  have hmOf_eq := M.mOf_img (A := vInH V H g) inf_le_right hDab hB₀D hB₀C
  have hlt2 : E3.mQuot (vInH V H g) B₀ +
      E3.mQuot (conjSubgroup V g) (vInH V H g) <
      mBar D.M V₀ V x.hyp.setting.isElemAbelian := by
    rw [← himg, ← hB₀img, hmOf_eq] at hlt'
    exact hlt'
  have hfix : fixSub B = M.sp (Subgroup.centralizer (B₀ : Set G)) := by
    rw [← hB₀img]
    exact M.fixSub_img hB₀H
  have hle : ⁅Subgroup.centralizer (B₀ : Set G) ⊓ eOmegaZ H D.T, vInH V H g⁆ ≤
      conjSubgroup V₀ g := by
    rw [inf_comm]
    exact (x.hyp.comm_centralizer_le_conj x.h162 x.mbar inf_le_left inf_le_right hB₀D
      hlt2).trans inf_le_right
  rw [← himg]
  calc CFSG.Quasithin.G11.commSpace (M.img (vInH V H g)) (fixSub B)
      = CFSG.Quasithin.G11.commSpace (M.img (vInH V H g))
          (M.sp (Subgroup.centralizer (B₀ : Set G))) := by rw [hfix]
    _ ≤ M.sp (conjSubgroup V₀ g) :=
        M.commSpace_img_sp_le (A := vInH V H g) inf_le_right hle
    _ = packSpaceU D V₀ V H i M (M.img (vInH V H g)) :=
        (x.packSpaceU_eq_apply M hg).symm

theorem br1_sylow (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    IsSylowIn 2 (M.img D.T) (M.img H) :=
  M.isSylowIn_img_of_isSylowIn x.hyp.isSylowIn_T

theorem br1_gens (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ B ∈ packGensU D V H i M, B ≤ M.img D.T ∧
      ∃ A ∈ packFamilyU D V H i M, B ≤ A ∧ mOf A B + packDeltaU D V H i M A ≤ i := by
  rintro B ⟨hB1, B₀, hB₀, rfl⟩
  obtain ⟨hB₀T, g, hB₀Vg, hB₀idx⟩ := E3.mem_gammaSet_iff.mp hB₀
  have hB₀H : B₀ ≤ H := hB₀T.trans x.hyp.hyp171.2.1
  set Dg : Subgroup G := vInH V H g with hDgeq
  have hDgVg : Dg ≤ conjSubgroup V g := by rw [hDgeq]; exact inf_le_left
  have hDgH : Dg ≤ H := by rw [hDgeq]; exact inf_le_right
  have hB₀Dg : B₀ ≤ Dg := fun b hb => ⟨hB₀Vg hb, hB₀H hb⟩
  have hDgab : IsElemAbelian 2 Dg :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono hDgVg
  have hmq : E3.mQuot (conjSubgroup V g) Dg ≤ i :=
    (E3.mQuot_mono hB₀Dg).trans_eq hB₀idx
  have hnotCent : ¬ Dg ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
    intro hle
    apply hB1
    rw [eq_bot_iff]
    rintro r hr
    obtain ⟨y, hy, rfl⟩ := M.mem_img.1 hr
    rw [Subgroup.mem_bot]
    exact (M.ρ_eq_one_iff y).2 (hle (hB₀Dg hy))
  have hgam : Gam183 V H (eOmegaZ H D.T) i g := ⟨hmq, hnotCent⟩
  set C : Subgroup G := Subgroup.centralizer (eOmegaZ H D.T : Set G) with hCeq
  have hCEbot : M.img (Dg ⊓ C) = ⊥ := by
    rw [eq_bot_iff]
    rintro r hr
    obtain ⟨y, hy, rfl⟩ := M.mem_img.1 hr
    rw [Subgroup.mem_bot]
    exact (M.ρ_eq_one_iff y).2 hy.2
  have hB₁H : B₀ ⊔ (Dg ⊓ C) ≤ H := sup_le hB₀H (le_trans inf_le_left hDgH)
  have hB₁img : M.img (B₀ ⊔ (Dg ⊓ C)) = M.img B₀ := by
    rw [M.img_sup hB₀H (le_trans inf_le_left hDgH), hCEbot, sup_bot_eq]
  have hmOfB₁ : mOf (M.img Dg) (M.img B₀) = E3.mQuot Dg (B₀ ⊔ (Dg ⊓ C)) := by
    rw [← hB₁img]
    exact M.mOf_img (A := Dg) hDgH hDgab (sup_le hB₀Dg inf_le_left) le_sup_right
  have hdelta_le : packDeltaU D V H i M (M.img Dg) ≤ E3.mQuot (conjSubgroup V g) Dg :=
    Nat.sInf_le ⟨g, hgam, rfl, rfl⟩
  have hle2 : E3.mQuot Dg (B₀ ⊔ (Dg ⊓ C)) ≤ E3.mQuot Dg B₀ :=
    E3.mQuot_mono le_sup_left
  have hadd : E3.mQuot Dg B₀ + E3.mQuot (conjSubgroup V g) Dg = i := by
    rw [← E3.mQuot_add hB₀Dg hDgVg, hB₀idx]
  refine ⟨M.img_mono hB₀T, M.img Dg, ⟨g, hgam, rfl⟩, M.img_mono hB₀Dg, ?_⟩
  calc mOf (M.img Dg) (M.img B₀) + packDeltaU D V H i M (M.img Dg)
      = E3.mQuot Dg (B₀ ⊔ (Dg ⊓ C)) + packDeltaU D V H i M (M.img Dg) := by
        rw [hmOfB₁]
    _ ≤ E3.mQuot Dg B₀ + E3.mQuot (conjSubgroup V g) Dg := add_le_add hle2 hdelta_le
    _ = i := hadd

theorem br1_noOffender (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ A ∈ packFamilyU D V H i M, ∃ B : Subgroup (LGL 2 M.W), B ≤ A ∧ mOf A B ≤ 2 ∧
      fixSub A ≠ fixSub B := by
  rintro A ⟨g, hg, rfl⟩
  obtain ⟨B₀, hB₀D, hB₀C, hm, hne⟩ := x.exists_index_witness hg
  have hB₀H : B₀ ≤ H := hB₀D.trans inf_le_right
  have hDab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left
  refine ⟨M.img B₀, M.img_mono hB₀D, ?_, ?_⟩
  · rw [M.mOf_img (A := vInH V H g) inf_le_right hDab hB₀D hB₀C]
    omega
  · intro heq
    have hsp : M.sp (Subgroup.centralizer (vInH V H g : Set G)) =
        M.sp (Subgroup.centralizer (B₀ : Set G)) := by
      rw [← M.fixSub_img (B := vInH V H g) inf_le_right, ← M.fixSub_img hB₀H, heq]
    exact hne (by simpa only [inf_comm] using w183_sp_inj M hsp)

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
