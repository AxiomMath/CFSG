module

public import CFSG.LocalAnalysis.WeakClosure81.W18KernPack
public import CFSG.LocalAnalysis.WeakClosure81.W172ModD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

private theorem w183_mQuot_le_iStar (x : Ctx188 D V₀ V H i j) {h : G}
    (hh : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H h) = 2) :
    E3.mQuot (vInH V H h)
      (vInH V H h ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) ≤ x.iStar := by
  have hrel : (vInH V H h ⊓
      Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H h) = 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact hh
  unfold E3.mQuot
  rw [hrel]
  have h2 : padicValNat 2 2 = 1 := by
    simpa using (padicValNat.prime_pow (p := 2) 1)
  rw [h2]
  exact x.iStar_pos

theorem Ctx188.mem_conj_M_of_img_normalizer (x : Ctx188 D V₀ V H i j)
    (M : ModDataE H (eOmegaZ H D.T)) {g : G} (hg : Gam183 V H (eOmegaZ H D.T) i g) {y : G}
    (hy : y ∈ H)
    (hn : M.ρ ⟨y, hy⟩ ∈ Subgroup.normalizer
      ((M.img (vInH V H g) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W))) :
    y ∈ conjSubgroup D.M g := by
  classical
  have hA : M.img (vInH V H g) ∈ packFamilyU D V H i M := ⟨g, hg, rfl⟩
  have hρH : M.ρ ⟨y, hy⟩ ∈ M.img H := M.mem_img.2 ⟨⟨y, hy⟩, hy, rfl⟩
  have hnorm : M.ρ ⟨y, hy⟩ ∈ M.img H ⊓
      Subgroup.normalizer ((M.img (vInH V H g) : Subgroup (LGL 2 M.W)) :
        Set (LGL 2 M.W)) := ⟨hρH, hn⟩
  rw [x.packU_normalizer_eq M (M.img (vInH V H g)) hA] at hnorm
  have hconj : conjSub (M.ρ ⟨y, hy⟩)
        (packSpaceU D V₀ V H i M (M.img (vInH V H g))) =
      packSpaceU D V₀ V H i M (M.img (vInH V H g)) := hnorm.2
  rw [x.packSpaceU_eq_apply M hg] at hconj
  rw [M.conjSub_sp (conjSubgroup V₀ g) ⟨y, hy⟩, conjSubgroup_conjSubgroup] at hconj
  have hspg_ne : M.sp (conjSubgroup V₀ g) ≠ ⊥ := by
    intro hbot
    have hbot' : conjSubgroup V₀ g ⊓ eOmegaZ H D.T = ⊥ := (M.sp_eq_bot_iff).1 hbot
    rw [inf_comm] at hbot'
    exact x.inf_ne_bot_of_gam183 hg hbot'
  have hsp_inf : M.sp (conjSubgroup V₀ g ⊓ conjSubgroup V₀ (g * y⁻¹)) ≠ ⊥ := by
    rw [M.sp_inf, hconj, inf_idem]
    exact hspg_ne
  have hne : conjSubgroup V₀ g ⊓ conjSubgroup V₀ (g * y⁻¹) ≠ ⊥ := by
    intro hbot
    exact hsp_inf ((M.sp_eq_bot_iff).2 (by rw [hbot, bot_inf_eq]))
  have hce := Hyp183.conj_eq_of_inf_ne_bot x.hyp hne
  have hyinv : conjSubgroup (conjSubgroup V₀ g) y⁻¹ = conjSubgroup V₀ g := by
    rw [conjSubgroup_conjSubgroup]
    exact hce.1.symm
  have hmemN : y ∈ Subgroup.normalizer (conjSubgroup V₀ g : Set G) := by
    have h1 : y⁻¹ ∈ Subgroup.normalizer (conjSubgroup V₀ g : Set G) :=
      conjSubgroup_eq_iff_mem_normalizer.mp hyinv
    simpa using (Subgroup.normalizer (conjSubgroup V₀ g : Set G)).inv_mem h1
  have hMn : Subgroup.normalizer (conjSubgroup V₀ g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, x.hyp.setting.normalizer₀ x.hyp.ne_bot]
  rw [hMn] at hmemN
  exact hmemN

theorem Hyp183.img_normalizer_of_mem_conj (h : Hyp183 D V₀ V H i)
    (M : ModDataE H (eOmegaZ H D.T)) {g y : G} (hy : y ∈ H) (hM : y ∈ conjSubgroup D.M g) :
    M.ρ ⟨y, hy⟩ ∈ Subgroup.normalizer
      ((M.img (vInH V H g) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
  have hMn : Subgroup.normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, h.setting.normalizer_eq]
  have hconjV : conjSubgroup (conjSubgroup V g) y⁻¹ = conjSubgroup V g := by
    rw [conjSubgroup_eq_iff_mem_normalizer, hMn]
    exact (conjSubgroup D.M g).inv_mem hM
  have hconjH : conjSubgroup H y⁻¹ = H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (H.le_normalizer (H.inv_mem hy))
  have hconjA : conjSubgroup (vInH V H g) y⁻¹ = vInH V H g := by
    unfold vInH
    rw [E3.conjSubgroup_inf, hconjV, hconjH]
  have hcj : cj (M.ρ ⟨y, hy⟩) (M.img (vInH V H g)) = M.img (vInH V H g) := by
    rw [M.img_conj (A := vInH V H g) inf_le_right ⟨y, hy⟩]
    exact congrArg M.img hconjA
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcj

theorem Ctx188.mem_M_of_wClos_normalizes (x : Ctx188 D V₀ V H i j)
    (M : ModDataE H (eOmegaZ H D.T)) {g : G} (hg : Gam183 V H (eOmegaZ H D.T) i g)
    (hgT : vInH V H g ≤ D.T)
    (hW : ∀ (w : G) (hw : w ∈ H), w ∈ E3.wClos V i D.T →
      M.ρ ⟨w, hw⟩ ∈ Subgroup.normalizer
        ((M.img (vInH V H g) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W))) :
    g ∈ D.M := by
  classical
  set W : Subgroup G := E3.wClos V i D.T with hWdef
  have hWH : W ≤ H := by
    rw [hWdef]
    exact (E3.wClos_le i D.T).trans x.hyp.hyp171.2.1
  have hWle : W ≤ conjSubgroup D.M g := by
    intro w hw
    exact x.mem_conj_M_of_img_normalizer M hg (hWH hw) (hW w (hWH hw) (by rwa [hWdef] at hw))
  have hW'M : conjSubgroup W g⁻¹ ≤ D.M :=
    (E3.conjSubgroup_le_iff_le_inv (A := W) (B := D.M) g⁻¹).mpr (by simpa using hWle)
  have hWP : IsPGroup 2 W := by
    rw [hWdef]
    exact (isSylowOf_two_iff_isSylowIn.mp D.sylowM).isPGroup.to_le (E3.wClos_le i D.T)
  have hW'P : IsPGroup 2 (conjSubgroup W g⁻¹) := E3.isPGroup_conjSubgroup hWP g⁻¹
  have hS : IsSylowIn 2 D.T D.M := isSylowOf_two_iff_isSylowIn.mp D.sylowM
  obtain ⟨m, hmM, hmle⟩ := E3.exists_le_conj_of_isSylowIn hS hW'M hW'P
  have hweak : CFSG.Quasithin.IsWeaklyClosedIn W D.T := by
    rw [hWdef]
    exact E3.e3_15_weaklyClosed (V := V) (i := i)
      (isSylowOf_two_iff_isSylowIn.mp D.sylowG) le_top
      (isSylowOf_two_iff_isSylowIn.mp D.sylowM).isPGroup
      (E3.wClos_le i D.T)
  have hleT : conjSubgroup W (g⁻¹ * m⁻¹) ≤ D.T := by
    have h1 := E3.conjSubgroup_mono_left m⁻¹ hmle
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one] at h1
    exact h1
  have heq : conjSubgroup W (g⁻¹ * m⁻¹) = W := hweak (g⁻¹ * m⁻¹) hleT
  have hmemN : g⁻¹ * m⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp heq
  have hgm : g⁻¹ * m⁻¹ ∈ D.M := by
    apply x.hyp.normW
    rwa [← hWdef]
  have hginv : g⁻¹ ∈ D.M := by
    have h1 := D.M.mul_mem hgm hmM
    simpa using h1
  simpa using D.M.inv_mem hginv

theorem Ctx188.mem_M_of_relIndex_two (x : Ctx188 D V₀ V H i j)
    (M : ModDataE H (eOmegaZ H D.T))
    (hall : ∀ g : G, Gam183 V H (eOmegaZ H D.T) i g →
      (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) = 2) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) (hgT : vInH V H g ≤ D.T) : g ∈ D.M := by
  classical
  have hcardA : Nat.card (M.img (vInH V H g)) = 2 := by
    rw [M.card_img (S := vInH V H g) inf_le_right, hall g hg]
  have hneA : M.img (vInH V H g) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardA
    norm_num at hcardA
  have hntA : Nontrivial (M.img (vInH V H g)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hneA
  obtain ⟨a, haA, ha1⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one (M.img (vInH V H g))).mp hntA
  have hAab : IsElemAbelian 2 (M.img (vInH V H g)) :=
    M.isElemAbelian_img
      ((E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left)
  have ha_sq : a * a = 1 := by
    have h := hAab.2 a haA
    rwa [pow_two] at h
  have hEq : Subgroup.zpowers a = M.img (vInH V H g) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haA) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [pow_two] : a ^ 2 = 1) ha1, hcardA]
  have hg188 : Gam188 V H (eOmegaZ H D.T) i x.iStar g :=
    ⟨hg, w183_mQuot_le_iStar x (hall g hg)⟩
  have ha_mem : a ∈ x.w172D M := ⟨ha1, ⟨g, hg188, hEq⟩⟩
  have haT : a ∈ M.img D.T := M.img_mono hgT haA
  have hB_le_Z : ∀ B ∈ E3.gammaSet V i D.T, B ≤
      ((Subgroup.centralizer ({a} : Set (LGL 2 M.W))).comap M.ρ).map H.subtype := by
    intro B hB
    obtain ⟨hBDT, h', hBh, hmB⟩ := (E3.mem_gammaSet_iff.mp hB)
    have hBH : B ≤ H := hBDT.trans x.hyp.hyp171.2.1
    have hmDh : E3.mQuot (conjSubgroup V h') (vInH V H h') ≤ i := by
      rw [← hmB]
      exact E3.mQuot_mono (U := B) (U' := vInH V H h') (fun b hb => ⟨hBh hb, hBH hb⟩)
    intro b hb
    have hbH : b ∈ H := hBH hb
    have hbDh : b ∈ vInH V H h' := ⟨hBh hb, hbH⟩
    by_cases hDhc : vInH V H h' ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)
    · have hb1 : M.ρ ⟨b, hbH⟩ = 1 :=
        (M.ρ_eq_one_iff ⟨b, hbH⟩).2 (hDhc hbDh)
      refine Subgroup.mem_map.2 ⟨⟨b, hbH⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap, hb1]
      exact Subgroup.one_mem _
    · have hgh : Gam183 V H (eOmegaZ H D.T) i h' := ⟨hmDh, hDhc⟩
      have hcardDh : Nat.card (M.img (vInH V H h')) = 2 := by
        rw [M.card_img (S := vInH V H h') inf_le_right, hall h' hgh]
      have hbimg : M.ρ ⟨b, hbH⟩ ∈ M.img (vInH V H h') :=
        M.mem_img.2 ⟨⟨b, hbH⟩, hbDh, rfl⟩
      have hDhab : IsElemAbelian 2 (M.img (vInH V H h')) :=
        M.isElemAbelian_img
          ((E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian h').mono inf_le_left)
      have hb_sq : M.ρ ⟨b, hbH⟩ * M.ρ ⟨b, hbH⟩ = 1 := by
        have hh := hDhab.2 _ hbimg
        rwa [pow_two] at hh
      by_cases hb1 : M.ρ ⟨b, hbH⟩ = 1
      · refine Subgroup.mem_map.2 ⟨⟨b, hbH⟩, ?_, rfl⟩
        rw [Subgroup.mem_comap, hb1]
        exact Subgroup.one_mem _
      · have hbD : M.ρ ⟨b, hbH⟩ ∈ x.w172D M := by
          refine ⟨hb1, ?_⟩
          have hord : orderOf (M.ρ ⟨b, hbH⟩) = 2 :=
            orderOf_eq_prime (by rwa [pow_two] : M.ρ ⟨b, hbH⟩ ^ 2 = 1) hb1
          have hzcard : Nat.card (Subgroup.zpowers (M.ρ ⟨b, hbH⟩)) = 2 := by
            rw [Nat.card_zpowers, hord]
          have hzp : Subgroup.zpowers (M.ρ ⟨b, hbH⟩) = M.img (vInH V H h') :=
            Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbimg) (by
              rw [hzcard, hcardDh])
          exact ⟨h', ⟨hgh, w183_mQuot_le_iStar x (hall h' hgh)⟩, hzp⟩
        have hbT : M.ρ ⟨b, hbH⟩ ∈ M.img D.T :=
          M.mem_img.2 ⟨⟨b, hbH⟩, hBDT hb, rfl⟩
        have hcomm := x.w172_comm_of_mem_img M (x.hyp.isSylowIn_T.isPGroup) hbD ha_mem
          hbT haT
        refine Subgroup.mem_map.2 ⟨⟨b, hbH⟩, ?_, rfl⟩
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
          rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact hcomm.symm
  have hWZ : E3.wClos V i D.T ≤
      ((Subgroup.centralizer ({a} : Set (LGL 2 M.W))).comap M.ρ).map H.subtype :=
    E3.wClos_le_of_forall hB_le_Z
  refine x.mem_M_of_wClos_normalizes M hg hgT (fun w hw hwW => ?_)
  have hwZ : w ∈ ((Subgroup.centralizer ({a} : Set (LGL 2 M.W))).comap M.ρ).map
      H.subtype := hWZ hwW
  rw [Subgroup.mem_map] at hwZ
  obtain ⟨y, hy, hyw⟩ := hwZ
  have hyw' : y = ⟨w, hw⟩ := Subtype.ext hyw
  rw [hyw'] at hy
  have hw_comm : M.ρ ⟨w, hw⟩ * a = a * M.ρ ⟨w, hw⟩ := by
    have h1 : M.ρ ⟨w, hw⟩ ∈ Subgroup.centralizer ({a} : Set (LGL 2 M.W)) :=
      Subgroup.mem_comap.mp hy
    exact (Subgroup.mem_centralizer_iff.mp h1 a (Set.mem_singleton a)).symm
  rw [← hEq]
  exact (w172_mem_normalizer_zpowers_iff ha_sq ha1).mpr hw_comm

end CFSG.LocalAnalysis.WeakClosure81

end
