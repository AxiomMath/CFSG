module

public import CFSG.LocalAnalysis.WeakClosure81.W18PackG
public import CFSG.LocalAnalysis.WeakClosure81.W18PackMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_iff_cj_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {g : LGL 2 W} {A : Subgroup (LGL 2 W)} :
    g ∈ Subgroup.normalizer (A : Set (LGL 2 W)) ↔ cj g A = A :=
  Subgroup.mem_normalizer_iff_map_conj_eq

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

@[expose] def packFamily (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    Set (Subgroup (LGL 2 M.W)) :=
  {A | ∃ g : G, Gam188 V H (eOmegaZ H D.T) i x.iStar g ∧ A = M.img (vInH V H g)}

@[expose] noncomputable def packSpace (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (A : Subgroup (LGL 2 M.W)) : Submodule (ZMod 2) M.W :=
  ⨆ g : {g : G // Gam188 V H (eOmegaZ H D.T) i x.iStar g ∧ M.img (vInH V H g) = A},
    M.sp (conjSubgroup V₀ g.1)

private theorem packSpace_eq {x : Ctx188 D V₀ V H i j} (M : ModDataE H (eOmegaZ H D.T))
    {g g' : G} (hg : Gam188 V H (eOmegaZ H D.T) i x.iStar g)
    (hg' : Gam188 V H (eOmegaZ H D.T) i x.iStar g')
    (himg : M.img (vInH V H g) = M.img (vInH V H g')) :
    M.sp (conjSubgroup V₀ g) = M.sp (conjSubgroup V₀ g') := by
  classical
  have hEH : H ≤ Subgroup.normalizer (eOmegaZ H D.T : Set G) := Hyp183.normalizer_eOmegaZ H D.T
  have hcommE : ∀ {a : G}, a ∈ H → ∀ {e : G}, e ∈ eOmegaZ H D.T → ⁅a, e⁆ ∈ eOmegaZ H D.T := by
    intro a ha e he
    have h1 : a * e * a⁻¹ ∈ eOmegaZ H D.T :=
      (Subgroup.mem_normalizer_iff.1 (hEH ha) e).1 he
    rw [commutatorElement_def]
    exact (eOmegaZ H D.T).mul_mem h1 ((eOmegaZ H D.T).inv_mem he)
  obtain ⟨d, hdD, hdC⟩ : ∃ d ∈ vInH V H g, d ∉ Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
    by_contra h
    exact hg.1.2 fun x hx => by
      by_contra hxc
      exact h ⟨x, hx, hxc⟩
  have hdH : d ∈ H := hdD.2
  obtain ⟨e, heE, hed⟩ : ∃ e ∈ eOmegaZ H D.T, e * d ≠ d * e := by
    by_contra h
    exact hdC (Subgroup.mem_centralizer_iff.2 fun x hx => by
      by_contra hxd
      exact h ⟨x, hx, hxd⟩)
  have heCB : e ∈ Subgroup.centralizer
      ((vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 hb.2 e heE).symm
  have he_d_mem : ⁅e, d⁆ ∈ eOmegaZ H D.T ⊓ conjSubgroup V₀ g :=
    (Ctx188.comm_le x x.iStar_add_lt hg.1 inf_le_left hg.2)
      (Subgroup.commutator_mem_commutator ⟨heE, heCB⟩ hdD)
  have hd_e_mem : ⁅d, e⁆ ∈ eOmegaZ H D.T ⊓ conjSubgroup V₀ g := by
    have := (eOmegaZ H D.T ⊓ conjSubgroup V₀ g).inv_mem he_d_mem
    rwa [commutatorElement_inv] at this
  have hρ : M.ρ ⟨d, hdH⟩ ∈ M.img (vInH V H g) := M.mem_img.2 ⟨⟨d, hdH⟩, hdD, rfl⟩
  rw [himg] at hρ
  obtain ⟨j', hj'D', hj'ρ⟩ := M.mem_img.1 hρ
  have hι : M.ι ⁅d, e⁆ = M.ι ⁅(j' : G), e⁆ := by
    rw [M.ι_commutator hdH heE, M.ι_commutator (j := (j' : G)) j'.2 heE]
    exact (congrArg (fun r => r (M.ι e) - M.ι e) hj'ρ).symm
  have hde_eq : ⁅d, e⁆ = ⁅(j' : G), e⁆ :=
    M.ι_injOn (hcommE hdH heE) (hcommE j'.2 heE) hι
  have heCB' : e ∈ Subgroup.centralizer
      ((vInH V H g' ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 hb.2 e heE).symm
  have he_d'_mem : ⁅e, (j' : G)⁆ ∈ eOmegaZ H D.T ⊓ conjSubgroup V₀ g' :=
    (Ctx188.comm_le x x.iStar_add_lt hg'.1 inf_le_left hg'.2)
      (Subgroup.commutator_mem_commutator ⟨heE, heCB'⟩ hj'D')
  have hd'_e_mem : ⁅(j' : G), e⁆ ∈ eOmegaZ H D.T ⊓ conjSubgroup V₀ g' := by
    have := (eOmegaZ H D.T ⊓ conjSubgroup V₀ g').inv_mem he_d'_mem
    rwa [commutatorElement_inv] at this
  have hwne : ⁅d, e⁆ ≠ 1 := fun hw =>
    hed ((commutatorElement_eq_one_iff_mul_comm.1 hw).symm)
  have hne : conjSubgroup V₀ g ⊓ conjSubgroup V₀ g' ≠ ⊥ := by
    intro hbot
    have hw_both : ⁅d, e⁆ ∈ conjSubgroup V₀ g ⊓ conjSubgroup V₀ g' :=
      ⟨hd_e_mem.2, by rw [hde_eq]; exact hd'_e_mem.2⟩
    exact hwne (Subgroup.mem_bot.mp (hbot ▸ hw_both))
  exact congrArg M.sp (Hyp183.conj_eq_of_inf_ne_bot x.hyp hne).1

private theorem sp_conjSubgroup_le_packSpace {x : Ctx188 D V₀ V H i j}
    (M : ModDataE H (eOmegaZ H D.T)) {g : G} (hg : Gam188 V H (eOmegaZ H D.T) i x.iStar g) :
    M.sp (conjSubgroup V₀ g) ≤ x.packSpace M (M.img (vInH V H g)) := by
  unfold packSpace
  exact le_iSup (fun g' : {g₁ : G // Gam188 V H (eOmegaZ H D.T) i x.iStar g₁ ∧
    M.img (vInH V H g₁) = M.img (vInH V H g)} => M.sp (conjSubgroup V₀ g'.1))
    ⟨g, hg, rfl⟩

private theorem packSpace_eq_apply {x : Ctx188 D V₀ V H i j} (M : ModDataE H (eOmegaZ H D.T))
    {g : G} (hg : Gam188 V H (eOmegaZ H D.T) i x.iStar g) :
    x.packSpace M (M.img (vInH V H g)) = M.sp (conjSubgroup V₀ g) := by
  apply le_antisymm
  · unfold packSpace
    refine iSup_le fun g' => ?_
    exact le_of_eq (packSpace_eq M g'.2.1 hg g'.2.2)
  · exact sp_conjSubgroup_le_packSpace M hg

theorem assumption131 (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    Assumption131 (M.img H) (x.packFamily M) (x.packSpace M) x.iStar := by
  refine
    { pos_i := x.iStar_pos
      le_G := ?_
      isElemAb := ?_
      invariant := ?_
      ne_bot := ?_
      inf_pCore := ?_
      normalizer_eq := ?_
      disjoint := ?_
      cond2 := ?_
      quadratic := ?_
      equivariant := ?_ }
  · rintro A ⟨g, hg, rfl⟩
    exact M.img_mono inf_le_right
  · rintro A ⟨g, hg, rfl⟩
    exact M.isElemAbelian_img
      ((E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left)
  · rintro A ⟨h, hg, rfl⟩ g hgmem
    obtain ⟨y, hyH, rfl⟩ := M.mem_img.1 hgmem
    refine ⟨h * (y : G)⁻¹, ?_, ?_⟩
    · exact Gam188.conj (Hyp183.normalizer_eOmegaZ H D.T) (H.inv_mem y.2) hg
    · rw [M.img_conj (A := vInH V H h) inf_le_right y, vInH_mul h (H.inv_mem y.2)]
  · rintro A ⟨h, hg, rfl⟩ hbot
    have hle : vInH V H h ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
      intro d hd
      have hdH : d ∈ H := hd.2
      have h1 : M.ρ ⟨d, hdH⟩ = 1 := by
        have hmem : M.ρ ⟨d, hdH⟩ ∈ M.img (vInH V H h) :=
          M.mem_img.2 ⟨⟨d, hdH⟩, hd, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hmem
      exact (M.ρ_eq_one_iff ⟨d, hdH⟩).1 h1
    exact hg.1.2 hle
  · intro A _
    have hZcent : D.T ≤ Subgroup.centralizer (omegaOneCenterOf D.T : Set G) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hΩ : omegaOneCenterOf D.T ≤ centerOf D.T := by
        rw [omegaOneCenterOf, omegaOneOf]
        exact (Subgroup.closure_le _).mpr fun u hu => hu.1
      have hz' : z ∈ centerOf D.T := hΩ hz
      exact (Subgroup.mem_centralizer_iff.1 hz'.2 t ht).symm
    have hpc : pCoreOf 2 (M.img H) = ⊥ :=
      M.pCoreOf_img_eq_bot (J := H) (T := D.T) (Z := omegaOneCenterOf D.T)
        x.hyp.isSylowIn_T (Hyp183.omegaOneCenterOf_le_eOmegaZ H D.T) hZcent (le_refl _)
    rw [hpc, inf_bot_eq]
  · rintro A ⟨g, hg, rfl⟩
    rw [packSpace_eq_apply M hg]
    ext r
    constructor
    · rintro ⟨hrG, hrN⟩
      obtain ⟨y, hyH, rfl⟩ := M.mem_img.1 hrG
      refine ⟨M.mem_img.2 ⟨y, y.2, rfl⟩, ?_⟩
      have hNA : cj (M.ρ y) (M.img (vInH V H g)) = M.img (vInH V H g) :=
        cj_eq_of_mem_normalizer hrN
      rw [M.img_conj (A := vInH V H g) inf_le_right y, ← vInH_mul g (H.inv_mem y.2)] at hNA
      have hgy : Gam188 V H (eOmegaZ H D.T) i x.iStar (g * (y : G)⁻¹) :=
        Gam188.conj (Hyp183.normalizer_eOmegaZ H D.T) (H.inv_mem y.2) hg
      rw [M.conjSub_sp (conjSubgroup V₀ g) y, conjSubgroup_conjSubgroup]
      exact packSpace_eq M hgy hg hNA
    · rintro ⟨hrG, hrS⟩
      obtain ⟨y, hyH, rfl⟩ := M.mem_img.1 hrG
      refine ⟨M.mem_img.2 ⟨y, y.2, rfl⟩, ?_⟩
      apply mem_normalizer_iff_cj_eq.mpr
      rw [M.img_conj (A := vInH V H g) inf_le_right y, ← vInH_mul g (H.inv_mem y.2)]
      rw [M.conjSub_sp (conjSubgroup V₀ g) y, conjSubgroup_conjSubgroup] at hrS
      have hspg_ne : M.sp (conjSubgroup V₀ g) ≠ ⊥ := by
        intro hbot
        have hbot' : conjSubgroup V₀ g ⊓ eOmegaZ H D.T = ⊥ := (M.sp_eq_bot_iff).1 hbot
        rw [inf_comm] at hbot'
        exact x.inf_ne_bot x.iStar_add_lt hg hbot'
      have hsp_inf : M.sp (conjSubgroup V₀ g ⊓ conjSubgroup V₀ (g * (y : G)⁻¹)) ≠ ⊥ := by
        rw [M.sp_inf, hrS, inf_idem]
        exact hspg_ne
      have hne : conjSubgroup V₀ g ⊓ conjSubgroup V₀ (g * (y : G)⁻¹) ≠ ⊥ := by
        intro hbot
        exact hsp_inf ((M.sp_eq_bot_iff).2 (by rw [hbot, bot_inf_eq]))
      have hce := Hyp183.conj_eq_of_inf_ne_bot x.hyp hne
      have hD : vInH V H (g * (y : G)⁻¹) = vInH V H g := by
        unfold vInH
        rw [hce.2.symm]
      rw [hD]
  · rintro A ⟨g, hg, rfl⟩ B ⟨g', hg', rfl⟩ hAB
    rw [packSpace_eq_apply M hg, packSpace_eq_apply M hg']
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    by_contra hv0
    have hsp_ne : M.sp (conjSubgroup V₀ g ⊓ conjSubgroup V₀ g') ≠ ⊥ := by
      intro hbot
      have hmem : v ∈ (⊥ : Submodule (ZMod 2) M.W) := by
        rw [← hbot, M.sp_inf]
        exact hv
      rw [Submodule.mem_bot] at hmem
      exact hv0 hmem
    have hne : conjSubgroup V₀ g ⊓ conjSubgroup V₀ g' ≠ ⊥ := fun hbot =>
      hsp_ne ((M.sp_eq_bot_iff).2 (by rw [hbot, bot_inf_eq]))
    have hD : vInH V H g = vInH V H g' := by
      unfold vInH
      rw [(Hyp183.conj_eq_of_inf_ne_bot x.hyp hne).2]
    exact hAB (by rw [hD])
  · rintro A ⟨g, hg, rfl⟩ B hBA hBk
    obtain ⟨B₀, hB₀D, hB₀C, hB₀img⟩ := M.exists_preimage (A := vInH V H g) inf_le_right hBA
    have hB₀H : B₀ ≤ H := hB₀D.trans inf_le_right
    have hDab : IsElemAbelian 2 (vInH V H g) :=
      (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left
    have hmOf : E3.mQuot (vInH V H g) B₀ ≤ x.iStar := by
      rw [← M.mOf_img (A := vInH V H g) inf_le_right hDab hB₀D hB₀C, hB₀img]
      exact hBk
    have hfix : fixSub B = M.sp (Subgroup.centralizer (B₀ : Set G)) := by
      rw [← hB₀img]
      exact M.fixSub_img hB₀H
    have hle : ⁅Subgroup.centralizer (B₀ : Set G) ⊓ eOmegaZ H D.T, vInH V H g⁆ ≤
        conjSubgroup V₀ g := by
      rw [inf_comm]
      exact (Ctx188.comm_le x x.iStar_add_lt hg.1 hB₀D hmOf).trans inf_le_right
    calc commSpace (M.img (vInH V H g)) (fixSub B)
        = commSpace (M.img (vInH V H g)) (M.sp (Subgroup.centralizer (B₀ : Set G))) := by
          rw [hfix]
      _ ≤ M.sp (conjSubgroup V₀ g) := M.commSpace_img_sp_le (A := vInH V H g) inf_le_right hle
      _ ≤ x.packSpace M (M.img (vInH V H g)) := sp_conjSubgroup_le_packSpace M hg
  · rintro A ⟨g, hg, rfl⟩
    exact M.commSpace_commSub_img_eq_bot (A := vInH V H g) inf_le_right
      (Ctx188.quadratic x x.iStar_add_lt hg)
  · rintro A ⟨h, hg, rfl⟩ g hgmem
    obtain ⟨y, hyH, rfl⟩ := M.mem_img.1 hgmem
    have hgy : Gam188 V H (eOmegaZ H D.T) i x.iStar (h * (y : G)⁻¹) :=
      Gam188.conj (Hyp183.normalizer_eOmegaZ H D.T) (H.inv_mem y.2) hg
    have hcj : cj (M.ρ y) (M.img (vInH V H h)) = M.img (vInH V H (h * (y : G)⁻¹)) := by
      rw [M.img_conj (A := vInH V H h) inf_le_right y, vInH_mul h (H.inv_mem y.2)]
    rw [hcj, packSpace_eq_apply M hgy, packSpace_eq_apply M hg,
      M.conjSub_sp (conjSubgroup V₀ h) y, conjSubgroup_conjSubgroup]

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end