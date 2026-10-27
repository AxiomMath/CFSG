module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Sixteen21
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47Conj
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
public import CFSG.LocalAnalysis.WeakClosure81.W183Mem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem w183b2_conjSubgroup_sup (A B : Subgroup G) (c : G) :
    conjSubgroup (A ⊔ B) c = conjSubgroup A c ⊔ conjSubgroup B c :=
  Subgroup.map_sup A B (MulAut.conj c⁻¹).toMonoidHom

private theorem w183b2_conjSubgroup_coe_mul (A B U : Subgroup G) (c : G)
    (h : (A : Set G) = (B : Set G) * (U : Set G)) :
    (conjSubgroup A c : Set G) = (conjSubgroup B c : Set G) * (conjSubgroup U c : Set G) := by
  change (A.map (MulAut.conj c⁻¹).toMonoidHom : Set G) =
    (B.map (MulAut.conj c⁻¹).toMonoidHom : Set G) *
      (U.map (MulAut.conj c⁻¹).toMonoidHom : Set G)
  simp only [Subgroup.coe_map, h, Set.image_mul]

private theorem w183b2_oFirst_conj (n : ℕ) (M V₀ V : Subgroup G) (c x : G) :
    OFirst n (conjSubgroup M c) (conjSubgroup V₀ c) (conjSubgroup V c) (c⁻¹ * x * c) ↔
      OFirst n M V₀ V x := by
  have hVx : conjSubgroup (conjSubgroup V c) (c⁻¹ * x * c) = conjSubgroup (conjSubgroup V x) c := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  have hMx : conjSubgroup (conjSubgroup M c) (c⁻¹ * x * c) = conjSubgroup (conjSubgroup M x) c := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  have hle : conjSubgroup (conjSubgroup V x) c ≤ conjSubgroup M c ↔ conjSubgroup V x ≤ M :=
    E3.conjSubgroup_le_conjSubgroup_iff c
  have hquot : E3.mQuot (conjSubgroup V c) (conjSubgroup (conjSubgroup M x) c) =
      E3.mQuot V (conjSubgroup M x) := E3.mQuot_conjSubgroup V (conjSubgroup M x) c
  have hinf : conjSubgroup V₀ c ⊓ conjSubgroup (conjSubgroup M x) c =
      conjSubgroup (V₀ ⊓ conjSubgroup M x) c :=
    (E3.conjSubgroup_inf V₀ (conjSubgroup M x) c).symm
  unfold OFirst
  simp only [hVx, hMx, hle, hquot, conjSubgroup_eq_bot_iff, hinf, ne_eq]

private theorem w183b2_oDual_conj (n : ℕ) (M V₀ V : Subgroup G) (c x : G) :
    ODual n (conjSubgroup M c) (conjSubgroup V₀ c) (conjSubgroup V c) (c⁻¹ * x * c) ↔
      ODual n M V₀ V x := by
  have hVx : conjSubgroup (conjSubgroup V c) (c⁻¹ * x * c) = conjSubgroup (conjSubgroup V x) c := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  have hMx : conjSubgroup (conjSubgroup M c) (c⁻¹ * x * c) = conjSubgroup (conjSubgroup M x) c := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  have hV₀x : conjSubgroup (conjSubgroup V₀ c) (c⁻¹ * x * c) =
      conjSubgroup (conjSubgroup V₀ x) c := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  have hle : conjSubgroup V c ≤ conjSubgroup (conjSubgroup M x) c ↔ V ≤ conjSubgroup M x :=
    E3.conjSubgroup_le_conjSubgroup_iff c
  have hquot : E3.mQuot (conjSubgroup (conjSubgroup V x) c) (conjSubgroup M c) =
      E3.mQuot (conjSubgroup V x) M := E3.mQuot_conjSubgroup (conjSubgroup V x) M c
  have hinf : conjSubgroup (conjSubgroup V₀ x) c ⊓ conjSubgroup M c =
      conjSubgroup (conjSubgroup V₀ x ⊓ M) c :=
    (E3.conjSubgroup_inf (conjSubgroup V₀ x) M c).symm
  unfold ODual
  simp only [hVx, hMx, hV₀x, hle, hquot, conjSubgroup_eq_bot_iff, hinf, ne_eq]

private theorem w183b2_inCalO_conj (n : ℕ) (M V₀ V : Subgroup G) (c x : G) :
    InCalO n (conjSubgroup M c) (conjSubgroup V₀ c) (conjSubgroup V c) (c⁻¹ * x * c) ↔
      InCalO n M V₀ V x := by
  unfold InCalO
  exact and_congr (w183b2_oFirst_conj n M V₀ V c x) (w183b2_oDual_conj n M V₀ V c x)

private theorem w183b2_inCalOStar_conj_aux (n : ℕ) (M V₀ V : Subgroup G) (c x : G)
    (h : InCalOStar n M V₀ V x) :
    InCalOStar n (conjSubgroup M c) (conjSubgroup V₀ c) (conjSubgroup V c) (c⁻¹ * x * c) := by
  unfold InCalOStar at h ⊢
  obtain ⟨hO, K, hKnorm, hKset, hQuot, hconjStar, hcomm, hcentral, hne⟩ := h
  have hVx : conjSubgroup (conjSubgroup V c) (c⁻¹ * x * c) = conjSubgroup (conjSubgroup V x) c := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  have hMx : conjSubgroup (conjSubgroup M c) (c⁻¹ * x * c) = conjSubgroup (conjSubgroup M x) c := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  have hL : conjSubgroup V c ⊔ conjSubgroup (conjSubgroup V c) (c⁻¹ * x * c) =
      conjSubgroup (V ⊔ conjSubgroup V x) c := by
    rw [hVx, w183b2_conjSubgroup_sup]
  have hI : conjSubgroup (conjSubgroup V x ⊓ M) c =
      conjSubgroup (conjSubgroup V c) (c⁻¹ * x * c) ⊓ conjSubgroup M c := by
    rw [E3.conjSubgroup_inf, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
      show c * (c⁻¹ * x * c) = x * c by group]
  have hJ : conjSubgroup (V ⊓ conjSubgroup M x) c =
      conjSubgroup V c ⊓ conjSubgroup (conjSubgroup M c) (c⁻¹ * x * c) := by
    rw [E3.conjSubgroup_inf, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
      show c * (c⁻¹ * x * c) = x * c by group]
  have hquot : E3.mQuot (conjSubgroup V c) (conjSubgroup (conjSubgroup M c) (c⁻¹ * x * c)) =
      E3.mQuot V (conjSubgroup M x) := by
    rw [hMx, E3.mQuot_conjSubgroup]
  refine ⟨(w183b2_inCalO_conj n M V₀ V c x).2 hO, conjSubgroup K c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hL.symm ▸ s16c1_normal_conj hKnorm c
  · rw [← hI, ← hJ]
    exact w183b2_conjSubgroup_coe_mul K (conjSubgroup V x ⊓ M) (V ⊓ conjSubgroup M x) c hKset
  · letI : ((conjSubgroup K c).subgroupOf (conjSubgroup (V ⊔ conjSubgroup V x) c)).Normal :=
      s16c1_normal_conj hKnorm c
    have hqs : QuotShape (conjSubgroup (V ⊔ conjSubgroup V x) c) (conjSubgroup K c)
        (E3.mQuot V (conjSubgroup M x)) :=
      s16c1_quotShape_conj c hQuot
    simp only [← hL, ← hquot] at hqs
    exact hqs
  · obtain ⟨l, hl, hgl⟩ := hconjStar
    refine ⟨c⁻¹ * l * c, ?_, ?_⟩
    · rw [hL, mem_conjSubgroup_iff]
      have : c * (c⁻¹ * l * c) * c⁻¹ = l := by group
      rw [this]
      exact hl
    · have hlx : conjSubgroup (conjSubgroup V c) (c⁻¹ * l * c) =
          conjSubgroup (conjSubgroup V l) c := by
        rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
        congr 1
        group
      rw [hVx, hlx, hgl]
  · have h0 : conjSubgroup (conjSubgroup V₀ c) (c⁻¹ * x * c) =
        conjSubgroup (conjSubgroup V₀ x) c := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group
    rw [h0, ← E3.conjSubgroup_commutator]
    exact E3.conjSubgroup_mono_left c hcomm
  · have h := congrArg (fun X : Subgroup G => conjSubgroup X c) hcentral
    simp only [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, w183b2_conjSubgroup_sup, hI,
      hVx] at h
    simpa only [hVx] using h
  · intro hEq
    apply hne
    have hEq' := hEq
    simp only [hVx, hMx] at hEq'
    have h' := congrArg (fun X : Subgroup G => conjSubgroup X c⁻¹) hEq'
    have hLHS : conjSubgroup ((conjSubgroup V c ⊓ conjSubgroup (conjSubgroup V x) c) ⊔
        conjSubgroup V₀ c) c⁻¹ = (V ⊓ conjSubgroup V x) ⊔ V₀ := by
      rw [w183b2_conjSubgroup_sup, E3.conjSubgroup_inf, conjSubgroup_conjSubgroup_inv,
        conjSubgroup_conjSubgroup_inv, conjSubgroup_conjSubgroup_inv]
    have hRHS : conjSubgroup (conjSubgroup V c ⊓ conjSubgroup (conjSubgroup M x) c) c⁻¹ =
        V ⊓ conjSubgroup M x := by
      rw [E3.conjSubgroup_inf, conjSubgroup_conjSubgroup_inv, conjSubgroup_conjSubgroup_inv]
    rw [hLHS, hRHS] at h'
    exact h'

theorem w183b2_inCalOStar_conj (n : ℕ) (M V₀ V : Subgroup G) (c x : G) :
    InCalOStar n (conjSubgroup M c) (conjSubgroup V₀ c) (conjSubgroup V c) (c⁻¹ * x * c) ↔
      InCalOStar n M V₀ V x := by
  constructor
  · intro h
    have hM : conjSubgroup (conjSubgroup M c) c⁻¹ = M := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    have hV₀ : conjSubgroup (conjSubgroup V₀ c) c⁻¹ = V₀ := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    have hV : conjSubgroup (conjSubgroup V c) c⁻¹ = V := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    have hinv : (c⁻¹)⁻¹ * (c⁻¹ * x * c) * c⁻¹ = x := by group
    have h' := w183b2_inCalOStar_conj_aux n (conjSubgroup M c) (conjSubgroup V₀ c)
      (conjSubgroup V c) c⁻¹ (c⁻¹ * x * c) h
    rw [hM, hV₀, hV, hinv] at h'
    exact h'
  · intro h
    exact w183b2_inCalOStar_conj_aux n M V₀ V c x h

section Certified



namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

private theorem w183b2_eOmegaZ_le_conj_M (x : Ctx188 D V₀ V H i 3) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) : eOmegaZ H D.T ≤ conjSubgroup D.M g := by
  have hbot := x.inf_ne_bot_of_gam183 hg
  obtain ⟨w, hw, hwbot⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hbot)
  have hw1 : w ≠ 1 := fun h1 => hwbot (Subgroup.mem_bot.mpr h1)
  have hwCent : eOmegaZ H D.T ≤ Subgroup.centralizer ({w} : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr x.hyp.isElemAbelian_eOmegaZ.1).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw.1))
  exact hwCent.trans (centralizer_le_conj_M x.hyp.setting x.hyp.ne_bot g hw.2 hw1)

private theorem w183b2_V₀_inf_conj_M_ne_bot (x : Ctx188 D V₀ V H i 3) {g g' : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) (hg' : Gam183 V H (eOmegaZ H D.T) i g') :
    conjSubgroup V₀ g ⊓ conjSubgroup D.M g' ≠ ⊥ := by
  have hE : eOmegaZ H D.T ≤ conjSubgroup D.M g' := x.w183b2_eOmegaZ_le_conj_M hg'
  have hne : eOmegaZ H D.T ⊓ conjSubgroup V₀ g ≠ ⊥ := x.inf_ne_bot_of_gam183 hg
  intro hbot
  apply hne
  rw [eq_bot_iff] at hbot ⊢
  exact fun y hy => hbot ⟨hy.2, hE hy.1⟩

private theorem w183b2_mQuot_le (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    {g₁ g₂ : G} (hg₁ : Gam183 V H (eOmegaZ H D.T) i g₁)
    (hg₂ : Gam183 V H (eOmegaZ H D.T) i g₂)
    (hk : mOfG (M.img (vInH V H g₁))
      (M.img (vInH V H g₁) ⊓ Subgroup.normalizer (M.img (vInH V H g₂) : Set _)) ≤ 2) :
    E3.mQuot (conjSubgroup V g₁) (conjSubgroup D.M g₂) ≤ i + 2 := by
  have hDab : IsElemAbelian 2 (vInH V H g₁) :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g₁).mono inf_le_left
  have hB'le : M.img (vInH V H g₁) ⊓
      Subgroup.normalizer (M.img (vInH V H g₂) : Set (LGL 2 M.W)) ≤ M.img (vInH V H g₁) :=
    inf_le_left
  obtain ⟨B₀, hB₀A, hB₀C, hB₀img⟩ := M.exists_preimage (A := vInH V H g₁) inf_le_right hB'le
  have hB₀H : B₀ ≤ H := hB₀A.trans inf_le_right
  have hmq : E3.mQuot (vInH V H g₁) B₀ ≤ 2 := by
    rw [← M.mOf_img (A := vInH V H g₁) inf_le_right hDab hB₀A hB₀C, hB₀img, mOf_eq_mOfG]
    exact hk
  have hB₀M : B₀ ≤ conjSubgroup D.M g₂ := by
    intro b hb
    refine x.mem_conj_M_of_img_normalizer M hg₂ (hB₀H hb) ?_
    have hmem : M.ρ ⟨b, hB₀H hb⟩ ∈ M.img B₀ :=
      M.mem_img.2 ⟨⟨b, hB₀H hb⟩, hb, rfl⟩
    rw [hB₀img] at hmem
    exact (Subgroup.mem_inf.1 hmem).2
  calc E3.mQuot (conjSubgroup V g₁) (conjSubgroup D.M g₂)
      = E3.mQuot (conjSubgroup V g₁) (conjSubgroup V g₁ ⊓ conjSubgroup D.M g₂) :=
        (mQuot_inf_left (conjSubgroup V g₁) (conjSubgroup D.M g₂)).symm
    _ ≤ E3.mQuot (conjSubgroup V g₁) B₀ :=
        E3.mQuot_mono (le_inf (hB₀A.trans inf_le_left) hB₀M)
    _ = E3.mQuot (vInH V H g₁) B₀ + E3.mQuot (conjSubgroup V g₁) (vInH V H g₁) :=
        E3.mQuot_add hB₀A inf_le_left
    _ ≤ i + 2 := by
        have h2 : E3.mQuot (conjSubgroup V g₁) (vInH V H g₁) ≤ i := hg₁.1
        omega

theorem pair_inCalOStar (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    {g h : G} (hg : Gam183 V H (eOmegaZ H D.T) i g) (hh : h ∈ H)
    (hnot1 : ¬ M.img (vInH V H (g * h)) ≤ Subgroup.normalizer (M.img (vInH V H g) : Set _))
    (hnot2 : ¬ M.img (vInH V H g) ≤ Subgroup.normalizer (M.img (vInH V H (g * h)) : Set _))
    (hk1 : mOfG (M.img (vInH V H g))
      (M.img (vInH V H g) ⊓ Subgroup.normalizer (M.img (vInH V H (g * h)) : Set _)) ≤ 2)
    (hk2 : mOfG (M.img (vInH V H (g * h)))
      (M.img (vInH V H (g * h)) ⊓ Subgroup.normalizer (M.img (vInH V H g) : Set _)) ≤ 2) :
    InCalOStar (i + 2) (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) h := by
  have hg' : Gam183 V H (eOmegaZ H D.T) i (g * h) :=
    Gam183.conj (Hyp183.normalizer_eOmegaZ H D.T) hh hg
  have hO : InCalO (i + 2) (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) h := by
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · rw [conjSubgroup_conjSubgroup]
      intro hle
      apply hnot1
      intro r hr
      obtain ⟨y, hyS, hyr⟩ := M.mem_img.1 hr
      rw [← hyr]
      exact Hyp183.img_normalizer_of_mem_conj x.hyp M y.2 (hle (Subgroup.mem_inf.1 hyS).1)
    · rw [conjSubgroup_conjSubgroup]
      exact w183b2_mQuot_le x M hg hg' hk1
    · intro _
      rw [conjSubgroup_conjSubgroup]
      exact x.w183b2_V₀_inf_conj_M_ne_bot hg hg'
    · rw [conjSubgroup_conjSubgroup]
      intro hle
      apply hnot2
      intro r hr
      obtain ⟨y, hyS, hyr⟩ := M.mem_img.1 hr
      rw [← hyr]
      exact Hyp183.img_normalizer_of_mem_conj x.hyp M y.2 (hle (Subgroup.mem_inf.1 hyS).1)
    · rw [conjSubgroup_conjSubgroup]
      exact w183b2_mQuot_le x M hg' hg hk2
    · intro _
      rw [conjSubgroup_conjSubgroup]
      exact x.w183b2_V₀_inf_conj_M_ne_bot hg' hg
  have hbnd : i + 2 < mBar D.M V₀ V x.hyp.setting.isElemAbelian := by
    have := x.bound
    omega
  have he : g⁻¹ * (g * h * g⁻¹) * g = h := by group
  have hO' : InCalO (i + 2) (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g)
      (g⁻¹ * (g * h * g⁻¹) * g) := he.symm ▸ hO
  have hO'' : InCalO (i + 2) D.M V₀ V (g * h * g⁻¹) :=
    (w183b2_inCalO_conj (i + 2) D.M V₀ V g (g * h * g⁻¹)).1 hO'
  have h64 := w183b2_sixteen21 x.h162 x.hyp.setting x.hyp.ne_bot x.mbar hbnd hO''
  exact he ▸ (w183b2_inCalOStar_conj (i + 2) D.M V₀ V g (g * h * g⁻¹)).2 h64.inCalOStar

end Ctx188

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
