module

public import CFSG.Quasithin.Background.C31SporJB
public import CFSG.Quasithin.Background.C48SporSetup
public import CFSG.Quasithin.Background.C48SporCenter
public import CFSG.Quasithin.Background.F918V3S3Aux
public import CFSG.Quasithin.Vol2.KGFactHeInspJ4

public section

namespace CFSG.Quasithin.C31SporJ

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits C48Spor
open scoped Pointwise

@[expose] def J4Cond {A : Type} [Group A] (R M : Subgroup A) : Prop :=
  Subgroup.normalizer (thompsonJ R : Set A) ≤ M ∧ Subgroup.normalizer (centerOf R : Set A) ≤ M ∧
    Subgroup.normalizer (omegaOneCenterOf (thompsonJ R) : Set A) ≤ M

section Component

variable {G : Type} [Group G]

theorem exists_mul_of_normalizer_j4
    {K : Subgroup G} (hKj : IsSporadic .J4 ↥K) {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ K, k⁻¹ * x ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨e⟩ := hKj
  obtain ⟨g, hg⟩ := H13.KGInsp.j4_all_inner
    (e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat))
    (K.normalizerMonoidHom ⟨x, hx⟩)
  refine ⟨g, g.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have h1 : x * y * x⁻¹ = (g : G) * y * (g : G)⁻¹ := by
    have := congrArg (fun α : MulAut ↥K => ((α ⟨y, hy⟩ : ↥K) : G)) hg
    simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv] using this
  calc y * ((g : G)⁻¹ * x) = (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * x := by group
    _ = (g : G)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
    _ = (g : G)⁻¹ * x * y := by group

theorem inf_centralizer_eq_bot {K : Subgroup G} (hZ : Subgroup.center ↥K = ⊥) :
    K ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxC⟩
  have hx : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
  rw [hZ, Subgroup.mem_bot] at hx
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx)

variable [Finite G]

theorem pCoreOf_le_centralizer {H K : Subgroup G} (hK : CFSG.Open.IsComponentOf K H) :
    pCoreOf 2 K ≤ Subgroup.centralizer (K : Set G) := by
  have hq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (CFSG.LieType.BorelTits.pCore_normal (G := ↥K) 2) with htop | hle
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥K := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K) 2).of_equiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
    have : Group.IsNilpotent ↥K := hp.isNilpotent
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have : Group.IsPerfect ↥K := hq.1
    exact Group.IsPerfect.not_isNilpotent ↥K inferInstance
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hle hx) ⟨k, hk⟩)

theorem centralizerSection_le_centralizer {H K : Subgroup G} (hK : CFSG.Open.IsComponentOf K H)
    (X : Subgroup G) : centralizerSection X K (pCoreOf 2 K) ≤ Subgroup.centralizer (K : Set G) := by
  have hq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  intro m hm
  refine mem_centralizer_of_perfect hperf hm.2.1 fun k hk => ?_
  have e : m * k * m⁻¹ * k⁻¹ = (k * m * k⁻¹ * m⁻¹)⁻¹ := by group
  rw [e]
  exact pCoreOf_le_centralizer hK (Subgroup.inv_mem _ (hm.2.2.2 k hk))

end Component

section Img

variable {G : Type} [Group G] {H K : Subgroup G}

@[expose] noncomputable def kHom (hKX : K ≤ sporX H K) : ↥K →* ↥(sporX H K) ⧸ sporN H K :=
  (img (sporN H K) K).subtype.comp (imgHom (N := sporN H K) hKX)

theorem kHom_injective (hKX : K ≤ sporX H K) (hZ : Subgroup.center ↥K = ⊥) :
    Function.Injective (kHom hKX) :=
  (img (sporN H K) K).subtype_injective.comp
    ((MonoidHom.ker_eq_bot_iff _).mp ((ker_imgHom_K hKX).trans hZ))

theorem img_eq_map_kHom (hKX : K ≤ sporX H K) {Y : Subgroup G} (hYK : Y ≤ K) :
    img (sporN H K) Y = (Y.subgroupOf K).map (kHom hKX) := by
  ext a
  rw [mem_img, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hxY, rfl⟩
    exact ⟨⟨x, hYK hxY⟩, hxY, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hKX y.2⟩, hy, rfl⟩

variable {F : ∀ {G : Type} [Group G], Subgroup G → Subgroup G}

theorem prodFunctor_img (hF : ProdFunctor F) (hKX : K ≤ sporX H K) (hZ : Subgroup.center ↥K = ⊥)
    {Y : Subgroup G} (hYK : Y ≤ K) : F (img (sporN H K) Y) = img (sporN H K) (F Y) := by
  have hFY : F Y = (F (Y.subgroupOf K)).map K.subtype := by
    conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hYK]
    exact hF.map_inj _ K.subtype_injective _
  have hsub : (F Y).subgroupOf K = F (Y.subgroupOf K) := by
    rw [hFY]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  rw [img_eq_map_kHom hKX hYK, img_eq_map_kHom hKX ((hF.le_self Y).trans hYK), hsub]
  exact hF.map_inj _ (kHom_injective hKX hZ) _

theorem eq_of_mk_eq (hZ : Subgroup.center ↥K = ⊥) {u v : ↥(sporX H K)} (hu : (u : G) ∈ K)
    (hv : (v : G) ∈ K) (h : (u : ↥(sporX H K) ⧸ sporN H K) = (v : ↥(sporX H K) ⧸ sporN H K)) :
    u = v := by
  have hN : u⁻¹ * v ∈ sporN H K := QuotientGroup.eq.mp h
  have hc : ((u⁻¹ * v : ↥(sporX H K)) : G) ∈ Subgroup.centralizer (K : Set G) := hN
  have hk : ((u⁻¹ * v : ↥(sporX H K)) : G) ∈ K := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact K.mul_mem (K.inv_mem hu) hv
  have h1 : ((u⁻¹ * v : ↥(sporX H K)) : G) ∈ K ⊓ Subgroup.centralizer (K : Set G) := ⟨hk, hc⟩
  rw [inf_centralizer_eq_bot hZ, Subgroup.mem_bot] at h1
  have h2 : u⁻¹ * v = 1 := Subtype.ext h1
  exact (inv_mul_eq_one.mp h2)

end Img

section Discharge

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

theorem eq_sup_of_j4
    (h22 : ASC22One G) (h : HypC28 H R M L V)
    (hK : CFSG.Open.IsComponentOf K H) (h31 : C31Basic H R M L V K) (hKj : IsSporadic .J4 ↥K) :
    R = (R ⊓ K) ⊔ (R ⊓ Subgroup.centralizer (K : Set G)) := by
  refine le_antisymm (fun r hr => ?_) (sup_le inf_le_left inf_le_left)
  have hrN : r ∈ Subgroup.normalizer (K : Set G) := h31.2.1 (h.le_M hr)
  obtain ⟨k, hk, hkc⟩ := exists_mul_of_normalizer_j4 hKj hrN
  have hc22 := h22 H R K h.sqtk (c2_9_two h).2 (F918V3S3.mem_cComp_of_isComponentOf hK)
  have hcS : k⁻¹ * r ∈ centralizerSection H K (pCoreOf 2 K) := by
    refine ⟨H.mul_mem (H.inv_mem (hK.1 hk)) (h.le_H (h.le_M hr)),
      Subgroup.centralizer_le_normalizer _ hkc,
      Subgroup.centralizer_le_normalizer _
        (Subgroup.centralizer_le (fun z hz => pCoreOf_le 2 K hz) hkc), fun y hy => ?_⟩
    rw [show y * (k⁻¹ * r) * y⁻¹ * (k⁻¹ * r)⁻¹ = 1 by
      rw [Subgroup.mem_centralizer_iff.mp hkc y hy]; group]
    exact Subgroup.one_mem _
  have hmem : r ∈ (R : Set G) ∩ ((K : Set G) * (centralizerSection H K (pCoreOf 2 K) : Set G)) :=
    ⟨hr, Set.mem_mul.mpr ⟨k, hk, k⁻¹ * r, hcS, by group⟩⟩
  rw [hc22] at hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hmem
  rw [← hxy]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
    (Subgroup.mem_sup_right ⟨hy.1, centralizerSection_le_centralizer hK R hy⟩)

variable {F : ∀ {G : Type} [Group G], Subgroup G → Subgroup G}

theorem normalizer_prodFunctor_img_le
    (hF : ProdFunctor F)
    (h22 : ASC22One G) (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (h31 : C31Basic H R M L V K) (hKj : IsSporadic .J4 ↥K) :
    Subgroup.normalizer (F (img (sporN H K) R) : Set (↥(sporX H K) ⧸ sporN H K)) ≤
      img (sporN H K) M := by
  have hKX : K ≤ sporX H K := K_le_sporX hK.1
  have hZ : Subgroup.center ↥K = ⊥ := center_eq_bot_j4 hKj hK.2.2
  have hRX : R ≤ sporX H K := le_sporX (h.le_M.trans h.le_H) (h.le_M.trans h31.2.1)
  set C := R ⊓ Subgroup.centralizer (K : Set G) with hC
  set D := R ⊓ K with hD
  have hReq : R = D ⊔ C := eq_sup_of_j4 h22 h hK h31 hKj
  have hcomm : ∀ x ∈ D, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx.2
  have hDC : D ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hxK⟩, ⟨-, hxC⟩⟩
    have h1 : x ∈ K ⊓ Subgroup.centralizer (K : Set G) := ⟨hxK, hxC⟩
    rwa [inf_centralizer_eq_bot hZ] at h1
  have hFR : F R = F D ⊔ F C := (congrArg (fun X => F X) hReq).trans (hF.sup_eq hcomm hDC)
  have hDX : D ≤ sporX H K := inf_le_left.trans hRX
  have hCX : C ≤ sporX H K := inf_le_left.trans hRX
  have himgC : img (sporN H K) C = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨x, hx, rfl⟩ := mem_img.1 ha
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact hx.2
  have himgR : img (sporN H K) R = img (sporN H K) D := by
    rw [show img (sporN H K) R = img (sporN H K) (D ⊔ C) from congrArg _ hReq,
      img_sup hDX hCX, himgC, sup_bot_eq]
  have hFimg : F (img (sporN H K) R) = img (sporN H K) (F D) := by
    rw [himgR]
    exact prodFunctor_img hF hKX hZ inf_le_right
  intro a ha
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨k, hk, hkc⟩ := exists_mul_of_normalizer_j4 hKj (Subgroup.mem_inf.mp x.2).2
  set k' : ↥(sporX H K) := ⟨k, hKX hk⟩ with hk'
  have hxk : ((x : ↥(sporX H K)) : ↥(sporX H K) ⧸ sporN H K) = (k' : ↥(sporX H K) ⧸ sporN H K) := by
    refine QuotientGroup.eq.mpr ?_
    show (x : G)⁻¹ * k ∈ Subgroup.centralizer (K : Set G)
    have := Subgroup.inv_mem _ hkc
    rwa [mul_inv_rev, inv_inv] at this
  rw [hxk] at ha ⊢
  rw [hFimg] at ha
  have hkFD : k ∈ Subgroup.normalizer (F D : Set G) := by
    refine A4.mem_normalizer_of_conj_mem fun z hz => ?_
    have hzK : z ∈ K := (hF.le_self D hz).2
    set z' : ↥(sporX H K) := ⟨z, hKX hzK⟩ with hz'
    have hmk : (z' : ↥(sporX H K) ⧸ sporN H K) ∈ img (sporN H K) (F D) := mk_mem_img hz
    obtain ⟨w, hwF, hw⟩ := mem_img.1 ((Subgroup.mem_normalizer_iff.mp ha _).mp hmk)
    have hwK : (w : G) ∈ K := (hF.le_self D hwF).2
    have hkzK : ((k' * z' * k'⁻¹ : ↥(sporX H K)) : G) ∈ K := by
      simp only [hk', hz', Subgroup.coe_mul, Subgroup.coe_inv]
      exact K.mul_mem (K.mul_mem hk hzK) (K.inv_mem hk)
    have hw' : w = k' * z' * k'⁻¹ := eq_of_mk_eq hZ hwK hkzK (by
      rw [hw, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv])
    have : (w : G) = k * z * k⁻¹ := by
      rw [hw']
      simp only [hk', hz', Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← this]
    exact hwF
  have hkFC : k ∈ Subgroup.normalizer (F C : Set G) := by
    refine A4.mem_normalizer_of_conj_mem fun z hz => ?_
    have hzc : k * z = z * k := Subgroup.mem_centralizer_iff.mp (hF.le_self C hz).2 k hk
    rw [hzc, mul_inv_cancel_right]
    exact hz
  have hkFR : k ∈ Subgroup.normalizer (F R : Set G) := by
    rw [hFR]
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hkFD, hkFC⟩
  have hRne : R ≠ ⊥ := (c2_9_two h).2.2.1
  have hcgs : H ⊓ Subgroup.normalizer (F R : Set G) ≤ cgsIn H R :=
    le_iSup_of_le (F R) (le_iSup_of_le (hF.le_self R) (le_iSup_of_le (hF.ne_bot h.pgroup hRne)
      (le_iSup_of_le (hF.characteristic R) le_rfl)))
  exact mk_mem_img (h.cgs (hcgs ⟨hK.1 hk, hkFR⟩))

theorem normalizer_img_le_of_j4
    (h22 : ASC22One G) (h : HypC28 H R M L V)
    (hK : CFSG.Open.IsComponentOf K H) (h31 : C31Basic H R M L V K) (hKj : IsSporadic .J4 ↥K) :
    J4Cond (img (sporN H K) R) (img (sporN H K) M) :=
  ⟨normalizer_prodFunctor_img_le prodFunctor_thompsonJ h22 h hK h31 hKj,
    normalizer_prodFunctor_img_le prodFunctor_centerOf h22 h hK h31 hKj,
    normalizer_prodFunctor_img_le prodFunctor_omegaOneCenterJ h22 h hK h31 hKj⟩

end Discharge

end CFSG.Quasithin.C31SporJ
