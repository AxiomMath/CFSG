module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapSecA
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {U₂ U₁ : Subgroup W}

private theorem w16f_rk_subgroupOf {A U : Subgroup W} (hAU : A ≤ U) :
    rk ↥(A.subgroupOf U) = rk ↥A := by
  unfold rk
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAU).toEquiv]

private theorem w16f_secImg_zpowers {t : MulAut W} (hts : t ∈ secStabAll U₂ U₁) :
    secImg (Subgroup.zpowers t) U₂ U₁ = Subgroup.zpowers (secAut U₂ U₁ ⟨t, hts⟩) := by
  have hsub : (Subgroup.zpowers t).subgroupOf (secStabAll U₂ U₁) =
      Subgroup.zpowers (⟨t, hts⟩ : ↥(secStabAll U₂ U₁)) := by
    ext a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [Subgroup.coe_zpow] using congrArg Subtype.val hk⟩
  rw [secImg, hsub, MonoidHom.map_zpowers]

theorem isQuasisimple_secImg {K : Subgroup (MulAut W)} (hK : IsQuasisimple ↥K)
    (hKs : K ≤ secStabAll U₂ U₁) (hnt : ¬ commSub U₂ K ≤ U₁) :
    IsQuasisimple ↥(secImg K U₂ U₁) := by
  haveI : Nontrivial ↥(secImg K U₂ U₁) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr fun hbot => hnt ((secImg_eq_bot_iff hKs).mp hbot)
  refine (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥(secImg K U₂ U₁)).2.2.1.mpr ?_
  refine CFSG.LocalAnalysis.UniquenessCase.UC22.uc22br4_isQuasisimple_of_surjective
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥K).2.2.1.mp hK)
    (((secAut U₂ U₁).comp (Subgroup.inclusion hKs)).codRestrict (secImg K U₂ U₁)
      fun k => mem_secImg.mpr ⟨⟨k.1, hKs k.2⟩, k.2, rfl⟩) ?_
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, hgφ⟩ := mem_secImg.mp hφ
  refine ⟨⟨g.1, hg⟩, Subtype.ext ?_⟩
  show secAut U₂ U₁ (⟨g.1, hKs hg⟩ : ↥(secStabAll U₂ U₁)) = φ
  rw [show (⟨g.1, hKs hg⟩ : ↥(secStabAll U₂ U₁)) = g from Subtype.ext rfl, hgφ]

theorem orderOf_secAut {t : MulAut W} (ht2 : orderOf t = 2) (hts : t ∈ secStabAll U₂ U₁)
    (hnt : ¬ commSub U₂ (Subgroup.zpowers t) ≤ U₁) :
    orderOf (secAut U₂ U₁ ⟨t, hts⟩) = 2 := by
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have hsq : (⟨t, hts⟩ : ↥(secStabAll U₂ U₁)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two, ht2']
    rfl
  have hpow : (secAut U₂ U₁ ⟨t, hts⟩) ^ 2 = 1 := by
    rw [← map_pow, hsq, map_one]
  have hne : secAut U₂ U₁ ⟨t, hts⟩ ≠ 1 := by
    intro h1
    apply hnt
    rw [← secImg_eq_bot_iff (Subgroup.zpowers_le.mpr hts),
      w16f_secImg_zpowers hts, h1, Subgroup.zpowers_one_eq_bot]
  exact orderOf_eq_prime hpow hne

theorem commV_secAut {t : MulAut W} (hts : t ∈ secStabAll U₂ U₁) :
    commV (Subgroup.zpowers (secAut U₂ U₁ ⟨t, hts⟩)) =
      ((commSub U₂ (Subgroup.zpowers t) ⊔ U₁).subgroupOf U₂).map
        (QuotientGroup.mk' (U₁.subgroupOf U₂)) := by
  have hsub : commSub U₂ (Subgroup.zpowers t) ≤ U₂ :=
    commSub_le_of_invariant fun y hy w hw =>
      (mem_stabSub.mp (Subgroup.zpowers_le.mpr hts.1 hy) w).2 hw
  have key : ∀ c (hc : c ∈ commSub U₂ (Subgroup.zpowers t)),
      QuotientGroup.mk' (U₁.subgroupOf U₂) ⟨c, hsub hc⟩ ∈
        commV (Subgroup.zpowers (secAut U₂ U₁ ⟨t, hts⟩)) := by
    intro c hc
    refine Subgroup.closure_induction (p := fun c hc =>
      QuotientGroup.mk' (U₁.subgroupOf U₂) ⟨c, hsub hc⟩ ∈
        commV (Subgroup.zpowers (secAut U₂ U₁ ⟨t, hts⟩))) ?_ ?_ ?_ ?_ hc
    · intro y hy
      obtain ⟨x, hx, w, hw, rfl⟩ := hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hmem : (t ^ k) w * w⁻¹ ∈ commSub U₂ (Subgroup.zpowers t) :=
        Subgroup.subset_closure
          ⟨t ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩, w, hw, rfl⟩
      have heq : QuotientGroup.mk' (U₁.subgroupOf U₂) ⟨(t ^ k) w * w⁻¹, hsub hmem⟩ =
          ((secAut U₂ U₁ ⟨t, hts⟩) ^ k)
              (QuotientGroup.mk' (U₁.subgroupOf U₂) ⟨w, hw⟩) *
            (QuotientGroup.mk' (U₁.subgroupOf U₂) ⟨w, hw⟩)⁻¹ := by
        have h1 : (⟨(t ^ k) w * w⁻¹, hsub hmem⟩ : ↥U₂) =
            resAut U₂ ⟨((⟨t, hts⟩ : ↥(secStabAll U₂ U₁)) ^ k).1,
              ((⟨t, hts⟩ : ↥(secStabAll U₂ U₁)) ^ k).2.1⟩ ⟨w, hw⟩ * ⟨w, hw⟩⁻¹ :=
          Subtype.ext rfl
        rw [h1, map_mul, map_inv, ← map_zpow (secAut U₂ U₁) ⟨t, hts⟩ k]
        simp only [QuotientGroup.mk'_apply]
        rw [secAut_mk]
      rw [heq]
      exact Subgroup.subset_closure ⟨_, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩, _, rfl⟩
    · have h1 : (⟨1, hsub (Subgroup.one_mem _)⟩ : ↥U₂) = 1 := Subtype.ext rfl
      rw [h1, map_one]
      exact Subgroup.one_mem _
    · intro x y hx hy ihx ihy
      have hxy : (⟨x * y, hsub (Subgroup.mul_mem _ hx hy)⟩ : ↥U₂) =
          ⟨x, hsub hx⟩ * ⟨y, hsub hy⟩ := Subtype.ext rfl
      rw [hxy, map_mul]
      exact Subgroup.mul_mem _ ihx ihy
    · intro x hx ihx
      have hxinv : (⟨x⁻¹, hsub (Subgroup.inv_mem _ hx)⟩ : ↥U₂) = (⟨x, hsub hx⟩)⁻¹ :=
        Subtype.ext rfl
      rw [hxinv, map_inv]
      exact Subgroup.inv_mem _ ihx
  apply le_antisymm
  · rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (U₁.subgroupOf U₂) v
    have hmem : (t ^ k) (u : W) * (u : W)⁻¹ ∈ commSub U₂ (Subgroup.zpowers t) :=
      Subgroup.subset_closure
        ⟨t ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩, u, u.2, rfl⟩
    have hgen : (⟨(t ^ k) (u : W) * (u : W)⁻¹, hsub hmem⟩ : ↥U₂) ∈
        (commSub U₂ (Subgroup.zpowers t) ⊔ U₁).subgroupOf U₂ :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hmem)
    refine Subgroup.mem_map.mpr ⟨⟨(t ^ k) (u : W) * (u : W)⁻¹, hsub hmem⟩, hgen, ?_⟩
    have h1 : (⟨(t ^ k) (u : W) * (u : W)⁻¹, hsub hmem⟩ : ↥U₂) =
        resAut U₂ ⟨((⟨t, hts⟩ : ↥(secStabAll U₂ U₁)) ^ k).1,
          ((⟨t, hts⟩ : ↥(secStabAll U₂ U₁)) ^ k).2.1⟩ u * u⁻¹ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_inv, ← map_zpow (secAut U₂ U₁) ⟨t, hts⟩ k]
    simp only [QuotientGroup.mk'_apply]
    rw [secAut_mk]
  · rintro _ ⟨v, hv, rfl⟩
    have hvW : (v : W) ∈ commSub U₂ (Subgroup.zpowers t) ⊔ U₁ := Subgroup.mem_subgroupOf.mp hv
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hvW
    have hbU : b ∈ U₂ := by
      have hb' : b = a⁻¹ * (v : W) := by rw [← hab]; group
      rw [hb']
      exact U₂.mul_mem (U₂.inv_mem (hsub ha)) v.2
    have hv_eq : v = (⟨a * b, U₂.mul_mem (hsub ha) hbU⟩ : ↥U₂) := Subtype.ext hab.symm
    have hker : QuotientGroup.mk' (U₁.subgroupOf U₂) ⟨b, hbU⟩ = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact Subgroup.mem_subgroupOf.mpr hb
    have hprod_eq : (⟨a * b, U₂.mul_mem (hsub ha) hbU⟩ : ↥U₂) =
        ⟨a, hsub ha⟩ * ⟨b, hbU⟩ := Subtype.ext rfl
    rw [hv_eq, hprod_eq, map_mul, hker, mul_one]
    exact key a ha

theorem rk_commV_secAut (hle : U₁ ≤ U₂) {t : MulAut W} (hts : t ∈ secStabAll U₂ U₁) :
    rk ↥(commV (Subgroup.zpowers (secAut U₂ U₁ ⟨t, hts⟩))) = secCost t U₂ U₁ := by
  have hsub : commSub U₂ (Subgroup.zpowers t) ⊔ U₁ ≤ U₂ :=
    sup_le (commSub_le_of_invariant fun x hx w hw =>
      (mem_stabSub.mp (Subgroup.zpowers_le.mpr hts.1 hx) w).2 hw) hle
  have hleker : U₁.subgroupOf U₂ ≤
      (commSub U₂ (Subgroup.zpowers t) ⊔ U₁).subgroupOf U₂ :=
    Subgroup.subgroupOf_mono U₂ le_sup_right
  have hkinf : ((commSub U₂ (Subgroup.zpowers t) ⊔ U₁).subgroupOf U₂) ⊓
      (QuotientGroup.mk' (U₁.subgroupOf U₂)).ker = U₁.subgroupOf U₂ := by
    rw [QuotientGroup.ker_mk']
    exact inf_eq_right.mpr hleker
  have h3 : rk ↥(((commSub U₂ (Subgroup.zpowers t) ⊔ U₁).subgroupOf U₂).map
        (QuotientGroup.mk' (U₁.subgroupOf U₂))) + rk ↥U₁ =
      rk ↥(commSub U₂ (Subgroup.zpowers t) ⊔ U₁) := by
    have h := rk_map_add_rk_inf_ker (QuotientGroup.mk' (U₁.subgroupOf U₂))
      ((commSub U₂ (Subgroup.zpowers t) ⊔ U₁).subgroupOf U₂)
    rw [hkinf, w16f_rk_subgroupOf hsub, w16f_rk_subgroupOf hle] at h
    exact h
  rw [commV_secAut hts]
  unfold secCost
  rw [← h3, Nat.add_sub_cancel]

theorem rkIdx_fixV_secAut (hle : U₁ ≤ U₂) {t : MulAut W} (hts : t ∈ secStabAll U₂ U₁) :
    rkIdx (fixV (Subgroup.zpowers (secAut U₂ U₁ ⟨t, hts⟩))) = secCost t U₂ U₁ := by
  rw [rkIdx_fixV_zpowers (secAut U₂ U₁ ⟨t, hts⟩), rk_commV_secAut hle hts]

theorem secImg_diag {K : Subgroup (MulAut W)} {t : MulAut W} (hKs : K ≤ secStabAll U₂ U₁)
    (hts : t ∈ secStabAll U₂ U₁)
    (htr : ∀ a ∈ K, ∀ u ∈ commSub ⊤ (Subgroup.zpowers t), (a * (t * a * t⁻¹)) u = u) :
    ∀ x ∈ secImg K U₂ U₁, ∀ w ∈ commV (Subgroup.zpowers (secAut U₂ U₁ ⟨t, hts⟩)),
      (x * (secAut U₂ U₁ ⟨t, hts⟩ * x * (secAut U₂ U₁ ⟨t, hts⟩)⁻¹)) w = w := by
  intro x hx w hw
  obtain ⟨g, hg, hgx⟩ := mem_secImg.mp hx
  rw [← hgx]
  rw [commV_secAut hts] at hw
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
  have hsubtop : commSub U₂ (Subgroup.zpowers t) ≤ commSub ⊤ (Subgroup.zpowers t) :=
    commSub_mono le_top le_rfl
  obtain ⟨c, hc, u₁, hu₁, hcu⟩ := Subgroup.mem_sup.mp (Subgroup.mem_subgroupOf.mp hv)
  set h : ↥(secStabAll U₂ U₁) := g * (⟨t, hts⟩ * g * ⟨t, hts⟩⁻¹) with hh
  have hhval : (h : MulAut W) = (g : MulAut W) * (t * (g : MulAut W) * t⁻¹) := by
    rw [hh]; simp
  have hfix : (h : MulAut W) c = c := by
    rw [hhval]; exact htr (g : MulAut W) hg c (hsubtop hc)
  have hstab : (h : MulAut W) u₁ ∈ U₁ := (mem_stabSub.mp h.2.2 u₁).2 hu₁
  have hprod : (h : MulAut W) (v : W) * (v : W)⁻¹ ∈ U₁ := by
    rw [← hcu, map_mul, hfix]
    have : c * (h : MulAut W) u₁ * (c * u₁)⁻¹ = (h : MulAut W) u₁ * u₁⁻¹ := by
      simp [mul_assoc, mul_left_comm, mul_comm]
    rw [this]
    exact U₁.mul_mem hstab (U₁.inv_mem hu₁)
  have hxeq : secAut U₂ U₁ g * (secAut U₂ U₁ ⟨t, hts⟩ * secAut U₂ U₁ g *
      (secAut U₂ U₁ ⟨t, hts⟩)⁻¹) = secAut U₂ U₁ h := by
    rw [hh]; simp only [map_mul, map_inv]
  rw [hxeq]
  simp only [QuotientGroup.mk'_apply]
  rw [secAut_mk]
  refine (QuotientGroup.mk'_eq_mk' (U₁.subgroupOf U₂)).mpr
    ⟨(resAut U₂ ⟨h.1, h.2.1⟩ v)⁻¹ * v, ?_, by group⟩
  refine Subgroup.mem_subgroupOf.mpr ?_
  have hzv : (((resAut U₂ ⟨h.1, h.2.1⟩ v)⁻¹ * v : ↥U₂) : W) =
      (((h : MulAut W) (v : W) * (v : W)⁻¹)⁻¹) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, resAut, mul_inv_rev, inv_inv]
    exact mul_comm _ _
  rw [hzv]
  exact U₁.inv_mem hprod

end CFSG.LocalAnalysis.WeakClosure81
