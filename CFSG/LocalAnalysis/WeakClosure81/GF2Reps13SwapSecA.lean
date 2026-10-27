module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapSec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] {X Y : Subgroup (MulAut W)} {U₂ U₁ : Subgroup W}

private theorem w16f_commutator_subgroupOf {G : Type*} [Group G] {S X Y : Subgroup G}
    (hX : X ≤ S) (hY : Y ≤ S) :
    (⁅X, Y⁆).subgroupOf S = ⁅X.subgroupOf S, Y.subgroupOf S⁆ := by
  apply Subgroup.map_injective (f := S.subtype) Subtype.coe_injective
  simp only [Subgroup.subgroupOf, Subgroup.map_commutator,
    Subgroup.map_comap_eq_self (f := S.subtype) (H := ⁅X, Y⁆) (by
      rw [Subgroup.range_subtype]; exact Subgroup.commutator_le_of_le hX hY),
    Subgroup.map_comap_eq_self (f := S.subtype) (H := X) (by
      rw [Subgroup.range_subtype]; exact hX),
    Subgroup.map_comap_eq_self (f := S.subtype) (H := Y) (by
      rw [Subgroup.range_subtype]; exact hY)]

private theorem w16f_subgroupOf_le_subgroupOf {J : Subgroup W} (hJ : J ≤ U₂) :
    J.subgroupOf U₂ ≤ U₁.subgroupOf U₂ ↔ J ≤ U₁ := by
  constructor
  · intro h j hj
    have hj' : ((⟨j, hJ hj⟩ : ↥U₂) : W) ∈ J := hj
    have := Subgroup.mem_subgroupOf.mp (h (Subgroup.mem_subgroupOf.mpr hj'))
    simpa using this
  · intro h j hj
    exact Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hj))

private def w16f_secLift (U₂ U₁ : Subgroup W) (J : Subgroup (SecT U₂ U₁)) : Subgroup W :=
  (J.comap (QuotientGroup.mk' (U₁.subgroupOf U₂))).map U₂.subtype

private theorem w16f_mem_secLift {J : Subgroup (SecT U₂ U₁)} {w : W} :
    w ∈ w16f_secLift U₂ U₁ J ↔
      ∃ u : ↥U₂, QuotientGroup.mk' (U₁.subgroupOf U₂) u ∈ J ∧ (u : W) = w := by
  simp only [w16f_secLift, Subgroup.mem_map, Subgroup.mem_comap]
  exact ⟨fun ⟨u, hu, huw⟩ => ⟨u, hu, huw⟩, fun ⟨u, hu, huw⟩ => ⟨u, hu, huw⟩⟩

private theorem w16f_secLift_map_eq_self {J : Subgroup W} (hle : U₁ ≤ U₂) (hJ : J ≤ U₂)
    (hU₁ : U₁ ≤ J) :
    w16f_secLift U₂ U₁ ((J.subgroupOf U₂).map (QuotientGroup.mk' (U₁.subgroupOf U₂))) = J := by
  unfold w16f_secLift
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', ← Subgroup.subgroupOf_sup hJ hle,
    Subgroup.map_subgroupOf_eq_of_le (sup_le hJ hle), sup_eq_left.mpr hU₁]

private theorem w16f_recover (J : Subgroup (SecT U₂ U₁)) :
    ((w16f_secLift U₂ U₁ J).subgroupOf U₂).map (QuotientGroup.mk' (U₁.subgroupOf U₂)) = J := by
  unfold w16f_secLift
  change Subgroup.map (QuotientGroup.mk' (U₁.subgroupOf U₂))
    (Subgroup.comap U₂.subtype (Subgroup.map U₂.subtype
      (Subgroup.comap (QuotientGroup.mk' (U₁.subgroupOf U₂)) J))) = J
  rw [Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

private theorem w16f_map_mk_eq_bot_iff {J : Subgroup W} (hJ : J ≤ U₂) :
    (J.subgroupOf U₂).map (QuotientGroup.mk' (U₁.subgroupOf U₂)) = ⊥ ↔ J ≤ U₁ := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact w16f_subgroupOf_le_subgroupOf hJ

private theorem w16f_map_mk_eq_top_iff {J : Subgroup W} (hle : U₁ ≤ U₂) (hJ : J ≤ U₂) :
    (J.subgroupOf U₂).map (QuotientGroup.mk' (U₁.subgroupOf U₂)) = ⊤ ↔ U₂ ≤ J ⊔ U₁ := by
  rw [← QuotientGroup.range_mk', Subgroup.map_eq_range_iff, codisjoint_iff, QuotientGroup.ker_mk',
    ← Subgroup.subgroupOf_sup hJ hle, Subgroup.subgroupOf_eq_top]

private theorem w16f_stableUnder_top (X : Subgroup (MulAut W)) : StableUnder X ⊤ :=
  fun _ _ _ _ => Subgroup.mem_top _

private theorem w16f_stableUnder_bot (X : Subgroup (MulAut W)) : StableUnder X ⊥ :=
  fun _ _ u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]

private theorem w16f_stableUnder_secLift_iff (hX : X ≤ secStabAll U₂ U₁)
    (J : Subgroup (SecT U₂ U₁)) :
    StableUnder X (w16f_secLift U₂ U₁ J) ↔ StableUnder (secImg X U₂ U₁) J := by
  constructor
  · intro h φ hφ v hv
    obtain ⟨g, hg, rfl⟩ := mem_secImg.mp hφ
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    have hw : (u : W) ∈ w16f_secLift U₂ U₁ J :=
      w16f_mem_secLift.mpr ⟨u, hv, rfl⟩
    obtain ⟨u', hu'J, hu'eq⟩ := w16f_mem_secLift.mp (h (g : MulAut W) hg (u : W) hw)
    rw [secAut_mk]
    have hres : resAut U₂ ⟨(g : MulAut W), g.2.1⟩ u = u' := by
      ext
      simpa [resAut] using hu'eq.symm
    rw [hres]
    exact hu'J
  · intro h x hx w hw
    obtain ⟨u, huJ, rfl⟩ := w16f_mem_secLift.mp hw
    refine w16f_mem_secLift.mpr
      ⟨⟨x (u : W), (mem_stabSub.mp (hX hx).1 (u : W)).2 u.2⟩, ?_, rfl⟩
    have hmem : secAut U₂ U₁ ⟨x, hX hx⟩ (QuotientGroup.mk u) ∈ J :=
      h (secAut U₂ U₁ ⟨x, hX hx⟩) (mem_secImg.mpr ⟨⟨x, hX hx⟩, hx, rfl⟩)
        (QuotientGroup.mk u) huJ
    rw [secAut_mk] at hmem
    exact hmem

theorem secImg_sup (hX : X ≤ secStabAll U₂ U₁) (hY : Y ≤ secStabAll U₂ U₁) :
    secImg (X ⊔ Y) U₂ U₁ = secImg X U₂ U₁ ⊔ secImg Y U₂ U₁ := by
  unfold secImg
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem secImg_commutator (hX : X ≤ secStabAll U₂ U₁) (hY : Y ≤ secStabAll U₂ U₁) :
    ⁅secImg X U₂ U₁, secImg Y U₂ U₁⁆ = secImg ⁅X, Y⁆ U₂ U₁ := by
  unfold secImg
  rw [w16f_commutator_subgroupOf hX hY]
  exact (Subgroup.map_commutator (X.subgroupOf (secStabAll U₂ U₁))
    (Y.subgroupOf (secStabAll U₂ U₁)) (secAut U₂ U₁)).symm

private theorem w16f_map_conj_subgroupOf {G : Type*} [Group G] {S X : Subgroup G} {t : G}
    (ht : t ∈ S) (hX : X ≤ S) :
    (X.map (MulAut.conj t).toMonoidHom).subgroupOf S =
      (X.subgroupOf S).map (MulAut.conj ⟨t, ht⟩).toMonoidHom := by
  ext g
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxg⟩
    refine ⟨⟨x, hX hx⟩, hx, ?_⟩
    ext
    simpa [MulAut.conj_apply] using hxg
  · rintro ⟨y, hy, hyg⟩
    refine ⟨(y : G), hy, ?_⟩
    have h := congrArg (Subtype.val) hyg
    simpa [MulAut.conj_apply] using h

theorem secImg_map_conj (hX : X ≤ secStabAll U₂ U₁) {t : MulAut W} (ht : t ∈ secStabAll U₂ U₁) :
    secImg (X.map (MulAut.conj t).toMonoidHom) U₂ U₁ =
      (secImg X U₂ U₁).map (MulAut.conj (secAut U₂ U₁ ⟨t, ht⟩)).toMonoidHom := by
  unfold secImg
  rw [w16f_map_conj_subgroupOf ht hX]
  rw [Subgroup.map_map (g := secAut U₂ U₁) (f := (MulAut.conj ⟨t, ht⟩).toMonoidHom)]
  rw [Subgroup.map_map (g := (MulAut.conj (secAut U₂ U₁ ⟨t, ht⟩)).toMonoidHom)
    (f := secAut U₂ U₁)]
  have hcomp : (secAut U₂ U₁).comp (MulAut.conj ⟨t, ht⟩).toMonoidHom =
      (MulAut.conj (secAut U₂ U₁ ⟨t, ht⟩)).toMonoidHom.comp (secAut U₂ U₁) := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply]
    change secAut U₂ U₁ (MulAut.conj ⟨t, ht⟩ x) =
      MulAut.conj (secAut U₂ U₁ ⟨t, ht⟩) (secAut U₂ U₁ x)
    simp only [MulAut.conj_apply, map_mul, map_inv]
  rw [hcomp]

private theorem w16f_secAut_eq_one_iff (g : ↥(secStabAll U₂ U₁)) :
    secAut U₂ U₁ g = 1 ↔ ∀ u : ↥U₂, (g : MulAut W) u * (u : W)⁻¹ ∈ U₁ := by
  constructor
  · intro h u
    have h1 : secAut U₂ U₁ g (QuotientGroup.mk u) = QuotientGroup.mk u := by rw [h]; rfl
    rw [secAut_mk] at h1
    have h2 := (QuotientGroup.eq_iff_div_mem).mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa [resAut, div_eq_mul_inv] using h2
  · intro h
    refine MulEquiv.ext fun v => ?_
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    rw [MulAut.one_apply, secAut_mk]
    exact (QuotientGroup.eq_iff_div_mem).mpr
      (Subgroup.mem_subgroupOf.mpr (by simpa [resAut, div_eq_mul_inv] using h u))

theorem secImg_eq_bot_iff (hX : X ≤ secStabAll U₂ U₁) :
    secImg X U₂ U₁ = ⊥ ↔ commSub U₂ X ≤ U₁ := by
  rw [secImg, Subgroup.map_eq_bot_iff, commSub, Subgroup.closure_le]
  constructor
  · rintro h _ ⟨x, hx, w, hw, rfl⟩
    have hker : secAut U₂ U₁ ⟨x, hX hx⟩ = 1 :=
      MonoidHom.mem_ker.mp (h (Subgroup.mem_subgroupOf.mpr hx))
    exact (w16f_secAut_eq_one_iff ⟨x, hX hx⟩).mp hker ⟨w, hw⟩
  · intro h g hg
    rw [MonoidHom.mem_ker, w16f_secAut_eq_one_iff]
    intro u
    have hmem : (g : MulAut W) (u : W) * (u : W)⁻¹ ∈
        {c | ∃ x ∈ X, ∃ w ∈ U₂, x w * w⁻¹ = c} :=
      ⟨(g : MulAut W), Subgroup.mem_subgroupOf.mp hg, (u : W), u.2, rfl⟩
    exact h hmem

private theorem w16f_secT_bot_lt_top_iff (hle : U₁ ≤ U₂) :
    (⊥ : Subgroup (SecT U₂ U₁)) < ⊤ ↔ U₁ < U₂ := by
  constructor
  · intro hlt
    refine lt_of_le_of_ne hle (fun heq => (bot_lt_iff_ne_bot.mp hlt) ?_)
    rw [Subgroup.eq_bot_iff_forall]
    intro v _
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, heq]
    exact u.2
  · intro hlt
    refine bot_lt_iff_ne_bot.mpr fun hbot => hlt.2 ?_
    intro w hw
    have hv : (QuotientGroup.mk (⟨w, hw⟩ : ↥U₂) : SecT U₂ U₁) = 1 := by
      have : (QuotientGroup.mk (⟨w, hw⟩ : ↥U₂) : SecT U₂ U₁) ∈
          (⊥ : Subgroup (SecT U₂ U₁)) := by
        rw [← hbot]; exact Subgroup.mem_top _
      simpa using this
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hv
    exact hv

theorem isIrrOn_secImg_iff (hle : U₁ ≤ U₂) (hX : X ≤ secStabAll U₂ U₁) :
    IsIrrOn (secImg X U₂ U₁) ⊤ ⊥ ↔ IsIrrOn X U₂ U₁ := by
  constructor
  · intro h
    rw [IsIrrOn] at h
    obtain ⟨hlt, -, -, hmax⟩ := h
    rw [IsIrrOn]
    refine ⟨(w16f_secT_bot_lt_top_iff hle).mp hlt, ?_, ?_, ?_⟩
    · exact fun x hx u hu => (mem_stabSub.mp (hX hx).1 u).2 hu
    · exact fun x hx u hu => (mem_stabSub.mp (hX hx).2 u).2 hu
    · intro J hJstab hU₁J hJU₂
      let J' := (J.subgroupOf U₂).map (QuotientGroup.mk' (U₁.subgroupOf U₂))
      have hstab' : StableUnder (secImg X U₂ U₁) J' := by
        refine (w16f_stableUnder_secLift_iff hX J').mp ?_
        rw [w16f_secLift_map_eq_self hle hJU₂ hU₁J]
        exact hJstab
      rcases hmax J' hstab' bot_le le_top with hJ' | hJ'
      · left
        exact le_antisymm ((w16f_map_mk_eq_bot_iff hJU₂).mp hJ') hU₁J
      · right
        exact le_antisymm hJU₂
          (le_trans ((w16f_map_mk_eq_top_iff hle hJU₂).mp hJ') (sup_le le_rfl hU₁J))
  · intro h
    rw [IsIrrOn] at h
    obtain ⟨hlt, -, -, hmax⟩ := h
    rw [IsIrrOn]
    refine ⟨(w16f_secT_bot_lt_top_iff hle).mpr hlt, w16f_stableUnder_top _,
      w16f_stableUnder_bot _, ?_⟩
    intro J hJstab _ _
    have hstab : StableUnder X (w16f_secLift U₂ U₁ J) :=
      (w16f_stableUnder_secLift_iff hX J).mpr hJstab
    have hU₁L : U₁ ≤ w16f_secLift U₂ U₁ J := by
      intro u hu
      refine w16f_mem_secLift.mpr ⟨⟨u, hle hu⟩, ?_, rfl⟩
      have h1 : QuotientGroup.mk' (U₁.subgroupOf U₂) (⟨u, hle hu⟩ : ↥U₂) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hu
      rw [h1]
      exact J.one_mem
    have hLU₂ : w16f_secLift U₂ U₁ J ≤ U₂ := by
      intro w hw
      obtain ⟨u, -, rfl⟩ := w16f_mem_secLift.mp hw
      exact u.2
    rcases hmax (w16f_secLift U₂ U₁ J) hstab hU₁L hLU₂ with hL | hL
    · left
      have hrec := w16f_recover (U₂ := U₂) (U₁ := U₁) J
      rw [hL] at hrec
      rw [← hrec, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    · right
      have hrec := w16f_recover (U₂ := U₂) (U₁ := U₁) J
      rw [hL] at hrec
      rw [← hrec, Subgroup.subgroupOf_self, Subgroup.map_top, QuotientGroup.range_mk']

end CFSG.LocalAnalysis.WeakClosure81
