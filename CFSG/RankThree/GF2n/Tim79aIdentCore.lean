module

public import CFSG.RankThree.GF2n.Tim79aUbar
public import CFSG.RankThree.GF2n.Tim79aLift
public import CFSG.RankThree.GF2n.Tim79aSec23Inv
public import CFSG.RankThree.GF2n.Tim79aSec23Statements

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] noncomputable def xToXbar {V H : Subgroup G} (hVH : V ≤ H) :
    ↥(xOf V H) →* Xbar V H :=
  ((piBar V H).comp (Subgroup.inclusion (xOf_le_H hVH))).codRestrict (barOf V H (xOf V H))
    (fun x => mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) x, x.2, rfl⟩)

@[expose] noncomputable def xToZ {V H : Subgroup G} (hVH : V ≤ H) :
    ↥(xOf V H) →* XbarZ V H :=
  (projZ V H).comp (xToXbar hVH)

theorem coe_xToXbar {V H : Subgroup G} (hVH : V ≤ H) (x : ↥(xOf V H)) :
    ((xToXbar hVH x : Xbar V H) : Hbar V H) =
      piBar V H (Subgroup.inclusion (xOf_le_H hVH) x) := rfl

theorem xToZ_apply {V H : Subgroup G} (hVH : V ≤ H) (x : ↥(xOf V H)) :
    xToZ hVH x = projZ V H (xToXbar hVH x) := rfl

theorem xToXbar_surjective {V H : Subgroup G} (hVH : V ≤ H) :
    Function.Surjective (xToXbar hVH) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := mem_barOf_iff.mp y.2
  exact ⟨⟨x.1, hx⟩, Subtype.ext hxy⟩

theorem xToZ_surjective {V H : Subgroup G} (hVH : V ≤ H) :
    Function.Surjective (xToZ hVH) :=
  (QuotientGroup.mk'_surjective _).comp (xToXbar_surjective hVH)

@[expose] def imgZ (V H S : Subgroup G) : Subgroup (XbarZ V H) :=
  ((barOf V H S).subgroupOf (barOf V H (xOf V H))).map (projZ V H)

theorem VZ_eq_imgZ (V H : Subgroup G) : VZ V H = imgZ V H V := rfl

theorem imgZ_conj {V H : Subgroup G} (hVH : V ≤ H) (x : ↥(xOf V H)) :
    imgZ V H (conjSubgroup (x : G) V) = conjSubgroup (xToZ hVH x) (VZ V H) := by
  unfold imgZ VZ
  have h1 := conjSubgroup_piBar_barOf (V := V) (H := H) (Subgroup.inclusion (xOf_le_H hVH) x) V
  have h2 : conjSubgroup ((xToXbar hVH x : Xbar V H) : Hbar V H) (barOf V H V) =
      barOf V H (conjSubgroup (x : G) V) := h1
  rw [← h2, subgroupOf_conjSubgroup (barOf V H (xOf V H)) (barOf V H V) (xToXbar hVH x)]
  exact (conjSubgroup_map_hom (projZ V H) (Vy V H) (xToXbar hVH x)).symm

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem commute_conj_of_commute_tilde (hc : MinCex M V Q P H) {x₁ x₂ : ↥(xOf V H)}
    (hcomm : ∀ a ∈ conjSubgroup (xToZ hc.V_le_H x₁) (VZ V H),
      ∀ b ∈ conjSubgroup (xToZ hc.V_le_H x₂) (VZ V H), a * b = b * a) :
    ∀ y ∈ conjSubgroup (x₁ : G) V, ∀ u ∈ conjSubgroup (x₂ : G) V, y * u = u * y := by
  have hVH : V ≤ H := hc.V_le_H
  set ρ := xToZ hVH with hρ
  set k : ↥(xOf V H) := x₁⁻¹ * x₂ with hk
  have hkH : (k : G) ∈ H := xOf_le_H hVH k.2
  have hA : ∀ a ∈ VZ V H, ∀ b ∈ conjSubgroup (ρ k) (VZ V H), a * b = b * a := by
    intro a ha b hb
    have ha' : ρ x₁ * a * (ρ x₁)⁻¹ ∈ conjSubgroup (ρ x₁) (VZ V H) := by
      rw [mem_conjSubgroup, show (ρ x₁)⁻¹ * (ρ x₁ * a * (ρ x₁)⁻¹) * ρ x₁ = a by group]
      exact ha
    have hb' : ρ x₁ * b * (ρ x₁)⁻¹ ∈ conjSubgroup (ρ x₂) (VZ V H) := by
      rw [mem_conjSubgroup]
      have h1 := mem_conjSubgroup.mp hb
      have e : (ρ x₂)⁻¹ * (ρ x₁ * b * (ρ x₁)⁻¹) * ρ x₂ = (ρ k)⁻¹ * b * ρ k := by
        simp only [hk, map_mul, map_inv]
        group
      rwa [e]
    have h2 := hcomm _ ha' _ hb'
    calc a * b = (ρ x₁)⁻¹ * ((ρ x₁ * a * (ρ x₁)⁻¹) * (ρ x₁ * b * (ρ x₁)⁻¹)) * ρ x₁ := by group
      _ = (ρ x₁)⁻¹ * ((ρ x₁ * b * (ρ x₁)⁻¹) * (ρ x₁ * a * (ρ x₁)⁻¹)) * ρ x₁ := by rw [h2]
      _ = b * a := by group
  have hP2 : IsPGroup 2 ↥(Vtilde V H ⊔ conjSubgroup (ρ k) (Vtilde V H)) := by
    have hV2 : IsPGroup 2 ↥(Vtilde V H) := hc.isElemAbelian_Vtilde.isPGroup
    have hU2 : IsPGroup 2 ↥(conjSubgroup (ρ k) (Vtilde V H)) :=
      hV2.of_equiv ((Vtilde V H).equivMapOfInjective (MulAut.conj (ρ k)).toMonoidHom
        (MulAut.conj (ρ k)).injective)
    refine IsPGroup.to_sup_of_normal_right' hV2 hU2 (fun a ha => ?_)
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hA a ha b hb).symm
  have hP2' := (hc.isPGroup_barOf_sup_iff_tilde hkH (y := xToXbar hVH k) rfl).mpr hP2
  have hcomm2 := hc.commute_of_isPGroup_barOf_sup hkH hP2'
  intro y hy u hu
  have hy0 : (x₁ : G)⁻¹ * y * x₁ ∈ V := mem_conjSubgroup.mp hy
  have hu0 : (x₁ : G)⁻¹ * u * x₁ ∈ conjSubgroup (k : G) V := by
    rw [mem_conjSubgroup]
    have h1 := mem_conjSubgroup.mp hu
    have e : (k : G)⁻¹ * ((x₁ : G)⁻¹ * u * x₁) * k = (x₂ : G)⁻¹ * u * x₂ := by
      simp only [hk, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [e]
  have h3 := hcomm2 _ hy0 _ hu0
  calc y * u = (x₁ : G) * (((x₁ : G)⁻¹ * y * x₁) * ((x₁ : G)⁻¹ * u * x₁)) * (x₁ : G)⁻¹ := by group
    _ = (x₁ : G) * (((x₁ : G)⁻¹ * u * x₁) * ((x₁ : G)⁻¹ * y * x₁)) * (x₁ : G)⁻¹ := by rw [h3]
    _ = u * y := by group


theorem false_of_ubar_gen (hc : MinCex M V Q P H) {h : G} (hh : h ∈ H)
    (hne : conjSubgroup h V ≠ V) (T : Set G)
    (hV : ∀ g ∈ T, ∀ y ∈ conjSubgroup g V, ∀ u ∈ V, y * u = u * y)
    (hVh : ∀ g ∈ T, ∀ y ∈ conjSubgroup g V, ∀ u ∈ conjSubgroup h V, y * u = u * y)
    {r : G} (hr : r ∈ xOf V H) {a : G} (ha : a ∈ conjSubgroup r V)
    (hgen : xOf V H ≤ ((⨆ g ∈ T, conjSubgroup g V) ⊔ wOf V H) ⊔ Subgroup.zpowers a) :
    False := by
  set F : Subgroup G := (V ⊓ wOf V H) ⊔ (conjSubgroup h V ⊓ wOf V H) with hF
  have hFW : F ≤ wOf V H := sup_le inf_le_right inf_le_right
  set U : Subgroup G := (⨆ g ∈ T, conjSubgroup g V) ⊔ wOf V H with hU
  have hUle : U ≤ Subgroup.centralizer (F : Set G) := by
    refine sup_le (iSup₂_le fun g hg => ?_) ?_
    · rw [Subgroup.le_centralizer_iff]
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_iff.mpr fun y hy => hV g hg y hy x hx.1
      · exact Subgroup.mem_centralizer_iff.mpr fun y hy => hVh g hg y hy x hx.1
    · intro y hy
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => hc.wOf_isElemAbelian.comm (hFW hx) hy
  have hFU : ∀ x ∈ F, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hUle hy) x hx
  have hEq : V ⊓ wOf V H = F := hc.eq_inf_wOf_of_centralizes hFW hFU le_sup_left hr ha hgen
  have hBF : conjSubgroup h V ⊓ wOf V H ≤ V ⊓ wOf V H := hEq ▸ le_sup_right
  apply hc.conj_inf_wOf_ne_bot hh
  rw [eq_bot_iff]
  intro x hx
  have hxV : x ∈ V ⊓ conjSubgroup h V := ⟨(hBF hx).1, hx.1⟩
  rw [inf_conjSubgroup_eq_bot_of_isTI hc.ti hne] at hxV
  exact hxV

theorem exists_lift_conj (hc : MinCex M V Q P H) (hd : Sec23Data V H) {w a₀ : XbarZ V H}
    (hw : a₀ ∈ conjSubgroup w (VZ V H)) (ha₀ : a₀ ≠ 1) :
    ∃ (r : ↥(xOf V H)) (a : ↥H), xToZ hc.V_le_H r = w ∧ (a : G) ∈ conjSubgroup (r : G) V ∧
      ∃ y : Xbar V H, y ∈ Dy V H ∧ (y : Hbar V H) = piBar V H a ∧ projZ V H y = a₀ := by
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨r, hrρ⟩ := xToZ_surjective hVH w
  have ha₀mem : a₀ ∈ imgZ V H (conjSubgroup (r : G) V) := by
    rw [imgZ_conj hVH r, hrρ]
    exact hw
  obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp ha₀mem
  obtain ⟨x, hxV, hxy⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hy)
  have hy1 : (y : Hbar V H) ≠ 1 := by
    intro h1
    apply ha₀
    rw [← hya]
    have : y = 1 := Subtype.ext h1
    rw [this, map_one]
  have hyD : y ∈ Dy V H := by
    have hr' : (r : G)⁻¹ * (x : G) * r ∈ V := mem_conjSubgroup.mp hxV
    have hrH : (r : G) ∈ H := xOf_le_H hVH r.2
    set rH : ↥H := ⟨(r : G), hrH⟩ with hrH'
    set v : ↥H := rH⁻¹ * x * rH with hv
    have hvV : (v : G) ∈ V := by simpa [hv, hrH'] using hr'
    have hvbar : piBar V H v ∈ barOf V H V := mem_barOf_iff.mpr ⟨v, hvV, rfl⟩
    have hyeq : (y : Hbar V H) = piBar V H rH * piBar V H v * (piBar V H rH)⁻¹ := by
      rw [← hxy, hv]
      simp only [map_mul, map_inv]
      group
    have hv1 : piBar V H v ≠ 1 := by
      intro h1
      apply hy1
      rw [hyeq, h1]
      group
    have hmem := hc.conj_mem_dbarOf (y := piBar V H rH) (hc.barOf_V_subset_dbarOf hvbar hv1)
    show (y : Hbar V H) ∈ dbarOf V H
    rw [hyeq]
    exact hmem
  exact ⟨r, x, hrρ, hxV, y, hyD, hxy.symm, hya⟩

theorem false_of_cover (hc : MinCex M V Q P H) (hd : Sec23Data V H) (𝒩 : Set (XbarZ V H))
    {nh : XbarZ V H} (hne : conjSubgroup nh (VZ V H) ≠ VZ V H)
    (hV : ∀ n ∈ 𝒩, ∀ a ∈ conjSubgroup n (VZ V H), ∀ b ∈ VZ V H, a * b = b * a)
    (hVh : ∀ n ∈ 𝒩, ∀ a ∈ conjSubgroup n (VZ V H), ∀ b ∈ conjSubgroup nh (VZ V H),
      a * b = b * a)
    {w a₀ : XbarZ V H} (hw : a₀ ∈ conjSubgroup w (VZ V H)) (ha₀ : a₀ ≠ 1)
    (hgen : (⨆ n ∈ 𝒩, conjSubgroup n (VZ V H)) ⊔ Subgroup.zpowers a₀ = ⊤) : False := by
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨h, hhρ⟩ := xToZ_surjective hVH nh
  obtain ⟨r, x, hrρ, hxV, y, hyD, hxy, hya⟩ := hc.exists_lift_conj hd hw ha₀
  have hhH : (h : G) ∈ H := xOf_le_H hVH h.2
  have hne' : conjSubgroup (h : G) V ≠ V := by
    intro heq
    apply hne
    rw [← hhρ, ← imgZ_conj hVH h, heq]
    rfl
  set T : Set G := {g | ∃ x : ↥(xOf V H), (x : G) = g ∧ xToZ hVH x ∈ 𝒩} with hT
  set U : Subgroup G := (⨆ g ∈ T, conjSubgroup g V) ⊔ wOf V H with hU
  have hV' : ∀ g ∈ T, ∀ y ∈ conjSubgroup g V, ∀ u ∈ V, y * u = u * y := by
    rintro g ⟨x₁, rfl, hx₁⟩ y' hy' u hu
    have hc2 := hc.commute_conj_of_commute_tilde (x₁ := x₁) (x₂ := 1) (by
      intro a ha b hb
      rw [map_one, conjSubgroup_one] at hb
      exact hV _ hx₁ a ha b hb)
    exact hc2 y' hy' u (by rwa [show ((1 : ↥(xOf V H)) : G) = 1 from rfl, conjSubgroup_one])
  have hVh' : ∀ g ∈ T, ∀ y ∈ conjSubgroup g V, ∀ u ∈ conjSubgroup (h : G) V, y * u = u * y := by
    rintro g ⟨x₁, rfl, hx₁⟩ y' hy' u hu
    exact hc.commute_conj_of_commute_tilde (x₁ := x₁) (x₂ := h) (by
      intro a ha b hb
      rw [hhρ] at hb
      exact hVh _ hx₁ a ha b hb) y' hy' u hu
  have hU_le : ∀ g ∈ T, conjSubgroup g V ≤ U ⊔ Subgroup.zpowers (x : G) := fun g hg =>
    le_trans (le_iSup₂ (f := fun g (_ : g ∈ T) => conjSubgroup g V) g hg)
      (le_trans le_sup_left le_sup_left)
  set K₀ : Subgroup (Xbar V H) :=
    (barOf V H (U ⊔ Subgroup.zpowers (x : G))).subgroupOf (barOf V H (xOf V H)) with hK₀
  have hyK₀ : y ∈ K₀ := by
    rw [hK₀, Subgroup.mem_subgroupOf]
    exact mem_barOf_iff.mpr ⟨x, Subgroup.mem_sup_right (Subgroup.mem_zpowers (x : G)), hxy.symm⟩
  have hmap : K₀.map (projZ V H) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sup_le (iSup₂_le fun n hn => ?_) (Subgroup.zpowers_le.mpr ⟨y, hyK₀, hya⟩)
    obtain ⟨x₀, hx₀⟩ := xToZ_surjective hVH n
    have hx₀T : (x₀ : G) ∈ T := ⟨x₀, rfl, by rw [hx₀]; exact hn⟩
    rw [← hx₀, ← imgZ_conj hVH x₀]
    refine Subgroup.map_mono (fun z hz => ?_)
    rw [hK₀, Subgroup.mem_subgroupOf]
    exact barOf_mono (hU_le _ hx₀T) (Subgroup.mem_subgroupOf.mp hz)
  have hker : (projZ V H).ker = Subgroup.center (Xbar V H) := QuotientGroup.ker_mk' _
  have hK : K₀ ⊔ Subgroup.center (Xbar V H) = ⊤ := by
    have h1 := Subgroup.comap_map_eq (projZ V H) K₀
    rw [hmap, Subgroup.comap_top, hker] at h1
    exact h1.symm
  have hgen' : xOf V H ≤ U ⊔ Subgroup.zpowers (x : G) :=
    xOf_le_sup_of_sup_center hd hVH le_sup_right hK ⟨y, hyD, hyK₀⟩
  exact hc.false_of_ubar_gen hhH hne' T hV' hVh' r.2 hxV hgen'

end MinCex

end CFSG.RankThree.GF2n.Tim79a
