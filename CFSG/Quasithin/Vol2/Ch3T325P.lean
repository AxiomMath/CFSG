module

public import CFSG.Quasithin.Background.InternalSecIso

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] {L V₀ VM : Subgroup G}

omit [Group G] in
theorem mem_conjugate_iff {G : Type} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    simp [mul_assoc]

theorem fixV_autOn_eq_bot [IsMulCommutative ↥VM] (h : VM ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hLVM : L ≤ Subgroup.normalizer (VM : Set G)) : fixV (autOn L VM) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have hvC : (v : G) ∈ VM ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    have h1 := congrArg Subtype.val (hv _ (Setup.mem_autOn_iff.mpr ⟨⟨g, hLVM hg⟩, hg, rfl⟩))
    rw [coe_conjAct_apply] at h1
    calc g * (v : G) = (g * v * g⁻¹) * g := by group
      _ = v * g := by rw [h1]
  rw [h, Subgroup.mem_bot] at hvC
  exact Subgroup.mem_bot.mpr (Subtype.ext hvC)

theorem mem_normalizer_of_mem_stabSub [IsMulCommutative ↥VM] (hV : V₀ ≤ VM) {g : G}
    (hg : g ∈ Subgroup.normalizer (VM : Set G))
    (h : conjAct VM ⟨g, hg⟩ ∈ stabSub (V₀.subgroupOf VM)) :
    g ∈ Subgroup.normalizer (V₀ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ hx : x ∈ VM, (x ∈ V₀ ↔ g * x * g⁻¹ ∈ V₀) := by
    intro hx
    have h1 := h ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, coe_conjAct_apply] at h1
    exact h1.symm
  constructor
  · intro hx
    exact (key (hV hx)).1 hx
  · intro hx
    have hxVM : x ∈ VM := (Subgroup.mem_normalizer_iff.mp hg x).mpr (hV hx)
    exact (key hxVM).2 hx

theorem map_conjAct_inv_eq {t : G} (ht : t⁻¹ ∈ Subgroup.normalizer (VM : Set G)) :
    (V₀.subgroupOf VM).map (conjAct VM ⟨t⁻¹, ht⟩).toMonoidHom =
      (CFSG.conjugate V₀ t).subgroupOf VM := by
  ext u
  rw [Subgroup.mem_subgroupOf, mem_conjugate_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : (w : G) ∈ V₀ := hw
    show t * ((conjAct VM ⟨t⁻¹, ht⟩ w : ↥VM) : G) * t⁻¹ ∈ V₀
    rw [coe_conjAct_apply]
    simpa [mul_assoc] using hw'
  · intro hu
    have htN : t ∈ Subgroup.normalizer (VM : Set G) := by
      simpa using (Subgroup.normalizer (VM : Set G)).inv_mem ht
    have hw : t * (u : G) * t⁻¹ ∈ VM := (Subgroup.mem_normalizer_iff.mp htN u).mp u.2
    refine ⟨⟨t * u * t⁻¹, hw⟩, hu, Subtype.ext ?_⟩
    show ((conjAct VM ⟨t⁻¹, ht⟩ ⟨t * u * t⁻¹, hw⟩ : ↥VM) : G) = u
    rw [coe_conjAct_apply]
    group

theorem secIsoL_of_isXSectionIso₂ {V A B : Subgroup G} [IsMulCommutative ↥V] (hAV : A ≤ V)
    (hBV : B ≤ V) (hLA : L ≤ Subgroup.normalizer (A : Set G))
    (hLB : L ≤ Subgroup.normalizer (B : Set G)) (h : IsXSectionIso₂ L A ⊥ B ⊥) :
    SecIsoL (autOn L V) (A.subgroupOf V) ⊥ (B.subgroupOf V) ⊥ := by
  obtain ⟨hn₁, hn₂, e, he⟩ := h
  set f : ↥(A.subgroupOf V) ≃* ↥(B.subgroupOf V) :=
    (botQuotEquiv hAV).symm.trans (e.trans (botQuotEquiv hBV)) with hf
  refine secIsoL_of_equiv (autOn_inv_subgroupOf hLA) (autOn_inv_subgroupOf hLB) f ?_
  intro k w
  obtain ⟨g, hgL, hgk⟩ := Setup.mem_autOn_iff.mp k.2
  set a : ↥A := ⟨(w : G), w.2⟩ with ha
  have hwa : (botQuotEquiv hAV).symm w = QuotientGroup.mk a := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (Subtype.ext rfl)
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk a))
  have hfw : ((f w : ↥V) : G) = b := by
    rw [hf, MulEquiv.trans_apply, MulEquiv.trans_apply, hwa, ← hb]
    rfl
  have hj : (g : G) * (a : G) * (g : G)⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp (hLA hgL) _).mp a.2
  have hk : (g : G) * (b : G) * (g : G)⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp (hLB hgL) _).mp b.2
  have h1 := he (g : G) hgL a b hj hk hb.symm
  have hkw : (k : MulAut ↥V) w = ⟨(g : G) * (w : G) * (g : G)⁻¹, hAV hj⟩ := by
    rw [← hgk]
    exact Subtype.ext (coe_conjAct_apply _ _)
  have hwa' : (botQuotEquiv hAV).symm ⟨(k : MulAut ↥V) w,
      autOn_inv_subgroupOf (V := V) hLA (k : MulAut ↥V) k.2 w w.2⟩ =
      QuotientGroup.mk (⟨(g : G) * (a : G) * (g : G)⁻¹, hj⟩ : ↥A) := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    apply Subtype.ext
    show (((k : MulAut ↥V) w : ↥V) : G) = (g : G) * (a : G) * (g : G)⁻¹
    rw [hkw]
  apply Subtype.ext
  have hR : ((((k : MulAut ↥V) ((f w : ↥(B.subgroupOf V)) : ↥V)) : ↥V) : G) =
      (g : G) * (b : G) * (g : G)⁻¹ := by
    rw [← hgk, coe_conjAct_apply, hfw]
  rw [hR, hf, MulEquiv.trans_apply, MulEquiv.trans_apply, hwa', h1]
  rfl

end CFSG.Quasithin.H13.T325
