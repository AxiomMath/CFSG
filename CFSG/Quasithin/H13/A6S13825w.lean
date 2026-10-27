module

public import CFSG.Quasithin.H13.A6S13825v
public import CFSG.Quasithin.H13.A6S13834
public import CFSG.Quasithin.Background.B69Red

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

namespace A6Mod

variable {G : Type} [Group G] {U C Y : Subgroup G} [IsMulCommutative ↥U]

theorem secMk_mem_fixV_iff (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hYC : Y ≤ Subgroup.normalizer ((U ⊓ C : Subgroup G) : Set G)) {F : Subgroup G}
    (hFY : F ≤ Y) (u : ↥U) :
    InternalSec.secMk (C.subgroupOf U) u ∈ fixV (autSec (autOn F U) ⊤ (C.subgroupOf U)) ↔
      ∀ f ∈ F, f * (u : G) * f⁻¹ * (u : G)⁻¹ ∈ C := by
  constructor
  · intro h f hf
    have h1 := h _ ((mem_autSec_iff hYU hYC hFY).2 ⟨⟨f, hFY hf⟩, hf, rfl⟩)
    rw [secAct_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul, secMk_eq_one_iff] at h1
    have e : ((Setup.rho U Y hYU ⟨f, hFY hf⟩ u * u⁻¹ : ↥U) : G) =
        f * (u : G) * f⁻¹ * (u : G)⁻¹ := by
      rw [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv]
    rw [← e]
    exact h1
  · intro h ψ hψ
    obtain ⟨f, hf, rfl⟩ := (mem_autSec_iff hYU hYC hFY).1 hψ
    rw [secAct_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul, secMk_eq_one_iff]
    rw [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv]
    exact h f hf

variable [Finite G]

theorem index_fixV_le (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hYC : Y ≤ Subgroup.normalizer ((U ⊓ C : Subgroup G) : Set G)) {F : Subgroup G}
    (hFY : F ≤ Y) :
    (fixV (autSec (autOn F U) ⊤ (C.subgroupOf U))).index ≤
      (centralizerMod C U F).relIndex U := by
  set D : Subgroup ↥U := (centralizerMod C U F).subgroupOf U with hD
  have hle : D.map (InternalSec.secMk (C.subgroupOf U)) ≤
      fixV (autSec (autOn F U) ⊤ (C.subgroupOf U)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [secMk_mem_fixV_iff hYU hYC hFY]
    intro f hf
    have h1 := (Subgroup.mem_subgroupOf.mp hu).2.2 f hf
    have e : f * (u : G) * f⁻¹ * (u : G)⁻¹ = ((u : G) * f * (u : G)⁻¹ * f⁻¹)⁻¹ := by group
    rw [e]
    exact C.inv_mem h1
  have h1 : (fixV (autSec (autOn F U) ⊤ (C.subgroupOf U))).index ∣
      (D.map (InternalSec.secMk (C.subgroupOf U))).index := Subgroup.index_dvd_of_le hle
  have h2 : (D.map (InternalSec.secMk (C.subgroupOf U))).index ∣ D.index :=
    Subgroup.index_map_dvd D (InternalSec.secMk_surjective _)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero D.index_ne_zero_of_finite) (h1.trans h2)

theorem mem_Qset_autSec (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hYC : Y ≤ Subgroup.normalizer ((U ⊓ C : Subgroup G) : Set G)) {B K : Subgroup G}
    (hBY : B ≤ Y) (hBel : IsElemAbelian 2 B)
    (hK : ∀ b ∈ B, b ∈ K ↔ ∀ u ∈ U, b * u * b⁻¹ * u⁻¹ ∈ C) (hnt : ¬ B ≤ K)
    (hquad : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ u ∈ U,
      b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ ∈ C)
    (hr : (centralizerMod C U B).relIndex U ≤ ((B ⊓ K).relIndex B) ^ 2) :
    autSec (autOn B U) ⊤ (C.subgroupOf U) ∈ Qset (autSec (autOn Y U) ⊤ (C.subgroupOf U)) := by
  set A := autSec (autOn B U) ⊤ (C.subgroupOf U) with hA
  have hW2 : ∀ w : Sec (⊤ : Subgroup ↥U) (C.subgroupOf U), w ^ 2 = 1 :=
    L13825.sec_sq_eq_one hU2
  have hmemA : ∀ b : ↥Y, (b : G) ∈ B → secAct hYU hYC b ∈ A := fun b hb =>
    (mem_autSec_iff hYU hYC hBY).2 ⟨b, hb, rfl⟩
  have hAY : A ≤ autSec (autOn Y U) ⊤ (C.subgroupOf U) := by
    intro ψ hψ
    obtain ⟨b, -, rfl⟩ := (mem_autSec_iff hYU hYC hBY).1 hψ
    exact (mem_autSec_iff hYU hYC le_rfl).2 ⟨b, b.2, rfl⟩
  have hA2 : IsA2 (autSec (autOn Y U) ⊤ (C.subgroupOf U)) A := by
    refine ⟨hAY, ?_, ?_, ?_⟩
    ·
      obtain ⟨b, hb, hbK⟩ : ∃ b ∈ B, b ∉ K := by
        by_contra hcon
        push Not at hcon
        exact hnt hcon
      intro hbot
      apply hbK
      rw [hK b hb, ← secAct_eq_one_iff hYU hYC ⟨b, hBY hb⟩]
      have := hmemA ⟨b, hBY hb⟩ hb
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    · intro ψ hψ χ hχ
      obtain ⟨b₁, hb₁, rfl⟩ := (mem_autSec_iff hYU hYC hBY).1 hψ
      obtain ⟨b₂, hb₂, rfl⟩ := (mem_autSec_iff hYU hYC hBY).1 hχ
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (F7.isElemAbelian_comm hBel hb₁ hb₂)
    · intro ψ hψ
      obtain ⟨b, hb, rfl⟩ := (mem_autSec_iff hYU hYC hBY).1 hψ
      rw [← map_pow]
      have : b ^ 2 = 1 := Subtype.ext (by simpa using hBel.2 b hb)
      rw [this, map_one]
  refine ⟨⟨hA2, ?_⟩, ?_⟩
  ·
    rw [rAV_le_two_iff hW2 hA2]
    have hcA : Nat.card A = (B ⊓ K).relIndex B := card_autSec_eq hYU hYC hBY hK
    have h1 := Subgroup.index_mul_card (fixV A)
    have h2 := index_fixV_le hYU hYC hBY (C := C)
    rw [hcA]
    calc Nat.card (Sec (⊤ : Subgroup ↥U) (C.subgroupOf U))
        = (fixV A).index * Nat.card (fixV A) := h1.symm
      _ ≤ ((B ⊓ K).relIndex B) ^ 2 * Nat.card (fixV A) :=
          Nat.mul_le_mul_right _ (h2.trans hr)
  ·
    rw [← isQuadratic_iff_commSeries_two]
    show commV A ≤ fixV A
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨ψ, hψ, w, rfl⟩ χ hχ
    obtain ⟨b₁, hb₁, rfl⟩ := (mem_autSec_iff hYU hYC hBY).1 hψ
    obtain ⟨b₂, hb₂, rfl⟩ := (mem_autSec_iff hYU hYC hBY).1 hχ
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (C.subgroupOf U) w
    rw [secAct_secMk, ← map_inv, ← map_mul, secAct_secMk, ← mul_inv_eq_one, ← map_inv,
      ← map_mul, secMk_eq_one_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
    exact hquad _ hb₁ _ hb₂ _ u.2

end A6Mod

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem mem_Qset_sec (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    (hle : mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    {W : Subgroup G} (hV₁W : fsuV1 T V ≤ W) (hWU : W ≤ conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hfaith : ∀ h ∈ H, (∀ u ∈ conjClosure S.V3 H, h * u * h⁻¹ * u⁻¹ ∈ W) → h ∈ pCoreOf 2 H) :
    autSec (autOn (F8.Uγ S.V3 H (g : G)) (conjClosure S.V3 H)) ⊤
        (W.subgroupOf (conjClosure S.V3 H)) ∈
      Qset (autSec (autOn H (conjClosure S.V3 H)) ⊤ (W.subgroupOf (conjClosure S.V3 H))) := by
  have hF98 := hS.hF H hH
  have hF := hF98.toHypF91
  obtain ⟨hBH, hBel, hnt, hquad, hr⟩ := (hF98.F916_2_aux s hpos hle).1
  set U := conjClosure S.V3 H with hU
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure S.V3 H
  have hHUW : H ≤ Subgroup.normalizer ((U ⊓ W : Subgroup G) : Set G) := fun _ hh =>
    F7.mem_normalizer_inf (hHU hh) (hHW hh)
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := (L13825.isElemAbelian_UH hS hH).2
  have hK : ∀ b ∈ F8.Uγ S.V3 H (g : G), b ∈ pCoreOf 2 H ↔
      ∀ u ∈ U, b * u * b⁻¹ * u⁻¹ ∈ W := by
    intro b hb
    constructor
    · intro hbQ u hu
      rw [hF.pCoreOf_eq_centralizerMod] at hbQ
      exact hV₁W (hbQ.2.2 u hu)
    · exact hfaith b (hBH hb)
  refine A6Mod.mem_Qset_autSec hU2 hHU hHUW hBH hBel hK hnt
    (fun b₁ hb₁ b₂ hb₂ u hu => hV₁W (hquad b₁ hb₁ b₂ hb₂ u hu)) ?_
  refine le_trans ?_ hr
  refine Subgroup.relIndex_le_of_le_left ?_ Subgroup.index_ne_zero_of_finite
  intro u hu
  refine ⟨hu.1, ?_, fun b hb => hV₁W (hu.2.2 b hb)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro w
  have hcomm : ∀ x ∈ U, u * x = x * u := fun x hx =>
    congrArg Subtype.val ((L13825.isElemAbelian_UH hS hH).1.is_comm.comm ⟨u, hu.1⟩ ⟨x, hx⟩)
  constructor
  · intro hw
    rw [hcomm w (hWU hw), mul_inv_cancel_right]
    exact hw
  · intro hw
    have h3 : u * w * u⁻¹ = w :=
      mul_left_cancel ((hcomm _ (hWU hw)).trans (by group))
    rw [← h3]
    exact hw

theorem case2_data (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hnt : ∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V)) :
    ∃ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g ∧
      F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G) ∧
      F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H ∧
      0 < mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) ∧
      mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
        mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) ∧
      ∃ c ∈ H, conjSub c (F8.Uγ V H (g : G)) ≤ pCoreOf 2 (S.L1 ⊔ T) := by
  have hF := hS.hF H hH
  obtain ⟨γ, γ', g, s⟩ := hF.exists_F8Setup
  obtain ⟨δ, δ', k, sk, hpos, hle, -, c, hcH, hcV⟩ :=
    exists_case13_8_8_two hF s (S.Dγ_lt_of_no_transv hF hnt s)
  refine ⟨δ, δ', k, sk, S.Dγ_lt_of_no_transv hF hnt sk, ?_, hpos, hle, c, hcH, hcV⟩
  refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hDH => ?_
  have hlt := S.Dγ_lt_of_no_transv hF hnt sk
  obtain ⟨ε, ε', m, y, sm, -, -, hUm, -, -, hDγm⟩ :=
    hF.exists_symmetric_setup sk (hF.not_Vγ_le_ballStab_of_lt sk hlt)
  have := S.Dγ_lt_of_no_transv hF hnt sm
  rw [hDγm, hDH, hUm] at this
  exact lt_irrefl _ this

theorem sqtkGroup_autSec (hA21 : AsA21SQTKSection) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {C : Subgroup G}
    (hHC : H ≤ Subgroup.normalizer ((conjClosure S.V3 H ⊓ C : Subgroup G) : Set G))
    {X : Subgroup G} (hXH : X ≤ H)
    (hq : CFSG.IsQuasisimple ↥(autSec (autOn X (conjClosure S.V3 H)) ⊤
      (C.subgroupOf (conjClosure S.V3 H)))) :
    SQTKGroup ↥(autSec (autOn X (conjClosure S.V3 H)) ⊤ (C.subgroupOf (conjClosure S.V3 H))) := by
  have : IsSimpleGroup G := S.h13.simple
  have hsq : SQTKGroup ↥H := G64.sqtkGroup_of_isSQTKCat
    ((QuasithinUnique.qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1 H hH.1.2)
  have hHU := le_normalizer_conjClosure S.V3 H
  let π : ↥(X.subgroupOf H) →* ↥(autSec (autOn X (conjClosure S.V3 H)) ⊤
      (C.subgroupOf (conjClosure S.V3 H))) :=
    ((A6Mod.secAct hHU hHC).comp (X.subgroupOf H).subtype).codRestrict _
      (fun x => (A6Mod.mem_autSec_iff hHU hHC hXH).2 ⟨x, x.2, rfl⟩)
  refine B69.sqtk_of_surj hA21 hsq π ?_ hq
  rintro ⟨ψ, hψ⟩
  obtain ⟨f, hf, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hXH).1 hψ
  exact ⟨⟨f, hf⟩, rfl⟩

end Setting4

end CFSG.Quasithin.H13.A6
