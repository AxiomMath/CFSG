module

public import CFSG.Quasithin.H13.A6S1372Twelve
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6Mod

variable {G : Type} [Group G] {U C Y : Subgroup G} [IsMulCommutative ↥U]

theorem autOn_le_stab (hYC : Y ≤ Subgroup.normalizer ((U ⊓ C : Subgroup G) : Set G)) :
    autOn Y U ≤ stabSub (⊤ : Subgroup ↥U) ⊓ stabSub (C.subgroupOf U) :=
  le_inf (InternalSec.le_stabSub_top _) (InternalSec.autOn_le_stabSub hYC)

@[expose] noncomputable def secAct (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hYC : Y ≤ Subgroup.normalizer ((U ⊓ C : Subgroup G) : Set G)) :
    ↥Y →* MulAut (Sec (⊤ : Subgroup ↥U) (C.subgroupOf U)) :=
  (secHom ⊤ (C.subgroupOf U)).comp ((Setup.rho U Y hYU).codRestrict _
    (fun y => autOn_le_stab hYC ((Setup.mem_autOn_self_iff hYU).2 ⟨y, rfl⟩)))

theorem secAct_secMk (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hYC : Y ≤ Subgroup.normalizer ((U ⊓ C : Subgroup G) : Set G)) (y : ↥Y) (u : ↥U) :
    secAct hYU hYC y (InternalSec.secMk (C.subgroupOf U) u) =
      InternalSec.secMk (C.subgroupOf U) (Setup.rho U Y hYU y u) := rfl

theorem secAct_eq_one_iff (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hYC : Y ≤ Subgroup.normalizer ((U ⊓ C : Subgroup G) : Set G)) (y : ↥Y) :
    secAct hYU hYC y = 1 ↔ ∀ u ∈ U, (y : G) * u * (y : G)⁻¹ * u⁻¹ ∈ C := by
  unfold secAct
  rw [MonoidHom.comp_apply, secHom_eq_one_iff]
  constructor
  · rintro ⟨-, h⟩ u hu
    have h1 := h ⟨u, hu⟩ trivial
    rw [Subgroup.mem_subgroupOf] at h1
    have e : ((((Setup.rho U Y hYU y : MulAut ↥U) ⟨u, hu⟩ * (⟨u, hu⟩ : ↥U)⁻¹ : ↥U)) : G) =
        (y : G) * u * (y : G)⁻¹ * u⁻¹ := by
      rw [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv]
    rw [← e]
    exact h1
  · intro h
    refine ⟨InternalSec.mem_stabSub_top _, fun w _ => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    show (((Setup.rho U Y hYU y : MulAut ↥U) w * w⁻¹ : ↥U) : G) ∈ C
    rw [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv]
    exact h (w : G) w.2

theorem mem_autSec_iff (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hYC : Y ≤ Subgroup.normalizer ((U ⊓ C : Subgroup G) : Set G)) {F : Subgroup G}
    (hFY : F ≤ Y) {ψ : MulAut (Sec (⊤ : Subgroup ↥U) (C.subgroupOf U))} :
    ψ ∈ autSec (autOn F U) ⊤ (C.subgroupOf U) ↔
      ∃ f : ↥Y, (f : G) ∈ F ∧ secAct hYU hYC f = ψ := by
  rw [mem_autSec_iff_secHom (autOn_le_stab (hFY.trans hYC))]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨n, hnF, hn⟩ := Setup.mem_autOn_iff.1 hg
    refine ⟨⟨n, hFY hnF⟩, hnF, ?_⟩
    unfold secAct
    rw [MonoidHom.comp_apply]
    congr 1
    apply Subtype.ext
    rw [← hn]
    rfl
  · rintro ⟨f, hfF, rfl⟩
    exact ⟨_, (Setup.mem_autOn_iff_rho hYU hFY).2 ⟨f, hfF, rfl⟩, rfl⟩

theorem card_autSec_eq (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hYC : Y ≤ Subgroup.normalizer ((U ⊓ C : Subgroup G) : Set G)) {F K : Subgroup G}
    (hFY : F ≤ Y) (hK : ∀ f ∈ F, f ∈ K ↔ ∀ u ∈ U, f * u * f⁻¹ * u⁻¹ ∈ C) :
    Nat.card (autSec (autOn F U) ⊤ (C.subgroupOf U)) = (F ⊓ K).relIndex F := by
  set φ := (secAct hYU hYC).comp (Subgroup.inclusion hFY) with hφ
  have hrange : φ.range = autSec (autOn F U) ⊤ (C.subgroupOf U) := by
    ext ψ
    rw [mem_autSec_iff hYU hYC hFY, MonoidHom.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨_, f.2, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
  have hker : φ.ker = (F ⊓ K).subgroupOf F := by
    ext f
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ, MonoidHom.comp_apply,
      secAct_eq_one_iff]
    exact ⟨fun h => ⟨f.2, (hK f f.2).2 h⟩, fun h => (hK f f.2).1 h.2⟩
  rw [← hrange, Subgroup.relIndex, ← hker]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm

theorem secMk_eq_one_iff (u : ↥U) : InternalSec.secMk (C.subgroupOf U) u = 1 ↔ (u : G) ∈ C := by
  unfold InternalSec.secMk
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  rfl

theorem secMk_mem_fixV (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hYC : Y ≤ Subgroup.normalizer ((U ⊓ C : Subgroup G) : Set G)) {F : Subgroup G}
    (hFY : F ≤ Y) {u : ↥U} (hu : ∀ f ∈ F, f * (u : G) = (u : G) * f) :
    InternalSec.secMk (C.subgroupOf U) u ∈ fixV (autSec (autOn F U) ⊤ (C.subgroupOf U)) := by
  intro ψ hψ
  obtain ⟨f, hfF, rfl⟩ := (mem_autSec_iff hYU hYC hFY).1 hψ
  rw [secAct_secMk]
  congr 1
  apply Subtype.ext
  rw [Setup.rho_apply_coe, hu f hfF, mul_inv_cancel_right]

theorem card_sec_le [Finite G] (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hYC : Y ≤ Subgroup.normalizer ((U ⊓ C : Subgroup G) : Set G)) {F K : Subgroup G}
    (hFY : F ≤ Y) (hK : ∀ f ∈ F, f ∈ K ↔ ∀ u ∈ U, f * u * f⁻¹ * u⁻¹ ∈ C)
    (hr : (U ⊓ Subgroup.centralizer (F : Set G)).relIndex U ≤ (F ⊓ K).relIndex F) :
    Nat.card (Sec (⊤ : Subgroup ↥U) (C.subgroupOf U)) ≤
      Nat.card (autSec (autOn F U) ⊤ (C.subgroupOf U)) *
        Nat.card (fixV (autSec (autOn F U) ⊤ (C.subgroupOf U))) := by
  set N := U ⊓ Subgroup.centralizer (F : Set G) with hN
  have hsec : Nat.card (Sec (⊤ : Subgroup ↥U) (C.subgroupOf U)) = C.relIndex U := by
    show ((C.subgroupOf U).subgroupOf ⊤).index = C.relIndex U
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    rfl
  set ψ : ↥N →* Sec (⊤ : Subgroup ↥U) (C.subgroupOf U) :=
    (InternalSec.secMk (C.subgroupOf U)).comp (Subgroup.inclusion (inf_le_left : N ≤ U))
    with hψ
  have hψker : ψ.ker = C.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, secMk_eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hψrange : ψ.range ≤ fixV (autSec (autOn F U) ⊤ (C.subgroupOf U)) := by
    rintro _ ⟨n, rfl⟩
    exact secMk_mem_fixV hYU hYC hFY fun f hf => Subgroup.mem_centralizer_iff.mp n.2.2 f hf
  have hfix : C.relIndex N ≤ Nat.card (fixV (autSec (autOn F U) ⊤ (C.subgroupOf U))) := by
    have h1 : ψ.ker.index = Nat.card ψ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    rw [hψker] at h1
    rw [Subgroup.relIndex, h1]
    exact Subgroup.card_le_of_le hψrange
  have hcard := card_autSec_eq hYU hYC hFY hK
  have h1 := Subgroup.relIndex_mul_relIndex (C ⊓ N) N U inf_le_right inf_le_left
  rw [Subgroup.inf_relIndex_right] at h1
  have h2 : C.relIndex U ≤ (C ⊓ N).relIndex U :=
    Subgroup.relIndex_le_of_le_left inf_le_left Subgroup.index_ne_zero_of_finite
  rw [hsec, hcard]
  calc C.relIndex U ≤ C.relIndex N * N.relIndex U := h1 ▸ h2
    _ ≤ Nat.card (fixV (autSec (autOn F U) ⊤ (C.subgroupOf U))) * (F ⊓ K).relIndex F :=
        Nat.mul_le_mul hfix hr
    _ = _ := mul_comm _ _

theorem isElemAbelian2_autOn {A : Subgroup G} (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (U : Set G))
    (hsq : ∀ a ∈ A, a * a ∈ Subgroup.centralizer (U : Set G)) : IsElemAbelian2 (autOn A U) := by
  rw [← Setup.range_rho hAU]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul,
      Setup.rho_eq_one_iff]
    have e : ((a * b * (b * a)⁻¹ : ↥A) : G) = (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
      group
    rw [e]
    exact hcomm a a.2 b b.2
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, Setup.rho_eq_one_iff, pow_two]
    exact hsq a a.2

end A6Mod

@[expose] def Lem1374One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) →
      ∀ h ∈ H, (∀ u ∈ conjClosure S.V3 H,
        h * u * h⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G)) → h ∈ pCoreOf 2 H

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

omit hNS h13315 h1356two hH hab in
theorem le_normalizer_U0 :
    H ≤ Subgroup.normalizer ((conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :
      Subgroup G) : Set G) := fun _ hh =>
  F7.mem_normalizer_inf (le_normalizer_conjClosure _ _ hh)
    (InternalSec.le_normalizer_centralizer (le_normalizer_pCoreOf 2 H) hh)

theorem mem_QH_iff_plus (hNU : ¬ LieModel G .PSU 4 3 1)
    (hhat : ¬ IsHatA6 L) (hLem : Lem1374One) {h : G} (hh : h ∈ H) :
    h ∈ pCoreOf 2 H ↔ ∀ u ∈ conjClosure S.V3 H,
      h * u * h⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  constructor
  · intro hq u hu
    exact S.V1_le_centralizer_QH hNS h13315 h1356two hH (hF.commutator_mem_V₁ hq hu)
  · exact hLem G T L V S hNS hNU hhat H hH hab h hh

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

theorem A_le_H : C.A ≤ H :=
  (C.A_le_T hNS h13315 h1356two hH hab hhat).trans (S.hypF91 hNS h13315 h1356two hH).T_le_H

theorem card_A_plus (hNU : ¬ LieModel G .PSU 4 3 1)
    (hLem : Lem1374One) [IsMulCommutative ↥(conjClosure S.V3 H)] :
    Nat.card (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) =
      (C.A ⊓ pCoreOf 2 H).relIndex C.A :=
  A6Mod.card_autSec_eq (le_normalizer_conjClosure _ _) S.le_normalizer_U0
    (C.A_le_H hNS h13315 h1356two hH hab hhat) fun _ ha =>
      S.mem_QH_iff_plus hNS h13315 h1356two hH hab hNU hhat hLem
        (C.A_le_H hNS h13315 h1356two hH hab hhat ha)

theorem card_sec_le_A_plus (hNU : ¬ LieModel G .PSU 4 3 1)
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (hLem : Lem1374One)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    Nat.card (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ≤
      Nat.card (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) *
        Nat.card (fixV (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))) :=
  A6Mod.card_sec_le (le_normalizer_conjClosure _ _) S.le_normalizer_U0
    (C.A_le_H hNS h13315 h1356two hH hab hhat)
    (fun _ ha => S.mem_QH_iff_plus hNS h13315 h1356two hH hab hNU hhat hLem
      (C.A_le_H hNS h13315 h1356two hH hab hhat ha))
    (C.relIndex_centralizer_A_le hNS h13315 h1356two hH hab hhat hna)

theorem isA2_A_plus (hNU : ¬ LieModel G .PSU 4 3 1)
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14) (hLem : Lem1374One)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    IsA2 (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
      (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
  have hAH := C.A_le_H hNS h13315 h1356two hH hab hhat
  have hVC : V ≤ Subgroup.centralizer (conjClosure S.V3 H : Set G) :=
    (le_conjClosure V H).trans (S.VH_le_centralizer_UH hNS h13315 h1356two hH hab)
  refine ⟨autSec_mono (InternalSec.autOn_le_autOn_of_le hAH) _ _, ?_, ?_⟩
  ·
    intro hbot
    have h1 := C.card_A_plus hNS h13315 h1356two hH hab hhat hNU hLem
    rw [hbot, Subgroup.card_bot, eq_comm, Subgroup.relIndex_eq_one] at h1
    apply C.not_UHg_le_QH hNS h13315 h1356two hH hab hhat hna h13314
    exact fun x hx => (h1 (C.UHg_le_A hNS h13315 h1356two hH hab hx)).2
  · refine Bridge.isElemAbelian2_autSec (A6Mod.isElemAbelian2_autOn
      ((hAH.trans (le_normalizer_conjClosure _ _))) (fun a ha b hb => hVC
        (C.comm_VHg_mem_V hNS h13315 h1356two hH hab ha.1 hb.1)) (fun a ha => hVC ?_))
      (A6Mod.autOn_le_stab (hAH.trans S.le_normalizer_U0))
    have h := S.sq_VH_mem_V1 hNS h13315 h1356two hH hab ((C.mem_VHg).1 ha.1)
    have hV := ((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V) h
    have e : (C.g : G) * a * (C.g : G)⁻¹ * ((C.g : G) * a * (C.g : G)⁻¹) =
        (C.g : G) * (a * a) * (C.g : G)⁻¹ := by group
    rw [e] at hV
    exact (Subgroup.mem_normalizer_iff.mp C.g.2 _).mpr hV

theorem exists_isFFStarMin_A_plus
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14) (hLem : Lem1374One) [IsMulCommutative ↥(conjClosure S.V3 H)] :
    ∃ B, IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B ∧
      B ≤ autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) := by
  have hV : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  have hA := C.isA2_A_plus hNS h13315 h1356two hH hab hhat hNU hna h13314 hLem
  have hr := (rAV_le_one_iff (Bridge.sec_sq_eq_one hV _ _) hA).2
    (C.card_sec_le_A_plus hNS h13315 h1356two hH hab hhat hNU hna hLem)
  obtain ⟨B, hBA, hB, -⟩ := B1_4_4_le (Bridge.sec_sq_eq_one hV _ _) hA hr
  obtain ⟨B', hB', hB'B⟩ := B1Red.exists_isFFStarMin_below hB
  exact ⟨B', hB', hB'B.trans hBA⟩

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
