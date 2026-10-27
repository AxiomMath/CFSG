module

public import CFSG.Quasithin.H13.A6S13826k

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace D826

variable {H K : Subgroup G} (hd : S.D826 H K)
include hd

theorem exists_realizesVia_alt [IsMulCommutative ↥(conjClosure S.V3 H)]
    {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) {W : Subgroup G}
    (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H)
    (hW : ∀ u ∈ conjClosure S.V3 H, u ∈ W ↔ ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V)
    (h16 : W.relIndex (conjClosure S.V3 H) = 16) :
    ∃ (α' : ↥K →* alternatingGroup (Fin 6))
      (π : alternatingGroup (Fin 6) →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))),
      Function.Surjective α' ∧ (∀ k : ↥K, α' k = 1 ↔ (k : G) ∈ pCoreOf 2 H) ∧
      (∀ k : ↥K, ((π (α' k) : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) :
          MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) =
        L13825.sigmaH hd.hH ⟨(k : G), hd.hKH k.2⟩) ∧
      (FFModel.altDn 6).RealizesVia (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊤
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π := by
  classical
  have hF1 := hd.hF.toHypF91
  set U := conjClosure S.V3 H with hU
  have hsV := hd.secU le_rfl hd.V1_lt_UH.le le_rfl (le_normalizer_conjClosure _ _)
    hF1.H_normalizes_V₁ (hd.knt_top hd.V1_lt_UH) hαs hαk
  have hsW := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
    hαs hαk
  obtain ⟨M⟩ := hsW.nonempty_n6Model hmax hαs hαk h16
  set Kt := autSec (autOn K U) ⊤ ((fsuV1 T V).subgroupOf U) with hKt
  set LW := autSec (autOn K U) ⊤ (W.subgroupOf U) with hLW
  let rV : ↥K →* ↥Kt := (hsV.act.comp (Subgroup.inclusion hd.hKH)).codRestrict Kt fun k =>
    (hsV.mem_autSec_iff hd.hKH).2 ⟨_, k.2, rfl⟩
  let rW : ↥K →* ↥LW := (hsW.act.comp (Subgroup.inclusion hd.hKH)).codRestrict LW fun k =>
    (hsW.mem_autSec_iff hd.hKH).2 ⟨_, k.2, rfl⟩
  have hrVs : Function.Surjective rV := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨f, hf, rfl⟩ := (hsV.mem_autSec_iff hd.hKH).1 hψ
    exact ⟨⟨f, hf⟩, rfl⟩
  have hrWs : Function.Surjective rW := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨f, hf, rfl⟩ := (hsW.mem_autSec_iff hd.hKH).1 hψ
    exact ⟨⟨f, hf⟩, rfl⟩
  have hrVk : ∀ k : ↥K, rV k = 1 ↔ (k : G) ∈ pCoreOf 2 H := fun k => by
    rw [← Subtype.coe_inj]
    exact hsV.act_eq_one_iff _
  have hrWk : ∀ k : ↥K, rW k = 1 ↔ (k : G) ∈ pCoreOf 2 H := fun k => by
    rw [← Subtype.coe_inj]
    exact hsW.act_eq_one_iff _
  have hρinj : Function.Injective M.ρL := fun a b h =>
    Subtype.ext (M.ρ_inj (congrArg Subtype.val h))
  let eρ : alternatingGroup (Fin 6) ≃* ↥LW := MulEquiv.ofBijective M.ρL ⟨hρinj, M.ρL_surjective⟩
  let α' : ↥K →* alternatingGroup (Fin 6) := eρ.symm.toMonoidHom.comp rW
  have hρα : ∀ k : ↥K, M.ρL (α' k) = rW k := fun k => eρ.apply_symm_apply (rW k)
  have hα'k : ∀ k : ↥K, α' k = 1 ↔ (k : G) ∈ pCoreOf 2 H := fun k => by
    rw [← hrWk]
    show eρ.symm (rW k) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
  have hα's : Function.Surjective α' := eρ.symm.surjective.comp hrWs
  have hker : α'.ker ≤ rV.ker := fun k hk =>
    (MonoidHom.mem_ker).2 ((hrVk k).2 ((hα'k k).1 ((MonoidHom.mem_ker).1 hk)))
  let π : alternatingGroup (Fin 6) →* ↥Kt := (QuotientGroup.lift α'.ker rV hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective α' hα's).symm.toMonoidHom
  have hπα : ∀ k : ↥K, π (α' k) = rV k := by
    intro k
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective α' hα's).symm (α' k) =
        (QuotientGroup.mk k : ↥K ⧸ α'.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift α'.ker rV hker
      ((QuotientGroup.quotientKerEquivOfSurjective α' hα's).symm (α' k)) = rV k
    rw [h1, QuotientGroup.lift_mk]
  have hπs : Function.Surjective π := by
    intro x
    obtain ⟨k, rfl⟩ := hrVs x
    exact ⟨α' k, hπα k⟩
  refine ⟨α', π, hα's, hα'k, fun k => by rw [hπα]; rfl, ?_⟩
  have hle : ((fsuV1 T V).subgroupOf U).subgroupOf (⊤ : Subgroup ↥U) ≤
      ((W.subgroupOf U).subgroupOf (⊤ : Subgroup ↥U)).comap (MonoidHom.id _) := by
    intro x hx
    simp only [Subgroup.mem_comap, MonoidHom.id_apply, Subgroup.mem_subgroupOf] at hx ⊢
    exact hV1W hx
  let proj : Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U) →*
      Sec (⊤ : Subgroup ↥U) (W.subgroupOf U) := QuotientGroup.map _ _ (MonoidHom.id _) hle
  have hproj : ∀ u : ↥U, proj (InternalSec.secMk ((fsuV1 T V).subgroupOf U) u) =
      InternalSec.secMk (W.subgroupOf U) u := fun _ => rfl
  have hprojs : Function.Surjective proj := by
    intro y
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf U) y
    exact ⟨_, hproj u⟩
  have hfix : ∀ u : ↥U, InternalSec.secMk ((fsuV1 T V).subgroupOf U) u ∈ fixV Kt ↔
      ∀ k ∈ K, k * (u : G) * k⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
    intro u
    rw [mem_fixV]
    constructor
    · intro h k hk
      have h1 := h _ ((hsV.mem_autSec_iff hd.hKH).2 ⟨⟨k, hd.hKH hk⟩, hk, rfl⟩)
      rw [SecHyp.act_secMk] at h1
      have h2 : InternalSec.secMk ((fsuV1 T V).subgroupOf U)
          (Setup.rho U H hsV.hHX ⟨k, hd.hKH hk⟩ u * u⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      rw [A6Mod.secMk_eq_one_iff] at h2
      simpa only [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] using h2
    · intro h ψ hψ
      obtain ⟨f, hf, rfl⟩ := (hsV.mem_autSec_iff hd.hKH).1 hψ
      rw [SecHyp.act_secMk]
      have h2 : InternalSec.secMk ((fsuV1 T V).subgroupOf U)
          (Setup.rho U H hsV.hHX f u * u⁻¹) = 1 := by
        rw [A6Mod.secMk_eq_one_iff]
        simpa only [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] using h f hf
      rw [map_mul, map_inv, mul_inv_eq_one] at h2
      exact h2
  let β : ↥(⊤ : Subgroup (Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U))) →*
      ↥(FFModel.altDn 6).sec ⧸ (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec :=
    M.modEquiv.toMonoidHom.comp (proj.comp (Subgroup.subtype _))
  have hD := FFModel.altDn_isActionModel 6
  refine ⟨hπs, le_top, hD.ker_le, fun _ _ _ => trivial, fun h z hz => ?_, hD.sec_inv,
    hD.ker_inv, β, ?_, ?_, ?_⟩
  · rw [mem_fixV] at hz ⊢
    intro x hx
    rw [hz _ h.2, hz x hx]
  · intro q
    obtain ⟨y, rfl⟩ := M.modEquiv.surjective q
    obtain ⟨x, rfl⟩ := hprojs y
    exact ⟨⟨x, trivial⟩, rfl⟩
  · rintro ⟨x, -⟩
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective ((fsuV1 T V).subgroupOf U) x
    show M.modEquiv (proj (InternalSec.secMk _ u)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, hproj, A6Mod.secMk_eq_one_iff, hW u u.2, hfix]
  · intro γ ⟨x, hx⟩ m hu hm hβx
    obtain ⟨k, rfl⟩ := hα's γ
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective ((fsuV1 T V).subgroupOf U) x
    have hact : ((π (α' k) : ↥Kt) : MulAut (Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U)))
        (InternalSec.secMk ((fsuV1 T V).subgroupOf U) u) =
        InternalSec.secMk ((fsuV1 T V).subgroupOf U)
          (Setup.rho U H hsV.hHX ⟨k, hd.hKH k.2⟩ u) := by
      rw [hπα]
      exact SecHyp.act_secMk hsV _ u
    have hactW : (M.ρ (α' k : Perm (Fin 6))) (InternalSec.secMk (W.subgroupOf U) u) =
        InternalSec.secMk (W.subgroupOf U) (Setup.rho U H hsW.hHX ⟨k, hd.hKH k.2⟩ u) := by
      have h1 : M.ρ (α' k : Perm (Fin 6)) = ((M.ρL (α' k) : ↥LW) : MulAut _) := rfl
      rw [h1, hρα]
      exact SecHyp.act_secMk hsW _ u
    show M.modEquiv (proj ((π (α' k) : MulAut _) (InternalSec.secMk _ u))) = _
    rw [hact, hproj]
    have e : InternalSec.secMk (W.subgroupOf U) (Setup.rho U H hsV.hHX ⟨k, hd.hKH k.2⟩ u) =
        M.ρ (α' k : Perm (Fin 6)) (InternalSec.secMk (W.subgroupOf U) u) := by
      rw [hactW]
    rw [e]
    exact M.modEquiv_act _ _ m hm (by rw [← hproj]; exact hβx)

end D826

end Setting4

end CFSG.Quasithin.H13.A6
