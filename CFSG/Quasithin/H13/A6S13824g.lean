module

public import CFSG.Quasithin.H13.A6S13825v
public import CFSG.Quasithin.H13.A6S13824a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace DK

variable {H K : Subgroup G} (hd : S.DK H K)
include hd

theorem commV_autSec_eq_top [IsMulCommutative ↥(conjClosure S.V3 H)] :
    commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊤ := by
  rw [L13825.autSec_eq_map hd.hH hd.hKH]
  exact L13825.commV_eq_top_of_commutator hd.hH hd.hKH hd.hUK

theorem exists_realizesVia_top [IsMulCommutative ↥(conjClosure S.V3 H)] {D : FFModel}
    (hD : D.IsActionModel) {W : Subgroup G} (hV1W : fsuV1 T V ≤ W)
    (hWU : W < conjClosure S.V3 H) (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hW : ∀ u ∈ conjClosure S.V3 H, u ∈ W ↔ ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V)
    {π : D.Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      (W.subgroupOf (conjClosure S.V3 H)))}
    (hπ : D.RealizesVia (autSec (autOn K (conjClosure S.V3 H)) ⊤
      (W.subgroupOf (conjClosure S.V3 H))) ⊤ ⊥ π) :
    ∃ π' : D.Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))),
      D.RealizesVia (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊤
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π' := by
  classical
  have hF1 := hd.hF.toHypF91
  let U := conjClosure S.V3 H
  let Kt := autSec (autOn K U) ⊤ ((fsuV1 T V).subgroupOf U)
  let LW := autSec (autOn K U) ⊤ (W.subgroupOf U)
  have hsV := hd.secU le_rfl hd.V1_lt_UH.le le_rfl (le_normalizer_conjClosure _ _)
    hF1.H_normalizes_V₁ (hd.knt_top hd.V1_lt_UH)
  have hsW := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
  obtain ⟨hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
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
  have hker : rW.ker ≤ rV.ker := fun k hk =>
    (MonoidHom.mem_ker).2 ((hrVk k).2 ((hrWk k).1 ((MonoidHom.mem_ker).1 hk)))
  let φ : ↥LW →* ↥Kt := rW.liftOfSurjective hrWs ⟨rV, hker⟩
  have hφ : ∀ k : ↥K, φ (rW k) = rV k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply rW _ _ ⟨rV, hker⟩ k
  have hφs : Function.Surjective φ := by
    intro x
    obtain ⟨k, rfl⟩ := hrVs x
    exact ⟨rW k, hφ k⟩
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
  refine ⟨φ.comp π, ⟨hφs.comp hπs, le_top, hD.ker_le, fun _ _ _ => trivial, fun h z hz => ?_,
    hD.sec_inv, hD.ker_inv, β.comp ((Subgroup.topEquiv.symm.toMonoidHom.comp proj).comp
      (Subgroup.subtype _)), ?_, ?_, ?_⟩⟩
  · rw [mem_fixV] at hz ⊢
    intro x hx
    rw [hz _ h.2, hz x hx]
  · intro q
    obtain ⟨⟨y, -⟩, rfl⟩ := hβs q
    obtain ⟨x, rfl⟩ := hprojs y
    exact ⟨⟨x, trivial⟩, rfl⟩
  · rintro ⟨x, -⟩
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective ((fsuV1 T V).subgroupOf U) x
    show β ⟨proj (InternalSec.secMk _ u), trivial⟩ = 1 ↔ _
    rw [hβk]
    show proj (InternalSec.secMk _ u) ∈ (⊥ : Subgroup _) ↔ _
    rw [Subgroup.mem_bot, hproj, A6Mod.secMk_eq_one_iff, hW u u.2, hfix]
  · intro γ ⟨x, hx⟩ m hu hm hβx
    obtain ⟨k, hk⟩ := hrWs (π γ)
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective ((fsuV1 T V).subgroupOf U) x
    have hπγ : φ (π γ) = rV k := by rw [← hk, hφ]
    have hact : ((φ (π γ) : ↥Kt) : MulAut (Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U)))
        (InternalSec.secMk ((fsuV1 T V).subgroupOf U) u) =
        InternalSec.secMk ((fsuV1 T V).subgroupOf U)
          (Setup.rho U H hsV.hHX ⟨k, hd.hKH k.2⟩ u) := by
      rw [hπγ]
      exact SecHyp.act_secMk hsV _ u
    have hactW : ((π γ : ↥LW) : MulAut (Sec (⊤ : Subgroup ↥U) (W.subgroupOf U)))
        (InternalSec.secMk (W.subgroupOf U) u) =
        InternalSec.secMk (W.subgroupOf U) (Setup.rho U H hsW.hHX ⟨k, hd.hKH k.2⟩ u) := by
      rw [← hk]
      exact SecHyp.act_secMk hsW _ u
    have key := hβe γ ⟨InternalSec.secMk (W.subgroupOf U) u, trivial⟩ m trivial hm hβx
    show β ⟨proj ((φ (π γ) : MulAut _) (InternalSec.secMk _ u)), trivial⟩ = _
    rw [hact, hproj]
    have e : (⟨InternalSec.secMk (W.subgroupOf U) (Setup.rho U H hsV.hHX ⟨k, hd.hKH k.2⟩ u),
        trivial⟩ : ↥(⊤ : Subgroup (Sec (⊤ : Subgroup ↥U) (W.subgroupOf U)))) =
        ⟨((π γ : ↥LW) : MulAut _) (InternalSec.secMk (W.subgroupOf U) u), trivial⟩ := by
      apply Subtype.ext
      rw [hactW]
    rw [e]
    exact key

end DK

end Setting4

end CFSG.Quasithin.H13.A6
