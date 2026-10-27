module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem10
public import CFSG.Quasithin.H13.GoldschmidtM22EndCtx
public import CFSG.Quasithin.H13.GoldschmidtM22EndSec

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G]

theorem mul_mem_of_relIndex_two {A B : Subgroup G} (h2 : A.relIndex B = 2) {x y : G} (hx : x ∈ B)
    (hy : y ∈ B) (hxA : x ∉ A) (hyA : y ∉ A) : x * y ∈ A := by
  have := (Subgroup.mul_mem_iff_of_index_two (H := A.subgroupOf B) h2
    (a := (⟨x, hx⟩ : ↥B)) (b := ⟨y, hy⟩)).2 (by
      simp only [Subgroup.mem_subgroupOf]
      exact iff_of_false hxA hyA)
  simpa [Subgroup.mem_subgroupOf] using this

variable [Finite G] {T M L V : Subgroup G}

section Data

variable (h : Hyp6Sec2 G T M L V) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)

include h in
theorem card_ZS_eq_four : Nat.card (ch6ZS T L V) = 4 := by
  have := h.toHyp611Nat.card_ZS
  simpa using this

include h hZ in
theorem relIndex_Z_ZS : (quasithinOmegaOneCenter T).relIndex (ch6ZS T L V) = 2 := by
  have h1 := Subgroup.relIndex_mul_card (H := quasithinOmegaOneCenter T) (K := ch6ZS T L V)
  rw [inf_eq_left.mpr (Z_le_ZS h hZ), hZ, card_ZS_eq_four h] at h1
  omega

include h hZ in
theorem exists_ZS_not_Z : ∃ z₀ ∈ ch6ZS T L V, z₀ ∉ quasithinOmegaOneCenter T := by
  by_contra hcon
  push Not at hcon
  have := relIndex_Z_ZS h hZ
  have h1 : (quasithinOmegaOneCenter T).relIndex (ch6ZS T L V) = 1 :=
    Subgroup.relIndex_eq_one.mpr hcon
  omega

end Data

section Rep

variable (T L V) in
abbrev Ut : Type := Sec (UU T L V) (quasithinOmegaOneCenter T)

variable (T L V) in
abbrev tmk (u : ↥(UU T L V)) : Ut T L V := Sec.mk (UU T L V) (quasithinOmegaOneCenter T) u

variable [Fact (IsElemAbelianMod (UU T L V) (quasithinOmegaOneCenter T))]

variable (T L V) in
@[expose] noncomputable def rep : ↥(HH T) →* MulAut (Ut T L V) :=
  secHom (UU T L V) (quasithinOmegaOneCenter T) (HH T) (HH_le_normalizer_UU T L V)
    (HH_le_normalizer_Z T)

theorem rep_mk (x : ↥(HH T)) (u : ↥(UU T L V)) :
    rep T L V x (tmk T L V u) = tmk T L V (conjU (UU T L V) x (HH_le_normalizer_UU T L V x.2) u) :=
  secHom_mk _ _ _ _ _ x u

theorem rep_eq_one_iff (x : ↥(HH T)) : rep T L V x = 1 ↔ (x : G) ∈ CHU T L V :=
  secHom_eq_one_iff _ _ _ _ _ x

theorem tmk_mul (u v : ↥(UU T L V)) : tmk T L V (u * v) = tmk T L V u * tmk T L V v :=
  Sec.mk_mul _ _ u v

theorem tmk_inv (u : ↥(UU T L V)) : tmk T L V u⁻¹ = (tmk T L V u)⁻¹ :=
  QuotientGroup.mk_inv _ u

theorem tmk_eq_one_iff (u : ↥(UU T L V)) : tmk T L V u = 1 ↔ (u : G) ∈ quasithinOmegaOneCenter T :=
  Sec.mk_eq_one_iff _ _ u

variable (h : Hyp6Sec2 G T M L V) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)
  (h6210 : Stmt6_2_10) (hZS : ch6ZS T L V = V ⊓ UU T L V)

variable (T L V) in
abbrev zt (z : G) (hz : z ∈ ch6ZS T L V) : Ut T L V := tmk T L V ⟨z, le_conjClosure _ _ hz⟩

include h hZ in
theorem exists_z0 : ∃ z₀ : G, ∃ hz₀ : z₀ ∈ ch6ZS T L V, z₀ ∉ quasithinOmegaOneCenter T ∧
    ∀ (z : G) (hz : z ∈ ch6ZS T L V), zt T L V z hz = 1 ∨ zt T L V z hz = zt T L V z₀ hz₀ := by
  obtain ⟨z₀, hz₀, hz₀Z⟩ := exists_ZS_not_Z h hZ
  refine ⟨z₀, hz₀, hz₀Z, fun z hz => ?_⟩
  by_cases hzZ : z ∈ quasithinOmegaOneCenter T
  · exact Or.inl ((tmk_eq_one_iff _).mpr hzZ)
  · refine Or.inr ?_
    have hprod : z * z₀ ∈ quasithinOmegaOneCenter T :=
      mul_mem_of_relIndex_two (relIndex_Z_ZS h hZ) hz hz₀ hzZ hz₀Z
    have h1 : tmk T L V (⟨z, le_conjClosure _ _ hz⟩ * ⟨z₀, le_conjClosure _ _ hz₀⟩ :
        ↥(UU T L V)) = 1 := (tmk_eq_one_iff _).mpr hprod
    rw [tmk_mul] at h1
    have h2 : zt T L V z₀ hz₀ * zt T L V z₀ hz₀ = 1 := by
      rw [← pow_two]; exact Sec.sq_eq_one _ _ _
    exact (mul_eq_one_iff_eq_inv.mp h1).trans (inv_eq_of_mul_eq_one_right h2)

variable (z₀ : G) (hz₀ : z₀ ∈ ch6ZS T L V)
  (hw : ∀ (z : G) (hz : z ∈ ch6ZS T L V), zt T L V z hz = 1 ∨ zt T L V z hz = zt T L V z₀ hz₀)

include h hZS h6210 hw in
theorem rep_form (a : ↥(HH T)) (haV : (a : G) ∈ V) (x : Ut T L V) :
    rep T L V a x = x ∨ rep T L V a x = x * zt T L V z₀ hz₀ := by
  induction x using QuotientGroup.induction_on with | H u => ?_
  have hc : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ ∈ ch6ZS T L V := by
    have h1 := commutator_V_UU_le h h6210 (Subgroup.commutator_mem_commutator haV u.2)
    rw [commutatorElement_def] at h1
    rwa [hZS]
  have hcU : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ ∈ UU T L V := le_conjClosure _ _ hc
  have e : conjU (UU T L V) a (HH_le_normalizer_UU T L V a.2) u =
      ⟨(a : G) * u * (a : G)⁻¹ * (u : G)⁻¹, hcU⟩ * u := by
    apply Subtype.ext
    rw [coe_conjU]
    simp
  change rep T L V a (tmk T L V u) = tmk T L V u ∨
    rep T L V a (tmk T L V u) = tmk T L V u * zt T L V z₀ hz₀
  rw [rep_mk, e, tmk_mul]
  rcases hw _ hc with h1 | h1
  · have h1' : tmk T L V ⟨_, hcU⟩ = 1 := h1
    left; rw [h1', one_mul]
  · have h1' : tmk T L V ⟨_, hcU⟩ = zt T L V z₀ hz₀ := h1
    right; rw [h1', mul_comm]

omit h6210 hZS in
include h hZ hw in
theorem mem_normalizer_ZS_of_fix (x : ↥(HH T))
    (hx : rep T L V x (zt T L V z₀ hz₀) = zt T L V z₀ hz₀) :
    (x : G) ∈ Subgroup.normalizer (ch6ZS T L V : Set G) := by
  have fwd : ∀ y : ↥(HH T), rep T L V y (zt T L V z₀ hz₀) = zt T L V z₀ hz₀ →
      ∀ g ∈ ch6ZS T L V, (y : G) * g * (y : G)⁻¹ ∈ ch6ZS T L V := by
    intro y hy g hg
    have hgU : g ∈ UU T L V := le_conjClosure _ _ hg
    rcases hw g hg with h1 | h1
    · have hgZ : g ∈ quasithinOmegaOneCenter T := (tmk_eq_one_iff ⟨g, hgU⟩).mp h1
      have : (y : G) * g * (y : G)⁻¹ = g := by
        rw [Z_central T y.2 hgZ]
        group
      rw [this]
      exact hg
    · have e1 : tmk T L V (conjU (UU T L V) y (HH_le_normalizer_UU T L V y.2) ⟨g, hgU⟩) =
          tmk T L V ⟨z₀, le_conjClosure _ _ hz₀⟩ := by
        rw [← rep_mk]
        change rep T L V y (zt T L V g hg) = zt T L V z₀ hz₀
        rw [h1]
        exact hy
      have e3 := (QuotientGroup.eq_iff_div_mem).mp e1
      rw [Subgroup.mem_subgroupOf] at e3
      have e4 : (y : G) * g * (y : G)⁻¹ * z₀⁻¹ ∈ quasithinOmegaOneCenter T := by
        simpa [coe_conjU, div_eq_mul_inv] using e3
      have : (y : G) * g * (y : G)⁻¹ = ((y : G) * g * (y : G)⁻¹ * z₀⁻¹) * z₀ := by group
      rw [this]
      exact (ch6ZS T L V).mul_mem (Z_le_ZS h hZ e4) hz₀
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact fwd x hx g
  · intro hg
    have hx' : rep T L V x⁻¹ (zt T L V z₀ hz₀) = zt T L V z₀ hz₀ := by
      rw [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_eq]
      exact hx.symm
    have := fwd x⁻¹ hx' _ hg
    have e : ((x⁻¹ : ↥(HH T)) : G) * ((x : G) * g * (x : G)⁻¹) * ((x⁻¹ : ↥(HH T)) : G)⁻¹ = g := by
      simp only [Subgroup.coe_inv]
      group
    rwa [e] at this

end Rep

end CFSG.Quasithin.H13.GM22
