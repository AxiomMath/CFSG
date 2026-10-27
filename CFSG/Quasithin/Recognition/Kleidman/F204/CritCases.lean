module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CritBasic
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

variable {H M B S : Subgroup G}

omit [Finite G] in
private theorem isSylowTwoOf_conj_inv (g : ↥(H ⊔ M)) {δ : Geo H M} {T : Subgroup G}
    (hT : IsSylowTwoOf T (stab (g • δ))) : IsSylowTwoOf (conjSub (g : G)⁻¹ T) (stab δ) := by
  have := isSylowTwoOf_conj hT (g : G)⁻¹
  rwa [stab_smul, conjSub_conjSub_inv] at this

omit [Finite G] in
theorem ZCentral_smul (g : ↥(H ⊔ M)) {δ : Geo H M} (h : ZCentral δ) : ZCentral (g • δ) := by
  intro T hT
  rw [Zv_smul, h _ (isSylowTwoOf_conj_inv g hT), conjSub_omegaOneCenter, conjSub_inv_conjSub]

omit [Finite G] in
theorem ZFaithful_smul (g : ↥(H ⊔ M)) {δ : Geo H M} (h : ZFaithful δ) : ZFaithful (g • δ) := by
  intro T hT
  have e := congrArg (conjSub (g : G)) (h _ (isSylowTwoOf_conj_inv g hT))
  rwa [conjSub_inf, conjSub_inv_conjSub, ← conjSub_centralizer, ← Zv_smul, ← Qv_smul] at e

omit [Finite G] in
theorem ZCentral_of_vtype_eq {δ δ' : Geo H M} (hv : vtype δ = vtype δ') (h : ZCentral δ) :
    ZCentral δ' := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq hv
  exact ZCentral_smul g h

omit [Finite G] in
theorem ZFaithful_of_vtype_eq {δ δ' : Geo H M} (hv : vtype δ = vtype δ') (h : ZFaithful δ) :
    ZFaithful δ' := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq hv
  exact ZFaithful_smul g h

namespace Amal

variable (hA : Amal H M B S)
include hA

theorem config :
    (∀ δ : Geo H M, ZCentral δ ↔ vtype δ = false) ∨ (∀ δ : Geo H M, ZCentral δ ↔ vtype δ = true) ∨
      ∀ δ : Geo H M, ¬ ZCentral δ := by
  have hadj : γ₁ (H ⊔ M) H M ∈ nbrs (γ₀ (H ⊔ M) H M) := adj_γ₀_γ₁
  by_cases h0 : ZCentral (γ₀ (H ⊔ M) H M)
  · left
    intro δ
    constructor
    · intro hδ
      by_contra hv
      have hv' : vtype δ = vtype (γ₁ (H ⊔ M) H M) := by
        rw [vtype_γ₁]; simpa using hv
      exact hA.not_ZCentral_both hadj h0 (ZCentral_of_vtype_eq hv' hδ)
    · intro hv
      exact ZCentral_of_vtype_eq (by rw [vtype_γ₀, hv]) h0
  · by_cases h1 : ZCentral (γ₁ (H ⊔ M) H M)
    · right; left
      intro δ
      constructor
      · intro hδ
        by_contra hv
        have hv' : vtype δ = vtype (γ₀ (H ⊔ M) H M) := by
          rw [vtype_γ₀]; simpa using hv
        exact h0 (ZCentral_of_vtype_eq hv' hδ)
      · intro hv
        exact ZCentral_of_vtype_eq (by rw [vtype_γ₁, hv]) h1
    · right; right
      intro δ hδ
      cases hv : vtype δ with
      | false => exact h0 (ZCentral_of_vtype_eq (by rw [hv, vtype_γ₀]) hδ)
      | true => exact h1 (ZCentral_of_vtype_eq (by rw [hv, vtype_γ₁]) hδ)

theorem le_Qv_of_ZFaithful {δ : Geo H M} (hf : ZFaithful δ) {U : Subgroup G}
    (hU : U ≤ stab δ) (hU2 : IsPGroup 2 U) (hc : U ≤ Subgroup.centralizer (Zv δ : Set G)) :
    U ≤ Qv δ := by
  obtain ⟨T, hT, hUT⟩ := F1.exists_isSylowTwoOf_ge hU hU2
  rw [← hf T hT]
  exact le_inf hUT hc

theorem ZFaithful_of_bAt (hdich : ∀ δ : Geo H M, ZCentral δ ∨ ZFaithful δ) {δ : Geo H M}
    (h : bAt δ = bMin H M) : ZFaithful δ :=
  (hdich δ).resolve_left (hA.not_ZCentral_of_bAt h)

theorem caseI (hdich : ∀ δ : Geo H M, ZCentral δ ∨ ZFaithful δ) {α β α' : Geo H M}
    (hc : IsCritData α β α') (h : ¬ Zv α' ≤ Qv α) :
    bAt α' = bMin H M ∧ ZFaithful α ∧ ZFaithful α' := by
  have hb : bAt α' = bMin H M := by
    refine le_antisymm ?_ (bMin_le_bAt α')
    have := (Nat.sInf_le ⟨α, rfl, h⟩ : bAt α' ≤ dist α' α)
    rwa [CosetGeom.dist_comm, hc.dist_eq] at this
  exact ⟨hb, hA.ZFaithful_of_bAt hdich hc.bAt_eq, hA.ZFaithful_of_bAt hdich hb⟩

theorem caseII (hdich : ∀ δ : Geo H M, ZCentral δ ∨ ZFaithful δ) {α β α' : Geo H M}
    (hc : IsCritData α β α') (h : Zv α' ≤ Qv α) :
    ZCentral α' ∧ ZFaithful α ∧ ¬ ZCentral α ∧ Odd (bMin H M) ∧ vtype α' = vtype β := by
  have hnα : ¬ ZCentral α := hA.not_ZCentral_of_bAt hc.bAt_eq
  have hle : Zv α ≤ stab α' := hA.Zv_le_stab_of_dist_le (by rw [hc.dist_eq, hc.bAt_eq])
  have hcomm : Zv α ≤ Subgroup.centralizer (Zv α' : Set G) := fun x hx =>
    Subgroup.centralizer_le h ((hA.Zv_le_centerOf_Qv α hx).2)
  have hcen : ZCentral α' := by
    refine (hdich α').resolve_right fun hf => hc.not_le ?_
    exact hA.le_Qv_of_ZFaithful hf hle (F7.isPGroup_of_isElemAbelian (hA.isElemAbelian_Zv α))
      hcomm
  have hne : vtype α ≠ vtype α' := fun hv =>
    hnα (ZCentral_of_vtype_eq hv.symm hcen)
  have hodd : Odd (bMin H M) := by
    rw [← hc.dist_eq, ← Nat.not_even_iff_odd, ← vtype_eq_iff_even_dist hA.amalgam.gen]
    exact hne
  refine ⟨hcen, hA.ZFaithful_of_bAt hdich hc.bAt_eq, hnα, hodd, ?_⟩
  have hαβ : vtype α ≠ vtype β := vtype_ne_of_adj hc.adj
  cases h1 : vtype α <;> cases h2 : vtype α' <;> cases h3 : vtype β <;> simp_all

theorem offender_or (α α' : Geo H M) :
    (Zv α ⊓ Subgroup.centralizer (Zv α' : Set G)).relIndex (Zv α) ≤
        (Zv α' ⊓ Qv α).relIndex (Zv α') ∨
      (Zv α' ⊓ Subgroup.centralizer (Zv α : Set G)).relIndex (Zv α') ≤
        (Zv α ⊓ Qv α').relIndex (Zv α) := by
  have h1 : Zv α ⊓ Subgroup.centralizer (Zv α' : Set G) ≥ Zv α ⊓ Qv α' := fun x hx =>
    ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      ((Subgroup.mem_centralizer_iff.mp ((hA.Zv_le_centerOf_Qv α' hy).2)) x hx.2).symm⟩
  have h2 : Zv α' ⊓ Subgroup.centralizer (Zv α : Set G) ≥ Zv α' ⊓ Qv α := fun x hx =>
    ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      ((Subgroup.mem_centralizer_iff.mp ((hA.Zv_le_centerOf_Qv α hy).2)) x hx.2).symm⟩
  have i1 := Subgroup.relIndex_le_of_le_left (L := Zv α) h1 Subgroup.index_ne_zero_of_finite
  have i2 := Subgroup.relIndex_le_of_le_left (L := Zv α') h2 Subgroup.index_ne_zero_of_finite
  by_cases hle : (Zv α ⊓ Qv α').relIndex (Zv α) ≤ (Zv α' ⊓ Qv α).relIndex (Zv α')
  · exact Or.inl (i1.trans hle)
  · exact Or.inr (i2.trans (by omega))

end Amal

end CFSG.Quasithin.Kleidman.F204
