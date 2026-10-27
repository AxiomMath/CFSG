module

import CFSG.RankThree.GF2n.Stroth80.Sec117U3Field
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTauSetup
import CFSG.RankThree.GF2n.Stroth80.Sec108BarLift
import CFSG.RankThree.GF2n.Stroth80.InvolutionDim
import CFSG.ClassicalGroups.Unitary.ThreeEven
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec11Module

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.act_mem_range_of_mem_centralizer [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)} (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    {i : G} (hi : i ∈ LB M Q B)
    (hiX : (QuotientGroup.mk (⟨i, hc.LB_le_M hi⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    {g : G} (hg : g ∈ XbarPre M Q Z B) {w : M₀.E}
    (hw : w ∈ LinearMap.range ((φ ⟨i, hc.LB_le_H0 hi⟩ : M₀.E →ₗ[K] M₀.E) - 1)) :
    φ ⟨g, XbarPre_le_H0 hc hg⟩ w ∈
      LinearMap.range ((φ ⟨i, hc.LB_le_H0 hi⟩ : M₀.E →ₗ[K] M₀.E) - 1) := by
  obtain ⟨u, rfl⟩ := hw
  have hgM : g ∈ M := XbarPre_le_M hc hg
  have hgX : (QuotientGroup.mk (⟨g, hgM⟩ : ↥M) : Mbar M Q) ∈ Xbar M Q Z B :=
    (mem_XbarPre_iff hc hgM).mp hg
  have hcomm := Subgroup.mem_centralizer_iff.mp hiX _ hgX
  refine ⟨φ ⟨g, XbarPre_le_H0 hc hg⟩ u, ?_⟩
  have h1 := act_comm_of_mk_comm (m₁ := ⟨g, XbarPre_le_H0 hc hg⟩)
    (m₂ := ⟨i, hc.LB_le_H0 hi⟩) hφker hcomm u
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub, h1]

theorem Ctx.finrank_range_act_le_three (hc : Ctx M Q Z B) {K : Type} [Field K]
    [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    (hw : Width Q Z 3) {x : ℕ} (hZ : Nat.card Z = 2 ^ x)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)} (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    {i : G} (hi : i ∈ LB M Q B) :
    Module.finrank K (LinearMap.range ((φ ⟨i, hc.LB_le_H0 hi⟩ : M₀.E →ₗ[K] M₀.E) - 1)) ≤ 3 := by
  have : CharP K 2 := charP_two_of_globalModelData hD hZ
  have hK1 : 1 < Nat.card K := by
    have h4 := hc.hyp.q4
    rw [hD.card]
    omega
  have hdim := hD.finrank_E hw hK1
  exact Tim79.QuadModel.finrank_range_le_of_sq_eq_one M₀ hdim (by
    ext e
    simpa [LinearMap.comp_apply] using hc.act_sq_eq_of_mem_LB hφker hi e)

theorem exists_Xbar_hom_of_invariant [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E]
    (φ : ↥(H0 M Z) →* (E ≃ₗ[K] E)) (hφQ : ∀ m : ↥(H0 M Z), (m : G) ∈ Q → φ m = 1)
    (W : Submodule K E)
    (hW : ∀ (g : G) (hg : g ∈ XbarPre M Q Z B), ∀ w ∈ W, φ ⟨g, XbarPre_le_H0 hc hg⟩ w ∈ W) :
    ∃ ρ : ↥(Xbar M Q Z B) →* LinearMap.GeneralLinearGroup K W,
      ∀ (g : G) (hg : g ∈ XbarPre M Q Z B) (w : W),
        ((ρ ⟨QuotientGroup.mk ⟨g, XbarPre_le_M hc hg⟩,
          (mem_XbarPre_iff hc (XbarPre_le_M hc hg)).mp hg⟩ : W →ₗ[K] W) w : E) =
          φ ⟨g, XbarPre_le_H0 hc hg⟩ w := by
  let ψ : ↥(XbarPre M Q Z B) →* (E ≃ₗ[K] E) := φ.comp (Subgroup.inclusion (XbarPre_le_H0 hc))
  obtain ⟨ρ, hρ⟩ := CFSG.ClassicalGroups.Unitary.exists_hom_generalLinearGroup_restrict ψ W
    fun g w hw => hW g g.2 w hw
  have hρQ : ∀ s : ↥(XbarPre M Q Z B), (s : G) ∈ Q → ρ s = 1 := by
    intro s hs
    have hψ : ψ s = 1 := hφQ _ hs
    refine Units.ext (LinearMap.ext fun w => Subtype.ext ?_)
    rw [hρ s w, hψ]
    rfl
  let e : ↥(Xbar M Q Z B) ≃* ↥(bar M Q (XbarPre M Q Z B)) :=
    MulEquiv.subgroupCongr (bar_XbarPre hc).symm
  refine ⟨(barLift ρ hρQ).comp e.toMonoidHom, fun g hg w => ?_⟩
  have hgM : g ∈ M := XbarPre_le_M hc hg
  have hpi : HS6.piM M Q g ∈ bar M Q (XbarPre M Q Z B) :=
    (HS6.mem_bar _).mpr ⟨g, hg, hgM, rfl⟩
  have heq : e ⟨QuotientGroup.mk ⟨g, hgM⟩, (mem_XbarPre_iff hc hgM).mp hg⟩ =
      ⟨HS6.piM M Q g, hpi⟩ := Subtype.ext (HS6.piM_of_mem hgM).symm
  have h1 : (barLift ρ hρQ).comp e.toMonoidHom
      ⟨QuotientGroup.mk ⟨g, hgM⟩, (mem_XbarPre_iff hc hgM).mp hg⟩ = ρ ⟨g, hg⟩ := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, heq]
    exact barLift_piM ρ hρQ ⟨g, hg⟩ hgM hpi
  rw [h1]
  exact hρ ⟨g, hg⟩ w

theorem Ctx.act_eq_self_of_mem_range_of_psu3 [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {x : ℕ} (hw : Width Q Z 3) (hZ : Nat.card Z = 2 ^ x)
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 3 2 x) {K : Type} [Field K]
    [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)} (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    {i : G} (hi : i ∈ LB M Q B)
    (hiX : (QuotientGroup.mk (⟨i, hc.LB_le_M hi⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    {g : G} (hg : g ∈ XbarPre M Q Z B) {v : M₀.E}
    (hv : v ∈ LinearMap.range ((φ ⟨i, hc.LB_le_H0 hi⟩ : M₀.E →ₗ[K] M₀.E) - 1)) :
    φ ⟨g, XbarPre_le_H0 hc hg⟩ v = v := by
  obtain ⟨ρ, hρ⟩ := exists_Xbar_hom_of_invariant hc φ (fun m hm => (hφker m).mpr hm)
    (LinearMap.range ((φ ⟨i, hc.LB_le_H0 hi⟩ : M₀.E →ₗ[K] M₀.E) - 1))
    fun g' hg' w hw => hc.act_mem_range_of_mem_centralizer hφker hi hiX hg' hw
  have hdim := hc.finrank_range_act_le_three hD hw hZ hφker hi
  have hρ1 := CFSG.ClassicalGroups.Unitary.hom_eq_one_of_lieModel_psu3
    (hc.commutator_Xbar_eq_top_of_psu3 h) h (hD.card.trans hZ) (by omega) ρ
  have h1 := hρ g hg ⟨v, hv⟩
  rw [hρ1] at h1
  simpa using h1.symm

end CFSG.RankThree.GF2n.Stroth80
