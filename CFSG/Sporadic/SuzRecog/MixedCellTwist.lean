module

public import CFSG.Sporadic.SuzRecog.GluingProof2
public import CFSG.Sporadic.SuzRecog.C1ModelBase
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.Monster.Code.Weights
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

public section

namespace CFSG.Sporadic.SuzRecog.MixedCell

open Subgroup CFSG.Sporadic.SuzOddCore C1Model

local notation "Pm" => Equiv.Perm (Fin 1782)

section Remark

variable {G : Type} [Group G] {M : Subgroup G}

@[expose] noncomputable def remark (σ : M ≃* invE 1) (x : ↥(invE 1)) : M ≃* invE 1 :=
  σ.trans (MulAut.conj x).symm

theorem remark_symm_apply (σ : M ≃* invE 1) (x : ↥(invE 1)) (c : ↥(invE 1)) :
    (remark σ x).symm c = σ.symm (x * c * x⁻¹) :=
  rfl

theorem chartAgree_remark {w : Pm} {σ : M ≃* invE 1} {ζ : centM w →* G} (h : ChartAgree σ ζ)
    (x : ↥(invE 1)) :
    ChartAgree (remark σ x) ((MulAut.conj ((σ.symm x : M) : G)).toMonoidHom.comp ζ) := by
  intro y hy hyw
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h y hy hyw,
    remark_symm_apply, map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]

end Remark

private theorem mul_comm_of_conj {c y : Pm} (h : c * y * c⁻¹ = y) : c * y = y * c :=
  mul_inv_eq_iff_eq_mul.1 h

private theorem comm_t1
    {g : Pm} (hg : g ∈ invE 1) :
    g * suzInv 1 = suzInv 1 * g :=
  mem_centralizer_singleton_iff.1 (mem_inf.1 (invE_le_centM (by norm_num : 1 < 4) hg)).1

section Model


theorem mem_centralizer_R0_iff' {g : Pm} :
    g ∈ centralizer (Model.R0 : Set Pm) ↔ g * Model.w0 = Model.w0 * g ∧ g * r1 = r1 * g := by
  rw [R0_eq, centralizer_closure, mem_centralizer_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩

theorem zpowers_rho1_le_normalizer :
    zpowers Model.rho1 ≤ normalizer (centralizer (Model.R0 : Set Pm) : Set Pm) := by
  have hN : normalizer (Model.R0 : Set Pm) ≤
      normalizer (centralizer (Model.R0 : Set Pm) : Set Pm) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).1
      (normal_subgroupOf_centralizer_normalizer _)
  exact (zpowers_le.2 (mem_inf.1 rho1_mem_B0).2).trans hN

theorem commute_of_mem_B0Plus {x : Pm} (hxρ : x * Model.rho1 = Model.rho1 * x)
    (hV : ∀ v ∈ V0, v * r1 = r1 * v → v * x = x * v) {b : Pm} (hb : b ∈ B0Plus) :
    x * b = b * x := by
  obtain ⟨hB, hs⟩ := mem_inf.1 hb
  have hs' : b ∈ ((centralizer (Model.R0 : Set Pm) ⊔ zpowers Model.rho1 : Subgroup Pm) : Set Pm) :=
    hs
  rw [coe_mul_of_right_le_normalizer_left _ _ zpowers_rho1_le_normalizer] at hs'
  obtain ⟨c, hc, r, hr, rfl⟩ := hs'
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hr
  have hcC := mem_centralizer_R0_iff'.1 hc
  have hc1 : c ∈ invE 1 := by
    have h := mul_mem (mem_inf.1 hB).1 (inv_mem (zpow_mem rho1_mem_invE n))
    rwa [mul_inv_cancel_right] at h
  have hcx := hV c (mem_V0_iff.2 ⟨hcC.1, hc1⟩) hcC.2
  have hρx : Commute x (Model.rho1 ^ n) := (Commute.zpow_right hxρ n)
  calc x * (c * Model.rho1 ^ n) = c * x * Model.rho1 ^ n := by rw [← mul_assoc, hcx]
    _ = c * Model.rho1 ^ n * x := by rw [mul_assoc, hρx.eq, ← mul_assoc]

theorem mem_B0Plus_or_tau0_mul {b : Pm} (hb : b ∈ Model.B0) :
    b ∈ B0Plus ∨ tau0 * b ∈ B0Plus := by
  have hbN := (mem_inf.1 hb).2
  have hρN : Model.rho1 ∈ normalizer (Model.R0 : Set Pm) := (mem_inf.1 rho1_mem_B0).2
  obtain ⟨k, hk⟩ : ∃ k : ℕ,
      b * Model.w0 * b⁻¹ = Model.rho1 ^ k * Model.w0 * (Model.rho1 ^ k)⁻¹ := by
    have h := (mem_normalizer_iff.1 hbN Model.w0).1 w0_mem_R0
    rcases mem_R0_iff.1 h with h | h | h | h
    · exact absurd (conj_eq_one_iff.1 h) w0_ne_one
    · exact ⟨0, by rw [h]; group⟩
    · exact ⟨1, by rw [h]; simp [r1]⟩
    · refine ⟨2, ?_⟩
      rw [h, r2, r1, pow_two]
      group
  set h := (Model.rho1 ^ k)⁻¹ * b with hh
  have hN : h ∈ normalizer (Model.R0 : Set Pm) :=
    mul_mem (inv_mem (pow_mem hρN k)) hbN
  have hw0 : h * Model.w0 * h⁻¹ = Model.w0 := by
    calc h * Model.w0 * h⁻¹ = (Model.rho1 ^ k)⁻¹ * (b * Model.w0 * b⁻¹) * Model.rho1 ^ k := by
          rw [hh]; group
      _ = Model.w0 := by rw [hk]; group
  have hr1 : h * r1 * h⁻¹ = r1 ∨ h * r1 * h⁻¹ = r2 := by
    have hm := (mem_normalizer_iff.1 hN r1).1 r1_mem_R0
    rcases mem_R0_iff.1 hm with e | e | e | e
    · exact absurd (conj_eq_one_iff.1 e) r1_ne_one
    · refine absurd ?_ r1_ne_w0
      rw [← hw0] at e
      exact mul_left_cancel (mul_right_cancel e)
    · exact Or.inl e
    · exact Or.inr e
  have hbe : b = Model.rho1 ^ k * h := by rw [hh, mul_inv_cancel_left]
  rcases hr1 with e | e
  · left
    refine mem_inf.2 ⟨hb, ?_⟩
    have hC : h ∈ centralizer (Model.R0 : Set Pm) :=
      mem_centralizer_R0_iff'.2 ⟨mul_comm_of_conj hw0, mul_comm_of_conj e⟩
    rw [hbe, sup_comm]
    exact mul_mem_sup (pow_mem (mem_zpowers _) k) hC
  · right
    refine mem_inf.2 ⟨mul_mem tau0_mem_B0 hb, ?_⟩
    have hC : tau0 * h ∈ centralizer (Model.R0 : Set Pm) := by
      refine mem_centralizer_R0_iff'.2 ⟨mul_comm_of_conj ?_, mul_comm_of_conj ?_⟩
      · calc tau0 * h * Model.w0 * (tau0 * h)⁻¹ = tau0 * (h * Model.w0 * h⁻¹) * tau0⁻¹ := by group
          _ = Model.w0 := by rw [hw0, tau0_conj_w0]
      · calc tau0 * h * r1 * (tau0 * h)⁻¹ = tau0 * (h * r1 * h⁻¹) * tau0⁻¹ := by group
          _ = tau0 * Model.w0 * tau0⁻¹ * (tau0 * r1 * tau0⁻¹) := by rw [e, r2_eq]; group
          _ = r1 := by
            rw [tau0_conj_w0, tau0_conj_r1, r2_eq, ← mul_assoc, w0_mul_self, one_mul]
    have hτρ : tau0 * Model.rho1 ^ k = (Model.rho1 ^ k)⁻¹ * tau0 := by
      have e1 : tau0 * Model.rho1 ^ k * tau0⁻¹ = (Model.rho1 ^ k)⁻¹ := by
        rw [← conj_pow, tau0_conj_rho1, inv_pow]
      rw [← e1]
      group
    rw [hbe, ← mul_assoc, hτρ, mul_assoc, sup_comm]
    exact mul_mem_sup (inv_mem (pow_mem (mem_zpowers _) k)) hC

theorem conj_eq_mul_t1 {x : Pm} (hxρ : x * Model.rho1 = Model.rho1 * x)
    (hV : ∀ v ∈ V0, v * r1 = r1 * v → v * x = x * v) (hxτ : x * tau0 * x⁻¹ = tau0 * suzInv 1)
    {b : Pm} (hb : b ∈ Model.B0) (hb' : b ∉ B0Plus) : x * b * x⁻¹ = b * suzInv 1 := by
  have hτb : tau0 * b ∈ B0Plus := (mem_B0Plus_or_tau0_mul hb).resolve_left hb'
  have hc := commute_of_mem_B0Plus hxρ hV hτb
  have hb1 : b * suzInv 1 = suzInv 1 * b := comm_t1 (mem_inf.1 hb).1
  have ht : suzInv 1 * suzInv 1 = 1 := suzInv_sq (by norm_num : 1 < 4)
  calc x * b * x⁻¹ = (x * tau0 * x⁻¹)⁻¹ * (x * (tau0 * b) * x⁻¹) := by group
    _ = (tau0 * suzInv 1)⁻¹ * (tau0 * b) := by rw [hxτ, hc, mul_inv_cancel_right]
    _ = suzInv 1 * b := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht, mul_assoc, inv_mul_cancel_left]
    _ = b * suzInv 1 := hb1.symm

end Model

section Glue


variable {G : Type} [Group G] {M : Subgroup G}

theorem b0TwistAgree_remark {σ : M ≃* invE 1} {ψ : Model.NR0 →* G} (hB : B0Agree σ ψ)
    (x : ↥(invE 1)) (hxρ : (x : Pm) * Model.rho1 = Model.rho1 * x)
    (hV : ∀ v ∈ V0, v * r1 = r1 * v → v * (x : Pm) = x * v)
    (hxτ : (x : Pm) * tau0 * (x : Pm)⁻¹ = tau0 * suzInv 1) :
    B0TwistAgree (remark σ x) ψ := by
  refine ⟨fun b hbp hb hbN => ?_, fun b hbN hb hb' hbt => ?_⟩
  · have e : x * (⟨b, hb⟩ : ↥(invE 1)) * x⁻¹ = ⟨b, hb⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [commute_of_mem_B0Plus hxρ hV hbp, mul_inv_cancel_right]
    rw [hB b hb hbN, remark_symm_apply, e]
  · have hB0 : b ∈ Model.B0 := mem_inf.2 ⟨hb, (mem_inf.1 hbN).2⟩
    have hx1 : (x : Pm) * suzInv 1 = suzInv 1 * x := comm_t1 x.2
    have e : x * (⟨b * suzInv 1, hbt⟩ : ↥(invE 1)) * x⁻¹ = ⟨b, hb⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      calc (x : Pm) * (b * suzInv 1) * (x : Pm)⁻¹ =
            ((x : Pm) * b * (x : Pm)⁻¹) * ((x : Pm) * suzInv 1 * (x : Pm)⁻¹) := by group
        _ = b * suzInv 1 * suzInv 1 := by
            rw [conj_eq_mul_t1 hxρ hV hxτ hB0 hb', hx1, mul_inv_cancel_right]
        _ = b := by rw [mul_assoc, suzInv_sq (by norm_num : 1 < 4), mul_one]
    rw [hB b hb hbN, remark_symm_apply, e]

end Glue

end CFSG.Sporadic.SuzRecog.MixedCell
