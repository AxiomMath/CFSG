module

public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.Quasithin.Vol2.Ch11SecE43Out

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner centerQuotientOuterHom
  centerQuotient_outer_injective)
open scoped commutatorElement

theorem outer_sl2_mul_comm (K : Type) [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    (a b : Outer (Matrix.SpecialLinearGroup (Fin 2) K)) : a * b = b * a := by
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  apply centerQuotient_outer_injective
  rw [map_mul, map_mul]
  exact CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm K _ _

section Induced

variable {X : Type*} [Group X] {S : Type*} [Group S] (ψ : X →* S)

@[expose] noncomputable def quotKerAut (hF : ∀ α : MulAut X, ψ.ker.map α.toMonoidHom = ψ.ker) :
    MulAut X →* MulAut (X ⧸ ψ.ker) where
  toFun α := QuotientGroup.congr _ _ α (hF α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

@[expose] noncomputable def inducedAut (hF : ∀ α : MulAut X, ψ.ker.map α.toMonoidHom = ψ.ker)
    (hψ : Function.Surjective ψ) : MulAut X →* MulAut S :=
  (MulAut.congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).toMonoidHom.comp
    (quotKerAut ψ hF)

theorem inducedAut_apply (hF : ∀ α : MulAut X, ψ.ker.map α.toMonoidHom = ψ.ker)
    (hψ : Function.Surjective ψ) (α : MulAut X) (x : X) :
    inducedAut ψ hF hψ α (ψ x) = ψ (α x) := by
  have h1 : QuotientGroup.quotientKerEquivOfSurjective ψ hψ (QuotientGroup.mk x) = ψ x := rfl
  simp only [inducedAut, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply]
  rw [← h1, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
  rfl

theorem exists_conj_comm (hF : ∀ α : MulAut X, ψ.ker.map α.toMonoidHom = ψ.ker)
    (hψ : Function.Surjective ψ) (hS : ∀ a b : Outer S, a * b = b * a) (α β : MulAut X) :
    ∃ x : X, ∀ y : X, ψ ((α * β * α⁻¹ * β⁻¹) y) = ψ (x * y * x⁻¹) := by
  set Γ := inducedAut ψ hF hψ
  have h1 : (QuotientGroup.mk (Γ (α * β * α⁻¹ * β⁻¹)) : Outer S) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hS (QuotientGroup.mk (Γ α))]
    group
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨x, rfl⟩ := hψ g
  refine ⟨x, fun y => ?_⟩
  rw [← inducedAut_apply ψ hF hψ, ← hg, MulAut.conj_apply, map_mul, map_mul, map_inv]

end Induced

theorem out2Closed_of_comm_comm {X : Type*} [Group X] [Finite X]
    (h : ∀ σ τ ρ : MulAut X, σ * τ * σ⁻¹ * τ⁻¹ * ρ * (σ * τ * σ⁻¹ * τ⁻¹)⁻¹ * ρ⁻¹ ∈
      (MulAut.conj : X →* MulAut X).range) :
    SecE.Out2Closed X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range with hN
  have : N.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal X
  have hc : ∀ a b : MulAut X ⧸ N, ⁅a, b⁆ ∈ Subgroup.center (MulAut X ⧸ N) := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H σ =>
      induction b using QuotientGroup.induction_on with
      | H τ =>
        rw [Subgroup.mem_center_iff]
        intro c
        induction c using QuotientGroup.induction_on with
        | H ρ =>
          rw [commutatorElement_def, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv,
            ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
            ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          set c := σ * τ * σ⁻¹ * τ⁻¹
          have h1 : c * ρ⁻¹ * c⁻¹ * ρ⁻¹⁻¹ ∈ N := h σ τ ρ⁻¹
          have e : (ρ * c)⁻¹ * (c * ρ) = c⁻¹ * (c * ρ⁻¹ * c⁻¹ * ρ⁻¹⁻¹)⁻¹ * c⁻¹⁻¹ := by group
          rw [e]
          exact Subgroup.Normal.conj_mem ‹_› _ (N.inv_mem h1) c⁻¹
  have hnil : Group.IsNilpotent (MulAut X ⧸ N) := by
    refine ⟨⟨2, eq_top_iff.mpr fun a _ => ?_⟩⟩
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro b
    rw [Subgroup.upperCentralSeries_one]
    exact hc a b
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (MulAut X ⧸ N)))
  have hSn : (S : Subgroup (MulAut X ⧸ N)).Normal := inferInstance
  refine ⟨(S : Subgroup (MulAut X ⧸ N)).comap (QuotientGroup.mk' N),
    Subgroup.Normal.comap hSn _, fun x hx => ?_, fun α hα => ?_, fun α => ?_⟩
  · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  · obtain ⟨k, hk⟩ := S.isPGroup' ⟨QuotientGroup.mk' N α, hα⟩
    refine ⟨k, (QuotientGroup.eq_one_iff _).mp ?_⟩
    rw [QuotientGroup.mk_pow]
    exact congrArg Subtype.val hk
  · refine ⟨(S : Subgroup (MulAut X ⧸ N)).index, ?_, ?_⟩
    · rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      exact S.not_dvd_index
    · rw [Subgroup.mem_comap, map_pow]
      exact Subgroup.pow_index_mem _ _

end CFSG.Quasithin.Vol2.Ch11.O6
