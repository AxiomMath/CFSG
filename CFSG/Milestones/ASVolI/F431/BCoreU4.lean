module

public import CFSG.Milestones.ASVolI.F431.BCoreGen
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.H13.U4ParOuter

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Quasithin.H13.U4Par
open scoped commutatorElement

section U4Model

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem burnsideF4m_U4_inr_mem (σ : K ≃+* K) :
    (SemidirectProduct.inr σ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0 :=
  ⟨1, one_ne_zero, map_one _, by
    rw [SemidirectProduct.left_inr]
    simp⟩

@[expose] noncomputable def burnsideF4m_U4_fieldElt (σ : K ≃+* K) (g : hypSU h 2 0) :
    hypSU h 2 0 :=
  ⟨glAut σ (g : GL (HypIndex 2 0) K), by
    have := conj_mem_hypSU (burnsideF4m_U4_inr_mem h σ) g
    simpa using this⟩

theorem burnsideF4m_U4_coe_fieldElt (σ : K ≃+* K) (g : hypSU h 2 0) :
    ((burnsideF4m_U4_fieldElt h σ g : hypSU h 2 0) : GL (HypIndex 2 0) K) =
      glAut σ (g : GL (HypIndex 2 0) K) := rfl

@[expose] noncomputable def burnsideF4m_U4_fieldAut : (K ≃+* K) →* MulAut (hypSU h 2 0) where
  toFun σ :=
    { toFun := burnsideF4m_U4_fieldElt h σ
      invFun := burnsideF4m_U4_fieldElt h σ⁻¹
      left_inv := fun g => Subtype.ext (by
        rw [burnsideF4m_U4_coe_fieldElt, burnsideF4m_U4_coe_fieldElt, ← MulAut.mul_apply,
          ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun g => Subtype.ext (by
        rw [burnsideF4m_U4_coe_fieldElt, burnsideF4m_U4_coe_fieldElt, ← MulAut.mul_apply,
          ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun g g' => Subtype.ext (by
        rw [burnsideF4m_U4_coe_fieldElt, Subgroup.coe_mul, Subgroup.coe_mul, map_mul,
          burnsideF4m_U4_coe_fieldElt, burnsideF4m_U4_coe_fieldElt]) }
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    show glAut 1 (g : GL (HypIndex 2 0) K) = (g : GL (HypIndex 2 0) K)
    rw [map_one, MulAut.one_apply])
  map_mul' σ τ := MulEquiv.ext fun g => Subtype.ext (by
    show glAut (σ * τ) (g : GL (HypIndex 2 0) K) = glAut σ (glAut τ (g : GL (HypIndex 2 0) K))
    rw [map_mul, MulAut.mul_apply])

theorem burnsideF4m_U4_normalForm (θ : MulAut (hypSU h 2 0)) :
    ∃ (a : hypSU h 2 0) (σ : K ≃+* K), θ = MulAut.conj a * burnsideF4m_U4_fieldAut h σ := by
  let π := hypProj h 2 0
  let θ' : MulAut (hypPSU h 2 0) :=
    ((hypSUEquivPSU h).symm.trans θ).trans (hypSUEquivPSU h)
  have hπ : ∀ g, hypSUEquivPSU h g = π g := fun g => rfl
  have hθ' : ∀ g, θ' (π g) = π (θ g) := by
    intro g
    change hypSUEquivPSU h (θ ((hypSUEquivPSU h).symm (π g))) = π (θ g)
    rw [← hπ g, MulEquiv.symm_apply_apply, hπ]
  have hr : 1 ≤ 2 := by norm_num
  have hε : 0 ≤ 1 := by norm_num
  have hn4 : 3 ≤ 2 * 2 + 0 := by norm_num
  obtain ⟨x₀, hx₀⟩ := semilinearAutHom_surjective_of_admissible h hr hε hn4
    (fun h' => by omega) θ'
  obtain ⟨x₁, hx₁, -, hU⟩ := exists_unitary_rep h hr hε hn4 x₀
  rw [hx₀] at hx₁
  set A := (x₁ : SemiGL (HypIndex 2 0) K).left with hA
  set σ := (x₁ : SemiGL (HypIndex 2 0) K).right with hσ
  have hθA : ∀ g : hypSU h 2 0, ((θ g : hypSU h 2 0) : GL (HypIndex 2 0) K) =
      A * glAut σ (g : GL (HypIndex 2 0) K) * A⁻¹ := by
    intro g
    have h1 := semilinearAutHom_apply h hr hε x₁ g
    rw [hx₁, hθ'] at h1
    have h2 := hypProj_injective h h1
    exact congrArg Subtype.val h2
  obtain ⟨a, εu, hAa⟩ := exists_su_rep h hU
  have hc : ∀ X : GL (HypIndex 2 0) K, GeneralLinearGroup.scalar (HypIndex 2 0) εu * X =
      X * GeneralLinearGroup.scalar (HypIndex 2 0) εu := fun X => by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, mul_comm]
  refine ⟨a, σ, MulEquiv.ext fun g => Subtype.ext ?_⟩
  rw [hθA g, hAa]
  show _ = (a : GL (HypIndex 2 0) K) * glAut σ (g : GL (HypIndex 2 0) K) *
    (a : GL (HypIndex 2 0) K)⁻¹
  have hcen : ∀ Y : GL (HypIndex 2 0) K, GeneralLinearGroup.scalar (HypIndex 2 0) εu * Y *
      (GeneralLinearGroup.scalar (HypIndex 2 0) εu)⁻¹ = Y := fun Y => by
    rw [hc Y, mul_assoc, mul_inv_cancel, mul_one]
  calc GeneralLinearGroup.scalar (HypIndex 2 0) εu * (a : GL (HypIndex 2 0) K) *
        glAut σ (g : GL (HypIndex 2 0) K) *
        (GeneralLinearGroup.scalar (HypIndex 2 0) εu * (a : GL (HypIndex 2 0) K))⁻¹ =
      GeneralLinearGroup.scalar (HypIndex 2 0) εu * ((a : GL (HypIndex 2 0) K) *
        glAut σ (g : GL (HypIndex 2 0) K) * (a : GL (HypIndex 2 0) K)⁻¹) *
        (GeneralLinearGroup.scalar (HypIndex 2 0) εu)⁻¹ := by group
    _ = _ := hcen _

theorem burnsideF4m_U4_out_comm (α β : MulAut (hypSU h 2 0)) :
    ⁅α, β⁆ ∈ (MulAut.conj : hypSU h 2 0 →* MulAut (hypSU h 2 0)).range := by
  have := h.finite
  exact burnsideF4m_out_comm_of_normalForm (burnsideF4m_U4_fieldAut h)
    (CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K) (burnsideF4m_U4_normalForm h) α β

theorem burnsideF4m_U4_P_center_le (hm : 2 ≤ m) :
    centerOf (perfectCore (parP h)) ≤ ctr (oPPrime 2 (parP h)) := by
  have hOP : oPPrime 2 (parP h) ≤ perfectCore (parP h) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyP, k, hk⟩
    exact mem_perfectCore_parP_of_pow h hm hyP (k := k) (by rw [← hk]; exact pow_orderOf_eq_one y)
  rintro x ⟨hxC, hxc⟩
  have hxP : x ∈ parP h := perfectCore_le _ hxC
  have hxH := perfectCore_parP_le_parH h hxC
  have hxZ : x ∈ zRad h := burnsideF4gU4Inv_mem_zRad_of_comm h hxP hxH.2.1 fun g hg =>
    (Subgroup.mem_centralizer_iff.mp hxc g (radQ_le_perfectCore h hm hg)).symm
  have hx2 : x ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    exact burnsideF4gU4Inv_zRad_sq h hxZ
  refine ⟨burnsideF4gU4Inv_mem_oPPrime hxP hx2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  exact Subgroup.mem_centralizer_iff.mp hxc g (hOP hg)

theorem burnsideF4m_U4_P2_center_eq_bot (hm : 2 ≤ m) :
    centerOf (perfectCore (parP2 h)) = ⊥ := by
  have := h.charP
  rw [eq_bot_iff]
  rintro x ⟨hxC, hxc⟩
  have hxH : x ∈ parH2 h := perfectCore_parP2_le_parH2 h hxC
  have hcomm : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      lev2Hom h A * x = x * lev2Hom h A := fun A =>
    Subgroup.mem_centralizer_iff.mp hxc _ (lev2Hom_range_le_perfectCore h ⟨A, rfl⟩)
  have hcen : rho2F h ⟨x, hxH⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro A
    have e : (⟨lev2Hom h A, lev2Hom_le_parH2 h ⟨A, rfl⟩⟩ : parH2 h) * ⟨x, hxH⟩ =
        ⟨x, hxH⟩ * ⟨lev2Hom h A, lev2Hom_le_parH2 h ⟨A, rfl⟩⟩ := Subtype.ext (hcomm A)
    have e2 := congrArg (rho2F h) e
    rw [map_mul, map_mul, rho2F_lev2Hom] at e2
    exact e2
  rw [center_sl2_eq_bot_of_charTwo K, Subgroup.mem_bot] at hcen
  have hrho : rho2 h x = 1 := by
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K))
      hcen
    exact this
  have hxQ : x ∈ radQ2 h := mem_radQ2_of_rho2 h hxH.1 hrho
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_torus_param h hm
  set d : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![c, 0; 0, c⁻¹], by simp [det_fin_two_of, hc0]⟩ with hd
  exact Subgroup.mem_bot.2 (eq_one_of_comm_lev2 h hc0 hc1 hc2 (d := d) rfl hxQ (hcomm d).symm)

end U4Model

theorem burnsideF4m_U4_chart {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .U4 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K) (Φ : hypSU h 2 0 ≃* ↥Gp),
      Gp ⊓ M₁ = (parP h).map (Gp.subtype.comp Φ.toMonoidHom) ∧
      Gp ⊓ M₂ = (parP2 h).map (Gp.subtype.comp Φ.toMonoidHom) := by
  obtain ⟨marking, hpts, hlines, -, -⟩ := burnsideF4gU4Inv_marking hyp.chart
  obtain ⟨Φ, e0, e1, -, -⟩ := burnsideF4gU4Inv_equiv_roots marking
  refine ⟨marking.field, inferInstance, burnsideF4gU4_fieldData marking, Φ, ?_, ?_⟩
  · rw [hyp.chart_matches.2.1, hpts, e0, Subgroup.map_map]
  · rw [hyp.chart_matches.2.2, hlines, e1, Subgroup.map_map]

theorem burnsideF4m_core12_U4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    (∀ x ∈ centerOf (perfectCore M₁), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) ∧
    (∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 →
      GLKind.U4 = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) := by
  haveI := hyp.normal
  obtain ⟨K, fK, h, Φ, h1, h2⟩ := burnsideF4m_U4_chart hyp.toHypF_4_4g
  have hc : ∀ a b : E, ⁅a, b⁆ ∈ Gp := burnsideF4m_commutator_mem_of_out hyp.centralizer_trivial
    (burnsideF4m_out_transport Φ (burnsideF4m_U4_out_comm h))
  have hφ : Function.Injective (Gp.subtype.comp Φ.toMonoidHom) :=
    Gp.subtype_injective.comp Φ.injective
  refine ⟨burnsideF4m_core1_of_model hc _ hφ h1 (burnsideF4m_U4_P_center_le h hf), ?_⟩
  intro x hx hx1 _
  rw [burnsideF4m_centerOf_perfectCore_eq_bot_of_model hc _ hφ h2
    (burnsideF4m_U4_P2_center_eq_bot h hf)] at hx
  exact absurd (Subgroup.mem_bot.1 hx) hx1

end CFSG.ASVolI
