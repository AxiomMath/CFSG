module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaFlag
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaDickson
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUStd
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LieType.BorelTits.Families

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions CFSG.Assembly.LowTwoRank

variable (n : ℕ) (K : Type) [Field K]

@[expose] noncomputable def plusForm : QuadForm K (Fin n ⊕ Fin n → K) :=
  toQuadForm (quadPlus n K) (nondegenerate_polarBilin_quadPlus n K)

@[expose] noncomputable def plusRep :
    spinGroup (quadPlus n K) →* Module.End K (Fin n ⊕ Fin n → K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (spinAction (quadPlus n K))

variable {n K}

theorem plusRep_apply (x : spinGroup (quadPlus n K)) (v : Fin n ⊕ Fin n → K) :
    plusRep n K x v = spinAction (quadPlus n K) x v :=
  rfl

theorem plusForm_Q (v : Fin n ⊕ Fin n → K) : (plusForm n K).Q v = quadPlus n K v :=
  rfl

theorem plusForm_β (u v : Fin n ⊕ Fin n → K) :
    (plusForm n K).polar.β u v = polar (quadPlus n K) u v :=
  rfl

theorem quadPlusPolar_eq (u v : Fin n ⊕ Fin n → K) :
    quadPlusPolar n K u v = polar (quadPlus n K) u v := by
  rw [polar_quadPlus]
  rfl

theorem plusForm_polar [CharP K 2] : (plusForm n K).polar = spForm n K := by
  have hβ : (plusForm n K).polar.β = (spForm n K).β := by
    funext u v
    rw [plusForm_β, polar_quadPlus, spForm_β, dotProduct_spJ_mulVec, sub_eq_add_neg,
      CharTwo.neg_eq, dotProduct, dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.comp_apply]
    ring
  have hσ : (plusForm n K).polar.σ = (spForm n K).σ := rfl
  rcases h1 : (plusForm n K).polar with ⟨σ₁, β₁, _, _, _, _, _, _⟩
  rcases h2 : spForm n K with ⟨σ₂, β₂, _, _, _, _, _, _⟩
  rw [h1, h2] at hβ hσ
  simp only at hβ hσ
  subst hβ hσ
  rfl

theorem plusRep_Q (x : spinGroup (quadPlus n K)) (v : Fin n ⊕ Fin n → K) :
    (plusForm n K).Q (plusRep n K x v) = (plusForm n K).Q v :=
  map_spinAction _ x v

theorem plusRep_injective [CharP K 2] : Function.Injective (plusRep n K) := by
  intro x y hxy
  refine RootCentOmega.spinAction_quadPlus_injective (LinearEquiv.ext fun v => ?_)
  have := congrArg (fun f : Module.End K (Fin n ⊕ Fin n → K) => f v) hxy
  exact this

theorem isIsometric_plusRep : IsIsometric (plusForm n K).polar (plusRep n K) :=
  (plusForm n K).isIsometric_of_Q plusRep_Q

theorem plusForm_eichler_apply {x y : Fin n ⊕ Fin n → K} (hx : quadPlus n K x = 0)
    (hxy : polar (quadPlus n K) x y = 0) (v : Fin n ⊕ Fin n → K) :
    (plusForm n K).eichler x y v = eichler (quadPlus n K) x y v := by
  rw [eichler_apply hx hxy, QuadForm.eichler_apply, plusForm_β, plusForm_β, plusForm_Q,
    polar_comm (quadPlus n K) v x, polar_comm (quadPlus n K) v y]
  module

theorem exists_plusRep_eq_eichler (hn : 3 ≤ n) (x y : Fin n ⊕ Fin n → K)
    (hx : (plusForm n K).Q x = 0) (hxy : (plusForm n K).polar.β x y = 0) :
    ∃ h : spinGroup (quadPlus n K), ∀ v, plusRep n K h v = (plusForm n K).eichler x y v := by
  have hmem : eichler (quadPlus n K) x y ∈ (spinAction (quadPlus n K)).range := by
    rw [range_spinAction_quadPlus hn]
    exact eichler_mem_elementaryGroup _ x y
  obtain ⟨h, hh⟩ := hmem
  refine ⟨h, fun v => ?_⟩
  rw [plusRep_apply, hh, plusForm_eichler_apply hx hxy]

theorem noQuotientReflection_plusRep (hn : 3 ≤ n) :
    NoQuotientReflection (plusForm n K) (plusRep n K) := by
  intro h Z hZ a ha hQa hrefl
  have hmem : spinMatrix (quadPlus n K) h ∈ StatedOmega (StatedQuadPlus n K) := by
    rw [← range_spinMatrix_quadPlus hn]
    exact ⟨h, rfl⟩
  refine not_reflection_on_quotient_of_mem_statedOmega_quadPlus n hmem (Z := Z) (a := a)
    (fun z hz => ?_) (fun z hz => ?_) ?_ fun v hv => ?_
  · rw [← coe_quadPlus]
    exact hZ z hz
  · rw [quadPlusPolar_eq]
    exact ha z hz
  · rw [← coe_quadPlus]
    exact hQa
  · rw [spinMatrix_mulVec, ← coe_quadPlus, quadPlusPolar_eq]
    exact hrefl v fun z hz => by rw [plusForm_β, ← quadPlusPolar_eq]; exact hv z hz

theorem exists_finrank_three_quadPlus (hn : 3 ≤ n) :
    ∃ T : Submodule K (Fin n ⊕ Fin n → K), finrank K T = 3 ∧ ∀ x ∈ T, quadPlus n K x = 0 :=
  ⟨CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag n K 3,
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.finrank_flag hn,
    fun _ hx => CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.quadPlus_eq_zero_of_mem_flag hx⟩

theorem exists_spinAction_eq_of_mem_omegaGroup_plus [Finite K] [CharP K 2] (hn : 3 ≤ n)
    {g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hg : g ∈ omegaGroup (quadPlus n K) (nondegenerate_polarBilin_quadPlus n K)) :
    ∃ h : spinGroup (quadPlus n K), spinAction (quadPlus n K) h = g := by
  have h1 := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived
    (nondegenerate_polarBilin_quadPlus n K) (exists_finrank_three_quadPlus hn) hg
  rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadPlus hn,
    ← range_spinAction_quadPlus hn] at h1
  exact h1

theorem finite_spinGroup_quadPlus [Finite K] [CharP K 2] : Finite (spinGroup (quadPlus n K)) := by
  have : Finite ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :=
    Finite.of_injective (fun e : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) =>
      (e : (Fin n ⊕ Fin n → K) → (Fin n ⊕ Fin n → K))) fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  exact Finite.of_injective _ RootCentOmega.spinAction_quadPlus_injective

end GGOppRadOmega

end CFSG.StandardType
