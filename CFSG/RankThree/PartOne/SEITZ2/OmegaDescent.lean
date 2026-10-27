module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaTail
public import CFSG.RankThree.PartOne.S11c.Sec66Orth
public import CFSG.RankThree.PartOne.SEITZ2.OmegaSetup

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.SignalizerFunctorTheorem.CatalogBridge (orthMinus_hyps)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadMinus StatedClassicalModel)

noncomputable abbrev omegaQuad (K : Type) [Field K] (b c : K) :
    QuadraticForm K (Fin (2 * 4) → K) :=
  coordinateQuadMinus 4 K (by norm_num) b c

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {σ : K ≃+* K} {p f₀ : ℕ} {b c : k}

theorem exists_conj_fieldAutT (h : OmegaSetup K k σ p f₀ b c) {T : Type} [Group T] [Finite T]
    (e : T ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K (b : K) (c : K)))) {α : MulAut T}
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) :
    ∃ d ∈ (linearConjugationHom (omegaQuad K (b : K) (c : K))).range,
      ∃ (σ' : K ≃+* K) (hσ' : orderOf σ' = p),
        MulAut.congr (coordinateMinusWitnessEquiv K (by norm_num) (b : K) (c : K) e) α =
          d * fieldAutT (omegaQuad K (b : K) (c : K)) σ' (h.quad_invariant (by norm_num) hσ') *
            d⁻¹ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 := h.five_le
  have hp2 := h.ne_two
  have hp3 : 3 < p := by omega
  have : CharP K 2 := h.charP
  have hK : Nat.card K = 2 ^ (p * f₀) := h.card_K'
  have hirrK := h.irr_K
  have hn1 : 1 ≤ 4 := by norm_num
  have hC : StatedClassicalModel T .POmegaMinus 4 2 (p * f₀) :=
    ⟨⟨Nat.prime_two, Nat.mul_pos hp.pos h.one_le, le_rfl⟩, K, inferInstance, inferInstance, hK,
      b, c, hirrK, ⟨e⟩⟩
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp (fun h1 => hαinn (h1 ▸ (innerAut T).one_mem))
  obtain ⟨-, -, hidx⟩ := orthMinus_hyps hC K hK (b : K) (c : K) hirrK hn1 e
  obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_minus hC K hK (b : K) (c : K) hirrK e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinateMinusWitnessEquiv K hn1 (b : K) (c : K) e)
      α := ⟨_, rfl⟩
  have ha : orderOf a = p := by
    rw [ha_def]
    exact (orderOf_congr _ α).trans hαord
  have hainn : a ∉
      innerAut (matrixProjectiveDerived (coordinateQuadMinus 4 K hn1 (b : K) (c : K))) := by
    rw [ha_def]
    exact fun h => hαinn ((mem_innerAut_congr _ α).mp h)
  have haE : a ∈ matrixProjectiveImage (coordinateQuadMinus 4 K hn1 (b : K) (c : K)) :=
    orth_mem_image_of_orderOf _ hidx hp hp3 ha
  have hap : a ^ p = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have haD : a ∉ (linearConjugationHom (coordinateQuadMinus 4 K hn1 (b : K) (c : K))).range :=
    orth_not_mem_linearRange_of_not_inner _ hnd hS3 hp hp2 hap hainn
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent T .POmegaMinus
    (Or.inr (Or.inr rfl)) 4 2 (p * f₀) p hC hp hp3 hp2 hn1 K hK (b : K) (c : K) hirrK e a haE haD ha
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, V, cc, Q₀, hVκ, hVr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, hS₀, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', hSQ, hSS₀, hSA, Θ, hΘ1, g', hg'l, hg'r, hΘ⟩ := hT
  have hσV : orderOf V.val.right = p := by rw [hVr]; exact hord'
  have hfixV := h.fixed_of_orderOf hσV
  have hσk' : ∀ x, x ∈ semilinearFixedSubfield V.val.right ↔ V.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  have hb'k : (b' : K) ∈ k := (hfixV _).2 ((hσk' _).1 b'.2)
  have hc'k : (c' : K) ∈ k := (hfixV _).2 ((hσk' _).1 c'.2)
  have hirrkK : ∀ s ∈ k, s ^ 2 + (b : K) * s + (c : K) ≠ 0 := fun s hs hz =>
    h.irr ⟨s, hs⟩ (Subtype.ext (by simpa using hz))
  have hirr'kK : ∀ s ∈ k, s ^ 2 + (b' : K) * s + (c' : K) ≠ 0 := by
    intro s hs hz
    have hsV : s ∈ fixedField V.val := (hσk' s).2 ((hfixV s).1 hs)
    exact hirr' ⟨s, hsV⟩ (Subtype.ext (by simpa using hz))
  obtain ⟨μ, hμk, hμQ⟩ := exists_tail_isometry k hn1 b.2 c.2 hb'k hc'k hirrkK hirr'kK
  have hμσ : glFieldAut (Fin (2 * 4)) K V.val.right μ = μ := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact (hfixV _).1 (hμk i j)
  set S' : GL (Fin (2 * 4)) K := μ * S with hS'def
  have hS'Q : ∀ v, omegaQuad K (b : K) (c : K) (S'.val *ᵥ v) =
      ν' * omegaQuad K (b : K) (c : K) v := by
    intro v
    rw [hS'def, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hμQ _).trans (hSQ v)
  have hS'A : S' * V.val.left = glFieldAut (Fin (2 * 4)) K V.val.right S' := by
    rw [hS'def, mul_assoc, hSA, map_mul, hμσ]
  have hS'inv : ∀ v, omegaQuad K (b : K) (c : K) ((S'⁻¹ : GL (Fin (2 * 4)) K).val *ᵥ v) =
      ((ν'⁻¹ : Kˣ) : K) * omegaQuad K (b : K) (c : K) v := by
    intro v
    have h1 := hS'Q ((S'⁻¹ : GL (Fin (2 * 4)) K).val *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h1
    rw [h1, ← mul_assoc, Units.inv_mul, one_mul]
  have hQσV := h.quad_invariant (n := 4) hn1 hσV
  let Dp : similarityPairs (omegaQuad K (b : K) (c : K)) :=
    ⟨⟨S'⁻¹, 1⟩, ν'⁻¹, fun v => by
      rw [coordinateSemilinearMap_apply]
      have := hS'inv v
      simpa using this⟩
  have hDplin : Dp ∈ linearSimilarityPairs (omegaQuad K (b : K) (c : K)) :=
    (mem_linearSimilarityPairs_iff _ Dp).2 rfl
  have hVeq : V = Dp * fieldPair (omegaQuad K (b : K) (c : K)) V.val.right hQσV * Dp⁻¹ := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · have h1 : V.val.left = S'⁻¹ * glFieldAut (Fin (2 * 4)) K V.val.right S' := by
        rw [← hS'A]
        group
      rw [h1]
      simp [Dp, fieldPair]
    · simp [Dp, fieldPair]
  refine ⟨matrixProjectiveConjugationHom (omegaQuad K (b : K) (c : K)) Dp,
    ⟨⟨Dp, hDplin⟩, rfl⟩, V.val.right, hσV, ?_⟩
  have hκ := congrArg (matrixProjectiveConjugationHom (omegaQuad K (b : K) (c : K))) hVeq
  rw [map_mul, map_mul, map_inv] at hκ
  rw [← ha_def, ← hVκ]
  exact hκ

end CFSG.RankThree.PartOne.SEITZ2
