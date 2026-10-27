module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaDescent

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.SignalizerFunctorTheorem.CatalogBridge (orthMinus_hyps)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadMinus StatedClassicalModel)

theorem exists_rational_model {G : Type} [Group G] [Finite G] {p f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hM : StatedClassicalModel G .POmegaMinus 4 2 f)
    {α : MulAut G} (hαp : α ^ p = 1) (hαinn : α ∉ innerAut G) :
    ∃ (f₀ : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (k : Subfield K) (σ : K ≃+* K)
      (b c : k), f = p * f₀ ∧ OmegaSetup K k σ p f₀ b c ∧
        Nonempty (G ≃* matrixProjectiveDerived (omegaQuad K (b : K) (c : K))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  have hn1 : 1 ≤ 4 := by norm_num
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp (fun h1 => hαinn (h1 ▸ (innerAut G).one_mem))
  have hf1 : 1 ≤ f := hM.1.2.1
  obtain ⟨-, K, _, _, hK, b₁, c₁, hirr₁, ⟨e⟩⟩ := id hM
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, -, hidx⟩ := orthMinus_hyps hM K hK b₁ c₁ hirr₁ hn1 e
  obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_minus hM K hK b₁ c₁ hirr₁ e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinateMinusWitnessEquiv K hn1 b₁ c₁ e) α :=
    ⟨_, rfl⟩
  have ha : orderOf a = p := by
    rw [ha_def]
    exact (orderOf_congr _ α).trans hαord
  have hainn : a ∉ innerAut (matrixProjectiveDerived (coordinateQuadMinus 4 K hn1 b₁ c₁)) := by
    rw [ha_def]
    exact fun h => hαinn ((mem_innerAut_congr _ α).mp h)
  have haE : a ∈ matrixProjectiveImage (coordinateQuadMinus 4 K hn1 b₁ c₁) :=
    orth_mem_image_of_orderOf _ hidx hp hp3 ha
  have hap : a ^ p = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have haD : a ∉ (linearConjugationHom (coordinateQuadMinus 4 K hn1 b₁ c₁)).range :=
    orth_not_mem_linearRange_of_not_inner _ hnd hS3 hp hp2 hap hainn
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent G .POmegaMinus
    (Or.inr (Or.inr rfl)) 4 2 f p hM hp hp3 hp2 hn1 K hK b₁ c₁ hirr₁ e a haE haD ha
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, V, cc, Q₀, hVκ, hVr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, hS₀, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', hSQ, hSS₀, hSA, Θ, hΘ1, g', hg'l, hg'r, hΘ⟩ := hT
  obtain ⟨f₀, rfl⟩ := hpf
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf1
      omega
    · exact h0
  have hfdiv : p * f₀ / p = f₀ := Nat.mul_div_cancel_left f₀ hp.pos
  rw [hfdiv] at hcard
  have hσV : orderOf V.val.right = p := by rw [hVr]; exact hord'
  have hσk : ∀ x, x ∈ semilinearFixedSubfield V.val.right ↔ V.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  have hcard' : Nat.card (semilinearFixedSubfield V.val.right) = 2 ^ f₀ := by
    rw [hVr]
    exact hcard
  exact ⟨f₀, K, inferInstance, inferInstance, semilinearFixedSubfield V.val.right, V.val.right,
    b', c', rfl, ⟨hp, hp5, hf₀, hcard', by rw [mul_comm]; exact hK, hσV, hσk, hirr'⟩,
    ⟨(coordinateMinusWitnessEquiv K hn1 b₁ c₁ e).trans Θ⟩⟩

end CFSG.RankThree.PartOne.SEITZ2
