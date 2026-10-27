module

public import CFSG.RankThree.PartOne.S11c.Sec66Orth

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedClassicalModel StatedLieAdmissible)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveImage coordinateFieldMap)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus plusIndexEquiv minusIndexEquiv
    coordinatePlusWitnessEquiv coordinateMinusWitnessEquiv coordinate_model_witness_plus
    coordinate_model_witness_minus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  (IsExtension fieldAutT inclEquiv subfieldDerivedImage subfieldFixedGroup SubfieldSetup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (orthPlus_hyps orthMinus_hyps congr_eq_fieldAutT
  NonLocalized)

theorem exists_orth_model_plus {T : Type} [Group T] [Finite T] {p f₀ n : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hM : LieModel T .POmegaPlus n 2 (p * f₀)) (α : MulAut T)
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (k : Subfield K) (σ : K ≃+* K)
      (Q₀ : QuadraticForm k (Fin (2 * n) → k)) (Q : QuadraticForm K (Fin (2 * n) → K))
      (hS : SubfieldSetup k Q₀ Q σ p) (ψ : T ≃* matrixProjectiveDerived Q),
      Nat.card K = 2 ^ (p * f₀) ∧ 4 ≤ n ∧ MulAut.congr ψ α = fieldAutT Q σ hS.hQσ := by
  have hC : StatedClassicalModel T .POmegaPlus n 2 (p * f₀) :=
    (lieModel_classical_iff (by decide)).mp hM
  have : Fact p.Prime := ⟨hp⟩
  have hn4 : 4 ≤ n := hC.1.2.2
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hαord : orderOf α = p := orderOf_eq_prime hαp (fun h1 => hαinn (h1 ▸ (innerAut T).one_mem))
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hC
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := p * f₀) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, -, hidx⟩ := orthPlus_hyps hC K hK e
  obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_plus hC K hK e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinatePlusWitnessEquiv K e) α := ⟨_, rfl⟩
  have ha : orderOf a = p := by
    rw [ha_def]
    exact (orderOf_congr _ α).trans hαord
  have hainn : a ∉ innerAut (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    rw [ha_def]
    exact fun h => hαinn ((mem_innerAut_congr _ α).mp h)
  have haE : a ∈ matrixProjectiveImage (coordinateQuadPlus n K) :=
    orth_mem_image_of_orderOf _ hidx hp hp3 ha
  have hap : a ^ p = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have haD : a ∉ (linearConjugationHom (coordinateQuadPlus n K)).range :=
    orth_not_mem_linearRange_of_not_inner _ hnd hS3 hp hp2 hap hainn
  have hdesc := CFSG.RankThree.PartOne.orthogonal_prime_semilinear_actual_fixed_form_descent T
    .POmegaPlus (Or.inr (Or.inl rfl)) n 2 (p * f₀) p hC hp hp3 hp2 K hK e a haE haD ha
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, V, cc, Q₀, hVκ, hVr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hfdiv : p * f₀ / p = f₀ := Nat.mul_div_cancel_left f₀ hp.pos
  rw [hfdiv] at hcard
  have hord'' : orderOf V.val.right = p := by
    rw [hVr]
    exact hord'
  have hK' : Nat.card K = 2 ^ (f₀ * p) := by rw [mul_comm]; exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield V.val.right ↔ V.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  have hS := CFSG.RankThree.PartOne.KCOrthogonalSubfield.subfieldSetup_plus
    (semilinearFixedSubfield V.val.right) hσk hp hp2 hord'' (by omega : 3 ≤ n)
  exact ⟨K, inferInstance, inferInstance, inferInstance, semilinearFixedSubfield V.val.right,
    V.val.right, _, _, hS, (coordinatePlusWitnessEquiv K e).trans Θ, hK, hn4,
    congr_eq_fieldAutT _ Θ α V (hVκ.trans ha_def) g' hg'l hg'r hΘ _⟩

theorem exists_orth_model_minus {T : Type} [Group T] [Finite T] {p f₀ n : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hM : LieModel T .POmegaMinus n 2 (p * f₀)) (hf₀ : 1 ≤ f₀) (α : MulAut T)
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (k : Subfield K) (σ : K ≃+* K)
      (Q₀ : QuadraticForm k (Fin (2 * n) → k)) (Q : QuadraticForm K (Fin (2 * n) → K))
      (hS : SubfieldSetup k Q₀ Q σ p) (ψ : T ≃* matrixProjectiveDerived Q),
      Nat.card K = 2 ^ (p * f₀) ∧ 4 ≤ n ∧ MulAut.congr ψ α = fieldAutT Q σ hS.hQσ := by
  have hC : StatedClassicalModel T .POmegaMinus n 2 (p * f₀) :=
    (lieModel_classical_iff (by decide)).mp hM
  have : Fact p.Prime := ⟨hp⟩
  have hn4 : 4 ≤ n := hC.1.2.2
  have hn1 : 1 ≤ n := by omega
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hαord : orderOf α = p := orderOf_eq_prime hαp (fun h1 => hαinn (h1 ▸ (innerAut T).one_mem))
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hC
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := p * f₀) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, -, hidx⟩ := orthMinus_hyps hC K hK b c hirr hn1 e
  obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_minus hC K hK b c hirr e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) α :=
    ⟨_, rfl⟩
  have ha : orderOf a = p := by
    rw [ha_def]
    exact (orderOf_congr _ α).trans hαord
  have hainn : a ∉ innerAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) := by
    rw [ha_def]
    exact fun h => hαinn ((mem_innerAut_congr _ α).mp h)
  have haE : a ∈ matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) :=
    orth_mem_image_of_orderOf _ hidx hp hp3 ha
  have hap : a ^ p = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have haD : a ∉ (linearConjugationHom (coordinateQuadMinus n K hn1 b c)).range :=
    orth_not_mem_linearRange_of_not_inner _ hnd hS3 hp hp2 hap hainn
  have hdesc := CFSG.RankThree.PartOne.orthogonal_prime_semilinear_actual_fixed_form_descent T
    .POmegaMinus (Or.inr (Or.inr rfl)) n 2 (p * f₀) p hC hp hp3 hp2 hn1 K hK b c hirr e a haE haD ha
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, V, cc, Q₀, hVκ, hVr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hfdiv : p * f₀ / p = f₀ := Nat.mul_div_cancel_left f₀ hp.pos
  rw [hfdiv] at hcard
  have hcard' : Nat.card (semilinearFixedSubfield V.val.right) = 2 ^ f₀ := by
    rw [hVr]
    exact hcard
  have hord'' : orderOf V.val.right = p := by
    rw [hVr]
    exact hord'
  have hK' : Nat.card K = 2 ^ (f₀ * p) := by rw [mul_comm]; exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield V.val.right ↔ V.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  have hdeg : Module.finrank (semilinearFixedSubfield V.val.right) K = p :=
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.finrank_subfield_eq
      (semilinearFixedSubfield V.val.right) Nat.prime_two hf₀ hcard' hK'
  have hS := CFSG.RankThree.PartOne.KCOrthogonalSubfield.subfieldSetup_minus
    (semilinearFixedSubfield V.val.right) hσk hp hp2 hord'' hn4 hdeg b' c' hirr'
  exact ⟨K, inferInstance, inferInstance, inferInstance, semilinearFixedSubfield V.val.right,
    V.val.right, _, _, hS, (coordinateMinusWitnessEquiv K hn1 b c e).trans Θ, hK, hn4,
    congr_eq_fieldAutT _ Θ α V (hVκ.trans ha_def) g' hg'l hg'r hΘ _⟩

end CFSG.RankThree.PartOne.FieldFix
