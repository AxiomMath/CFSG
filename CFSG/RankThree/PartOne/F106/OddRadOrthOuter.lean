module

public import CFSG.RankThree.PartOne.S11c.Sec66Orth
public import CFSG.RankThree.PartOne.F106.OddRadGen
public import CFSG.RankThree.PartOne.F106.OddRadTools
public import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson

public section

namespace CFSG.RankThree.PartOne.F106.OddRadOrth

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedClassicalModel StatedLieAdmissible)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveImage coordinateFieldMap)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus plusIndexEquiv minusIndexEquiv
    coordinatePlusWitnessEquiv coordinateMinusWitnessEquiv coordinate_model_witness_plus
    coordinate_model_witness_minus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)
open CFSG.RankThree.PartOne (SubfieldConclusion)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  (IsExtension fieldAutT inclEquiv subfieldDerivedImage subfieldFixedGroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (orthPlus_hyps orthMinus_hyps congr_eq_fieldAutT
  NonLocalized)

theorem oddRadConcl_fieldAutT_of_subfieldConclusion {K : Type} [Field K] [Finite K] {d : ℕ}
    {k : Subfield K} {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}
    {σ : K ≃+* K} {p : ℕ} (hext : IsExtension k Q₀ Q)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hconc : SubfieldConclusion k Q₀ Q σ p hext hQσ)
    (hNJ : subfieldFixedGroup k Q₀ Q ≤ subfieldDerivedImage k hext) :
    OddRadConcl (matrixProjectiveDerived Q) (fieldAutT Q σ hQσ) := by
  obtain ⟨⟨-, hJs, hJn⟩, -, hfixiff, hJN, -, -, -, -, -, -⟩ := hconc
  have hfix : ((fieldAutT Q σ hQσ : MulAut (matrixProjectiveDerived Q)) :
      matrixProjectiveDerived Q →* matrixProjectiveDerived Q).eqLocus (MonoidHom.id _) =
      subfieldDerivedImage k hext := by
    ext t
    exact (hfixiff t).trans ⟨fun h => hNJ h, fun h => hJN h⟩
  unfold OddRadConcl
  rw [hfix]
  have := hJs
  obtain ⟨x, y, hxy⟩ := hJn
  have hperf : Group.IsPerfect ↥(subfieldDerivedImage k hext) :=
    CFSG.RankThree.PartOne.F106.isPerfect_of_simple_nonabelian ⟨x, y, hxy⟩
  rw [radical_perfectResidual_eq_bot_of_isSimpleGroup hperf, Subgroup.card_bot]
  exact odd_one

theorem oddRadConcl_POmegaPlus_outer {T : Type} [Group T] [Finite T] {n f : ℕ}
    (hM : LieModel T .POmegaPlus n 2 f) (α : MulAut T) (hαord : orderOf α = 5)
    (hαinn : α ∉ innerAut T) : OddRadConcl T α := by
  have hp : Nat.Prime 5 := by norm_num
  have hp3 : 3 < 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hC : StatedClassicalModel T .POmegaPlus n 2 f :=
    (lieModel_classical_iff (by decide)).mp hM
  have hn4 : 4 ≤ n := hC.1.2.2
  have hf : 1 ≤ f := hC.1.2.1
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hC
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, -, hidx⟩ := orthPlus_hyps hC K hK e
  obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_plus hC K hK e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinatePlusWitnessEquiv K e) α := ⟨_, rfl⟩
  have ha : orderOf a = 5 := by
    rw [ha_def]
    exact (orderOf_congr _ α).trans hαord
  have hainn : a ∉ innerAut (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    rw [ha_def]
    exact fun h => hαinn ((mem_innerAut_congr _ α).mp h)
  have haE : a ∈ matrixProjectiveImage (coordinateQuadPlus n K) :=
    orth_mem_image_of_orderOf _ hidx hp hp3 ha
  have hap : a ^ 5 = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have haD : a ∉ (linearConjugationHom (coordinateQuadPlus n K)).range :=
    orth_not_mem_linearRange_of_not_inner _ hnd hS3 hp hp2 hap hainn
  have hdesc := CFSG.RankThree.PartOne.orthogonal_prime_semilinear_actual_fixed_form_descent T
    .POmegaPlus (Or.inr (Or.inl rfl)) n 2 f 5 hC hp hp3 hp2 K hK e a haE haD ha
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, V, cc, Q₀, hVκ, hVr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hfp1 : 1 ≤ f / 5 := (Nat.one_le_div_iff hp.pos).mpr (Nat.le_of_dvd (by omega) hpf)
  have hcard' : Nat.card (semilinearFixedSubfield V.val.right) = 2 ^ (f / 5) := by
    rw [hVr]
    exact hcard
  have hord'' : orderOf V.val.right = 5 := by
    rw [hVr]
    exact hord'
  have hK' : Nat.card K = 2 ^ (f / 5 * 5) := by
    rw [Nat.div_mul_cancel hpf]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield V.val.right ↔ V.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  obtain ⟨-, hconc⟩ :=
    CFSG.RankThree.PartOne.orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
      .POmegaPlus (Or.inr (Or.inl rfl)) n 2 (f / 5) 5 hCM.1 hp hp3 hp2 K
      (semilinearFixedSubfield V.val.right) hcard' hK' V.val.right hord'' hσk
  have hS := CFSG.RankThree.PartOne.KCOrthogonalSubfield.subfieldSetup_plus
    (semilinearFixedSubfield V.val.right) hσk hp hp2 hord'' (by omega : 3 ≤ n)
  have hNJ := subfieldFixedGroup_le_derivedImage hS.hext hS.hnd₀ hS.hT₀ hS.hnd
  have hψ := congr_eq_fieldAutT _ Θ α V (hVκ.trans ha_def) g' hg'l hg'r hΘ hS.hQσ
  rw [← oddRadConcl_congr ((coordinatePlusWitnessEquiv K e).trans Θ) α, hψ]
  exact oddRadConcl_fieldAutT_of_subfieldConclusion hS.hext hS.hQσ hconc hNJ

theorem oddRadConcl_POmegaMinus_outer {T : Type} [Group T] [Finite T] {n f : ℕ}
    (hM : LieModel T .POmegaMinus n 2 f) (α : MulAut T) (hαord : orderOf α = 5)
    (hαinn : α ∉ innerAut T) : OddRadConcl T α := by
  have hp : Nat.Prime 5 := by norm_num
  have hp3 : 3 < 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hC : StatedClassicalModel T .POmegaMinus n 2 f :=
    (lieModel_classical_iff (by decide)).mp hM
  have hn4 : 4 ≤ n := hC.1.2.2
  have hn1 : 1 ≤ n := by omega
  have hf : 1 ≤ f := hC.1.2.1
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hC
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, -, hidx⟩ := orthMinus_hyps hC K hK b c hirr hn1 e
  obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_minus hC K hK b c hirr e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) α :=
    ⟨_, rfl⟩
  have ha : orderOf a = 5 := by
    rw [ha_def]
    exact (orderOf_congr _ α).trans hαord
  have hainn : a ∉ innerAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) := by
    rw [ha_def]
    exact fun h => hαinn ((mem_innerAut_congr _ α).mp h)
  have haE : a ∈ matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) :=
    orth_mem_image_of_orderOf _ hidx hp hp3 ha
  have hap : a ^ 5 = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have haD : a ∉ (linearConjugationHom (coordinateQuadMinus n K hn1 b c)).range :=
    orth_not_mem_linearRange_of_not_inner _ hnd hS3 hp hp2 hap hainn
  have hdesc := CFSG.RankThree.PartOne.orthogonal_prime_semilinear_actual_fixed_form_descent T
    .POmegaMinus (Or.inr (Or.inr rfl)) n 2 f 5 hC hp hp3 hp2 hn1 K hK b c hirr e a haE haD ha
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, V, cc, Q₀, hVκ, hVr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hfp1 : 1 ≤ f / 5 := (Nat.one_le_div_iff hp.pos).mpr (Nat.le_of_dvd (by omega) hpf)
  have hcard' : Nat.card (semilinearFixedSubfield V.val.right) = 2 ^ (f / 5) := by
    rw [hVr]
    exact hcard
  have hord'' : orderOf V.val.right = 5 := by
    rw [hVr]
    exact hord'
  have hK' : Nat.card K = 2 ^ (f / 5 * 5) := by
    rw [Nat.div_mul_cancel hpf]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield V.val.right ↔ V.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  obtain ⟨-, hconc⟩ :=
    CFSG.RankThree.PartOne.orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
      .POmegaMinus (Or.inr (Or.inr rfl)) n 2 (f / 5) 5 hCM.1 hp hp3 hp2 hn1 K
      (semilinearFixedSubfield V.val.right) hcard' hK' V.val.right hord'' hσk b' c' hirr'
  have hdeg : Module.finrank (semilinearFixedSubfield V.val.right) K = 5 :=
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.finrank_subfield_eq
      (semilinearFixedSubfield V.val.right) Nat.prime_two hfp1 hcard' hK'
  have hS := CFSG.RankThree.PartOne.KCOrthogonalSubfield.subfieldSetup_minus
    (semilinearFixedSubfield V.val.right) hσk hp hp2 hord'' hn4 hdeg b' c' hirr'
  have hNJ := subfieldFixedGroup_le_derivedImage hS.hext hS.hnd₀ hS.hT₀ hS.hnd
  have hψ := congr_eq_fieldAutT _ Θ α V (hVκ.trans ha_def) g' hg'l hg'r hΘ hS.hQσ
  rw [← oddRadConcl_congr ((coordinateMinusWitnessEquiv K hn1 b c e).trans Θ) α, hψ]
  exact oddRadConcl_fieldAutT_of_subfieldConclusion hS.hext hS.hQσ hconc hNJ

end CFSG.RankThree.PartOne.F106.OddRadOrth
