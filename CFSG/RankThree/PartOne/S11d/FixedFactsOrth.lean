module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.RankThree.PartOne.S11c.Sec66Orth
public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthContract
public import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson

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
open CFSG.RankThree.PartOne (SubfieldConclusion)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  (IsExtension fieldAutT inclEquiv subfieldDerivedImage subfieldFixedGroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (orthPlus_hyps orthMinus_hyps congr_eq_fieldAutT
  NonLocalized)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

section Generic

variable {K : Type} [Field K] [Finite K] {d : ℕ} {k : Subfield K}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K}

theorem orth_fixedFacts_of_subfieldConclusion {T : Type} [Group T] [Finite T] {p f₀ n : ℕ}
    {t : StatedLieTag} (hM : LieModel T t n 2 (p * f₀)) (hf₀ : 1 ≤ f₀)
    (hext : IsExtension k Q₀ Q)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hconc : SubfieldConclusion k Q₀ Q σ p hext hQσ)
    (hNJ : subfieldFixedGroup k Q₀ Q ≤ subfieldDerivedImage k hext) (hd : 0 < d)
    (hNL : NonLocalized (subfieldDerivedImage k hext))
    (hX : LieModel (matrixProjectiveDerived Q₀) t n 2 f₀) (ψ : T ≃* matrixProjectiveDerived Q)
    (α : MulAut T) (hα : MulAut.congr ψ α = fieldAutT Q σ hQσ) : FixedFacts p α := by
  obtain ⟨⟨-, hJs, hJn⟩, -, hfixiff, hJN, hJnorm, hq, -, -, -, -⟩ := hconc
  set J := subfieldDerivedImage k hext with hJ
  set N := subfieldFixedGroup k Q₀ Q with hN
  have hΓ : fixSub (fieldAutT Q σ hQσ) = N := Subgroup.ext hfixiff
  have hΓ' : fixSub (MulAut.congr ψ α) = N := by rw [hα, hΓ]
  have hperf : Group.IsPerfect ↥J := by
    have := hJs
    obtain ⟨x, y, hxy⟩ := hJn
    exact isPerfect_of_simple_nonabelian ⟨x, y, hxy⟩
  have hZ : Subgroup.center ↥J = ⊥ := by
    have := hJs
    obtain ⟨x, y, hxy⟩ := hJn
    exact center_eq_bot_of_simple' ⟨x, y, hxy⟩
  have hXJ : LieModel ↥J t n 2 f₀ := lieModel_of_mulEquiv (inclEquiv k hext hd) hX
  have hXQ : LieModel (↥J ⧸ Subgroup.center ↥J) t n 2 f₀ :=
    lieModel_of_mulEquiv (centerQuotientEquivSelf hZ).symm hXJ
  have hsolv0 : Group.IsSolvable (↥N ⧸ J.subgroupOf N) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpg : IsPGroup 2 (↥N ⧸ J.subgroupOf N) := @hq hJnorm
    have : Group.IsNilpotent (↥N ⧸ J.subgroupOf N) := hpg.isNilpotent
    infer_instance
  have hnormT : ∀ W : Subgroup (matrixProjectiveDerived Q), W = N → (J.subgroupOf W).Normal := by
    intro W hW
    subst hW
    exact hJnorm
  have hsolvT : ∀ W : Subgroup (matrixProjectiveDerived Q), W = N →
      ∀ (hn : (J.subgroupOf W).Normal), Group.IsSolvable (↥W ⧸ J.subgroupOf W) := by
    intro W hW hn
    subst hW
    exact hsolv0
  refine fixedFacts_of_iso ψ α hM hf₀ J ?_ (hnormT _ hΓ') hperf (hsolvT _ hΓ' (hnormT _ hΓ')) hNL ?_
    (Or.inl fun x hx _ => ?_) (Or.inl hXQ)
  · rw [hΓ']
    exact hJN
  · intro x hx _
    rw [hΓ'] at hx
    exact hNJ hx
  · rw [hΓ'] at hx
    exact hNJ hx

end Generic


theorem fixedFacts_POmegaPlus {T : Type} [Group T] [Finite T] {p f₀ n : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hM : LieModel T .POmegaPlus n 2 (p * f₀)) (hf₀ : 1 ≤ f₀) (α : MulAut T)
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) : FixedFacts p α := by
  have hC : StatedClassicalModel T .POmegaPlus n 2 (p * f₀) :=
    (lieModel_classical_iff (by decide)).mp hM
  have : Fact p.Prime := ⟨hp⟩
  have hn4 : 4 ≤ n := hC.1.2.2
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hfdiv : p * f₀ / p = f₀ := Nat.mul_div_cancel_left f₀ hp.pos
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
  have hadm₀ : StatedLieAdmissible .POmegaPlus n 2 f₀ := ⟨Nat.prime_two, hf₀, hn4⟩
  obtain ⟨-, hconc⟩ :=
    CFSG.RankThree.PartOne.orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
      .POmegaPlus (Or.inr (Or.inl rfl)) n 2 f₀ p hadm₀ hp hp3 hp2 K
      (semilinearFixedSubfield V.val.right) hcard' hK' V.val.right hord'' hσk
  have hNL := (SignalizerFunctorTheorem.NonLocal.subfieldNonLocalizedOrthogonal).2.1 n 2 f₀ p
    hadm₀ hp hp3 hp2 K (semilinearFixedSubfield V.val.right) hcard' hK' V.val.right hord'' hσk
  have hS := CFSG.RankThree.PartOne.KCOrthogonalSubfield.subfieldSetup_plus
    (semilinearFixedSubfield V.val.right) hσk hp hp2 hord'' (by omega : 3 ≤ n)
  have hNJ := subfieldFixedGroup_le_derivedImage hS.hext hS.hnd₀ hS.hT₀ hS.hnd
  exact orth_fixedFacts_of_subfieldConclusion hM hf₀ _ _ hconc hNJ (by omega) hNL
    (lieModel_orthPlus_subfield hn4 hf₀ _ hcard')
    ((coordinatePlusWitnessEquiv K e).trans Θ) α
    (congr_eq_fieldAutT _ Θ α V (hVκ.trans ha_def) g' hg'l hg'r hΘ _)

theorem fixedFacts_POmegaMinus {T : Type} [Group T] [Finite T] {p f₀ n : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hM : LieModel T .POmegaMinus n 2 (p * f₀)) (hf₀ : 1 ≤ f₀) (α : MulAut T)
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) : FixedFacts p α := by
  have hC : StatedClassicalModel T .POmegaMinus n 2 (p * f₀) :=
    (lieModel_classical_iff (by decide)).mp hM
  have : Fact p.Prime := ⟨hp⟩
  have hn4 : 4 ≤ n := hC.1.2.2
  have hn1 : 1 ≤ n := by omega
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hfdiv : p * f₀ / p = f₀ := Nat.mul_div_cancel_left f₀ hp.pos
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
  have hadm₀ : StatedLieAdmissible .POmegaMinus n 2 f₀ := ⟨Nat.prime_two, hf₀, hn4⟩
  obtain ⟨-, hconc⟩ :=
    CFSG.RankThree.PartOne.orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
      .POmegaMinus (Or.inr (Or.inr rfl)) n 2 f₀ p hadm₀ hp hp3 hp2 hn1 K
      (semilinearFixedSubfield V.val.right) hcard' hK' V.val.right hord'' hσk b' c' hirr'
  have hNL := (SignalizerFunctorTheorem.NonLocal.subfieldNonLocalizedOrthogonal).2.2 n 2 f₀ p
    hadm₀ hp hp3 hp2 hn1 K (semilinearFixedSubfield V.val.right) hcard' hK' V.val.right hord''
    hσk b' c' hirr'
  have hdeg : Module.finrank (semilinearFixedSubfield V.val.right) K = p :=
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.finrank_subfield_eq
      (semilinearFixedSubfield V.val.right) Nat.prime_two hf₀ hcard' hK'
  have hS := CFSG.RankThree.PartOne.KCOrthogonalSubfield.subfieldSetup_minus
    (semilinearFixedSubfield V.val.right) hσk hp hp2 hord'' hn4 hdeg b' c' hirr'
  have hNJ := subfieldFixedGroup_le_derivedImage hS.hext hS.hnd₀ hS.hT₀ hS.hnd
  exact orth_fixedFacts_of_subfieldConclusion hM hf₀ _ _ hconc hNJ (by omega) hNL
    (lieModel_orthMinus_subfield hn4 hf₀ _ hcard' b' c' hirr')
    ((coordinateMinusWitnessEquiv K hn1 b c e).trans Θ) α
    (congr_eq_fieldAutT _ Θ α V (hVκ.trans ha_def) g' hg'l hg'r hΘ _)

theorem tagFixedFacts_POmegaPlus : TagFixedFacts .POmegaPlus := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM α₀ _ _ _ _ α hαp hαinn _ _
  exact fixedFacts_POmegaPlus hp hp5 hM hf₀ α hαp hαinn

theorem tagFixedFacts_POmegaMinus : TagFixedFacts .POmegaMinus := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM α₀ _ _ _ _ α hαp hαinn _ _
  exact fixedFacts_POmegaMinus hp hp5 hM hf₀ α hαp hαinn

theorem tagFixedFacts_POmegaOdd : TagFixedFacts .POmegaOdd := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM
  have hC : StatedClassicalModel T .POmegaOdd n 2 (p * f₀) :=
    (lieModel_classical_iff (by decide)).mp hM
  exact absurd rfl hC.1.2.2.2

end CFSG.RankThree.PartOne.FieldFix
