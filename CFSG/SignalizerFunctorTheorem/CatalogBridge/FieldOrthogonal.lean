module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfield
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY
import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.SignalizerFunctorTheorem
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.RankThree.Automorphisms
open CFSG.ComponentClassification (OuterAutomorphisms.inner)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedProj StatedOmega
  StatedQuadOdd StatedQuadPlus StatedQuadMinus)
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)
open scoped Pointwise
open CFSG.RankThree.PartOne (SubfieldConclusion)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (IsExtension fieldAutT fieldPair
  subfieldDerivedImage coordinateQuadOdd_fieldAut coordinateQuadPlus_fieldAut
  coordinateQuadMinus_fieldAut)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem mem_E_not_D_of_orderOf {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4)
    (hidx : (matrixProjectiveImage Q).index ≤ 3) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpP : ¬ p ∣ Nat.card (matrixProjectiveDerived Q))
    {a : MulAut (matrixProjectiveDerived Q)} (ha : orderOf a = p) :
    a ∈ matrixProjectiveImage Q ∧ a ∉ (linearConjugationHom Q).range := by
  have : Fact p.Prime := ⟨hp⟩
  have hp4 : 4 < p := by
    rcases (show p = 4 ∨ 4 < p by omega) with h4 | h4
    · subst h4
      norm_num at hp
    · exact h4
  have hQv := exists_nonzero_value Q hQ
  have hA : IsPGroup p (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  refine ⟨?_, fun haD => ?_⟩
  ·
    have hAE : Subgroup.zpowers a ≤ matrixProjectiveImage Q := by
      have h1 : (matrixProjectiveImage Q).relIndex (Subgroup.zpowers a) ≤ 3 := by
        refine (Subgroup.relIndex_le_of_le_right le_top ?_).trans ?_
        · rw [Subgroup.relIndex_top_right]
          exact Subgroup.index_ne_zero_of_finite
        · rwa [Subgroup.relIndex_top_right]
      obtain ⟨k, hk⟩ := hA.exists_card_eq
      have h2 : (matrixProjectiveImage Q).relIndex (Subgroup.zpowers a) ∣ p ^ k :=
        hk ▸ Subgroup.relIndex_dvd_card _ _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h2
      have hj0 : j = 0 := by
        by_contra hne
        have := Nat.le_self_pow hne p
        omega
      exact Subgroup.relIndex_eq_one.1 (by rw [hj, hj0, pow_zero])
    exact hAE (Subgroup.mem_zpowers a)
  ·
    have hIO : OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤
        (isometryConjugationHom Q).range := by
      rw [inner_eq_map_commutator Q]
      exact Subgroup.map_le_range _ _
    have hOD := isometryConjugationHom_range_le Q
    have hA0 : 0 < Nat.card (Abelianization (matrixIsometries Q)) := Nat.card_pos
    have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index ≤ 2 := by
      rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
      exact Nat.gcd_le_right _ two_pos
    have hsq0 : 0 < (powMonoidHom 2 : Kˣ →* Kˣ).range.index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hOcop : Nat.Coprime (Nat.card (isometryConjugationHom Q).range) p := by
      rw [← Subgroup.relIndex_mul_card (OuterAutomorphisms.inner (matrixProjectiveDerived Q)),
        inf_of_le_left hIO]
      exact Nat.Coprime.mul_left
        (coprime_of_dvd_of_lt hp (relIndex_inner_dvd Q) hA0 (by omega)) (coprime_card_inner hp hpP)
    have hDcop : Nat.Coprime (Nat.card (linearConjugationHom Q).range) p := by
      rw [← Subgroup.relIndex_mul_card (isometryConjugationHom Q).range, inf_of_le_left hOD]
      exact Nat.Coprime.mul_left
        (coprime_of_dvd_of_lt hp (relIndex_isometryRange_dvd Q hQv) hsq0 (by omega)) hOcop
    have hdvd := orderOf_dvd_natCard (⟨a, haD⟩ : (linearConjugationHom Q).range)
    rw [Subgroup.orderOf_mk, ha] at hdvd
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hDcop.symm hdvd)

theorem orthOdd_hyps {T : Type} [Group T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaOdd n ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : T ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    coordinateQuadOdd n K ≠ 0 ∧
      Nat.card (Abelianization (matrixIsometries (coordinateQuadOdd n K))) ≤ 4 ∧
      (matrixProjectiveImage (coordinateQuadOdd n K)).index ≤ 3 := by
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaOdd (.inl rfl)
    n ℓ f hm K hK (quadOdd n K) (coe_quadOdd n K) e
  have hE : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ := by
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaOdd (.inl rfl) n ℓ
      f hm) K hK e).1]
    exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T .POmegaOdd
      (.inl rfl) n ℓ f hm) K hK).2
  exact ⟨(coordinate_model_intrinsic_odd hm K hK e).1,
    card_abelianization_le_four_of_bound (oddIndexEquiv n) (quadOdd n K) hab,
    by rw [hE, Subgroup.index_top]; norm_num⟩

theorem orthPlus_hyps {T : Type} [Group T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaPlus n ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : T ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    coordinateQuadPlus n K ≠ 0 ∧
      Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus n K))) ≤ 4 ∧
      (matrixProjectiveImage (coordinateQuadPlus n K)).index ≤ 3 := by
  have hn : 4 ≤ n := hm.1.2.2
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
    (.inr (.inl rfl)) n ℓ f hm K hK (quadPlus n K) (coe_quadPlus n K) e
  have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
    (.inr (.inl rfl)) n ℓ f hm) K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit hm hK e
  have hidx : (matrixProjectiveImage (coordinateQuadPlus n K)).index ≤ 3 := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · have hst : (projectivePointFamilyAut (coordinateQuadPlus n K)).index =
          (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
            (projectivePointFamily (coordinateQuadPlus n K))).ncard :=
        MulAction.index_stabilizer _ _
      rw [← hEA, hst]
      exact (horbit.2.2.2.2.2 h4).2
    · rw [← hEA, horbit.2.2.2.2.1 h5, Subgroup.index_top]
      norm_num
  exact ⟨(coordinate_model_intrinsic_plus hm K hK e).1,
    card_abelianization_le_four_of_bound (plusIndexEquiv n) (quadPlus n K) hab, hidx⟩

theorem orthMinus_hyps {T : Type} [Group T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaMinus n ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hn1 : 1 ≤ n) (e : T ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    coordinateQuadMinus n K hn1 b c ≠ 0 ∧
      Nat.card (Abelianization (matrixIsometries (coordinateQuadMinus n K hn1 b c))) ≤ 4 ∧
      (matrixProjectiveImage (coordinateQuadMinus n K hn1 b c)).index ≤ 3 := by
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaMinus
    (.inr (.inr rfl)) n ℓ f hm K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hE : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ := by
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaMinus
      (.inr (.inr rfl)) n ℓ f hm) hn1 K hK b c hirr e).1]
    exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T
      .POmegaMinus (.inr rfl) n ℓ f hm) hn1 K hK b c hirr).2
  exact ⟨(coordinate_model_intrinsic_minus hm K hK b c hirr e).1,
    card_abelianization_le_four_of_bound (minusIndexEquiv n hn1) (quadMinus n K b c) hab,
    by rw [hE, Subgroup.index_top]; norm_num⟩

theorem orthogonal_prime_numerics {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {t : StatedLieTag} {n ℓ f p : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hm : StatedClassicalModel T t n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T) : 3 < p ∧ p ≠ ℓ := by
  have hp3 : 3 < p := by
    have h3 := (CFSG.RankThree.Classical.orthogonal_model_exists_orderOf_eq_three ht hm).2
    have hp3 : p ≠ 3 := fun h => hpT (h ▸ h3)
    have := hp.two_le
    omega
  refine ⟨hp3, ?_⟩
  rintro rfl
  have hf1 : 1 ≤ f := hm.1.2.1
  have hZ := center_eq_bot_of_isSimpleGroup_of_noncomm hs hn
  let eT : T ⧸ Subgroup.center T ≃* T :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  suffices h : 4 * f ≤ CFSG.Assembly.RankThreeEven.localRank p T from
    hpT (CFSG.RankThree.LocalRank.prime_dvd_card_of_localRank_pos hp (by omega))
  rcases ht with rfl | rfl | rfl
  · obtain ⟨⟨-, -, hn3, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    exact CFSG.RankThree.CentralLift.four_mul_le_localRank_of_omegaOdd hp hp3 hf1 hK hn3
      (eT.trans e)
  · obtain ⟨⟨-, -, hn4⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    exact CFSG.RankThree.CentralLift.four_mul_le_localRank_of_omegaPlus hp hp3 hf1 hK hn4
      (eT.trans e)
  · obtain ⟨⟨-, -, hn4⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hm
    exact CFSG.RankThree.CentralLift.four_mul_le_localRank_of_omegaMinus hp hp3 hf1 hK hn4 hirr
      (eT.trans e)

theorem congr_trans_eq {T A B : Type*} [Group T] [Group A] [Group B] (φ : T ≃* A) (Θ : A ≃* B)
    (f₁ : MulAut T) (a : MulAut A) (b : MulAut B) (ha : MulAut.congr φ f₁ = a)
    (hΘ : ∀ x, Θ (a x) = b (Θ x)) : MulAut.congr (φ.trans Θ) f₁ = b := by
  ext y
  have h1 : MulAut.congr (φ.trans Θ) f₁ y = Θ (a (Θ.symm y)) := by
    rw [← ha, MulAut.congr_apply, MulAut.congr_apply]
    rfl
  rw [h1, hΘ, MulEquiv.apply_symm_apply]

theorem congr_eq_fieldAutT {T : Type} [Group T] {K : Type} [Field K] {d : ℕ}
    {Q Q' : QuadraticForm K (Fin d → K)} (φ : T ≃* matrixProjectiveDerived Q)
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q') (f₁ : MulAut T)
    (U : similarityPairs Q) (hU : matrixProjectiveConjugationHom Q U = MulAut.congr φ f₁)
    (g' : similarityPairs Q') (hg'l : g'.val.left = 1) (hg'r : g'.val.right = U.val.right)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x))
    (hQσ : ∀ v, Q' (coordinateFieldMap d U.val.right v) = U.val.right (Q' v)) :
    MulAut.congr (φ.trans Θ) f₁ = fieldAutT Q' U.val.right hQσ := by
  have hg'eq : g' = fieldPair Q' U.val.right hQσ := Subtype.ext (SemidirectProduct.ext hg'l hg'r)
  refine congr_trans_eq φ Θ f₁ _ _ rfl fun x => ?_
  have h1 := hΘ x
  rw [hU, hg'eq] at h1
  exact h1

theorem fixedClauses_of_subfieldConclusion {T : Type} [Group T] [Finite T]
    (hs : IsSimpleGroup T) (hn : ∃ a b : T, a * b ≠ b * a) {p : ℕ} (hp : p.Prime)
    (hpT : ¬ p ∣ Nat.card T) {K : Type} [Field K] [Finite K] {d : ℕ} {k : Subfield K}
    {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K}
    (hext : IsExtension k Q₀ Q) (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hconc : SubfieldConclusion k Q₀ Q σ p hext hQσ) (ψ : T ≃* matrixProjectiveDerived Q)
    (f₁ : MulAut T) (hf₁ : MulAut.congr ψ f₁ = fieldAutT Q σ hQσ)
    (hJ : NonLocalized (subfieldDerivedImage k hext)) :
    FixedClauses p (signalizerFixedSubgroup f₁) := by
  have := hs
  have : Finite (matrixProjectiveDerived Q) := Finite.of_equiv T ψ.toEquiv
  have hsP : IsSimpleGroup (matrixProjectiveDerived Q) := ψ.symm.isSimpleGroup
  have hnP : ∃ x y : matrixProjectiveDerived Q, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hn
    exact ⟨ψ a, ψ b, fun h => hab (ψ.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hpP : ¬ p ∣ Nat.card (matrixProjectiveDerived Q) := by
    rwa [← Nat.card_congr ψ.toEquiv]
  obtain ⟨⟨-, hJs, hJn⟩, ha, hfix, hJN, hJnorm, -, -, -, hJst, -⟩ := hconc
  have hmain : FixedClauses p (signalizerFixedSubgroup (fieldAutT Q σ hQσ)) :=
    fixedClauses_of_simple_normal_stabilizer hp hsP hnP hpP ha hJN hJnorm hJs hJn hfix
      (fun g hg => by
        rw [← hJst]
        exact (mem_fixingSubgroup_iff _).2 fun y hy => hg y hy)
      (fun _ => NonLocalized.mono
        (fun x hx => show fieldAutT Q σ hQσ x = x from (hfix x).2 (hJN hx)) hJ)
  rw [← hf₁] at hmain
  exact FixedClauses.of_mulEquiv ψ.symm f₁ hmain

theorem fieldClauses_orthOdd {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {n ℓ f p : ℕ} (hm : StatedClassicalModel T .POmegaOdd n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T)
    (hNL : SubfieldNonLocalizedOrthogonal) :
    FieldClauses p T := by
  rintro ⟨f₁, hf₁⟩
  obtain ⟨hp3, hpℓ⟩ := orthogonal_prime_numerics hs hn (Or.inl rfl) hm hp hp2 hpT
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, hidx⟩ := orthOdd_hyps hm K hK e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinateOddWitnessEquiv K e) f₁ := ⟨_, rfl⟩
  have ha : orderOf a = p := by
    rw [ha_def, MulEquiv.orderOf_eq]
    exact hf₁
  have hpP : ¬ p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
    rwa [← Nat.card_congr (coordinateOddWitnessEquiv K e).toEquiv]
  obtain ⟨haE, haD⟩ := mem_E_not_D_of_orderOf _ hQ hab hidx hp hp3 hpP ha
  have hdesc := CFSG.RankThree.PartOne.orthogonal_prime_semilinear_actual_fixed_form_descent T
    .POmegaOdd (Or.inl rfl) n ℓ f p hm hp hp3 hpℓ K hK e a haE haD ha
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  have hK' : Nat.card K = ℓ ^ (f / p * p) := by
    rw [Nat.div_mul_cancel hpf]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  obtain ⟨-, hconc⟩ :=
    CFSG.RankThree.PartOne.orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
      .POmegaOdd (Or.inl rfl) n ℓ (f / p) p hCM.1 hp hp3 hpℓ K (semilinearFixedSubfield U.val.right)
      hcard' hK' U.val.right hord' hσk
  exact ⟨f₁, hf₁, fixedClauses_of_subfieldConclusion hs hn hp hpT _ _ hconc
    ((coordinateOddWitnessEquiv K e).trans Θ) f₁
    (congr_eq_fieldAutT _ Θ f₁ U (hUκ.trans ha_def) g' hg'l hg'r hΘ _)
    (hNL.1 n ℓ (f / p) p hCM.1 hp hp3 hpℓ K (semilinearFixedSubfield U.val.right) hcard' hK'
      U.val.right hord' hσk)⟩

theorem fieldClauses_orthPlus {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {n ℓ f p : ℕ} (hm : StatedClassicalModel T .POmegaPlus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T)
    (hNL : SubfieldNonLocalizedOrthogonal) :
    FieldClauses p T := by
  rintro ⟨f₁, hf₁⟩
  obtain ⟨hp3, hpℓ⟩ := orthogonal_prime_numerics hs hn (Or.inr (Or.inl rfl)) hm hp hp2 hpT
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, hidx⟩ := orthPlus_hyps hm K hK e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinatePlusWitnessEquiv K e) f₁ := ⟨_, rfl⟩
  have ha : orderOf a = p := by
    rw [ha_def, MulEquiv.orderOf_eq]
    exact hf₁
  have hpP : ¬ p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    rwa [← Nat.card_congr (coordinatePlusWitnessEquiv K e).toEquiv]
  obtain ⟨haE, haD⟩ := mem_E_not_D_of_orderOf _ hQ hab hidx hp hp3 hpP ha
  have hdesc := CFSG.RankThree.PartOne.orthogonal_prime_semilinear_actual_fixed_form_descent T
    .POmegaPlus (Or.inr (Or.inl rfl)) n ℓ f p hm hp hp3 hpℓ K hK e a haE haD ha
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  have hK' : Nat.card K = ℓ ^ (f / p * p) := by
    rw [Nat.div_mul_cancel hpf]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  obtain ⟨-, hconc⟩ :=
    CFSG.RankThree.PartOne.orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
      .POmegaPlus (Or.inr (Or.inl rfl)) n ℓ (f / p) p hCM.1 hp hp3 hpℓ K
      (semilinearFixedSubfield U.val.right) hcard' hK' U.val.right hord' hσk
  exact ⟨f₁, hf₁, fixedClauses_of_subfieldConclusion hs hn hp hpT _ _ hconc
    ((coordinatePlusWitnessEquiv K e).trans Θ) f₁
    (congr_eq_fieldAutT _ Θ f₁ U (hUκ.trans ha_def) g' hg'l hg'r hΘ _)
    (hNL.2.1 n ℓ (f / p) p hCM.1 hp hp3 hpℓ K (semilinearFixedSubfield U.val.right) hcard' hK'
      U.val.right hord' hσk)⟩

theorem fieldClauses_orthMinus {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {n ℓ f p : ℕ} (hm : StatedClassicalModel T .POmegaMinus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T)
    (hNL : SubfieldNonLocalizedOrthogonal) :
    FieldClauses p T := by
  rintro ⟨f₁, hf₁⟩
  obtain ⟨hp3, hpℓ⟩ := orthogonal_prime_numerics hs hn (Or.inr (Or.inr rfl)) hm hp hp2 hpT
  have hn1 : 1 ≤ n := by
    have := hm.1.2.2
    omega
  have h0 := hm
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, hidx⟩ := orthMinus_hyps hm K hK b c hirr hn1 e
  obtain ⟨a, ha_def⟩ : ∃ a, a = MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) f₁ :=
    ⟨_, rfl⟩
  have ha : orderOf a = p := by
    rw [ha_def, MulEquiv.orderOf_eq]
    exact hf₁
  have hpP : ¬ p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) := by
    rwa [← Nat.card_congr (coordinateMinusWitnessEquiv K hn1 b c e).toEquiv]
  obtain ⟨haE, haD⟩ := mem_E_not_D_of_orderOf _ hQ hab hidx hp hp3 hpP ha
  have hdesc := CFSG.RankThree.PartOne.orthogonal_prime_semilinear_actual_fixed_form_descent T
    .POmegaMinus (Or.inr (Or.inr rfl)) n ℓ f p hm hp hp3 hpℓ hn1 K hK b c hirr e a haE haD ha
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  have hK' : Nat.card K = ℓ ^ (f / p * p) := by
    rw [Nat.div_mul_cancel hpf]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  obtain ⟨-, hconc⟩ :=
    CFSG.RankThree.PartOne.orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
      .POmegaMinus (Or.inr (Or.inr rfl)) n ℓ (f / p) p hCM.1 hp hp3 hpℓ hn1 K
      (semilinearFixedSubfield U.val.right) hcard' hK' U.val.right hord' hσk b' c' hirr'
  exact ⟨f₁, hf₁, fixedClauses_of_subfieldConclusion hs hn hp hpT _ _ hconc
    ((coordinateMinusWitnessEquiv K hn1 b c e).trans Θ) f₁
    (congr_eq_fieldAutT _ Θ f₁ U (hUκ.trans ha_def) g' hg'l hg'r hΘ _)
    (hNL.2.2 n ℓ (f / p) p hCM.1 hp hp3 hpℓ hn1 K (semilinearFixedSubfield U.val.right) hcard'
      hK' U.val.right hord' hσk b' c' hirr')⟩

theorem fieldClauses_statedOrthogonal {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {t : StatedLieTag} {n ℓ f p : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hm : StatedClassicalModel T t n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T)
    (hNL : SubfieldNonLocalizedOrthogonal) :
    FieldClauses p T := by
  rcases ht with rfl | rfl | rfl
  · exact fieldClauses_orthOdd hs hn hm hp hp2 hpT hNL
  · exact fieldClauses_orthPlus hs hn hm hp hp2 hpT hNL
  · exact fieldClauses_orthMinus hs hn hm hp hp2 hpT hNL

theorem nearOrField_statedOrthogonal {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {t : StatedLieTag} {n ℓ f p : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hm : StatedClassicalModel T t n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T)
    (hNL : SubfieldNonLocalizedOrthogonal) :
    CFSG.Open.signalizerNearPSolvable p T ∨ FieldClauses p T :=
  Or.inr (fieldClauses_statedOrthogonal hs hn ht hm hp hp2 hpT hNL)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
