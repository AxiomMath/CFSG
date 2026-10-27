module

public import CFSG.RankThree.SteinbergR3ECoprimeRankOne
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification (OuterAutomorphisms.inner)
open scoped Pointwise

theorem isCyclic_of_isPGroup_matrixProjectiveDerived {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4)
    (hidx : (matrixProjectiveImage Q).index ≤ 3) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpP : ¬ p ∣ Nat.card (matrixProjectiveDerived Q))
    {A : Subgroup (MulAut (matrixProjectiveDerived Q))} (hA : IsPGroup p A) : IsCyclic A := by
  have : Fact p.Prime := ⟨hp⟩
  have hp4 : 4 < p := by
    rcases (show p = 4 ∨ 4 < p by omega) with h4 | h4
    · subst h4
      norm_num at hp
    · exact h4
  have hQv := exists_nonzero_value Q hQ
  have hAE : A ≤ matrixProjectiveImage Q := by
    have h1 : (matrixProjectiveImage Q).relIndex A ≤ 3 := by
      refine (Subgroup.relIndex_le_of_le_right le_top ?_).trans ?_
      · rw [Subgroup.relIndex_top_right]
        exact Subgroup.index_ne_zero_of_finite
      · rwa [Subgroup.relIndex_top_right]
    obtain ⟨k, hk⟩ := hA.exists_card_eq
    have h2 : (matrixProjectiveImage Q).relIndex A ∣ p ^ k :=
      hk ▸ Subgroup.relIndex_dvd_card _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h2
    have hj0 : j = 0 := by
      by_contra hne
      have := Nat.le_self_pow hne p
      omega
    exact Subgroup.relIndex_eq_one.1 (by rw [hj, hj0, pow_zero])
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
    exact Nat.Coprime.mul_left (coprime_of_dvd_of_lt hp (relIndex_inner_dvd Q) hA0 (by omega))
      (coprime_card_inner hp hpP)
  have hDcop : Nat.Coprime (Nat.card (linearConjugationHom Q).range) p := by
    rw [← Subgroup.relIndex_mul_card (isometryConjugationHom Q).range, inf_of_le_left hOD]
    exact Nat.Coprime.mul_left
      (coprime_of_dvd_of_lt hp (relIndex_isometryRange_dvd Q hQv) hsq0 (by omega)) hOcop
  have hAD : A ⊓ (linearConjugationHom Q).range = ⊥ := inf_eq_bot_of_isPGroup_of_coprime hA hDcop
  have hDmap : (fieldProjection Q).ker.map (matrixProjectiveConjugationHom Q) =
      (linearConjugationHom Q).range := by
    rw [linearConjugationHom, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  exact isCyclic_of_le_range_of_inf_map_ker_eq_bot (matrixProjectiveConjugationHom Q)
    (fieldProjection Q) (fieldProjection_range_cyclic Q) hAE (by rw [hDmap]; exact hAD)

theorem card_abelianization_le_four_of_bound {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {d ℓ : ℕ} (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hab : IsometryAbelianizationBound ℓ Q₀) :
    Nat.card (Abelianization (matrixIsometries (reindexQuadraticForm e Q₀))) ≤ 4 := by
  rw [card_abelianization_matrixIsometries_reindex]
  rcases eq_or_ne ℓ 2 with h2 | h2
  · exact (hab.2.2 h2).trans (by norm_num)
  · exact hab.2.1 h2

theorem orthogonal_coprime_large_prime_automorphism_subgroups_cyclic (T : Type) [Group T]
    (c : StatedLieTag) (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) (n ℓ f : ℕ)
    (h : StatedClassicalModel T c n ℓ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpT : ¬ p ∣ Nat.card T) :
    (∀ P : Subgroup (MulAut T), IsPGroup p P → IsCyclic P) ∧
    ∀ (E : Type*) [Group E] [IsElementaryAbelian p E], Nat.card E = p ^ 2 →
      ∀ α : E →* MulAut T, p ≤ Nat.card α.ker := by
  have hcyc : ∀ P : Subgroup (MulAut T), IsPGroup p P → IsCyclic P := by
    intro P hP
    rcases hc with rfl | rfl | rfl
    ·
      have h0 := h
      obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
      have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaOdd (.inl rfl)
        n ℓ f h K hK (quadOdd n K) (coe_quadOdd n K) e
      have hE : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ := by
        rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaOdd (.inl rfl) n ℓ
          f h) K hK e).1]
        exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T .POmegaOdd
          (.inl rfl) n ℓ f h) K hK).2
      have hpP : ¬ p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
        rwa [← Nat.card_congr (coordinateOddWitnessEquiv K e).toEquiv]
      exact isCyclic_of_isPGroup_of_mulEquiv (coordinateOddWitnessEquiv K e)
        (fun A hA => isCyclic_of_isPGroup_matrixProjectiveDerived _
          (coordinate_model_intrinsic_odd h K hK e).1
          (card_abelianization_le_four_of_bound (oddIndexEquiv n) (quadOdd n K) hab)
          (by rw [hE, Subgroup.index_top]; norm_num) hp hp3 hpP hA) hP
    ·
      have h0 := h
      obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h0
      have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
        (.inr (.inl rfl)) n ℓ f h K hK (quadPlus n K) (coe_quadPlus n K) e
      have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
        (.inr (.inl rfl)) n ℓ f h) K hK e).1
      have horbit := orthogonal_geometry_plus_point_family_orbit h hK e
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
      have hpP : ¬ p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
        rwa [← Nat.card_congr (coordinatePlusWitnessEquiv K e).toEquiv]
      exact isCyclic_of_isPGroup_of_mulEquiv (coordinatePlusWitnessEquiv K e)
        (fun A hA => isCyclic_of_isPGroup_matrixProjectiveDerived _
          (coordinate_model_intrinsic_plus h K hK e).1
          (card_abelianization_le_four_of_bound (plusIndexEquiv n) (quadPlus n K) hab)
          hidx hp hp3 hpP hA) hP
    ·
      have h0 := h
      obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
      have hn1 : 1 ≤ n := by omega
      have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaMinus
        (.inr (.inr rfl)) n ℓ f h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
      have hE : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ := by
        rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaMinus
          (.inr (.inr rfl)) n ℓ f h) hn1 K hK b c hirr e).1]
        exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T
          .POmegaMinus (.inr rfl) n ℓ f h) hn1 K hK b c hirr).2
      have hpP : ¬ p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) := by
        rwa [← Nat.card_congr (coordinateMinusWitnessEquiv K hn1 b c e).toEquiv]
      exact isCyclic_of_isPGroup_of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e)
        (fun A hA => isCyclic_of_isPGroup_matrixProjectiveDerived _
          (coordinate_model_intrinsic_minus h K hK b c hirr e).1
          (card_abelianization_le_four_of_bound (minusIndexEquiv n hn1) (quadMinus n K b c) hab)
          (by rw [hE, Subgroup.index_top]; norm_num) hp hp3 hpP hA) hP
  exact ⟨hcyc, fun E _ _ hE α => le_card_ker_of_isElementaryAbelian hp hcyc hE α⟩

end CFSG.RankThree.Automorphisms
