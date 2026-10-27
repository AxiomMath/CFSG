module

public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneCore
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorModel
public import CFSG.RankThree.PartOne.KC.SymplecticOrthogonalNoninner

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.LocalRank CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalNoninner CFSG.RankThree.Classical.SteinbergBY

theorem orthogonal_noninner_plane_local_core_product_odd_of_subfield
    (hsub : OrthogonalSubfieldCoreClause) : OrthogonalNoninnerPlaneLocalCoreOdd := by
  intro T _ _ c ℓ f n p hc h hp hp3 hpℓ B hB A hAB hAel hAcard hAH
  have hodd : 3 < ℓ ^ f → ∀ t ∈ (MulAut.conj : T →* MulAut T).range, orderOf t = p →
      ∀ A' : Subgroup (MulAut T), A' ≤ B ⊓ Subgroup.centralizer {t} → IsPGroup p A' →
        Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}), A'⁆ :
          Subgroup (MulAut T))) :=
    fun hq t ht htp A' hA' hA'p =>
      orthogonal_large_field_inner_actor_local_core_commutators_odd T c hc ℓ f n p h hp hp3 hpℓ hq
        B hB t ht htp A' hA'p hA'
  obtain ⟨hcap, hpf, hq2, hcore⟩ : Nat.card (A ⊓ (MulAut.conj : T →* MulAut T).range :
        Subgroup (MulAut T)) = p ∧ p ∣ f ∧ 2 ^ p ≤ ℓ ^ f ∧
      ∀ a ∈ A, a ∉ (MulAut.conj : T →* MulAut T).range →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
    rcases hc with rfl | rfl | rfl
    ·
      have h' := h
      obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
      have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates T .POmegaOdd
        (Or.inl rfl) n ℓ f h' K hK e
      exact noninner_facts_of_model (coordinateQuadOdd n K) hK hgates hp hp3
        (fun B' hB' a' ha'E ha'D hap ha'B =>
          noninner_core_odd hsub h' hp hp3 hpℓ K hK e B' hB' a' ha'E ha'D hap ha'B)
        (coordinateOddWitnessEquiv K e) B hB A hAB hAel hAcard hAH
    ·
      have h' := h
      obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
      have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates T .POmegaPlus
        (Or.inr (Or.inl rfl)) n ℓ f h' K hK e
      exact noninner_facts_of_model (coordinateQuadPlus n K) hK hgates hp hp3
        (fun B' hB' a' ha'E ha'D hap ha'B =>
          noninner_core_plus hsub h' hp hp3 hpℓ K hK e B' hB' a' ha'E ha'D hap ha'B)
        (coordinatePlusWitnessEquiv K e) B hB A hAB hAel hAcard hAH
    ·
      have h' := h
      obtain ⟨⟨-, -, hn4⟩, K, _, _, hK, b, c', hirr, ⟨e⟩⟩ := h
      have hn : 1 ≤ n := by omega
      have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates T .POmegaMinus
        (Or.inr (Or.inr rfl)) n ℓ f h' hn K hK b c' hirr e
      exact noninner_facts_of_model (coordinateQuadMinus n K hn b c') hK hgates hp hp3
        (fun B' hB' a' ha'E ha'D hap ha'B =>
          noninner_core_minus hsub h' hn hp hp3 hpℓ K hK b c' hirr e B' hB' a' ha'E ha'D hap ha'B)
        (coordinateMinusWitnessEquiv K hn b c' e) B hB A hAB hAel hAcard hAH
  exact noninner_plane_conclusion_of_core hp B A hAB hAel hAcard hAH hcap hpf hq2 hcore hodd

end CFSG.RankThree.PartOne
