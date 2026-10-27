module

public import CFSG.RankThree.PartOne.KC.OrthogonalRegularCoverage

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Transport

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

theorem isQuasisimple_commutator_of_quasisimple (Q : QuadraticForm K W)
    (J : Subgroup (W ≃ₗ[K] W)) (hJO : J ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hq : CFSG.IsQuasisimple ↥J)
    (hcomm : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ = J) :
    CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have hc : commutator ↥O = J.subgroupOf O := by
    apply Subgroup.map_injective O.subtype_injective
    rw [Subgroup.map_subtype_commutator, Subgroup.map_subgroupOf_eq_of_le hJO]
    exact hcomm
  let e : ↥(commutator ↥O) ≃* ↥J :=
    (MulEquiv.subgroupCongr hc).trans (Subgroup.subgroupOfEquivOfLe hJO)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq

end Transport

section Main

variable {K : Type} [Field K] [Finite K] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem orthogonal_regular_space_derived_quasisimple (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K W) (hnexc : ¬ SmallFixedException Q)
    (hns : ¬ (finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)) :
    CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  classical
  by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  ·
    exact isQuasisimple_commutator_of_quasisimple Q (orthDerived Q)
      (fun g hg => orthDerived_le_orthogonalGroup hg) (isQuasisimple_orthDerived hQ hT) rfl
  · rcases Nat.even_or_odd (Nat.card K) with hev | hod
    ·
      have hchar : CharP K 2 := by
        have := Fintype.ofFinite K
        refine ringChar.of_eq ?_
        rw [FiniteField.even_card_iff_char_two]
        rw [← Nat.card_eq_fintype_card]
        exact Nat.even_iff.mp hev
      obtain ⟨⟨n, hn⟩, -, hnf, -⟩ :=
        CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
          Q hQ
      by_cases hS : ∃ U : Submodule K W, finrank K U = n ∧ ∀ u ∈ U, Q u = 0
      ·
        obtain ⟨U, hUn, hUQ⟩ := hS
        have hn2 : n = 2 := by
          by_contra hne
          exact hT (exists_threeSingular_of_le Q hUQ (by omega))
        subst hn2
        exact absurd ⟨by omega, U, hUn, hUQ⟩ hns
      · have hts : ∀ U : Submodule K W, finrank K U = n → ∃ u ∈ U, Q u ≠ 0 := by
          intro U hU
          by_contra hcon
          push Not at hcon
          exact hS ⟨U, hU, hcon⟩
        rcases hnf n (by omega) hn with ⟨b, hb⟩ | ⟨β, γ, -, -, b, hb⟩
        · exfalso
          refine hS ⟨Submodule.span K (Set.range fun i : Fin n => b (Sum.inl i)), ?_, ?_⟩
          · exact (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans
              (by simp)
          · intro u hu
            obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
            simpa using hb x 0
        ·
          have hU : ∀ u ∈ Submodule.span K (Set.range fun i : Fin (n - 1) => b (Sum.inl i)),
              Q u = 0 := by
            intro u hu
            obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
            simpa using hb x 0 0 0
          have hdU : finrank K (Submodule.span K (Set.range fun i : Fin (n - 1) =>
              b (Sum.inl i))) = n - 1 :=
            (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans (by simp)
          have hn23 : n = 2 ∨ n = 3 := by
            by_contra hne
            exact hT (exists_threeSingular_of_le Q hU (by omega))
          rcases hn23 with rfl | rfl
          · obtain ⟨E, _, _, D, ψ, ρ, hψ, hρψ, hinj, hmem, hcomm, hsimple, hperf, hnonab, hcard,
              hidx, hnorm, hodd⟩ := even_minus_four_actual_derived_extraction Q hQ (by omega) hts
            have := hsimple
            exact isQuasisimple_commutator_of_quasisimple Q ρ.range
              (by rintro _ ⟨g, rfl⟩; exact hmem g) (isQuasisimple_of_simple_nonabelian hnonab)
              hcomm
          · obtain ⟨E, _, _, D, ψ, ρ, hψ, hρψ, hinj, hmem, hcomm, hsimple, hperf, hnonab, hcard,
              hidx, hnorm, hodd⟩ := even_minus_six_actual_derived_extraction Q hQ (by omega) hts
            have := hsimple
            exact isQuasisimple_commutator_of_quasisimple Q ρ.range
              (by rintro _ ⟨g, rfl⟩; exact hmem g) (isQuasisimple_of_simple_nonabelian hnonab)
              hcomm
    ·
      have hdim6 : finrank K W ≤ 6 :=
        (finite_odd_quadratic_low_Witt_dimension_bound hod Q hQ).2.2 hT
      have hcase : (Odd (Nat.card K) ∧ (finrank K W = 3 ∨ finrank K W = 4 ∨ finrank K W = 5)) ∨
          (Odd (Nat.card K) ∧ finrank K W = 6 ∧
            ¬ ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) ∨
          (finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) := by
        by_cases hd6 : finrank K W = 6
        · exact Or.inr (Or.inl ⟨hod, hd6, hT⟩)
        · exact Or.inl ⟨hod, by omega⟩
      obtain ⟨-, -, hq3, -, hq4, hq5, hq6⟩ :=
        orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ hcase
      have hdim : finrank K W = 3 ∨ finrank K W = 4 ∨ finrank K W = 5 ∨ finrank K W = 6 := by
        omega
      rcases hdim with hd | hd | hd | hd
      · obtain ⟨-, -, -, -, -, -, hq⟩ :=
          hq3 hod hd (fun hK => hnexc (Or.inl ⟨hd, hK⟩))
        exact hq
      · obtain ⟨-, -, -, -, -, -, -, -, hq⟩ := hq4 hod hd (fun hS => hns ⟨hd, hS⟩)
        exact hq
      · obtain ⟨-, -, -, -, -, -, hq⟩ := hq5 hod hd
        exact hq
      · obtain ⟨-, -, -, -, -, -, -, -, hq⟩ := hq6 hod hd hT
        exact hq

end Main

end CFSG.RankThree.PartOne.KCOrthogonal
