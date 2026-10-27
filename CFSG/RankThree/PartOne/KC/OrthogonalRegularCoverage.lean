module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverage
public import CFSG.LocalAnalysis.ComponentInitial.QuadraticLowDimension
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticRankTwoCounts
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourExtract
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixExtract

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Defs

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

@[expose] def SmallFixedException (Q : QuadraticForm K W) : Prop :=
  (finrank K W = 3 ∧ Nat.card K = 3) ∨
    ((finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
      (Nat.card K = 2 ∨ Nat.card K = 3))

@[expose] def DerivedCoverage (Q : QuadraticForm K W) : Prop :=
  Group.IsPerfect (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
  (∃ (n : ℕ) (L : Fin n → Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q)),
      1 ≤ n ∧ n ≤ 2 ∧ (⨆ i, L i) = commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      (∀ i, CFSG.IsQuasisimple (L i) ∧
        L i ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) ∧
        ((L i).subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q))).Normal) ∧
      ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x) ∧
  ∀ (g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) (p : ℕ), p.Prime → 3 < p → orderOf g = p →
      g ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)

end Defs

section Helpers

variable {G : Type*} [Group G]

theorem isQuasisimple_of_simple_nonabelian [IsSimpleGroup G] (hn : ¬ ∀ x y : G, x * y = y * x) :
    CFSG.IsQuasisimple G := by
  have hperf : Group.IsPerfect G := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exfalso
      apply hn
      intro x y
      have : ⁅x, y⁆ ∈ commutator G := Subgroup.commutator_mem_commutator trivial trivial
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact ⟨h⟩
  have hcenter : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      apply hn
      intro x y
      exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y)) x
  let e : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  refine ⟨hperf, MulEquiv.isSimpleGroup e, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hn
  intro x y
  have := hcon (e.symm x) (e.symm y)
  simpa using congrArg e this

end Helpers

section Quasisimple

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

theorem derivedCoverage_of_quasisimple (Q : QuadraticForm K W) (J : Subgroup (W ≃ₗ[K] W))
    (hJO : J ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hq : CFSG.IsQuasisimple ↥J)
    (hcomm : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ = J)
    (hodd : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, Odd (orderOf g) → g ∈ J) :
    DerivedCoverage Q := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have hc : commutator ↥O = J.subgroupOf O := by
    apply Subgroup.map_injective O.subtype_injective
    rw [Subgroup.map_subtype_commutator, Subgroup.map_subgroupOf_eq_of_le hJO]
    exact hcomm
  let e : ↥(commutator ↥O) ≃* ↥J :=
    (MulEquiv.subgroupCongr hc).trans (Subgroup.subgroupOfEquivOfLe hJO)
  have hqc : CFSG.IsQuasisimple ↥(commutator ↥O) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  refine ⟨hqc.1, ⟨1, fun _ => commutator ↥O, le_rfl, by norm_num, iSup_const,
    fun _ => ⟨hqc, le_rfl, ?_⟩, fun i j hij => absurd (Subsingleton.elim i j) hij⟩, ?_⟩
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · intro g p hp hp3 hg
    have h1 : Odd (orderOf (g : W ≃ₗ[K] W)) := by
      rw [Subgroup.orderOf_coe, hg]
      exact hp.odd_of_ne_two (by omega)
    rw [hc]
    exact hodd g g.2 h1

end Quasisimple

section Main

variable {K : Type} [Field K] [Finite K] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

omit [Finite K] [FiniteDimensional K W] in
theorem exists_threeSingular_of_le (Q : QuadraticForm K W) {U : Submodule K W}
    (hU : ∀ u ∈ U, Q u = 0) (h3 : 3 ≤ finrank K U) :
    ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := U) (n := 3) h3
  have hf' : LinearIndependent K (U.subtype ∘ f) := hf.map' U.subtype (Submodule.ker_subtype U)
  set T := Submodule.span K (Set.range (U.subtype ∘ f)) with hT
  have hTU : T ≤ U := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (f i).2)
  refine ⟨T, ?_, fun x hx => hU x (hTU hx)⟩
  rw [hT, finrank_span_eq_card hf']
  simp

theorem orthogonal_regular_space_coverage (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K W) :
    (SmallFixedException Q → ∀ (g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) (p : ℕ),
      p.Prime → 3 < p → orderOf g ≠ p) ∧
    (¬ SmallFixedException Q → DerivedCoverage Q) := by
  classical
  by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  ·
    have hnexc : ¬ SmallFixedException Q := by
      obtain ⟨T, hT3, hTQ⟩ := hT
      have := CFSG.ComponentClassification.UnbalancedCatalog.two_mul_finrank_le_of_singular hQ hTQ
      rintro (⟨hd3, -⟩ | ⟨⟨hd4, -⟩, -⟩) <;> omega
    refine ⟨fun h => absurd h hnexc, fun _ => ?_⟩
    obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
    exact derivedCoverage_of_quasisimple Q (orthDerived Q)
      (fun g hg => orthDerived_le_orthogonalGroup hg) (isQuasisimple_orthDerived hQ hT) rfl hodd
  ·
    have hcov : ∀ hcase : (Odd (Nat.card K) ∧ (finrank K W = 3 ∨ finrank K W = 4 ∨
          finrank K W = 5)) ∨
        (Odd (Nat.card K) ∧ finrank K W = 6 ∧
          ¬ ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) ∨
        (finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0),
        (SmallFixedException Q → ∀ (g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) (p : ℕ),
          p.Prime → 3 < p → orderOf g ≠ p) ∧
        (¬ SmallFixedException Q → DerivedCoverage Q) := by
      intro hcase
      obtain ⟨h1, h2, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ hcase
      exact ⟨fun h => (h1 h).2, fun h => by
        obtain ⟨hp, -, hL, hg⟩ := h2 h
        exact ⟨hp, hL, hg⟩⟩
    rcases Nat.even_or_odd (Nat.card K) with hev | hod
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
        exact hcov (Or.inr (Or.inr ⟨by omega, U, hUn, hUQ⟩))
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
          have hnexc : ¬ SmallFixedException Q := by
            rintro (⟨hd3, -⟩ | ⟨⟨hd4, S, hS2, hSQ⟩, -⟩)
            · omega
            · exact hS ⟨S, by omega, hSQ⟩
          refine ⟨fun h => absurd h hnexc, fun _ => ?_⟩
          rcases hn23 with rfl | rfl
          · obtain ⟨E, _, _, D, ψ, ρ, hψ, hρψ, hinj, hmem, hcomm, hsimple, hperf, hnonab, hcard,
              hidx, hnorm, hodd⟩ := even_minus_four_actual_derived_extraction Q hQ (by omega) hts
            have := hsimple
            exact derivedCoverage_of_quasisimple Q ρ.range
              (by rintro _ ⟨g, rfl⟩; exact hmem g) (isQuasisimple_of_simple_nonabelian hnonab)
              hcomm hodd
          · obtain ⟨E, _, _, D, ψ, ρ, hψ, hρψ, hinj, hmem, hcomm, hsimple, hperf, hnonab, hcard,
              hidx, hnorm, hodd⟩ := even_minus_six_actual_derived_extraction Q hQ (by omega) hts
            have := hsimple
            exact derivedCoverage_of_quasisimple Q ρ.range
              (by rintro _ ⟨g, rfl⟩; exact hmem g) (isQuasisimple_of_simple_nonabelian hnonab)
              hcomm hodd
    ·
      have hdim6 : finrank K W ≤ 6 :=
        (finite_odd_quadratic_low_Witt_dimension_bound hod Q hQ).2.2 hT
      by_cases hd6 : finrank K W = 6
      · exact hcov (Or.inr (Or.inl ⟨hod, hd6, hT⟩))
      · exact hcov (Or.inl ⟨hod, by omega⟩)

end Main

end CFSG.RankThree.PartOne.KCOrthogonal
