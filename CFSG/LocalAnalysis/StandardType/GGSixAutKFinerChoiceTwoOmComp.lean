module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmBlock

public section

namespace CFSG.StandardType

namespace ChoiceTwoOm

open Module QuadraticMap Polynomial ChoiceTwo CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.OrthogonalInvolutions

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Dickson

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W}

theorem omegaGroup_le_commutator (hR : (polarBilin R).Nondegenerate) (h3 : 3 ≤ finrank K W)
    (hns : ¬ OmNonsplit.SplitFour R) :
    omegaGroup R hR ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup R,
      TauCeti.QuadraticMap.orthogonalGroup R⁆ := by
  classical
  by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, R x = 0
  · exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT
  have hidx : (⁅TauCeti.QuadraticMap.orthogonalGroup R,
      TauCeti.QuadraticMap.orthogonalGroup R⁆).relIndex
        (TauCeti.QuadraticMap.orthogonalGroup R) = 2 := by
    obtain ⟨⟨n, hn⟩, -, hnf, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
        R hR
    by_cases hS : ∃ U : Submodule K W, finrank K U = n ∧ ∀ u ∈ U, R u = 0
    · obtain ⟨U, hUn, hUQ⟩ := hS
      have hn2 : n = 2 := by
        by_contra hne
        exact hT (exists_threeSingular_of_le R hUQ (by omega))
      subst hn2
      exact absurd ⟨by omega, U, hUn, hUQ⟩ hns
    · have hts : ∀ U : Submodule K W, finrank K U = n → ∃ u ∈ U, R u ≠ 0 := by
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
      · have hU : ∀ u ∈ Submodule.span K (Set.range fun i : Fin (n - 1) => b (Sum.inl i)),
            R u = 0 := by
          intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0 0 0
        have hdU : finrank K (Submodule.span K (Set.range fun i : Fin (n - 1) =>
            b (Sum.inl i))) = n - 1 :=
          (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans (by simp)
        have hn23 : n = 2 ∨ n = 3 := by
          by_contra hne
          exact hT (exists_threeSingular_of_le R hU (by omega))
        rcases hn23 with rfl | rfl
        · obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, -, -, -, hidx, -⟩ :=
            CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction R hR (by omega) hts
          rw [hcomm]
          exact hidx
        · obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, -, -, -, hidx, -⟩ :=
            CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction R hR (by omega) hts
          rw [hcomm]
          exact hidx
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hΩO : omegaGroup R hR ≤ TauCeti.QuadraticMap.orthogonalGroup R := omegaGroup_le R hR
  have hNΩ : ⁅TauCeti.QuadraticMap.orthogonalGroup R, TauCeti.QuadraticMap.orthogonalGroup R⁆ ≤
      omegaGroup R hR := CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hR
  have hmul := Subgroup.relIndex_mul_relIndex _ (omegaGroup R hR)
    (TauCeti.QuadraticMap.orthogonalGroup R) hNΩ hΩO
  rw [relIndex_omegaGroup R hR, hidx] at hmul
  exact Subgroup.relIndex_eq_one.mp (by omega)

end Dickson

section Fixed

open CFSG.LocalAnalysis.ComponentInitial SevOm LayerCores

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {a : V ≃ₗ[K] V}

theorem mem_of_fixedBlock (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hp : Odd p) (hx : OddOrderIsometry Q p a) {L₁ : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L₁
      (CFSG.RankThree.Classical2.orthDerived Q ⊓ Subgroup.centralizer {a}))
    (hLF : L₁ ≤ supportedBlock Q a (X - 1)) {g : V ≃ₗ[K] V}
    (hg : g ∈ supportedBlock Q a (X - 1)) (hgΩ : g ∈ omegaGroup Q hQ) : g ∈ L₁ := by
  classical
  have hL' := isComponentOf_isometryCentralizer hL
  set F := supportedBlock Q a (X - 1) with hF
  set R := Q.comp (fixedSpace a).subtype with hR
  set OW := TauCeti.QuadraticMap.orthogonalGroup R with hOW
  have hRnd : (QuadraticMap.polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  set ρ := fixRho hx with hρ
  have hρinj : Function.Injective ρ := fixRho_injective hx
  set T := (L₁.subgroupOf F).map ρ with hT
  have hLq : CFSG.IsQuasisimple L₁ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L₁).1 hL'.2.2
  have hTq : CFSG.IsQuasisimple T :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hLF).symm.trans
        ((L₁.subgroupOf F).equivMapOfInjective ρ hρinj)) hLq
  have hTs : CFSG.Assembly.IsSubnormal T OW := by
    have h1 : CFSG.Assembly.IsSubnormal L₁ F :=
      ggSubnormal_mono hL'.2.1 hLF (supportedBlock_le_isometryCentralizer _)
    have h2 := ggSubnormal_comap F.subtype h1
    rw [show F.comap F.subtype = ⊤ from Subgroup.subgroupOf_self F] at h2
    have h3 := ggSubnormal_map ρ h2
    rwa [← MonoidHom.range_eq_map, hρ, range_fixRho] at h3
  obtain ⟨h4, ⟨hns, hTc⟩ | ⟨-, h4K, -⟩⟩ := OmNonsplit.structure_of_isSubnormal hRnd hTq hTs
  swap
  · rw [hK] at h4K
    omega
  have hX : (X - 1 : K[X]) ∈ primaryFactors a.toLinearMap := by
    by_contra hX
    rw [fixedSpace_eq_bot_of_not_mem hX, finrank_bot] at h4
    omega
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hgΩ.1
  have hδ := hx.dicksonHom_eq_restrict_of_mem_supportedBlock hp hQ hX hg
  have hδ1 : dicksonHom Q hQ ⟨g, (Subgroup.mem_inf.mp
      (supportedBlock_le_isometryCentralizer (X - 1) hg)).1⟩ = 1 := by
    have : (⟨g, (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer (X - 1) hg)).1⟩ :
        ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) ∈ (dicksonHom Q hQ).ker := by
      rw [dicksonHom_ker, Subgroup.mem_subgroupOf]
      exact hgΩ
    exact this
  rw [hδ1] at hδ
  have hmemΩ : isometryRestrictFixed Q a ⟨g, supportedBlock_le_isometryCentralizer (X - 1) hg⟩ ∈
      omegaGroup R hRnd := by
    have : (⟨isometryRestrictFixed Q a ⟨g, supportedBlock_le_isometryCentralizer (X - 1) hg⟩,
        isometryRestrictFixed_mem_orthogonalGroup _⟩ : ↥OW) ∈ (dicksonHom R hRnd).ker :=
      hδ.symm
    rw [dicksonHom_ker, Subgroup.mem_subgroupOf] at this
    exact this
  have hmemT := omegaGroup_le_commutator hRnd (by omega) hns hmemΩ
  rw [← hTc] at hmemT
  obtain ⟨y, hy, hyg⟩ := hmemT
  have hyg' : y = ⟨g, hg⟩ := hρinj (hyg.trans rfl)
  rw [hyg'] at hy
  exact Subgroup.mem_subgroupOf.mp hy

theorem mem_of_fixedBlock_of_pow (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hp : Odd p) (hx : OddOrderIsometry Q p a) {L₁ : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L₁
      (CFSG.RankThree.Classical2.orthDerived Q ⊓ Subgroup.centralizer {a}))
    (hLF : L₁ ≤ supportedBlock Q a (X - 1)) {g : V ≃ₗ[K] V}
    (hg : g ∈ supportedBlock Q a (X - 1)) {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) : g ∈ L₁ :=
  mem_of_fixedBlock hK hQ hp hx hL hLF hg
    (CFSG.RankThree.PartOne.mem_omegaGroup_of_pow_eq_one hQ hm
      (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer (X - 1) hg)).1 hgm)

end Fixed

section Phi3

open CFSG.LocalAnalysis.ComponentInitial SevOm

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {a : V ≃ₗ[K] V}

theorem eq_specialBlock_of_phi3 (hx : OddOrderIsometry Q 3 a)
    {L₁ : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L₁
      (CFSG.RankThree.Classical2.orthDerived Q ⊓ Subgroup.centralizer {a}))
    (hh : phi3 K ∈ primaryFactors a.toLinearMap) (hLF : L₁ ≤ supportedBlock Q a (phi3 K)) :
    L₁ = specialBlock Q a (phi3 K) :=
  free_case hx Nat.prime_three (by decide) hh phi3_ne_X_sub_one
    (isComponentOf_isometryCentralizer hL) hLF

omit [FiniteDimensional K V] in
theorem mem_specialBlock_of_mul_self (hK : Nat.card K = 2) {g : V ≃ₗ[K] V}
    (hg : g ∈ supportedBlock Q a (phi3 K)) (hgg : g * g = 1) : g ∈ specialBlock Q a (phi3 K) := by
  have : Fact (Irreducible (phi3 K)) := ⟨phi3_irreducible hK⟩
  refine mem_specialBlock.mpr ⟨hg, ?_⟩
  set d := blockDet Q a (phi3 K) ⟨g, hg⟩ with hd
  have hd2 : d * d = 1 := by
    rw [hd, ← map_mul]
    have : (⟨g, hg⟩ : ↥(supportedBlock Q a (phi3 K))) * ⟨g, hg⟩ = 1 := Subtype.ext hgg
    rw [this, map_one]
  have h2 : (2 : AdjoinRoot (phi3 K)) = 0 := by
    rw [← map_ofNat (algebraMap K (AdjoinRoot (phi3 K))) 2, CharTwo.two_eq_zero, map_zero]
  have h3 : (d + 1) * (d + 1) = 0 := by linear_combination hd2 + (d + 1) * h2
  have h4 : d + 1 = 0 := mul_self_eq_zero.mp h3
  show d = 1
  linear_combination h4 - h2

end Phi3

end ChoiceTwoOm

end CFSG.StandardType
