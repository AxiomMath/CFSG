module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE78Kac
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE78RatLabel
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelA
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6CompLabel
import CFSG.LocalAnalysis.StandardType.GGLangSolvBridge
import CFSG.LocalAnalysis.StandardType.GGTablePThreeF4A2A2
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacDispatch

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def E78CompLabel (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .A ∨ lab.tag = .twA) ∧ 3 ≤ lab.rank) ∨ ((lab.tag = .D ∨ lab.tag = .twD) ∧ 5 ≤ lab.rank) ∨
    lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8

section E78Lang

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.StandardType.LangRat
  CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem e78_shape_of_class
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a)) :
    (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1)) ∨
      (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1)) ∨
      (6 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          eRootCount (compRank (componentRoots (rootCharHom a) i))) := by
  rcases hτ with rfl | rfl
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
    have h := e7_shape c hc hlen
    rw [← hncard, ← hrank] at h
    exact h
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
    have h := e8_shape c hc hlen
    rw [← hncard, ← hrank] at h
    exact h

private theorem langE78_dispatch
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hTp : rootDiagUnit τ a ^ 3 = 1) (hpL : ((3 : ℕ) : L) ≠ 0)
    (hnorank4 : compRank (componentRoots (rootCharHom a) i) ≠ 4)
    (j0 : KernelComponent (rootCharHom a)) (hj0card : 30 ≤ (componentRoots (rootCharHom a) j0).ncard)
    (hshape : (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1)) ∨
      (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1)) ∨
      (6 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          eRootCount (compRank (componentRoots (rootCharHom a) i)))) :
    (∃ j : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) j) ∧
          rationalComponent S.ρ S.Γ (rootCharHom a) j ≠ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      ∃ lab : LargeEvenLabel, RationalLabelIs S i lab ∧ E78CompLabel lab := by
  classical
  have hτne : τ ≠ .G2 := by
    rintro rfl
    rcases hτ with h | h <;> cases h
  rcases hshape with hA | hD | hE
  ·
    by_cases hr2 : compRank (componentRoots (rootCharHom a) i) ≤ 2
    ·
      have hQSj0 : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) j0) := by
        refine isQuasisimple_rationalComponent_of_not_langSmallSolv (τ := τ) (p := 3)
          S hτne Nat.prime_three hpL hT hap h1 j0 ?_
        rintro (⟨-, h2⟩ | ⟨-, -, h6⟩) <;> omega
      refine Or.inl ⟨j0, hQSj0, ?_⟩
      refine rationalComponent_ne_of_forall_iterate_ne S hT j0 i ?_ hQSj0
      intro k heq
      have hinj : Function.Injective ((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k]) :=
        S.ρ.injective.iterate k
      have hcard := Set.ncard_image_of_injective (componentRoots (rootCharHom a) j0) hinj
      rw [heq] at hcard
      have hi6 : (componentRoots (rootCharHom a) i).ncard ≤ 6 := by
        rw [hA.2]
        calc compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) + 1)
            ≤ 2 * 3 := Nat.mul_le_mul hr2 (by omega)
          _ = 6 := by norm_num
      omega
    ·
      have hr3 : 3 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
      obtain ⟨lab, hdeg, hrank, hinn, hsu, hRL⟩ :=
        rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hqs
      have hkind : twistKind S.ρ (rootCharHom a) i = .inner ∨
          twistKind S.ρ (rootCharHom a) i = .suN := by
        by_cases htw : twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)])
        · left; unfold twistKind; rw [if_pos htw]
        · right
          unfold twistKind
          rw [if_neg htw]
          have hexc : ¬ ((compRank (componentRoots (rootCharHom a) i) = 6 ∧
              (componentRoots (rootCharHom a) i).ncard = 72) ∨
              (compRank (componentRoots (rootCharHom a) i) = 4 ∧
                (componentRoots (rootCharHom a) i).ncard = 24 ∧
                ¬ twistInner (componentRoots (rootCharHom a) i)
                  ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
                    (componentRoots (rootCharHom a) i)]))) := by
            rintro (⟨h6, h72⟩ | ⟨h4, h24, -⟩)
            · rw [hA.2, h6] at h72; norm_num at h72
            · rw [hA.2, h4] at h24; norm_num at h24
          have htwoD : ¬ (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
              (componentRoots (rootCharHom a) i).ncard =
                2 * compRank (componentRoots (rootCharHom a) i) *
                  (compRank (componentRoots (rootCharHom a) i) - 1)) := by
            rintro ⟨h4, htwo⟩
            rw [hA.2] at htwo
            have h1r : 1 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
            nlinarith [htwo, Nat.sub_add_cancel h1r]
          rw [if_neg hexc, if_neg htwoD,
            if_pos (show 2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
                (componentRoots (rootCharHom a) i).ncard =
                  compRank (componentRoots (rootCharHom a) i) *
                    (compRank (componentRoots (rootCharHom a) i) + 1) from
              ⟨by omega, hA.2⟩)]
      refine Or.inr ⟨lab, hRL, Or.inl ⟨?_, ?_⟩⟩
      · rcases hkind with hk | hk
        · exact Or.inl (hinn hk)
        · exact Or.inr (hsu hk)
      · rw [hrank]; exact hr3
  ·
    have h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · obtain ⟨lab, hdeg, htag, hrank, hRL⟩ :=
        rationalLabel_innerD_E78 hτ S Nat.prime_three hpL hT hTp i hD hinner hqs
      refine Or.inr ⟨lab, hRL, Or.inr (Or.inl ⟨Or.inl htag, ?_⟩)⟩
      rw [hrank]; exact h5
    · obtain ⟨lab, hdeg, h1c, h2c, h3c, hRL⟩ :=
        rationalLabel_outerD S Nat.prime_three hT hap h1 i hD hinner hqs
      have htwo : twistKind S.ρ (rootCharHom a) i = .twoD := by
        rcases twistKind_outerD S.ρ (rootCharHom a) i hD hinner with h | ⟨h, h4⟩
        · exact h
        · exact absurd h4 hnorank4
      obtain ⟨htag, hrank⟩ := h1c htwo hnorank4
      refine Or.inr ⟨lab, hRL, Or.inr (Or.inl ⟨Or.inr htag, ?_⟩)⟩
      rw [hrank]; exact h5
  ·
    by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · obtain ⟨lab, hdeg, htag, hRL⟩ :=
        rationalLabel_innerE_E78 hτ S Nat.prime_three hpL hT hTp i hE hinner hqs
      refine Or.inr ⟨lab, hRL, ?_⟩
      unfold E78CompLabel
      rcases htag with h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · obtain ⟨lab, hdeg, htag, hRL⟩ :=
        rationalLabel_outerE_E78 hτ S Nat.prime_three hpL hT hTp i hE hinner hqs
      exact Or.inr ⟨lab, hRL, Or.inr (Or.inr (Or.inr (Or.inl htag)))⟩

end E78Lang

theorem langE78_comp_cases
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    (∃ j : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) j) ∧
          rationalComponent S.ρ S.Γ (rootCharHom a) j ≠ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      ∃ lab : LargeEvenLabel, RationalLabelIs S i lab ∧ E78CompLabel lab := by
  classical
  have hpL : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      have hcast : ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 := by norm_num
      rw [hcast, h2, zero_add]
    rw [h3]; exact one_ne_zero
  have hTp : rootDiagUnit τ a ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    rw [show a ^ 3 = 1 from funext fun j => hap j, rootDiagUnit_one]
  obtain ⟨hnorank4, j0, hj0card⟩ := e78_three_classes hτ hpL hap
  have hshape := e78_shape_of_class hτ S Nat.prime_three hpL hTp i
  exact langE78_dispatch hτ S hT hap h1 i hqs hTp hpL (hnorank4 i) j0 hj0card hshape

end CFSG.StandardType.TablePThreeKG

end
