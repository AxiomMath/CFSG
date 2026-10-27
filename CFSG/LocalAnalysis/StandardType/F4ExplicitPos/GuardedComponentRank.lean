module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelected
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelA
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecC2
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RationalComponentEq
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private theorem not_guarded_of_labelIso_small_typeA {lab lab' : LargeEvenLabel}
    (hg : GuardedLargeEvenLabel lab) (hi : GGLabelIso lab lab')
    (ht : lab'.tag = .A ∨ lab'.tag = .twA) (hr : lab'.rank ≤ 2) : False := by
  obtain ⟨t, r, n⟩ := lab'
  rcases ht with rfl | rfl
  · have h5 : 5 ≤ r := (hg.linear_bounds_of_ggLabelIso hi).1
    change r ≤ 2 at hr
    omega
  · exact hg.not_ggLabelIso_unitary r n hi

private theorem not_guarded_of_labelIso_C2 {lab : LargeEvenLabel} {N : ℕ}
    (hg : GuardedLargeEvenLabel lab) (hi : GGLabelIso lab ⟨.C, 2, N⟩) : False := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp_all [GuardedLargeEvenLabel, GGLabelIso]

private theorem not_guarded_of_labelIso_B2der {lab : LargeEvenLabel}
    (hg : GuardedLargeEvenLabel lab) (hi : GGLabelIso lab ⟨.B2der, 0, 1⟩) : False := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp_all [GuardedLargeEvenLabel, GGLabelIso]


theorem f4_guarded_rationalComponent_root_rank
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p f : ℕ}
    (S : LangSetup .F4 L p₀) (hf : 1 ≤ f) (hq : S.D.q = 2 ^ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (a : Fin Tag.F4.rank → Lˣ)
    (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit .F4 a ≠ 1)
    (hT : rootDiagUnit .F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hRq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hmark : LargeEvenMarking (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    3 ≤ compRank (componentRoots (rootCharHom a) i) := by
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, hg⟩ := largeEvenMarking_exists_hasLabel hmark
  by_contra hmin
  have hrle : compRank (componentRoots (rootCharHom a) i) ≤ 2 := by omega
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hpL : (p : L) ≠ 0 := by
    intro hzero
    have hd : 2 ∣ p := (CharP.cast_eq_zero_iff L 2 p).1 hzero
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · omega
    · exact hp2 h.symm
  have hTp : rootDiagUnit .F4 a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1)
  · obtain ⟨lab', -, hrank', hinn, hsu, hRL⟩ :=
      TablePThreeKG.rationalLabel_typeA S hp hT hap h1 i hA hRq
    have hkind : twistKind S.ρ (rootCharHom a) i = .inner ∨
        twistKind S.ρ (rootCharHom a) i = .suN := by
      unfold twistKind
      split_ifs with h₁ h₂ h₃ h₄
      · exact Or.inl rfl
      · rcases h₂ with ⟨h6, -⟩ | ⟨h4, -, -⟩ <;> omega
      · obtain ⟨h4, -⟩ := h₃
        omega
      · exact Or.inr rfl
      · exact Or.inl rfl
    obtain ⟨hlab', hhas'⟩ := hRL
    have hi := ggLabelRigidInput_holds lab lab' _ hlab hlab' hhas hhas'
    exact not_guarded_of_labelIso_small_typeA hg hi (hkind.imp hinn hsu) (by omega)
  · rcases f4_nonA_casesP2 hp hpodd S hpL hTp h1 i hA with
      ⟨v, -, h2, h8⟩ | ⟨v, J, -, -, h3, -⟩
    · let s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
      obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
      have hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s]) :=
        LieCore.twistInner_of_small_inner i hs (S.ρ.injective.iterate s)
          (iform_rho_iterate S s) (rho_iterate_neg S s) (Or.inr (Or.inl ⟨h2, h8⟩))
      let N := f * s
      have hN : S.D.q ^ s = 2 ^ N := by dsimp only [N]; rw [hq, pow_mul]
      have hNpos : 0 < N := Nat.mul_pos (by omega) hs0
      by_cases hN1 : N = 1
      · have hlow := GGK0LQ.lq_rec_B2der rfl S hp hpL hT hTp h1 i h2 h8 hinner hN hN1
        have hΛ : LargeEvenInLambda2 ⟨.B2der, 0, 1⟩ := by norm_num [LargeEvenInLambda2]
        have hi := ggLabelRigidInput_holds lab ⟨.B2der, 0, 1⟩ _ hlab hΛ hhas hlow
        exact not_guarded_of_labelIso_B2der hg hi
      · have hN2 : 2 ≤ N := by omega
        have hlow := GGK0LQ.lq_rec_C2 rfl S hp hpL hT hTp h1 i h2 h8 hinner hN hN2
        rw [h2] at hlow
        have hΛ : LargeEvenInLambda2 ⟨.C, 2, N⟩ := by
          change 1 ≤ N ∧ 2 ≤ 2 ∧ (2 = 2 → 2 ≤ N)
          exact ⟨by omega, by omega, fun _ => hN2⟩
        have hi := ggLabelRigidInput_holds lab ⟨.C, 2, N⟩ _ hlab hΛ hhas hlow
        exact not_guarded_of_labelIso_C2 hg hi
    · omega

end CFSG.StandardType
