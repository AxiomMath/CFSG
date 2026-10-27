module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLangCompAdm

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section LangComp

open CFSG.StandardType.LangRat

theorem e6TwoLangComp_ne_A22_of_tag {lab : LargeEvenLabel} {t : LargeEvenLieTag}
    {r n : ℕ} (h : lab = ⟨t, r, n⟩) (ht : t ≠ .A) : lab ≠ ⟨.A, 2, 2⟩ := by
  intro heq
  rw [h] at heq
  exact ht (congrArg LargeEvenLabel.tag heq)

theorem e6TwoLangComp_ne_A22_of_rank {lab : LargeEvenLabel} {t : LargeEvenLieTag}
    {r n : ℕ} (h : lab = ⟨t, r, n⟩) (hr : r ≠ 2) : lab ≠ ⟨.A, 2, 2⟩ := by
  intro heq
  rw [h] at heq
  exact hr (congrArg LargeEvenLabel.rank heq)

theorem e6TwoLangComp_labelW
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hq : S.D.q = 2) (hAlg : S.IsAlgebraic) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hrow : E6RowTwoW S.ρ (componentRoots (rootCharHom a) i)) :
    ∃ lab : LargeEvenLabel, RationalLabelIs S i lab ∧ E6TwoCompLabelW lab ∧
      (lab = ⟨.A, 2, 2⟩ →
        rootDiagUnit Tag.E6 a ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  rcases hrow with ⟨hr5, hn30, horb1, htw⟩ | ⟨hr4, hn24, horb1, hout, hsq⟩ |
    ⟨hr2, hn6, horb2, htw2⟩
  · have hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) := by
      rw [hr5, hn30]; norm_num
    obtain ⟨lab, hdeg, hrank, hinn, -, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQS
    have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
      unfold twistKind
      rw [if_pos ?_]
      rwa [horb1, Function.iterate_one]
    have htag : lab.tag = .A := hinn hkind
    have hn1 : lab.n = 1 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      dsimp only
      rw [hdeg, horb1, hq]
    have hlab : lab = ⟨.A, 5, 1⟩ := by
      rcases lab with ⟨tag, r, n⟩
      simp only at htag hrank hn1
      have hr : r = 5 := by rw [hrank, hr5]
      simp only [htag, hr, hn1]
    refine ⟨lab, hRL, ?_, ?_⟩
    · rw [hlab]; exact Or.inl rfl
    · exact fun h => absurd h (e6TwoLangComp_ne_A22_of_rank hlab (by decide))
  · have hshape : compRank (componentRoots (rootCharHom a) i) = 4 ∧
        (componentRoots (rootCharHom a) i).ncard = 24 := ⟨hr4, hn24⟩
    have hout' : ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      rwa [horb1, Function.iterate_one]
    have hsq' : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      simpa [horb1] using hsq
    obtain ⟨lab, hdeg, htag, hrank, hRL⟩ :=
      rationalLabel_outerD_four_sq S Nat.prime_three hT hap h1 i hshape hout' hsq' hQS
    have hn1 : lab.n = 1 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      dsimp only
      rw [hdeg, horb1, hq]
    have hlab : lab = ⟨.twD, 4, 1⟩ := by
      rcases lab with ⟨tag, r, n⟩
      simp only at htag hrank hn1
      simp only [htag, hrank, hn1]
    refine ⟨lab, hRL, ?_, ?_⟩
    · rw [hlab]; exact Or.inr (Or.inl rfl)
    · exact fun h => absurd h (e6TwoLangComp_ne_A22_of_rank hlab (by decide))
  · have hshape : compRank (componentRoots (rootCharHom a) i) = 2 ∧
        (componentRoots (rootCharHom a) i).ncard = 6 := ⟨hr2, hn6⟩
    have hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) := by
      rw [hr2, hn6]; norm_num
    obtain ⟨lab, hdeg, hrank, hinn, -, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQS
    have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
      unfold twistKind
      rw [if_pos ?_]
      rwa [horb2]
    have htag : lab.tag = .A := hinn hkind
    have hn1 : lab.n = 2 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      dsimp only
      rw [hdeg, horb2, hq]
    have hlab : lab = ⟨.A, 2, 2⟩ := by
      rcases lab with ⟨tag, r, n⟩
      simp only at htag hrank hn1
      have hr : r = 2 := by rw [hrank, hr2]
      simp only [htag, hr, hn1]
    refine ⟨lab, hRL, ?_, ?_⟩
    · rw [hlab]; exact Or.inr (Or.inr rfl)
    · intro _
      exact e6Two_rootDiagUnit_mem_rationalComponent S hq hAlg hT hap h1 i hshape horb2 htw2

theorem e6TwoLangComp_labelT
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hq : S.D.q = 2) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hrow : E6RowTwoT S.ρ (componentRoots (rootCharHom a) i)) :
    ∃ lab : LargeEvenLabel, RationalLabelIs S i lab ∧ E6TwoCompLabelT lab ∧
      (lab = ⟨.A, 2, 2⟩ →
        rootDiagUnit Tag.E6 a ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have h3ne : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      have hcast : ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 := by norm_num
      rw [hcast, h2, zero_add]
    rw [h3]; exact one_ne_zero
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    rw [show a ^ 3 = 1 from funext fun j => hap j, rootDiagUnit_one]
  rcases hrow with ⟨hr5, hn40, horb1, hout⟩ | ⟨hr4, hn20, horb1, hout⟩ |
    ⟨hr5, hn30, horb1, hout⟩ | ⟨hr2, hn6, horb3, hout3⟩ |
    ⟨hr4, hn24, horb1, htw⟩ | ⟨hr4, hn24, horb1, hout, hsq_out⟩
  ·
    have hshape : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) := by
      rw [hr5, hn40]; norm_num
    have hout' : ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      rwa [horb1, Function.iterate_one]
    obtain ⟨lab, hdeg, h1, -, -, hRL⟩ :=
      rationalLabel_outerD S Nat.prime_three hT hap h1 i hshape hout' hQS
    have hkind := twistKind_outerD S.ρ (rootCharHom a) i hshape hout'
    have htwoD : twistKind S.ρ (rootCharHom a) i = .twoD := by
      rcases hkind with hk | ⟨hk, h4⟩
      · exact hk
      · exfalso; omega
    obtain ⟨htag, hrank⟩ := h1 htwoD (by omega)
    have hn1 : lab.n = 1 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      dsimp only
      rw [hdeg, horb1, hq]
    have hlab : lab = ⟨.twD, 5, 1⟩ := by
      rcases lab with ⟨tag, r, n⟩
      simp only at htag hrank hn1
      have hr : r = 5 := by rw [hrank, hr5]
      simp only [htag, hr, hn1]
    refine ⟨lab, hRL, ?_, ?_⟩
    · rw [hlab]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact fun h => absurd h (e6TwoLangComp_ne_A22_of_tag hlab (by decide))
  ·
    have hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) := by
      rw [hr4, hn20]; norm_num
    obtain ⟨lab, hdeg, hrank, -, hsu, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQS
    have hout' : ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      rwa [horb1, Function.iterate_one]
    have hexc : ¬ ((compRank (componentRoots (rootCharHom a) i) = 6 ∧
        (componentRoots (rootCharHom a) i).ncard = 72) ∨
        (compRank (componentRoots (rootCharHom a) i) = 4 ∧
          (componentRoots (rootCharHom a) i).ncard = 24 ∧
          ¬ twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)]))) := by
      rintro (⟨h6, -⟩ | ⟨h4, h24, -⟩) <;> omega
    have htwoD : ¬ (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1)) := by
      rintro ⟨h4, h24⟩
      rw [hr4] at h24
      omega
    have hsuN : 2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) :=
      ⟨by omega, by rw [hn20, hr4]⟩
    have hkind : twistKind S.ρ (rootCharHom a) i = .suN := by
      unfold twistKind
      rw [if_neg hout', if_neg hexc, if_neg htwoD, if_pos hsuN]
    have htag : lab.tag = .twA := hsu hkind
    have hn1 : lab.n = 1 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      dsimp only
      rw [hdeg, horb1, hq]
    have hlab : lab = ⟨.twA, 4, 1⟩ := by
      rcases lab with ⟨tag, r, n⟩
      simp only at htag hrank hn1
      have hr : r = 4 := by rw [hrank, hr4]
      simp only [htag, hr, hn1]
    refine ⟨lab, hRL, ?_, ?_⟩
    · rw [hlab]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact fun h => absurd h (e6TwoLangComp_ne_A22_of_tag hlab (by decide))
  ·
    have hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) := by
      rw [hr5, hn30]; norm_num
    obtain ⟨lab, hdeg, hrank, -, hsu, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQS
    have hout' : ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      rwa [horb1, Function.iterate_one]
    have hexc : ¬ ((compRank (componentRoots (rootCharHom a) i) = 6 ∧
        (componentRoots (rootCharHom a) i).ncard = 72) ∨
        (compRank (componentRoots (rootCharHom a) i) = 4 ∧
          (componentRoots (rootCharHom a) i).ncard = 24 ∧
          ¬ twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)]))) := by
      rintro (⟨h6, -⟩ | ⟨h4, h24, -⟩) <;> omega
    have htwoD : ¬ (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1)) := by
      rintro ⟨h4, h24⟩
      rw [hr5] at h24
      omega
    have hsuN : 2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) :=
      ⟨by omega, by rw [hn30, hr5]⟩
    have hkind : twistKind S.ρ (rootCharHom a) i = .suN := by
      unfold twistKind
      rw [if_neg hout', if_neg hexc, if_neg htwoD, if_pos hsuN]
    have htag : lab.tag = .twA := hsu hkind
    have hn1 : lab.n = 1 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      dsimp only
      rw [hdeg, horb1, hq]
    have hlab : lab = ⟨.twA, 5, 1⟩ := by
      rcases lab with ⟨tag, r, n⟩
      simp only at htag hrank hn1
      have hr : r = 5 := by rw [hrank, hr5]
      simp only [htag, hr, hn1]
    refine ⟨lab, hRL, ?_, ?_⟩
    · rw [hlab]; exact Or.inl rfl
    · exact fun h => absurd h (e6TwoLangComp_ne_A22_of_tag hlab (by decide))
  ·
    have hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) := by
      rw [hr2, hn6]; norm_num
    obtain ⟨lab, hdeg, hrank, -, hsu, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQS
    have hout' : ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      rwa [horb3]
    have hexc : ¬ ((compRank (componentRoots (rootCharHom a) i) = 6 ∧
        (componentRoots (rootCharHom a) i).ncard = 72) ∨
        (compRank (componentRoots (rootCharHom a) i) = 4 ∧
          (componentRoots (rootCharHom a) i).ncard = 24 ∧
          ¬ twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)]))) := by
      rintro (⟨h6, -⟩ | ⟨h4, h24, -⟩) <;> omega
    have htwoD : ¬ (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1)) := by
      rintro ⟨h4, -⟩
      omega
    have hsuN : 2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) :=
      ⟨by omega, by rw [hn6, hr2]⟩
    have hkind : twistKind S.ρ (rootCharHom a) i = .suN := by
      unfold twistKind
      rw [if_neg hout', if_neg hexc, if_neg htwoD, if_pos hsuN]
    have htag : lab.tag = .twA := hsu hkind
    have hn1 : lab.n = 3 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      dsimp only
      rw [hdeg, horb3, hq]
    have hlab : lab = ⟨.twA, 2, 3⟩ := by
      rcases lab with ⟨tag, r, n⟩
      simp only at htag hrank hn1
      have hr : r = 2 := by rw [hrank, hr2]
      simp only [htag, hr, hn1]
    refine ⟨lab, hRL, ?_, ?_⟩
    · rw [hlab]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact fun h => absurd h (e6TwoLangComp_ne_A22_of_tag hlab (by decide))
  ·
    have hshape : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) := by
      rw [hr4, hn24]; norm_num
    have hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      rwa [horb1, Function.iterate_one]
    obtain ⟨lab, hdeg, htag, hrank, hRL⟩ :=
      rationalLabel_innerD_E6 S Nat.prime_three h3ne hT hTp i hshape hinner hQS
    have hn1 : lab.n = 1 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      dsimp only
      rw [hdeg, horb1, hq]
    have hlab : lab = ⟨.D, 4, 1⟩ := by
      rcases lab with ⟨tag, r, n⟩
      simp only at htag hrank hn1
      have hr : r = 4 := by rw [hrank, hr4]
      simp only [htag, hr, hn1]
    refine ⟨lab, hRL, ?_, ?_⟩
    · rw [hlab]; exact Or.inr (Or.inl rfl)
    · exact fun h => absurd h (e6TwoLangComp_ne_A22_of_tag hlab (by decide))
  ·
    have hshape : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) := by
      rw [hr4, hn24]; norm_num
    have hout' : ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      rwa [horb1, Function.iterate_one]
    obtain ⟨lab, hdeg, -, h2, h3, hRL⟩ :=
      rationalLabel_outerD S Nat.prime_three hT hap h1 i hshape hout' hQS
    have hkind := twistKind_outerD S.ρ (rootCharHom a) i hshape hout'
    have hcases : (lab.tag = .twD ∧ lab.rank = 4) ∨ lab.tag = .triD4 := by
      rcases hkind with hk | ⟨hk, -⟩
      · exact h2 hk hr4
      · exact h3 hk hr4
    have hn1 : lab.n = 1 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      dsimp only
      rw [hdeg, horb1, hq]
    rcases hcases with ⟨htag, hrank⟩ | htag
    · have hlab : lab = ⟨.twD, 4, 1⟩ := by
        rcases lab with ⟨tag, r, n⟩
        simp only at htag hrank hn1
        simp only [htag, hrank, hn1]
      refine ⟨lab, hRL, ?_, ?_⟩
      · rw [hlab]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      · exact fun h => absurd h (e6TwoLangComp_ne_A22_of_tag hlab (by decide))
    · have hlab : lab = ⟨.triD4, 0, 1⟩ := by
        have hrl := hRL.1
        rcases lab with ⟨tag, r, n⟩
        simp only at htag hn1
        subst htag
        have hr : r = 0 := by
          simp only [LargeEvenInLambda2] at hrl
          exact hrl.2
        simp only [hr, hn1]
      refine ⟨lab, hRL, ?_, ?_⟩
      · rw [hlab]; exact Or.inr (Or.inr (Or.inl rfl))
      · exact fun h => absurd h (e6TwoLangComp_ne_A22_of_tag hlab (by decide))

end LangComp

end CFSG.StandardType.TablePThreeKG

end
