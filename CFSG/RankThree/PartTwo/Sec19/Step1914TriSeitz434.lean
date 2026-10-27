module

public import CFSG.RankThree.PartTwo.Sec19.Step1914TriSeitz
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Seitz
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec4.Item413Cases

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def SeitzL3PiGap : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi X p e → (3 < p ∧ 3 ≤ e) ∨ (p = 2 ∧ (e = 3 ∨ e = 6)) →
    ∀ F : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 F → Nat.card F = 9 →
      Subgroup.closure {x : X | ∃ φ ∈ F, φ ≠ 1 ∧ φ x = x} = ⊤

namespace Step1914TriSeitz434

theorem seitzHyperGamma_le_closure {X : Type} [Group X] {F : Subgroup (MulAut X)}
    (hF9 : Nat.card F = 9) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 F ≤
      Subgroup.closure {x : X | ∃ φ ∈ F, φ ≠ 1 ∧ φ x = x} := by
  refine iSup₂_le fun F' hF' => ?_
  intro x hx
  have hcard : Nat.card F' = 3 := by
    have h1 := Subgroup.card_mul_index (F'.subgroupOf F)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF'.1).toEquiv, hF9] at h1
    have h2 : (F'.subgroupOf F).index = 3 := hF'.2
    rw [h2] at h1
    omega
  have hne : F' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨φ, hφ⟩, hφ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact Subgroup.subset_closure ⟨φ, hF'.1 hφ, fun h => hφ1 (Subtype.ext h),
    (CFSG.LieType.Seitz.mem_fixedPoints.mp hx) φ hφ⟩

theorem exists_mul_ne_of_isPerfect {X : Type*} [Group X] [Nontrivial X] [Group.IsPerfect X] :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact Group.IsPerfect.not_isMulCommutative X ⟨⟨h⟩⟩

end Step1914TriSeitz434

open Step1914TriProof Step1914TriSeitz434 in
theorem seitzL3Pi_of_seitz434 (h434 : Sec4.Seitz434) (hgap : SeitzL3PiGap) : SeitzL3Pi := by
  intro X _ _ p e hp he hiso h2 h4 F hF hF9
  by_cases hg : (3 < p ∧ 3 ≤ e) ∨ (p = 2 ∧ (e = 3 ∨ e = 6))
  · exact hgap X p e he hiso hg F hF hF9
  have hpp : p.Prime := hp.out
  have hp3 : p ≠ 3 := by
    rintro rfl
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    rcases hiso with ⟨hq, -⟩ | ⟨hq, -⟩ <;> simp [pow_succ, Nat.mul_mod_left] at hq
  have hq2 : 2 < p ^ e := by
    have h1 : 2 ≤ p ^ e := hpp.two_le.trans (Nat.le_self_pow (by omega) p)
    omega
  obtain ⟨hperf, hZ⟩ : Group.IsPerfect X ∧ Subgroup.center X = ⊥ := by
    rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · obtain ⟨hP, hZP⟩ := Sec13.isPerfect_center_projSL p e he hq
      have hXp : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom)
        φ.symm.surjective
      have := isSimpleGroup_projSL_three_of_field (GaloisField p e)
      have : IsSimpleGroup X := φ.isSimpleGroup
      exact ⟨hXp, center_eq_bot_of_isSimpleGroup_of_isPerfect⟩
    · obtain ⟨hP, hZP⟩ := Sec13.isPerfect_center_projSU p e he hq hq2
      have hXp : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom)
        φ.symm.surjective
      have := isSimpleGroup_projSU_three_of_ne_two p e he h2
      have : IsSimpleGroup X := φ.isSimpleGroup
      exact ⟨hXp, center_eq_bot_of_isSimpleGroup_of_isPerfect⟩
  have hsimple : IsSimpleGroup X := by
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · have := isSimpleGroup_projSL_three_of_field (GaloisField p e)
      exact φ.isSimpleGroup
    · have := isSimpleGroup_projSU_three_of_ne_two p e he h2
      exact φ.isSimpleGroup
  set ι : X ⧸ Subgroup.center X ≃* X := Sec4.quotientCenterEquivOfBot hZ with hι
  have : Nontrivial (X ⧸ Subgroup.center X) := ι.symm.injective.nontrivial
  have hqs : CFSG.IsQuasisimple X := ⟨hperf, ι.isSimpleGroup, exists_mul_ne_of_isPerfect⟩
  have hZ3 : IsPGroup 3 (Subgroup.center X) := by
    rw [hZ]
    exact IsPGroup.of_card (n := 0) (by rw [Subgroup.card_bot, pow_zero])
  have hL42 : Sec4.IsLie42Generic (X ⧸ Subgroup.center X) := by
    push Not at hg
    rcases hpp.eq_two_or_odd' with rfl | hodd
    ·
      have he1 : e ≠ 1 := fun h => h2 (by rw [h]; norm_num)
      have he2 : e ≠ 2 := fun h => h4 (by rw [h]; norm_num)
      have he3 : e ≠ 3 ∧ e ≠ 6 := (hg.2 rfl)
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨e, by omega, he3.2, ?_⟩)))
      rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
      · exact Or.inr (Or.inl ⟨ι.trans φ⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨ι.trans φ⟩))
    ·
      have hp5 : 3 < p := by
        have : p ≠ 2 := by rintro rfl; norm_num at hodd
        have h2p := hpp.two_le
        rcases Nat.lt_or_ge 3 p with h | h
        · exact h
        · interval_cases p <;> simp_all
      have he2 : e ≤ 2 := by
        by_contra h
        exact absurd (hg.1 hp5) (by omega)
      refine Or.inr (Or.inl ⟨p, e, hp, hp5, he, he2, ?_⟩)
      rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
      · exact Or.inl ⟨ι.trans φ⟩
      · exact Or.inr ⟨ι.trans φ⟩
  have h := h434 X hqs hZ3 hL42 F hF (Or.inl hF9)
  rw [eq_top_iff, ← h]
  exact seitzHyperGamma_le_closure hF9

end CFSG.RankThree.PartTwo.Sec19
