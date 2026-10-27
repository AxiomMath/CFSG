module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.StandardType.S2MathAs51600RALabels

open CFSG.Assembly
open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem admissible_typeA_of_psl
    {Q : Type} [Group Q] [IsSimpleGroup Q]
    {a m : ℕ} {E : Type} [Field E] [Finite E]
    (ha : 2 ≤ a) (hE : Nat.card E = 2 ^ m)
    (e : Q ≃* StatedProj (StatedSL a E)) :
    LargeEvenInLambda2 ⟨.A, a - 1, m⟩ ∧
      GGHasLabel ⟨.A, a - 1, m⟩ Q := by
  have hM : StatedClassicalModel Q .PSL a 2 m :=
    Y10GInnLin.statedClassicalModel_psl_of_isSimpleGroup ha hE e
  have hM' : StatedClassicalModel Q .PSL (a - 1 + 1) 2 m := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ a)]
    exact hM
  exact ⟨largeEvenInLambda2_typeA hM', ggHasLabel_typeA hM'⟩

theorem admissible_label_of_heldSU_quot_exact
    {Q : Type} [Group Q] [IsSimpleGroup Q] {a m : ℕ} {E : Type} [Field E] [Finite E]
    (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x) (ha : 2 ≤ a)
    (hτ'm : ∀ x, τ' x = x ^ 2 ^ m) (hE : Nat.card E = (2 ^ m) ^ 2)
    (e : Q ≃* heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ')) :
    (a = 2 ∧ GGHasLabel (⟨.A, 1, m⟩ : LargeEvenLabel) Q ∧
        LargeEvenInLambda2 (⟨.A, 1, m⟩ : LargeEvenLabel)) ∨
      (3 ≤ a ∧ GGHasLabel (⟨.twA, a - 1, m⟩ : LargeEvenLabel) Q ∧
        LargeEvenInLambda2 (⟨.twA, a - 1, m⟩ : LargeEvenLabel)) := by
  by_cases ha2 : a = 2
  · subst ha2
    obtain ⟨k, hfK, hfinK, hk, ⟨ψ⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_quot_heldSU_two_equiv_psl τ' hτ' hτ'm hE
    letI : Field k := hfK
    let : Finite k := hfinK
    obtain ⟨hlam, hlab⟩ :=
      CFSG.StandardType.S2MathAs51600RALabels.admissible_typeA_of_psl
        (Q := Q) (a := 2) (m := m) (E := k) (le_refl 2) hk (e.trans ψ)
    exact Or.inl ⟨rfl, hlab, hlam⟩
  · have ha3 : 3 ≤ a := by omega
    have hm : 1 ≤ m := by
      by_contra hm
      have hm0 : m = 0 := by omega
      have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
      rw [hE, hm0] at h2
      norm_num at h2
    have ham : (a, 2 ^ m) ≠ (3, 2) := by
      intro h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      have hm1 : m = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 2)
        (by simpa [pow_one] using h2)
      subst h1
      subst hm1
      have : IsSimpleGroup
          (heldSU 3 E τ' hτ' ⧸ Subgroup.center (heldSU 3 E τ' hτ')) := e.symm.isSimpleGroup
      exact absurd
        (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isSolvable_quot_heldSU_three_two τ' hτ'
          (fun x => by simpa using hτ'm x) (by simpa using hE))
        (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.not_isSolvable_quot_center
          (J := heldSU 3 E τ' hτ'))
    obtain ⟨ψ⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
        CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds τ' hτ' hτ'm hE ha3 ham
    have hb : a - 1 + 1 = a := Nat.sub_add_cancel (by omega : 1 ≤ a)
    have hlab : GGHasLabel (⟨.twA, a - 1, m⟩ : LargeEvenLabel) Q := by
      refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA hE ?_
      rw [hb]
      exact e.trans ψ
    have hlam : LargeEvenInLambda2 (⟨.twA, a - 1, m⟩ : LargeEvenLabel) := by
      refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.largeEvenInLambda2_twA hm (by omega) ?_
      intro hb2
      have ha3' : a = 3 := by omega
      by_contra hm2
      have hm1 : m = 1 := by omega
      exact ham (by simp [ha3', hm1])
    exact Or.inr ⟨ha3, hlab, hlam⟩

theorem admissible_label_of_heldSU_quot
    {Q : Type} [Group Q] [IsSimpleGroup Q]
    {a m : ℕ} {E : Type} [Field E] [Finite E]
    (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x)
    (ha : 2 ≤ a) (hτ'm : ∀ x, τ' x = x ^ (2 ^ m))
    (hE : Nat.card E = (2 ^ m) ^ 2)
    (e : Q ≃* heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ')) :
    ∃ lab : LargeEvenLabel, (lab.tag = .A ∨ lab.tag = .twA) ∧
      LargeEvenInLambda2 lab ∧ GGHasLabel lab Q := by
  rcases admissible_label_of_heldSU_quot_exact τ' hτ' ha hτ'm hE e with
    ⟨rfl, hC, hΛ⟩ | ⟨ha3, hC, hΛ⟩
  · exact ⟨⟨.A, 1, m⟩, Or.inl rfl, hΛ, hC⟩
  · exact ⟨⟨.twA, a - 1, m⟩, Or.inr rfl, hΛ, hC⟩

end CFSG.StandardType.S2MathAs51600RALabels

end
