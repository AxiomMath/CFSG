module

import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L2OddWords
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Tools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup Matrix CFSG.GorensteinWalter

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

private theorem center_eq_bot_of_mulEquiv_L2Odd {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hg' : e g ∈ Subgroup.center H := Subgroup.mem_center_iff.mpr fun y => by
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hg x]
  rw [h, Subgroup.mem_bot] at hg'
  rw [Subgroup.mem_bot]
  exact e.injective (hg'.trans (map_one e).symm)

private theorem asc82Item1411_L2_sq (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    (h : Hyp1411 X L S) {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p 2)))
    (hS : IsCyclic ↥(S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))))
    {q k : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk : 1 ≤ k)
    (h8 : ∀ e : ℕ, 1 ≤ e → e ≤ 8 → ¬ q ^ k ∣ 2 ^ e - 1)
    (hW : ∀ α : MulAut (PSL2 (GaloisField p 2)), orderOf α = 2 →
      ∃ x₁ x₂ x₃, q ^ k ∣ orderOf (word1411 α x₁ x₂ x₃)) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal := by
  obtain ⟨e⟩ := hL
  set ε := e.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField p 2)) with hε
  have hcard : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hsimp : IsSimpleGroup ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) := by
    have := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField p 2) le_rfl
      (Or.inr (by rw [hcard]; nlinarith)) (Or.inr (by rw [hcard]; nlinarith))
    exact e.isSimpleGroup
  have hZ := center_eq_bot_of_mulEquiv_L2Odd ε (psl2_center_eq_bot (GaloisField p 2))
  refine asc82Item1411_of_forall_word1411 h hS hsimp hZ hq hq2 hk h8 fun α hα => ?_
  have hα' : orderOf (MulAut.congr ε α) = 2 := by rw [MulEquiv.orderOf_eq]; exact hα
  obtain ⟨y₁, y₂, y₃, hy⟩ := hW _ hα'
  refine ⟨ε.symm y₁, ε.symm y₂, ε.symm y₃, ?_⟩
  have e1 := word1411_congr ε α (ε.symm y₁) (ε.symm y₂) (ε.symm y₃)
  simp only [MulEquiv.apply_symm_apply] at e1
  rw [← MulEquiv.orderOf_eq ε, ← e1]
  exact hy

theorem asc82Item1411_L2_25 (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    [Fact (Nat.Prime 5)] (h : Hyp1411 X L S)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 5 2)))
    (hS : IsCyclic ↥(S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal := by
  refine asc82Item1411_L2_sq X L S h le_rfl hL hS (q := 13) (k := 1) (by norm_num) (by norm_num)
    le_rfl (fun e he1 he8 => by interval_cases e <;> norm_num) fun α hα => ?_
  rw [pow_one]
  exact exists_word1411_L2_25 (by rw [GaloisField.card 5 2 (by norm_num)]; norm_num) α hα

theorem asc82Item1411_L2_49 (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    [Fact (Nat.Prime 7)] (h : Hyp1411 X L S)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 7 2)))
    (hS : IsCyclic ↥(S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal := by
  refine asc82Item1411_L2_sq X L S h (by norm_num) hL hS (q := 5) (k := 2) (by norm_num)
    (by norm_num) (by norm_num) (fun e he1 he8 => by interval_cases e <;> norm_num)
    fun α hα => ?_
  exact exists_word1411_L2_49 (by rw [GaloisField.card 7 2 (by norm_num)]; norm_num) α hα

theorem asc82Item1411_L2_25_49 (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    (h : Hyp1411 X L S) {p : ℕ} [Fact p.Prime] (hp : p = 5 ∨ p = 7)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p 2)))
    (hS : IsCyclic ↥(S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal := by
  rcases hp with rfl | rfl
  · exact asc82Item1411_L2_25 X L S h hL hS
  · exact asc82Item1411_L2_49 X L S h hL hS

end CFSG.RankThree.PartTwo.Sec20
