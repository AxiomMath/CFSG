module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTLift
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTBlock
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTFix

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

section OrthTLabel

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal

private theorem orthTLabel_n_pos {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : 1 ≤ n := by
  have h2 : 1 < 2 ^ n := by
    rw [← hK]
    exact Finite.one_lt_card
  by_contra h
  have hn0 : n = 0 := by omega
  rw [hn0] at h2
  norm_num at h2

private theorem orthTLabel_lam2_A {m n : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) (h3 : 3 ∣ 2 ^ n - 1) :
    LargeEvenInLambda2 ⟨.A, m - 1, n⟩ := by
  show 1 ≤ n ∧ 1 ≤ m - 1 ∧ (m - 1 = 1 → 2 ≤ n)
  refine ⟨hn, by omega, ?_⟩
  intro h
  have hm2 : m = 2 := by omega
  by_contra hlt
  have hn1 : n = 1 := by omega
  rw [hn1] at h3
  exact absurd h3 (by norm_num)

private theorem orthTLabel_lam2_A1 {n : ℕ} (hn : 2 ≤ n) :
    LargeEvenInLambda2 ⟨.A, 1, n⟩ := by
  show 1 ≤ n ∧ 1 ≤ 1 ∧ (1 = 1 → 2 ≤ n)
  exact ⟨by omega, le_refl 1, fun _ => hn⟩

private theorem orthTLabel_lam2_A1_two {n : ℕ} (hn : 1 ≤ n) :
    LargeEvenInLambda2 ⟨.A, 1, 2 * n⟩ := by
  show 1 ≤ 2 * n ∧ 1 ≤ 1 ∧ (1 = 1 → 2 ≤ 2 * n)
  exact ⟨by omega, le_refl 1, fun _ => by omega⟩

private theorem orthTLabel_lam2_twA {m n : ℕ} (hn : 1 ≤ n) (hm : 3 ≤ m)
    (hne : ¬ (n = 1 ∧ m = 3)) : LargeEvenInLambda2 ⟨.twA, m - 1, n⟩ := by
  show 1 ≤ n ∧ 2 ≤ m - 1 ∧ (m - 1 = 2 → 2 ≤ n)
  refine ⟨hn, by omega, ?_⟩
  intro h
  have hm3 : m = 3 := by omega
  by_contra hlt
  have hn1 : n = 1 := by omega
  exact hne ⟨hn1, hm3⟩

private theorem orthTLabel_lam2_A3 {n : ℕ} (hn : 1 ≤ n) :
    LargeEvenInLambda2 ⟨.A, 3, n⟩ := by
  show 1 ≤ n ∧ 1 ≤ 3 ∧ (3 = 1 → 2 ≤ n)
  exact ⟨hn, by norm_num, fun h => absurd h (by norm_num)⟩

private theorem orthTLabel_lam2_twA3 {n : ℕ} (hn : 1 ≤ n) :
    LargeEvenInLambda2 ⟨.twA, 3, n⟩ := by
  show 1 ≤ n ∧ 2 ≤ 3 ∧ (3 = 2 → 2 ≤ n)
  exact ⟨hn, by norm_num, fun h => absurd h (by norm_num)⟩

private theorem orthTLabel_lam2_D {s n : ℕ} (hn : 1 ≤ n) (hs : 3 ≤ s) :
    LargeEvenInLambda2 ⟨.D, s, n⟩ := by
  show 1 ≤ n ∧ 3 ≤ s
  exact ⟨hn, hs⟩

private theorem orthTLabel_lam2_twD {s n : ℕ} (hn : 1 ≤ n) (hs : 2 ≤ s) :
    LargeEvenInLambda2 ⟨.twD, s, n⟩ := by
  show 1 ≤ n ∧ 2 ≤ s
  exact ⟨hn, hs⟩

private theorem orthTLabel_block {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    {h : K[X]} (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    {L : Subgroup (ProjOrthDerived Q)} (hL : L = componentImage Q (x : V ≃ₗ[K] V) h) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (L ⧸ Subgroup.center L) ∧
      (lab.tag = .A ∨ (lab.tag = .twA ∧ (lab.rank = 2 → lab.n = n ∧ 3 ∣ 2 ^ n + 1)) ∨
        lab.tag = .B ∨ lab.tag = .C ∨ ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ lab.n = n)) := by
  obtain ⟨hm2, -, hdisj⟩ := orthT_blockLabel hK hx hh hne1 hq hL
  have hn : 1 ≤ n := orthTLabel_n_pos hK
  rcases hdisj with ⟨_, h3dvd, hlabel⟩ | ⟨_, h3dvd, hlabel⟩
  · exact ⟨⟨.A, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩,
      orthTLabel_lam2_A hn hm2 h3dvd, hlabel, Or.inl rfl⟩
  · rcases hlabel with ⟨hm2', hn2, hlabel⟩ | ⟨hm3, hne', hlabel⟩
    · exact ⟨⟨.A, 1, n⟩, orthTLabel_lam2_A1 hn2, hlabel, Or.inl rfl⟩
    · exact ⟨⟨.twA, primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h - 1, n⟩,
        orthTLabel_lam2_twA hn hm3 hne', hlabel,
        Or.inr (Or.inl ⟨rfl, fun _ => ⟨rfl, h3dvd⟩⟩)⟩

private theorem orthTLabel_fixed {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V))
    (hFn : (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal)
    {L : Subgroup (ProjOrthDerived Q)}
    (hL : L = (F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (L ⧸ Subgroup.center L) ∧
      (lab.tag = .A ∨ (lab.tag = .twA ∧ (lab.rank = 2 → lab.n = n ∧ 3 ∣ 2 ^ n + 1)) ∨
        lab.tag = .B ∨ lab.tag = .C ∨ ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ lab.n = n)) := by
  obtain ⟨s, -, hdisj⟩ := orthT_fixedLabel hK hQ hx hFq hFle hFn hL
  have hn : 1 ≤ n := orthTLabel_n_pos hK
  rcases hdisj with ⟨h4s, _, hlabel⟩ | ⟨h4s, _, hlabel⟩ | ⟨hs3, _, hlabel⟩ |
    ⟨hs3, _, hlabel⟩ | ⟨hs2, _, hlabel⟩ | ⟨hs2, _, hn2, hlabel⟩
  · exact ⟨⟨.D, s, n⟩, orthTLabel_lam2_D hn (by omega), hlabel,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, h4s, rfl⟩)))⟩
  · exact ⟨⟨.twD, s, n⟩, orthTLabel_lam2_twD hn (by omega), hlabel,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr rfl, h4s, rfl⟩)))⟩
  · exact ⟨⟨.A, 3, n⟩, orthTLabel_lam2_A3 hn, hlabel, Or.inl rfl⟩
  · exact ⟨⟨.twA, 3, n⟩, orthTLabel_lam2_twA3 hn, hlabel,
      Or.inr (Or.inl ⟨rfl, fun h => absurd (show (3 : ℕ) = 2 from h) (by norm_num)⟩)⟩
  · exact ⟨⟨.A, 1, 2 * n⟩, orthTLabel_lam2_A1_two hn, hlabel, Or.inl rfl⟩
  · exact ⟨⟨.A, 1, n⟩, orthTLabel_lam2_A1 hn2, hlabel, Or.inl rfl⟩

end OrthTLabel

theorem orthT_label {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q)) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (J' ⧸ Subgroup.center J') ∧
      (lab.tag = .A ∨ (lab.tag = .twA ∧ (lab.rank = 2 → lab.n = n ∧ 3 ∣ 2 ^ n + 1)) ∨
        lab.tag = .B ∨ lab.tag = .C ∨ ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ lab.n = n)) := by
  obtain ⟨x, _, _, hx, _, _, _, _, _, _, _, _, hcases⟩ := orthT_lift hQ hT hR hĀI
  rcases hcases with ⟨h, hh, hne1, hq, hJ'⟩ | ⟨F, hFq, hFle, hFn, hJ'⟩
  · exact orthTLabel_block hK hx hh hne1 hq (L := J') hJ'
  · exact orthTLabel_fixed hK hQ hx hFq hFle hFn (L := J') hJ'

end CFSG.StandardType.TablePThreeKG

end
