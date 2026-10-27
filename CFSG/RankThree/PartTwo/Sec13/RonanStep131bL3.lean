module

import CFSG.Open.PGLModelStated
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bL3Lin
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bL3Uni
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitaryPSUEquiv)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.PGLModel (projSUEquivStatedProj)
open CFSG.RankThree.PartTwo.KFacts (eq_frobenius_pow_of_orderOf_eq_three)
open CFSG.RankThree.PartTwo.KFacts.L34 (projSLEquivProjectiveSL)
open L3 (exists_stable_of_mulEquiv norm2e_projectiveSL norm2e_unitaryPSU)

theorem norm2e_projSL (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hq : p ^ e % 3 = 1) :
    ∀ P : Subgroup (MulAut (projSL 3 (GaloisField p e))), IsPGroup 3 P → (∀ σ ∈ P, σ ^ 3 = 1) →
      Nat.card P ≤ 9 →
      ∃ V : Subgroup (projSL 3 (GaloisField p e)), V ≠ ⊥ ∧ IsPGroup 2 V ∧
        ∀ σ ∈ P, V.map σ.toMonoidHom = V := by
  intro P hP hP3 _
  refine exists_stable_of_mulEquiv (projSLEquivProjectiveSL 3 (GaloisField p e)) ?_
  exact norm2e_projectiveSL p e hp he1 he2 hq _ (hP.map _) (by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [← map_pow, hP3 σ hσ, map_one])

theorem norm2e_projSU (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hq : p ^ e % 3 = 2) :
    ∀ P : Subgroup (MulAut (projSU 3 p e)), IsPGroup 3 P → (∀ σ ∈ P, σ ^ 3 = 1) →
      Nat.card P ≤ 9 →
      ∃ V : Subgroup (projSU 3 p e), V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ σ ∈ P, V.map σ.toMonoidHom = V := by
  intro P hP hP3 _
  have hcard : Nat.card (GaloisField p (2 * e)) = p ^ (2 * e) :=
    GaloisField.card p (2 * e) (by omega)
  have h : UnitaryFieldData p e (GaloisField p (2 * e)) := ⟨Fact.out, he1, hcard⟩
  have hno : ∀ τ : GaloisField p (2 * e) ≃+* GaloisField p (2 * e), orderOf τ ≠ 3 := by
    intro τ hτ
    have := (eq_frobenius_pow_of_orderOf_eq_three (Fact.out : p.Prime) (by omega : 1 ≤ 2 * e)
      hcard hτ).1
    omega
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd (p ^ e) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hq2 : 2 < p ^ e :=
    lt_of_lt_of_le (by omega : 2 < p) (Nat.le_self_pow (by omega : e ≠ 0) p)
  let ι : projSU 3 p e ≃* unitaryPSU h 3 :=
    (projSUEquivStatedProj 3 p e).trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm
  refine exists_stable_of_mulEquiv ι ?_
  exact norm2e_unitaryPSU h hq2 hq hodd hp2 hno _ (hP.map _) (by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [← map_pow, hP3 σ hσ, map_one])

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
