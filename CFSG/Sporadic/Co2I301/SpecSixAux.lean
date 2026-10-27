
module

public import CFSG.Sporadic.Co2I301.SpecSixAuxBase
import all CFSG.Sporadic.Co2I301.SpecSixAuxBase

public import Certificates.Certificate810301

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2I301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
  CFSG.Sporadic.SmallF2 CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.HardMathSupport.Dickson.I271
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (basisMatrixEquiv
  basisMatrixEquiv_mulVec basisMatrixEquiv_val)
open scoped Matrix

section Small

theorem smallCheck_six_cols :
    Rep 2300 (i301K1 ()) (permOfArr 2300 (i301K1 ())) ∧
      Rep 2300 (i301K2 ()) (permOfArr 2300 (i301K2 ())) ∧
      Rep 2300 (i301D ()) (permOfArr 2300 (i301D ())) ∧
      sixColsOK (i301K1 ()) = true ∧ sixColsOK (i301K2 ()) = true ∧
      sixColsOK (i301D ()) = true := by
  have h := (Certificates.certificate810301).1
  simp only [smallCheck, Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, hD, -, -, -, -, -, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, h1, h2, h3⟩ := h
  obtain ⟨hc, -, -⟩ := caseChainOK2P_parts hK
  have hF := chainCheckFacts hc
  have hsz : (k0Arrs ()).size = 5 := by simp [k0Arrs]
  exact ⟨(rep_permOfArr (hF.strong_inv 0 (by omega))).1,
    (rep_permOfArr (hF.strong_inv 1 (by omega))).1, rep_of_validA hD, h1, h2, h3⟩

end Small

section Main

theorem six_facts_of_cols (c₁ c₂ c₃ : locC)
    (h₁ : (c₁ : Equiv.Perm (Fin 2300)) = permOfArr 2300 (i301K1 ()))
    (h₂ : (c₂ : Equiv.Perm (Fin 2300)) = permOfArr 2300 (i301K2 ()))
    (h₃ : (c₃ : Equiv.Perm (Fin 2300)) = permOfArr 2300 (i301D ())) :
    ∀ g ∈ Subgroup.closure {π | ∃ i < 2, sixPi i = π}, g * g = 1 → g ≠ 1 →
      ∃ w ∈ hlWords, ¬ Commute g
        ((w.map fun i => [toPerm63 (sixAction c₁), toPerm63 (sixAction c₂),
            toPerm63 (sixAction c₃)].getD i 1).prod * g *
          ((w.map fun i => [toPerm63 (sixAction c₁), toPerm63 (sixAction c₂),
            toPerm63 (sixAction c₃)].getD i 1).prod)⁻¹) := by
  obtain ⟨r₁, r₂, r₃, k₁, k₂, k₃⟩ := smallCheck_six_cols
  rw [← h₁] at r₁
  rw [← h₂] at r₂
  rw [← h₃] at r₃
  set Ys : List (Equiv.Perm (Fin 63)) :=
    [toPerm63 (sixAction c₁), toPerm63 (sixAction c₂), toPerm63 (sixAction c₃)]
  have hgen : ∀ i < 3, Rep 63
      (#[perm63Of (i301K1 ()), perm63Of (i301K2 ()), perm63Of (i301D ())] :
        Array (Array ℕ))[i]! (Ys.getD i 1) := by
    intro i hi
    interval_cases i
    · exact rep_perm63Of c₁ r₁ k₁
    · exact rep_perm63Of c₂ r₂ k₂
    · exact rep_perm63Of c₃ r₃ k₃
  have hHL : ∀ t < (hl63 ()).size,
      Rep 63 (hl63 ())[t]! (((hlWords.getD t []).map fun i => Ys.getD i 1).prod) := by
    intro t ht
    rw [hl63_size] at ht
    rw [hl63_get ht]
    refine rep_word63 _ fun i hi => hgen i (hlWords_letters _ ?_ i hi)
    rw [List.getD_eq_getElem _ _ ht]
    exact List.getElem_mem ht
  intro g hg hgg hg1
  have hsix : RowSixFacts := Certificates.certificate810301.2.2
  obtain ⟨t, ht, hc⟩ := hsix (fun t => ((hlWords.getD t []).map fun i => Ys.getD i 1).prod) hHL g
    hg hgg hg1
  rw [hl63_size] at ht
  refine ⟨hlWords.getD t [], ?_, hc⟩
  rw [List.getD_eq_getElem _ _ ht]
  exact List.getElem_mem ht

end Main

end CFSG.Sporadic.Co2I301
