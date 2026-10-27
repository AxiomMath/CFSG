module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Props
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Reduce
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6PSL3
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6PSL3Aut
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6PSU3
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6PSU3Aut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace Asch6

open CFSG.Open
open CFSG.GH74.GLS.IVK.Proofs2 (linU₀ uniU₀)

theorem l3OddPointed_psl {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : Odd e) (hq : 3 < p ^ e)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ e) :
    L3OddPointed (StatedProj (StatedSL 3 F)) (linU₀ F) := by
  have hFodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ Nat.card F := by
    rcases hFodd with ⟨k, hk⟩
    omega
  exact
    { orderOf_eq := psl3_orderOf_linU₀ hFodd
      conj := psl3_conj hFodd
      inner := psl3_inner hp hp2 he hF
      quasi := psl3_quasi hFodd h5
      cent := psl3_cent hFodd h5
      gen := psl3_gen hFodd h5
      four := psl3_four hFodd }

theorem l3OddPointed_psu {q : ℕ} (hq : Odd q) (hq3 : 3 < q) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = q ^ 2) : L3OddPointed (StatedProj (StatedSU 3 q F)) (uniU₀ F hq) := by
  have hq5 : 5 ≤ q := by
    rcases hq with ⟨k, hk⟩
    omega
  exact
    { orderOf_eq := psu3_orderOf_uniU₀ hq hF
      conj := psu3_conj hq hF
      inner := psu3_inner hq hq3 hF
      quasi := psu3_quasi hq hq5 hF
      cent := psu3_cent hq hq5 hF
      gen := psu3_gen hq hq5 hF
      four := psu3_four hq hF }

end Asch6

open Asch6 CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (CoverOf)
open CFSG.GH74.GLS.IVK.Proofs2 (linU₀ uniU₀)

theorem asch6_5Odd_holds : Asch6_5Odd := by
  intro Q _ _ V _ _ hV ρ hρ L A hL hZ hAL hA4 hA2 hquad hAC p e Y _ hp hp2 hq hcase hcover
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  unfold CFSG.Open.IsElemAbelian at hA2
  have hA2' : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    have h := hA2.2 a ha
    rwa [pow_two] at h
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.CoverOf] at hcover
  obtain ⟨-, ⟨e₁⟩⟩ := hcover
  rcases hcase with ⟨he, hmodel⟩ | hmodel
  · have hm := CFSG.Blueprint.LieModel.statedClassicalModel hmodel (by decide)
    unfold StatedClassicalModel at hm
    obtain ⟨-, K, _, _, hKcard, ⟨e₂⟩⟩ := hm
    have hX : L3OddPointed (↥L ⧸ Subgroup.center ↥L)
        ((e₁.trans e₂).symm (linU₀ K)) :=
      (l3OddPointed_psl hp hp2 he hq hKcard).of_mulEquiv (e₁.trans e₂).symm
    exact false_of_l3OddPointed_of_rep hV ρ hρ hLq hZ hX hAL hA4 hA2' hquad hAC
  · have hm := CFSG.Blueprint.LieModel.statedClassicalModel hmodel (by decide)
    unfold StatedClassicalModel at hm
    obtain ⟨-, K, _, _, hKcard, ⟨e₂⟩⟩ := hm
    have hqodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
    have hX : L3OddPointed (↥L ⧸ Subgroup.center ↥L)
        ((e₁.trans e₂).symm (uniU₀ K hqodd)) :=
      (l3OddPointed_psu hqodd hq hKcard).of_mulEquiv (e₁.trans e₂).symm
    exact false_of_l3OddPointed_of_rep hV ρ hρ hLq hZ hX hAL hA4 hA2' hquad hAC

end CFSG.LocalAnalysis.WeakClosure81

end
