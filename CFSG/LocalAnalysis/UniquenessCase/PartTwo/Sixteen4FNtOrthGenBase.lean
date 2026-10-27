module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOrthGenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOrthGenAux1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

private abbrev w183VecP (a0 a1 a2 b0 b1 b2 : ZMod 2) : Fin 3 ⊕ Fin 3 → ZMod 2 :=
  Sum.elim ![a0, a1, a2] ![b0, b1, b2]

private def w183BasePlus : Finset (Fin 3 ⊕ Fin 3 → ZMod 2) :=
  {w183VecP 0 0 1 0 0 1, w183VecP 0 0 1 0 1 1, w183VecP 0 0 1 1 0 1,
   w183VecP 0 0 1 1 1 1, w183VecP 0 1 0 0 1 0, w183VecP 0 1 0 0 1 1,
   w183VecP 1 0 0 1 0 0}

private abbrev w183VecM (x y u v : ZMod 2) :
    Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2 :=
  Sum.elim ![x] (Sum.elim ![y] ![u, v])

private def w183BaseMinus : Finset (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2) :=
  {w183VecM 0 0 0 1, w183VecM 0 0 1 0, w183VecM 0 1 0 1, w183VecM 1 0 0 1}

private theorem w183GenIterateNormOne {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq K] (Q : (ι → K) → K) (s : Finset (ι → K)) (k : ℕ)
    (hcheck : ∀ v, Q v = 1 → v ∈ (w183StepF Q (s16ntPolar Q))^[k] s) :
    S16ntNormOneGen Q (s : Set (ι → K)) := by
  intro T hT hcl v hv
  exact w183SubsetIterate Q (s16ntPolar Q)
    (fun u hu => hT (Finset.mem_coe.mpr hu)) hcl k v (hcheck v hv)

theorem s16nt_gen_base_plus : ∃ S : Set (Fin 3 ⊕ Fin 3 → ZMod 2), S.ncard ≤ 7 ∧
    (∀ v ∈ S, StatedQuadPlus 3 (ZMod 2) v = 1) ∧
      S16ntNormOneGen (StatedQuadPlus 3 (ZMod 2)) S := by
  refine ⟨↑w183BasePlus, ?_, ?_, ?_⟩
  · rw [Set.ncard_coe_finset]
    decide +kernel
  · intro v hv
    exact (by decide +kernel : ∀ v ∈ w183BasePlus,
      StatedQuadPlus 3 (ZMod 2) v = 1) v (Finset.mem_coe.mp hv)
  · refine w183GenIterateNormOne (StatedQuadPlus 3 (ZMod 2)) w183BasePlus 3 ?_
    decide +kernel

theorem s16nt_gen_base_minus : ∃ S : Set (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2),
    S.ncard ≤ 4 ∧ (∀ v ∈ S, StatedQuadMinus 2 (ZMod 2) 1 1 v = 1) ∧
      S16ntNormOneGen (StatedQuadMinus 2 (ZMod 2) 1 1) S := by
  refine ⟨↑w183BaseMinus, ?_, ?_, ?_⟩
  · rw [Set.ncard_coe_finset]
    decide +kernel
  · intro v hv
    exact (by decide +kernel : ∀ v ∈ w183BaseMinus,
      StatedQuadMinus 2 (ZMod 2) 1 1 v = 1) v (Finset.mem_coe.mp hv)
  · refine w183GenIterateNormOne (StatedQuadMinus 2 (ZMod 2) 1 1) w183BaseMinus 2 ?_
    decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
