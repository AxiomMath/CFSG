module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

open Equiv Equiv.Perm

theorem false_of_surjective_alt7 {W : Type} [Group W] [Finite W]
    (hcyc : ∀ P : Sylow 3 W, IsCyclic P) {f : W →* alternatingGroup (Fin 7)}
    (hf : Function.Surjective f) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : ∀ Q : Sylow 3 (alternatingGroup (Fin 7)), IsCyclic Q := fun Q =>
    CFSG.RankThree.PartTwo.Sec11.KS11LieProof.isCyclic_sylow_of_surjective f hf hcyc Q
  have hu : (c[0, 1, 2] : Perm (Fin 7)) ∈ alternatingGroup (Fin 7) := by
    rw [mem_alternatingGroup]
    decide
  have hv : (c[3, 4, 5] : Perm (Fin 7)) ∈ alternatingGroup (Fin 7) := by
    rw [mem_alternatingGroup]
    decide
  have hu3 : (c[0, 1, 2] : Perm (Fin 7)) ^ 3 = 1 := by decide
  have hv3 : (c[3, 4, 5] : Perm (Fin 7)) ^ 3 = 1 := by decide
  have hu1 : (c[0, 1, 2] : Perm (Fin 7)) ≠ 1 := by decide
  have huv : (c[0, 1, 2] : Perm (Fin 7)) * c[3, 4, 5] = c[3, 4, 5] * c[0, 1, 2] := by decide
  have hfix : (c[0, 1, 2] : Perm (Fin 7)) 3 = 3 := by decide
  have hmov : (c[3, 4, 5] : Perm (Fin 7)) 3 ≠ 3 := by decide
  refine CFSG.RankThree.PartTwo.Sec11.KS11LieProof.false_of_isCyclic_sylow hA
    (u := ⟨c[0, 1, 2], hu⟩) (v := ⟨c[3, 4, 5], hv⟩) ?_ ?_ ?_ ?_ ?_
  · exact Subtype.ext (by simpa using hu3)
  · exact Subtype.ext (by simpa using hv3)
  · exact fun h => hu1 (congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using huv)
  · rintro ⟨k, hk⟩
    have h := congrArg (fun a : alternatingGroup (Fin 7) => (a : Perm (Fin 7)) 3) hk
    simp only [Subgroup.coe_zpow] at h
    rw [zpow_apply_eq_self_of_apply_eq_self hfix k] at h
    exact hmov h.symm

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
