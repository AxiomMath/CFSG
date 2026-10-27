module

public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm
public import CFSG.LocalAnalysis.StandardType.PhanELocalGate

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def Adm4c (p L H : Submodule K (Fin 4 → K)) : Prop :=
  p ⊓ sgS K f 4 H = ⊥ ∧ L ⊓ sgS K f 4 L = ⊥ ∧ H ⊓ sgS K f 4 p = ⊥

private theorem plh_blockU_a3_4c (x : FlagK K 4) (r : ℕ) :
    blockU K 4 [0, 4] x.E 0 r = x.E r := by
  simp only [blockU, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, Nat.sub_self,
    Nat.zero_add, Vsub_self, Vsub_zero, inf_top_eq, sup_bot_eq]

private theorem plh_mem_farSet_a3_4c (x : FlagK K 4) : x ∈ farSet 4 [0, 4] := by
  intro i hi j hj
  have hi2 : i < 2 := by simpa using hi
  interval_cases i
  · rw [show ([0, 4] : List ℕ).getD 0 0 = 0 from rfl, Vsub_zero, inf_bot_eq, finrank_bot]
    omega
  · rw [show ([0, 4] : List ℕ).getD 1 0 = 4 from rfl, Vsub_self, inf_top_eq, x.dim j hj]
    omega

private theorem plh_blockOK_a3_4c_iff (x : FlagK K 4) :
    blockOK K f 4 [0, 4] [false] x.E 0 ↔
      x.E 1 ⊓ sgS K f 4 (x.E 3) = ⊥ ∧ x.E 2 ⊓ sgS K f 4 (x.E 2) = ⊥ ∧
        x.E 3 ⊓ sgS K f 4 (x.E 1) = ⊥ := by
  have hd : ∀ i, i < ([0, 4] : List ℕ).length → ([0, 4] : List ℕ).getD i 0 ≤ 4 := by
    intro i hi
    have hi2 : i < 2 := by simpa using hi
    interval_cases i <;> decide
  have hmono : ∀ i, i + 1 < ([0, 4] : List ℕ).length →
      ([0, 4] : List ℕ).getD i 0 ≤ ([0, 4] : List ℕ).getD (i + 1) 0 := by
    intro i hi
    have hi1 : i < 1 := by
      have : i + 1 < 2 := by simpa using hi
      omega
    interval_cases i <;> decide
  have hget : ([0, 4] : List ℕ).getD 1 0 = 4 := rfl
  have hget0 : ([0, 4] : List ℕ).getD 0 0 = 0 := rfl
  rw [blockOK_iff_of_far (K := K) (f := f) hd hmono (plh_mem_farSet_a3_4c x) (i := 0)
    (by decide)]
  simp only [plh_blockU_a3_4c, hget, hget0, Vsub_zero, Nat.sub_zero, List.getD_cons_zero,
    List.getD_cons_succ, List.getD_nil, Bool.false_eq_true, ↓reduceIte]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact h 1 (by norm_num) (by norm_num)
    · exact h 2 (by norm_num) (by norm_num)
    · exact h 3 (by norm_num) (by norm_num)
  · rintro ⟨h1, h2, h3⟩ r hr0 hr4
    have hr : r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3

theorem genSet_a3_4c_eq :
    genSet K f 4 [0, 4] [false] = admSet (Adm4c (K := K) f) := by
  ext x
  simp only [genSet, Set.mem_setOf_eq, admSet, Adm4c]
  constructor
  · rintro ⟨-, hblock⟩
    exact (plh_blockOK_a3_4c_iff (K := K) (f := f) x).mp (hblock 0 (by decide))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨plh_mem_farSet_a3_4c x, ?_⟩
    intro i hi
    have hi0 : i = 0 := by
      have : i + 1 < 2 := by simpa using hi
      omega
    rw [hi0]
    exact (plh_blockOK_a3_4c_iff (K := K) (f := f) x).mpr ⟨h1, h2, h3⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
