module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotMove
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree

public section

namespace CFSG.StandardType.QuotMove

open CFSG CFSG.Assembly Matrix

theorem isScalarQuot_PSU {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) :
    IsScalarQuot (TableB.projConj (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d))
      (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d) := by
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0, pow_zero, one_pow] at hK
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, Nat.mul_comm]⟩
  change IsScalarQuot (TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (LargeEvenSUGroup (Fin d) K (2 ^ n))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    refine TableB.scalar_mem_normalizer _ ?_
    rw [largeEvenScalars_def, MonoidHom.mem_range]
    exact ⟨u, rfl⟩
  · intro u
    exact TableB.projConj_of_scalar _ (by
      rw [largeEvenScalars_def, MonoidHom.mem_range]
      exact ⟨u, rfl⟩)
  · intro M hM
    have hu := TableBUE.mem_scalars_of_projConj_eq_one hfield hK hd hdq hp hpq hM
    rw [largeEvenScalars_def, MonoidHom.mem_range] at hu
    obtain ⟨u, hu⟩ := hu
    exact ⟨u, hu.symm⟩
  · exact Subgroup.le_normalizer
  · intro r
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K (2 ^ n))) r
    exact ⟨h, (TableB.projConj_of_mem _ (h : GL (Fin d) K) h.2).symm⟩
  · intro s
    exact ⟨(s : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))),
      (TableB.projConj_of_mem _ (s : GL (Fin d) K) s.2).symm⟩

end CFSG.StandardType.QuotMove
