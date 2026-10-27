module

public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructIso

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank

namespace Gold14610

namespace Struct

noncomputable def pglEquiv (K : Type) [Field K] :
    GL (Fin 2) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K ≃* PGL2 K :=
  QuotientGroup.quotientMulEquivOfEq
    (by rw [CFSG.Assembly.LowTwoRank.StatedScalars,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar])

variable {D : Type} [Group D]

theorem idx2Data_of_isPGL2 {q : ℕ} (hq : q.Prime) (hq24 : q % 24 = 11 ∨ q % 24 = 13)
    (h : F6.IsPGL2 q D) : Idx2Data D := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨q, 1, hq, by rw [Nat.odd_iff]; omega, le_rfl, by rw [hK, pow_one]⟩
  set Kb : Subgroup (PGL2 K) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range with hKb
  have hidx : Kb.index = 2 := pgl2_psl2Range_index_eq_two K hodd
  have : Kb.Normal := Subgroup.normal_of_index_eq_two hidx
  have : Kb.FiniteIndex := ⟨by omega⟩
  have hL2 : F6.IsL2 q 1 ↥Kb := by
    refine ⟨⟨hq, le_rfl, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, by rw [hK, pow_one],
      ⟨(psl2EquivToPGLRange K).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩⟩
    · rw [pow_one]; intro h; simp at h; omega
    · rw [pow_one]; intro h; simp at h; omega
  refine Idx2Data.of_mulEquiv (e.trans (pglEquiv K)) ⟨Kb, inferInstance,
    Or.inl ⟨q, hq, hq24, hL2⟩, fun x => ?_, Or.inl ?_⟩
  · have := Subgroup.pow_index_mem Kb x
    rwa [hidx] at this
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 q 1 hL2).2

end Struct

end Gold14610

end CFSG.Quasithin
