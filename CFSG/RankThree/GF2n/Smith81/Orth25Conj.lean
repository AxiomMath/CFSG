module

public import CFSG.RankThree.GF2n.Smith81.OrthStmt

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_mem_M_eq_conj_of_25 (h25 : Smith25OrthStatement) (hc : SmithOrthCfg M Q Z B)
    {C : Subgroup G} (hC : Ctx M Q Z C) : ∃ m ∈ M, C = conjSubgroup m B := by
  have hmem : C ⊔ Z ∈ {V : Subgroup G | ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧
      V = A ⊔ Z} := ⟨C, hC.conj, hC.le, hC.ne, rfl⟩
  rw [h25 G M Q Z B hc] at hmem
  obtain ⟨m, hm, hCm⟩ := hmem
  have hcm : Ctx M Q Z (conjSubgroup m B) := hc.ctx.conj_of_mem hm
  have hle : conjSubgroup m B ≤ Z ⊔ C := by
    rw [sup_comm, hCm]
    exact le_sup_left
  obtain ⟨p, hpQ, hp⟩ := hC.exists_conj_of_le_ZB hcm hle
  have hpM : p ∈ M := hc.ctx.hyp.Q_normal.1 hpQ
  refine ⟨p⁻¹ * m, M.mul_mem (M.inv_mem hpM) hm, ?_⟩
  rw [conjSubgroup_mul, ← hp, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

theorem LB_le_Lgen_of_25 (h25 : Smith25OrthStatement) (hc : SmithOrthCfg M Q Z B)
    {C : Subgroup G} (hC : Ctx M Q Z C) : LB M Q C ≤ Lgen M (LB M Q B) := by
  obtain ⟨m, hm, rfl⟩ := exists_mem_M_eq_conj_of_25 h25 hc hC
  rw [hc.ctx.LB_conj hm]
  exact le_iSup₂_of_le m hm le_rfl

end CFSG.RankThree.GF2n.Smith81
