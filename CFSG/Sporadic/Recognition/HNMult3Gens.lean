module

public import CFSG.Sporadic.GLQ.HNTwoRank
public import CFSG.Sporadic.Recognition.HNMult3Data

public section

namespace CFSG.Sporadic.Recognition.HNMult3

open CFSG.Sporadic.GLQ CFSG.Sporadic.GLQ.HNTwoRank

@[expose] def hn3Reg : Fin 3 → ℕ := ![11, 12, 13]


@[expose] noncomputable def Rg : ℕ → GLHN := runProg (initRegs gA gB) hn3Prog

theorem Rg_mem (r : ℕ) : Rg r ∈ J := by
  have hgA : gA ∈ J := Subgroup.subset_closure (Set.mem_insert _ _)
  have hgB : gB ∈ J := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact runProg_mem J hn3Prog (initRegs_mem J hgA hgB) r

@[expose] noncomputable def gN (i : Fin 3) : GLHN := Rg (hn3Reg i)

@[expose] noncomputable def Nsub : Subgroup GLHN := Subgroup.closure (Set.range gN)

theorem gN_mem (i : Fin 3) : gN i ∈ J := Rg_mem _

theorem Nsub_le_J : Nsub ≤ J := by
  rw [Nsub, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact gN_mem i

end CFSG.Sporadic.Recognition.HNMult3
