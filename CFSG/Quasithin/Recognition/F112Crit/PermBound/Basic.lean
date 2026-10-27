module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.F112Crit.PermBound

variable {H : Type*} [Group H]

@[expose] def commL (M : Type*) [AddCommGroup M] [DistribMulAction H M] (L : Subgroup H) :
    AddSubgroup M :=
  AddSubgroup.closure {x | ∃ l ∈ L, ∃ m : M, x = l • m - m}

theorem sub_mem_commL {M : Type*} [AddCommGroup M] [DistribMulAction H M] {L : Subgroup H}
    {l : H} (hl : l ∈ L) (m : M) : l • m - m ∈ commL M L :=
  AddSubgroup.subset_closure ⟨l, hl, m, rfl⟩

end CFSG.Quasithin.F112Crit.PermBound

end
