module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartOne.KFOUT3

abbrev Blk : Type := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

abbrev BComm (b b' : Blk) : Prop := b.1.2 ≠ b'.1.1 ∧ b'.1.2 ≠ b.1.1

@[expose] def rho (π : Equiv.Perm (Fin 3)) (ε : Bool) (b : Blk) : Blk :=
  if ε then ⟨(π b.1.2, π b.1.1), fun h => b.2 (π.injective h).symm⟩
  else ⟨(π b.1.1, π b.1.2), fun h => b.2 (π.injective h)⟩

theorem blk_eq_of_comm_iff : ∀ b b' : Blk, (∀ c, BComm c b ↔ BComm c b') → b = b' := by
  decide

set_option maxRecDepth 100000 in
theorem hexagon_aut : ∀ ρ : Equiv.Perm Blk, (∀ b b', BComm b b' ↔ BComm (ρ b) (ρ b')) →
    ∃ (π : Equiv.Perm (Fin 3)) (ε : Bool), ∀ b, ρ b = rho π ε b := by
  decide +kernel

end CFSG.RankThree.PartOne.KFOUT3
