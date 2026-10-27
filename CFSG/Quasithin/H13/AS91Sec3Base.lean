module

public import CFSG.Quasithin.H13.AS91Sec3Defs

public section

namespace CFSG.Quasithin.H13.AS91.M24G

@[expose] def maskFin (m : ℕ) : Finset (Fin 24) := Finset.univ.filter fun i => m.testBit i = true

theorem mem_maskFin {m : ℕ} {i : Fin 24} : i ∈ maskFin m ↔ m.testBit i = true := by
  simp [maskFin]

@[expose] def RepT (t : Array ℕ) (g : Equiv.Perm (Fin 24)) : Prop :=
  ∀ i : Fin 24, t[i.val]! = (g i).val

end CFSG.Quasithin.H13.AS91.M24G
