module

public import CFSG.Quasithin.Background.C126A5PermBasic

public section

namespace CFSG.Quasithin.C126.A5

open Equiv Equiv.Perm

@[expose] def permAct (g : Perm (Fin 5)) (x : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 :=
  fun i => x (g⁻¹ i)

@[expose] def alts : Finset (Perm (Fin 5)) := Finset.univ.filter fun g => sign g = 1

@[expose] def orb (x : Fin 5 → ZMod 2) : Finset (Fin 5 → ZMod 2) :=
  insert 0 (alts.image fun g => permAct g x)

@[expose] def delta5 : Finset (Fin 5 → ZMod 2) := Finset.univ.filter fun x => ∑ i, x i = 0

theorem mem_alts {g : Perm (Fin 5)} : g ∈ alts ↔ sign g = 1 := by simp [alts]

theorem mem_delta5 {x : Fin 5 → ZMod 2} : x ∈ delta5 ↔ ∑ i, x i = 0 := by simp [delta5]

theorem mem_orb {x y : Fin 5 → ZMod 2} :
    y ∈ orb x ↔ y = 0 ∨ ∃ g ∈ alts, permAct g x = y := by
  simp [orb, eq_comm]

set_option synthInstance.maxSize 2000 in
theorem ev5_irred : ∀ x ∈ delta5, x ≠ 0 → ∀ y ∈ delta5, ∃ a ∈ orb x, ∃ b ∈ orb x, y = a + b := by
  unfold delta5 orb alts permAct
  decide +kernel

theorem ev5_fix : ∀ x ∈ delta5, (∀ g ∈ alts, permAct g x = x) → x = 0 := by
  unfold delta5 alts permAct
  decide +kernel

theorem ev5_four : ∀ π : Perm (Fin 5),
    4 ≤ (delta5.image fun v => permAct (cyc3 π) v + v).card := by
  unfold delta5 permAct cyc3
  decide +kernel

end CFSG.Quasithin.C126.A5
