module

public import CFSG.Quasithin.H13.U3S1347Q
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.VolIH5

public section

namespace CFSG.Quasithin.H13.U3

namespace L32Mod

open CFSG.Quasithin.H6

theorem core_fix_three : ∀ g : Γ, g ^ 3 = 1 → g ≠ 1 →
    (Finset.univ.filter fun f : Fin 8 → ZMod 2 =>
      (f 0 = 0 ∧ ∑ i, f i = 0) ∧ actF g f = f).card ≤ 4 := by
  decide +kernel

theorem sum_fix_three : ∀ g : Γ, g ^ 3 = 1 → g ≠ 1 →
    (Finset.univ.filter fun p : V3 × V3 => g • p.1 = p.1 ∧ graph g • p.2 = p.2).card ≤ 4 := by
  decide +kernel

end L32Mod

open Equiv CFSG.Quasithin.H13.A6 S6Out

theorem a6_fix_three : ∀ σ : Perm (Fin 6), σ ^ 3 = 1 → σ ≠ 1 → Perm.sign σ = 1 →
    fixCount [σ] * fixCount [phi (cc⁻¹ * σ * cc)] ≤ 4 := by
  decide +kernel

end CFSG.Quasithin.H13.U3
