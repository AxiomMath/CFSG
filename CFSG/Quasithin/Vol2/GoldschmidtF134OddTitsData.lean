module

public import CFSG.Quasithin.Vol2.F134TitsTables

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin.F134

@[expose] def titsBad5L : List ℕ :=
  [0, 3107, 0, 5165, 2093, 3117, 6189, 16429, 2093, 2093, 4141, 16429, 3117, 2093, 1069, 5165,
    1069, 45]

@[expose] def titsBad5 (j : ℕ) : ℕ := titsBad5L.getD j 0

theorem tits_bad5_check : ∀ j < 18, j ≠ 0 → j ≠ 2 →
    (titsBad5 j % 32 = 3 ∨ titsBad5 j % 32 = 13) ∧ titsBad5 j / 1024 < 2048 ∧
    titsPow (titsBad5 j % 32)
        (titsPow (titsBad5 j / 32 % 32) (mulF26 (titsDC j) (titsNFC (titsBad5 j / 1024)))) =
      titsOneC ∧
    titsPow (titsBad5 j / 32 % 32) (mulF26 (titsDC j) (titsNFC (titsBad5 j / 1024))) ≠
      titsOneC := by
  decide +kernel

end CFSG.Quasithin.H13.NQCore
