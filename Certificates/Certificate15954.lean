module

public import CFSG.Monster.B.Pinned.Primes.Data
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import Certificates.Certificate3106
public import Certificates.Data.CFSGNative.MonsterB.Primes
public import Certificates.Data.Kernel.BabyMonster.Pair24

public section

namespace CFSG.Monster.B.Pinned

open Bin Primes.Native CFSG.Blueprint

private theorem cert15954_0 : ∀ i j : Fin 4, (fiveCommRows.getD i []).getD j 0 < 5 := by
  decide +kernel

private theorem cert15954_1 : ∀ i : Fin 4, (fiveActRows.getD i []).length = 4 := by
  decide +kernel

private theorem cert15954_2 : ∀ i j : Fin 4, (fiveActRows.getD i []).getD j 0 < 5 := by
  decide +kernel

private theorem cert15954_3 : ∀ i : Fin 4, fiveActC.getD i 0 < 5 := by
  decide +kernel

private theorem cert15954_4 : ∀ i j : Fin 4, (fiveCommRows.getD i []).getD j 0 < 5 := by
  decide +kernel

private theorem cert15954_5 : ∀ i : Fin 4, (fiveCommRows.getD i []).getD i 0 = 0 := by
  decide +kernel

private theorem cert15954_6 : ∀ i j : Fin 4,
    ((fiveCommRows.getD i []).getD j 0 + (fiveCommRows.getD j []).getD i 0) % 5 = 0 := by
  decide +kernel

end CFSG.Monster.B.Pinned

namespace Certificates

open CFSG.Monster.B.Pinned in
theorem certificate15954 : (
    ∀ i j : Fin 4, (fiveCommRows.getD i []).getD j 0 < 5
  ) ∧ (
    ∀ i : Fin 4, (fiveActRows.getD i []).length = 4
  ) ∧ (
    ∀ i j : Fin 4, (fiveActRows.getD i []).getD j 0 < 5
  ) ∧ (
    ∀ i : Fin 4, fiveActC.getD i 0 < 5
  ) ∧ (
    ∀ i j : Fin 4, (fiveCommRows.getD i []).getD j 0 < 5
  ) ∧ (
    ∀ i : Fin 4, (fiveCommRows.getD i []).getD i 0 = 0
  ) ∧ (
    ∀ i j : Fin 4,
      ((fiveCommRows.getD i []).getD j 0 + (fiveCommRows.getD j []).getD i 0) % 5 = 0
  ) := by
  exact ⟨CFSG.Monster.B.Pinned.cert15954_0, CFSG.Monster.B.Pinned.cert15954_1,
    CFSG.Monster.B.Pinned.cert15954_2, CFSG.Monster.B.Pinned.cert15954_3,
    CFSG.Monster.B.Pinned.cert15954_4, CFSG.Monster.B.Pinned.cert15954_5,
    CFSG.Monster.B.Pinned.cert15954_6⟩

end Certificates
