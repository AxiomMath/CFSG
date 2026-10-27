module

public import CFSG.Quasithin.EmptyFaithful.A38c10MSb
public import CFSG.Quasithin.Background.FLcPerf
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.EmptyFaithful.S1417Natural

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.InternalSec CFSG.Quasithin.S1417
open scoped commutatorElement IsMulCommutative

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_order_three_of_card {Y : Subgroup G} (hc : ∃ a, Nat.card ↥Y = 2 ^ a * 3) :
    ∃ y ∈ Y, orderOf y = 3 := by
  obtain ⟨a, ha⟩ := hc
  have h3 : 3 ∣ Nat.card ↥Y := ⟨2 ^ a, by rw [ha]; ring⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨x, x.2, ?_⟩
  rw [← Subgroup.orderOf_coe] at hx
  exact hx

end Main

variable {G : Type} [Group G] [Finite G]

end CFSG.Quasithin.A38c10
