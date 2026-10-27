module

public import CFSG.Quasithin.Background.C116Two.NatCount
public import CFSG.Quasithin.Background.C116Two.OrbitPieces
public import CFSG.Quasithin.Background.C116Two.OrbitFour
public import CFSG.Quasithin.Background.C116Two.OrbitArith

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Ctx.normalizer_of_isMaxElemAbelian {H T V L A : Subgroup G} (h : Ctx H T V L)
    (hA : IsMaxElemAbelian T A) : A ≤ Subgroup.normalizer (L : Set G) := by
  have hAT : A ≤ T := hA.1
  have hAe : IsElemAbelian 2 A := hA.2.1
  set A₀ : Subgroup G := A ⊓ Subgroup.normalizer (L : Set G) with hA₀
  obtain ⟨hWe, hWT⟩ := orbitW_elemAbelian_le h hAT
  have hoff := card_le_relIndex_mul_card hWe hWT hA
  have F1 := card_orbitW h hAT
  have F2 := relIndex_centralizer_orbitW h hAT hAe
  have F3 := card_fixed_orbitW_le h hAT
  have hNC := natCount_chiBlock h.chi (B := A₀) (isElemAbelian_of_le' inf_le_left hAe) inf_le_right
  have F5 := four_mul_card_le h.chi
  rw [F2] at hoff
  have hkpos : 0 < A₀.relIndex A := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hz : 0 < Nat.card ↥(blockZ L) := Nat.card_pos
  have hc : 0 < Nat.card ↥(orbitC A L) := Nat.card_pos
  have hu : 0 < Nat.card ↥(blockU L) := Nat.card_pos
  have hk1 : A₀.relIndex A = 1 := orbit_arith hz hc hu hkpos F1 hoff F3 hNC F5
  exact fun a ha => ((Subgroup.relIndex_eq_one.mp hk1) ha).2

end CFSG.Quasithin.C116Two
