module

public import CFSG.Monster.GMS.S35

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S36Lines

section Conj

variable {G : Type*} [Group G]

@[expose] def typeOrder : GMSType → ℕ
  | .twoA => 2
  | .twoB => 2
  | .threeA => 3
  | .threeC => 3
  | .fourA => 4
  | .fourB => 4
  | .fiveA => 5
  | .sixA => 6

theorem orderOf_mul_of_mem_typeSet {a z₀ b y : G} (ha : orderOf a = 2) (hz : orderOf z₀ = 2)
    {K : GMSType} (hK : y ∈ typeSet a z₀ b K) : orderOf (b * y) = typeOrder K := by
  cases K with
  | twoA => exact (orderOf_eq_of_isConj hK.2).symm.trans ha
  | twoB => exact (orderOf_eq_of_isConj hK.2).symm.trans hz
  | threeA =>
    obtain ⟨⟨-, -, -, w, hw, hwB⟩, hty⟩ := hK
    exact (s348_card hty hw hwB).1
  | threeC =>
    obtain ⟨⟨-, -, -, w, hw, hwB⟩, hty⟩ := hK
    exact (s348_card hty hw hwB).1
  | fiveA =>
    obtain ⟨⟨-, -, -, w, hw, hwB⟩, hty⟩ := hK
    exact (s348_card hty hw hwB).1
  | fourA => exact hK.2.1
  | fourB => exact hK.2.1
  | sixA => exact hK.2.1

theorem exists_typeSet_of_gammaCover {a z₀ : G} (hGC : GammaCover a z₀) {b y : G}
    (hb : IsConj a b) (hy : IsConj a y) (hyb : y ≠ b) : ∃ K, y ∈ typeSet a z₀ b K := by
  rcases hGC b y hb hy with h | h
  · exact absurd h hyb
  · obtain ⟨K, hK⟩ := Set.mem_iUnion.mp h
    exact ⟨K, hK⟩

end Conj

section Involutions

variable {G : Type*} [Group G] {a : G}

theorem sq_eq_one_of_isConj (ha : orderOf a = 2) {x : G} (hx : IsConj a x) : x * x = 1 :=
  mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hx).symm.trans ha)

theorem ne_one_of_isConj (ha : orderOf a = 2) {x : G} (hx : IsConj a x) : x ≠ 1 :=
  ne_one_of_orderOf ((orderOf_eq_of_isConj hx).symm.trans ha)

theorem mul_comm_of_isConj_mul (ha : orderOf a = 2) {x y : G} (hx : IsConj a x) (hy : IsConj a y)
    (hxy : IsConj a (x * y)) : x * y = y * x :=
  mul_comm_of_mul_self_eq_one (sq_eq_one_of_isConj ha hx) (sq_eq_one_of_isConj ha hy)
    (sq_eq_one_of_isConj ha hxy)

end Involutions

end S36Lines

end CFSG.Monster.GMS
