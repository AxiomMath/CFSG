module

public import CFSG.Quasithin.Background.D1Statement

public section

namespace CFSG.Quasithin.H13.L319.S66

theorem relIndex_le_four_pow_of_chiefSeries {G : Type} [Group G] [Finite G] {H U V : Subgroup G} {y : G}
    (hloc : ∀ L N : Subgroup G, IsChiefStep H U L N →
      (IsCentralStep H L N → (Subgroup.centralizer ({y} : Set G)).relIndex (V ⊓ N) ≤
          (Subgroup.centralizer ({y} : Set G)).relIndex (V ⊓ L)) ∧
      (¬ IsCentralStep H L N → (Subgroup.centralizer ({y} : Set G)).relIndex (V ⊓ N) ≤
          4 * (Subgroup.centralizer ({y} : Set G)).relIndex (V ⊓ L)))
    {N : Subgroup G} {n : ℕ} (hN : IsChiefSeriesFrom H U N n) :
    (Subgroup.centralizer ({y} : Set G)).relIndex (V ⊓ N) ≤ 4 ^ n := by
  induction hN with
  | bot =>
    rw [inf_bot_eq, Subgroup.relIndex_bot_right]
    simp
  | @central N' L' n' hstep hc hL ih =>
    exact le_trans ((hloc L' N' hstep).1 hc) ih
  | @noncentral N' L' n' hstep hnc hL ih =>
    calc (Subgroup.centralizer ({y} : Set G)).relIndex (V ⊓ N')
        ≤ 4 * (Subgroup.centralizer ({y} : Set G)).relIndex (V ⊓ L') := (hloc L' N' hstep).2 hnc
      _ ≤ 4 * 4 ^ n' := Nat.mul_le_mul_left 4 ih
      _ = 4 ^ (n' + 1) := by ring

end CFSG.Quasithin.H13.L319.S66

end
