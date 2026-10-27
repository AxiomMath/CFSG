module

public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
public import CFSG.Quasithin.Vol2.Ch10SecAFacts

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

theorem one_lt_of_shapeCard {N : ℕ} (h : ShapeCard N) : 1 < N := by
  rcases h with ⟨n, hn, rfl⟩ | ⟨a, ha, rfl⟩ | rfl
  · have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h16 : 16 ≤ 4 ^ n := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : 15 ≤ 4 ^ n - 1 := by omega
    nlinarith
  · have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 ≤ 2 ^ (2 * a + 1) - 1 := by omega
    have h2 : 1 < (2 ^ (2 * a + 1)) ^ 2 := by nlinarith
    have h3 : 1 ≤ (2 ^ (2 * a + 1)) ^ 2 + 1 := by omega
    calc 1 < (2 ^ (2 * a + 1)) ^ 2 := h2
      _ ≤ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := Nat.le_mul_of_pos_right _ h1
      _ ≤ _ := Nat.le_mul_of_pos_right _ h3
  · norm_num

theorem nontrivial_of_isShapeGroup
    {X : Type} [Group X] (h : IsShapeGroup X) : Nontrivial X := by
  have h1 := one_lt_of_shapeCard (shapeCard_of_isShapeGroup h)
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  exact Finite.one_lt_card_iff_nontrivial.mp h1

theorem factB4aM24_holds :
    FactB4aM24 := by
  intro X _ hsh π hπ
  have := nontrivial_of_isShapeGroup hsh
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective CFSG.Monster.Code.AutPerm_isSimpleGroup π hπ
  apply not_shapeCard_244823040
  rw [← CFSG.Monster.Code.card_AutPerm, Nat.card_congr e.toEquiv]
  exact shapeCard_of_isShapeGroup hsh

theorem factB4aJ2_holds :
    FactB4aJ2 := by
  rintro X _ hsh ⟨e⟩
  apply not_shapeCard_604800
  rw [← CFSG.Sporadic.J2.card_J2]
  change ShapeCard (Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J2))
  rw [← Nat.card_congr e.toEquiv]
  exact shapeCard_of_isShapeGroup hsh

end CFSG.Quasithin.Vol2.Ch10.SecA
