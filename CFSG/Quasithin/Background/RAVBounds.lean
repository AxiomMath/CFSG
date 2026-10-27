module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin

namespace RAV


variable {V : Type} [CommGroup V] [Finite V]

theorem two_le_rAV_iff (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} (hA : IsA2 X A) :
    (2 : ℚ) ≤ rAV A ↔ Nat.card A ^ 2 * Nat.card ↥(fixV A) ≤ Nat.card V := by
  have hBc := B1.card_elemAbelian hA.isElemAbelian2
  have hCc := card_eq_two_pow hV (fixV A)
  have hVc := card_eq_two_pow_rk hV
  have hsum := rk_add_rkIdx (fixV A)
  have hpos : 0 < rk ↥A := hA.rk_pos
  rw [hBc, hCc, hVc, ← pow_mul, ← pow_add, Nat.pow_le_pow_iff_right (by norm_num)]
  unfold rAV
  rw [le_div_iff₀ (by exact_mod_cast hpos)]
  constructor
  · intro h
    have h' : 2 * rk ↥A ≤ rkIdx (fixV A) := by exact_mod_cast h
    omega
  · intro h
    have h' : 2 * rk ↥A ≤ rkIdx (fixV A) := by omega
    exact_mod_cast h'

theorem two_lt_rAV_iff (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} (hA : IsA2 X A) :
    (2 : ℚ) < rAV A ↔ Nat.card A ^ 2 * Nat.card ↥(fixV A) < Nat.card V := by
  have hBc := B1.card_elemAbelian hA.isElemAbelian2
  have hCc := card_eq_two_pow hV (fixV A)
  have hVc := card_eq_two_pow_rk hV
  have hsum := rk_add_rkIdx (fixV A)
  have hpos : 0 < rk ↥A := hA.rk_pos
  rw [hBc, hCc, hVc, ← pow_mul, ← pow_add, Nat.pow_lt_pow_iff_right (by norm_num)]
  unfold rAV
  rw [lt_div_iff₀ (by exact_mod_cast hpos)]
  constructor
  · intro h
    have h' : 2 * rk ↥A < rkIdx (fixV A) := by exact_mod_cast h
    omega
  · intro h
    have h' : 2 * rk ↥A < rkIdx (fixV A) := by omega
    exact_mod_cast h'

theorem one_le_rAV_of_le_index (hV : ∀ v : V, v ^ 2 = 1) {X B : Subgroup (MulAut V)}
    (hB : IsA2 X B) (h : Nat.card B ≤ (fixV B).index) : 1 ≤ rAV B := by
  rw [← not_lt, rAV_lt_one_iff hV hB, not_lt]
  calc Nat.card B * Nat.card (fixV B) ≤ (fixV B).index * Nat.card (fixV B) :=
        Nat.mul_le_mul_right _ h
    _ = Nat.card V := Subgroup.index_mul_card _

theorem rAV_conjAut {W : Type*} [CommGroup W] (g : MulAut W) (A : Subgroup (MulAut W)) :
    rAV (B1.conjAut g A) = rAV A := by
  have h1 : rk (B1.conjAut g A) = rk A := by
    unfold rk
    rw [B1.card_conjAut]
  have h2 : rkIdx (fixV (B1.conjAut g A)) = rkIdx (fixV A) := by
    unfold rkIdx
    rw [B1.fixV_conjAut]
    exact congrArg (padicValNat 2) (Subgroup.index_map_equiv (fixV A) g)
  unfold rAV
  rw [h1, h2]

end RAV

end CFSG.Quasithin
