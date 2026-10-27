module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

theorem pow_mod_three {H : Type*} [Group H] {xb : H} (h3 : xb ^ 3 = 1) (n : ℕ) :
    xb ^ (n % 3) = xb ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one]

theorem conj_shift {H : Type*} [Group H] {xb : H} (h3 : xb ^ 3 = 1) (a : H) (i : Fin 3) :
    xb⁻¹ * ((xb ^ (i : ℕ))⁻¹ * a * xb ^ (i : ℕ)) * xb =
      (xb ^ ((i + 1 : Fin 3) : ℕ))⁻¹ * a * xb ^ ((i + 1 : Fin 3) : ℕ) := by
  have e : ((i + 1 : Fin 3) : ℕ) = ((i : ℕ) + 1) % 3 := by
    rw [Fin.val_add]
    simp
  rw [e, pow_mod_three h3, pow_succ]
  group

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {L : ZLab Γ G}

namespace Sec9Cfg

variable (S : Sec9Cfg L)

theorem xb_pow_three : S.xβ ^ 3 = 1 := by
  rw [← S.isBeta.order3]
  exact pow_orderOf_eq_one _

theorem zMuij_eq (F : FanTree Γ G) (i : Fin 3) (j : Fin 5) :
    S.zMuij i j = (S.xβ ^ (i : ℕ))⁻¹ * S.zMu1 j * S.xβ ^ (i : ℕ) := by
  unfold zMuij zMu1
  exact L.z_inv_smul (S.xβ ^ (i : ℕ)) (S.D.valence_alpha F j)

theorem zMu_eq (F : FanTree Γ G) (i : Fin 3) :
    S.zMu i = (S.xβ ^ (i : ℕ))⁻¹ * S.zMu1 0 * S.xβ ^ (i : ℕ) := by
  rw [← S.zMuij_eq F i 0]
  rfl

theorem zNb_eq (i : Fin 3) :
    S.zNb i = (S.xβ ^ (i : ℕ))⁻¹ * L.z S.α * S.xβ ^ (i : ℕ) := by
  have : S.zNb i = L.z ((S.xβ ^ (i : ℕ))⁻¹ • S.α) := by
    unfold zNb D10Set.bv
    simp [S.D.start 0]
  rw [this]
  exact L.z_inv_smul (S.xβ ^ (i : ℕ)) S.D.val

theorem yMu_eq (F : FanTree Γ G) (i : Fin 3) :
    S.yMu i = (S.xβ ^ (i : ℕ))⁻¹ * (S.zMu1 0 * S.zMu1 1) * S.xβ ^ (i : ℕ) := by
  unfold yMu
  rw [S.zMuij_eq F i 0, S.zMuij_eq F i 1]
  group

end Sec9Cfg

end CFSG.Quasithin.Fan86
