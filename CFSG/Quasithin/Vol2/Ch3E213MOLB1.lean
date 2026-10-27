module

public import CFSG.Quasithin.Vol2.Ch3E213MOLA9
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.ClassicalInvolution.AschTight.S19KLinStd
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.Ch3E213M.OLB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open scoped MatrixGroups

theorem card_gf3 : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 one_ne_zero, pow_one]

theorem odd_card_gf3 : Odd (Nat.card (GaloisField 3 1)) := by
  rw [card_gf3]
  decide

theorem two_ne_zero_gf3 : (2 : GaloisField 3 1) ≠ 0 :=
  Models.two_ne_zero_of_odd_natCard odd_card_gf3

theorem eq_zero_or_one_or_neg_one (c : GaloisField 3 1) : c = 0 ∨ c = 1 ∨ c = -1 := by
  have := Fintype.ofFinite (GaloisField 3 1)
  have h1 := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, card_gf3] at h1
  have h2 : c * (c - 1) * (c + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

theorem sq_eq_one_of_ne_zero {c : GaloisField 3 1} (hc : c ≠ 0) : c * c = 1 := by
  rcases eq_zero_or_one_or_neg_one c with h | h | h
  · exact absurd h hc
  · rw [h, one_mul]
  · rw [h, neg_mul_neg, one_mul]

theorem ringEquiv_eq_refl (φ : GaloisField 3 1 ≃+* GaloisField 3 1) :
    φ = RingEquiv.refl _ := by
  ext c
  rcases eq_zero_or_one_or_neg_one c with rfl | rfl | rfl <;> simp

theorem exists_equiv_sl3 {K : Type} [Group K] (hL : IsPSL 3 3 1 K) :
    Nonempty (SL(3, GaloisField 3 1) ≃* K) := by
  obtain ⟨θ, hθ, hker⟩ := OLA.exists_theta_lin (p := 3) hL
  have hZ : Subgroup.center SL(3, GaloisField 3 1) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := 3) (by norm_num)
      (GaloisField 3 1)
    have h3 : Nat.gcd 3 (Nat.card (GaloisField 3 1) - 1) = 1 := by rw [card_gf3]; norm_num
    rw [h3] at h
    exact Nat.dvd_one.mp h
  have hinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rw [hZ] at hker
    exact hker
  exact ⟨MulEquiv.ofBijective θ ⟨hinj, hθ⟩⟩

theorem isBlockDiag_of_commute_rootInv {x : SL(3, GaloisField 3 1)}
    (hx : x * Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) =
      Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) * x) :
    IsBlockDiag ((x : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) := by
  refine isBlockDiag_of_commute_negBlock two_ne_zero_gf3 _ ?_
  have h1 := congrArg (fun g : SL(3, GaloisField 3 1) =>
    (g : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))) hx
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv_three] at h1
  exact h1

end CFSG.Quasithin.Ch3E213M.OLB
