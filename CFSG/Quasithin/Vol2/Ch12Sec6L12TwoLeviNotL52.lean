module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeaves
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Quasithin.H13.ExcludedOrders

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.Orders

theorem not_isPSL52_of_char2LeviFamily {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {n f : ℕ}
    (hfam : Char2LeviFamily t n f) (ht : t ≠ StatedLieTag.Tits)
    (hmodel : LieModel X t n 2 f) : ¬ StatedClassicalModel X .PSL 5 2 1 := by
  rintro hclass
  have hL : Nat.card X = 9999360 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two hclass
  rcases hfam with ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hf⟩ |
    ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, -, -⟩ | ⟨rfl, rfl, -⟩
  ·
    have hX : Nat.card X = ordA 2 (2 ^ f) := by
      simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two
        (hmodel.statedClassicalModel (by decide))).1 rfl
    obtain ⟨r, hr, hrX⟩ :
        ∃ r, Odd r ∧ ordA 2 (2 ^ f) = 2 ^ (f * 3) * r :=
      (profile_ordA (n := 2) (f := f) (by norm_num) hf).two
    have hEq : 2 ^ (f * 3) * r = 2 ^ 10 * 9765 :=
      hrX.symm.trans (hX.symm.trans (hL.trans (by norm_num)))
    have h10 := eq_of_two_pow_mul_odd hr (by norm_num : Odd 9765) hEq
    omega
  ·
    have hX : Nat.card X = ordTwistedA 2 (2 ^ f) := by
      simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two
        (hmodel.statedClassicalModel (by decide))).2.1 rfl
    obtain ⟨r, hr, hrX⟩ :
        ∃ r, Odd r ∧ ordTwistedA 2 (2 ^ f) = 2 ^ (f * 3) * r :=
      (profile_ordTwistedA (n := 2) (g := f) le_rfl (by omega)).two
    have hEq : 2 ^ (f * 3) * r = 2 ^ 10 * 9765 :=
      hrX.symm.trans (hX.symm.trans (hL.trans (by norm_num)))
    have h10 := eq_of_two_pow_mul_odd hr (by norm_num : Odd 9765) hEq
    omega
  ·
    have hX : Nat.card X = ordBC 2 (2 ^ f) := by
      simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two
        (hmodel.statedClassicalModel (by decide))).2.2.1 rfl
    obtain ⟨r, hr, hrX⟩ :
        ∃ r, Odd r ∧ ordBC 2 (2 ^ f) = 2 ^ (f * 4) * r :=
      (profile_ordBC (n := 2) (f := f) (by omega)).two
    have hEq : 2 ^ (f * 4) * r = 2 ^ 10 * 9765 :=
      hrX.symm.trans (hX.symm.trans (hL.trans (by norm_num)))
    have h10 := eq_of_two_pow_mul_odd hr (by norm_num : Odd 9765) hEq
    omega
  ·
    have hX : Nat.card X = ordG2 (2 ^ f) := by
      simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
        (hmodel.chevalleyExceptionalModel (by decide))
    obtain ⟨r, hr, hrX⟩ :
        ∃ r, Odd r ∧ ordG2 (2 ^ f) = 2 ^ (f * 6) * r :=
      (profile_ordG2 (f := f) (by omega)).two
    have hEq : 2 ^ (f * 6) * r = 2 ^ 10 * 9765 :=
      hrX.symm.trans (hX.symm.trans (hL.trans (by norm_num)))
    have h10 := eq_of_two_pow_mul_odd hr (by norm_num : Odd 9765) hEq
    omega
  ·
    have hX : Nat.card X = ordTrialityD4 (2 ^ f) := by
      simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
        (hmodel.chevalleyExceptionalModel (by decide))
    obtain ⟨r, hr, hrX⟩ :
        ∃ r, Odd r ∧ ordTrialityD4 (2 ^ f) = 2 ^ (f * 12) * r :=
      (profile_ordTrialityD4 (f := f) hf).two
    have hEq : 2 ^ (f * 12) * r = 2 ^ 10 * 9765 :=
      hrX.symm.trans (hX.symm.trans (hL.trans (by norm_num)))
    have h10 := eq_of_two_pow_mul_odd hr (by norm_num : Odd 9765) hEq
    omega
  ·
    obtain ⟨-, hre⟩ := hmodel.reeTitsModel (by decide)
    obtain ⟨k, hk, hX⟩ := CFSG.Quasithin.H13.card_eq_ordTwistedF4_of_reeTitsModel hre
    obtain ⟨r, hr, hrX⟩ :
        ∃ r, Odd r ∧ ordTwistedF4 (2 ^ (2 * k + 1)) = 2 ^ ((2 * k + 1) * 12) * r :=
      (profile_ordTwistedF4 (f := 2 * k + 1) (by omega)).two
    have hEq : 2 ^ ((2 * k + 1) * 12) * r = 2 ^ 10 * 9765 :=
      hrX.symm.trans (hX.symm.trans (hL.trans (by norm_num)))
    have h10 := eq_of_two_pow_mul_odd hr (by norm_num : Odd 9765) hEq
    omega
  ·
    exact absurd rfl ht

end CFSG.Quasithin.H13.K1262Two
