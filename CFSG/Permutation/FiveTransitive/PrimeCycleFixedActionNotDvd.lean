module

public import CFSG.Permutation.FiveTransitive.SimpleGoursat
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.RingTheory.WittVector.IsPoly

public section

namespace CFSG

namespace FiveTransitive.PrimeCycleFixedActionNotDvd

open MulAction SubMulAction Subgroup

theorem alternating_card_not_dvd_pred_of_lt_fixed_card
    (F : Type) [Fintype F] [DecidableEq F]
    (hfive : 5 ≤ Fintype.card F)
    {p : ℕ} (hp : p.Prime)
    (hpLt : p < Fintype.card F) :
    ¬Nat.card (alternatingGroup F) ∣ p - 1 := by
  letI : Nontrivial F :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      omega)
  let f := Fintype.card F
  let A := Nat.card (alternatingGroup F)
  have htwoA :
      2 * A = f.factorial := by
    calc
      2 * A = Nat.card (Equiv.Perm F) := by
        simpa only [A] using
          (two_mul_nat_card_alternatingGroup (α := F))
      _ = f.factorial := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card]
  have htwoF : 2 * f ≤ f.factorial := by
    obtain ⟨k, hk⟩ :=
      Nat.exists_eq_succ_of_ne_zero (by
        exact Nat.ne_of_gt (by
          show 0 < Fintype.card F
          omega))
    have hkf : f = k + 1 := by
      simpa only [f, Nat.succ_eq_add_one] using hk
    have hkTwo : 2 ≤ k := by
      omega
    have hfactorialTwo : 2 ≤ k.factorial := by
      have hle := Nat.factorial_le hkTwo
      norm_num at hle
      exact hle
    calc
      2 * f = 2 * (k + 1) := by rw [hkf]
      _ = (k + 1) * 2 := by omega
      _ ≤ (k + 1) * k.factorial :=
        Nat.mul_le_mul_left (k + 1) hfactorialTwo
      _ = f.factorial := by
        rw [hkf, Nat.factorial_succ]
  have hfLeA : f ≤ A := by
    omega
  intro hdiv
  have hpPredPos : 0 < p - 1 := by
    have := hp.two_le
    omega
  have hALe : A ≤ p - 1 :=
    Nat.le_of_dvd hpPredPos hdiv
  change p < f at hpLt
  omega

end FiveTransitive.PrimeCycleFixedActionNotDvd

end CFSG
