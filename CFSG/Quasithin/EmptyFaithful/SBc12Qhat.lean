module

public import CFSG.Quasithin.Background.D216Sub

public section

namespace CFSG.Quasithin

namespace SBc12

variable {W : Type*} [CommGroup W] [Finite W]

theorem ratio_eq_three_halves {n k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2) (hge : (3 / 2 : ℚ) ≤ (n : ℚ) / k)
    (hlt : (n : ℚ) / k < 2) : (n : ℚ) / k = 3 / 2 := by
  have hk : (0 : ℚ) < k := by exact_mod_cast hk1
  rw [le_div_iff₀ hk] at hge
  rw [div_lt_iff₀ hk] at hlt
  interval_cases k
  · exfalso
    have h1 : (3 : ℚ) / 2 * 1 ≤ n := by exact_mod_cast hge
    have h2 : (n : ℚ) < 2 * 1 := by exact_mod_cast hlt
    have h3 : 2 ≤ n := by
      by_contra hn
      have : n ≤ 1 := by omega
      have : (n : ℚ) ≤ 1 := by exact_mod_cast this
      linarith
    have : (2 : ℚ) ≤ n := by exact_mod_cast h3
    linarith
  · have h1 : (3 : ℚ) / 2 * 2 ≤ n := by exact_mod_cast hge
    have h2 : (n : ℚ) < 2 * 2 := by exact_mod_cast hlt
    have h3 : n = 3 := by
      have h1' : (3 : ℚ) ≤ n := by linarith
      have h2' : (n : ℚ) < 4 := by linarith
      have h1'' : 3 ≤ n := by exact_mod_cast h1'
      have h2'' : n < 4 := by exact_mod_cast h2'
      omega
    subst h3
    norm_num

theorem qhatOf_eq_three_halves {X Xm : Subgroup (MulAut W)} (hX : X ≤ Xm) (hcard : Nat.card X ≤ 4)
    (hm : qhatOf Xm = (((3 : ℚ) / 2 : ℚ) : WithTop ℚ))
    (hlt : qhatOf X < ((2 : ℚ) : WithTop ℚ)) : qhatOf X = (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  unfold qhatOf at hlt hm ⊢
  obtain ⟨A, hA, hA3, hr2⟩ := kq_lt_iff.mp hlt
  have hAm : IsA2 Xm A := ⟨hA.1.trans hX, hA.2⟩
  have hge : (3 / 2 : ℚ) ≤ rAV A := le_kq_iff.mp hm.ge A hAm hA3
  have hAle : Nat.card A ≤ 4 := (Subgroup.card_le_of_le hA.1).trans hcard
  have hp : IsPGroup 2 A := IsElemAbelian2.isPGroup hA.isElemAbelian2
  have hk1 : 1 ≤ rk A := IsElemAbelian2.rk_pos hA.isElemAbelian2 hA.ne_bot
  have hk2 : rk A ≤ 2 := by
    have h := card_eq_two_pow_of_isPGroup hp
    by_contra hcon
    have : 8 ≤ 2 ^ rk A := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ rk A := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hr : rAV A = 3 / 2 := by
    unfold rAV at hge hr2 ⊢
    exact ratio_eq_three_halves hk1 hk2 hge hr2
  refine le_antisymm (kq_le_iff.mpr ⟨A, hA, hA3, hr.le⟩) ?_
  rw [← hm]
  exact kq_le_kq_of_le216 hX 3

end SBc12

end CFSG.Quasithin
