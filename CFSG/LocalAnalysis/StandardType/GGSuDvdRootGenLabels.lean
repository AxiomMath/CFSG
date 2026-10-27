module

public import CFSG.LocalAnalysis.StandardType.GGSuDvdRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNSRootGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGRootGenUnitaryDvdLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧ 2 ≤ lab.n ∧
    ¬ (lab.rank = 5 ∧ p = 3)

private theorem div_add_two_le_max_sub_three {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : 3 ≤ d) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ p = 3)) : d / p + 2 ≤ max (d - 3) 3 := by
  obtain ⟨k, rfl⟩ := hpd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rw [Nat.mul_div_cancel_left k hp.pos]
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> simp_all
  · rcases Nat.lt_or_ge p 4 with hp4 | hp4
    · have : p = 3 := by omega
      subst this
      have : k ≠ 2 := fun h => hnd ⟨by omega, rfl⟩
      omega
    · have : 4 * k ≤ p * k := Nat.mul_le_mul_right k hp4
      omega

theorem ggRootGenKGAvoidOn_unitaryDvd :
    GGRootGenKGAvoidOn GGRootGenUnitaryDvdLabel := by
  rintro p ⟨t, l, n⟩ hp hp2 hlab ⟨ht, hpn, hpd, hn, hno⟩
  dsimp only at ht hpn hpd hn hno
  subst ht
  have hl2 : 2 ≤ l := hlab.2.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have h3 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlift : GGTorusLift p (ggUnitaryTorusRank p (l + 1))
      (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))) :=
    ggTorusLift_unitary hK (by omega) (by omega) hdq hp hpn
  have hnd : ¬ (l + 1 = 6 ∧ p = 3) := fun h => hno ⟨by omega, h.2⟩
  have hrank : ggUnitaryTorusRank p (l + 1) = l + 1 - 3 := by
    simp [ggUnitaryTorusRank, hpd]
  have hr : (l + 1) / p + 2 ≤ max (ggUnitaryTorusRank p (l + 1)) 3 := by
    rw [hrank]
    exact div_add_two_le_max_sub_three hp hp2 (by omega) hpd hnd
  exact ⟨K, i1, i2, hK, hQ', ggUnitaryTorusRank p (l + 1), hlift,
    ggTorusRootGenAvoidKG_unitaryDvd hK hn (by omega) hp hpn hpd hr⟩

end CFSG.StandardType

end
