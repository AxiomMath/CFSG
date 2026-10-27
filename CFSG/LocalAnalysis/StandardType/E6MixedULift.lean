module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6DiagLang

public section

namespace CFSG.StandardType

theorem exists_pow_odd_order_of_odd_order_map {G H : Type*} [Group G] [Finite G] [Group H]
    (φ : G →* H) (g : G) (hodd : Odd (orderOf (φ g))) :
    ∃ k : ℕ, Odd (orderOf (g ^ k)) ∧ φ (g ^ k) = φ g := by
  classical
  obtain ⟨v, n', hn'odd, hn'⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hm0 : orderOf (φ g) ≠ 0 := by
    obtain ⟨r, hr⟩ := hodd
    omega
  have hcop : Nat.Coprime (2 ^ v) (orderOf (φ g)) :=
    (Odd.coprime_two_left hodd).pow_left v
  obtain ⟨t, -, ht⟩ :=
    Nat.exists_mul_mod_eq_of_coprime (n := 2 ^ v) (k := orderOf (φ g)) 1 hcop hm0
  refine ⟨2 ^ v * t, ?_, ?_⟩
  · have hdiv : orderOf g ∣ (2 ^ v * t) * n' := by
      rw [hn']
      exact ⟨t, by ring⟩
    have hpow : (g ^ (2 ^ v * t)) ^ n' = 1 := by
      rw [← pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.mp hdiv
    exact Odd.of_dvd_nat hn'odd (orderOf_dvd_of_pow_eq_one hpow)
  · rw [map_pow]
    exact (pow_eq_pow_of_modEq ht (pow_orderOf_eq_one (φ g))).trans (pow_one _)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

end CFSG.StandardType
