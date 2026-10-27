module

public import CFSG.Quasithin.Background.A1cSL2Facts
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic

public section

namespace CFSG.Quasithin

open Matrix
open scoped MatrixGroups

namespace A1c

theorem card_SL2_zmod {r : ℕ} [Fact r.Prime] : Nat.card SL(2, ZMod r) = r * (r ^ 2 - 1) := by
  rw [Matrix.card_SL_field (𝔽 := ZMod r), ZMod.card]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have hr1 : 1 < r := (Fact.out : r.Prime).one_lt
  have h1 : r ^ 2 - r = r * (r - 1) := by
    rw [Nat.mul_sub, mul_one, sq]
  have h2 : (r ^ 2 - 1) * (r * (r - 1)) = (r - 1) * (r * (r ^ 2 - 1)) := by ring
  rw [h1, h2, Nat.mul_div_cancel_left _ (by omega)]

theorem card_le_of_exponent_sl2 {r p : ℕ} [Fact r.Prime] [hp : Fact p.Prime] (hr2 : r ≠ 2)
    (hp2 : p ≠ 2) (hpr : p ≠ r) (K : Subgroup SL(2, ZMod r)) (hK : ∀ k ∈ K, k ^ p = 1) :
    Nat.card K ≤ p := by
  have hKp : IsPGroup p K := fun k => ⟨1, Subtype.ext (by simpa using hK k k.2)⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hKp
  have hr1 : 1 < r := (Fact.out : r.Prime).one_lt
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp.out Nat.prime_two).2 hp2
  have hcopr : Nat.Coprime p r := (Nat.coprime_primes hp.out (Fact.out : r.Prime)).2 hpr
  by_cases h7 : 7 ≤ r
  ·
    have hr7 : 7 ≤ Nat.card (ZMod r) := by rw [Nat.card_zmod]; exact h7
    have hKcard : Nat.card (ZMod r) = r ^ 1 := by rw [Nat.card_zmod, pow_one]
    let π₀ : SL(2, ZMod r) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r) :=
      QuotientGroup.mk' (Subgroup.center SL(2, ZMod r))
    let K' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r)) := K.map π₀
    have hK'p : IsPGroup p K' := hKp.map π₀
    obtain ⟨S, hS⟩ := hK'p.exists_le_sylow
    have hcop : Nat.Coprime p (Nat.card (ZMod r)) := by rw [Nat.card_zmod]; exact hcopr
    have hcyc : IsCyclic ↥(S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r))) :=
      CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card (ZMod r) hKcard hr7 p hp2
        hcop S
    have hK'cyc : IsCyclic K' := Subgroup.isCyclic_of_le hS
    have hK'card : Nat.card K' ≤ p := by
      obtain ⟨g, hg⟩ := hK'cyc.exists_generator
      have hgp : g ^ p = 1 := by
        obtain ⟨_, ⟨k, hk, hkg⟩⟩ := g
        apply Subtype.ext
        simp only [Subgroup.coe_pow, OneMemClass.coe_one]
        rw [← hkg, ← map_pow, hK k hk, map_one]
      have h1 : orderOf g = Nat.card K' := orderOf_eq_card_of_forall_mem_zpowers hg
      have h2 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
      rw [← h1]
      exact Nat.le_of_dvd hp.out.pos h2
    let f : ↥K → ↥K' := fun k => ⟨π₀ k, Subgroup.mem_map_of_mem _ k.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : π₀ a = π₀ b := congrArg Subtype.val hab
      have h2 : (a : SL(2, ZMod r))⁻¹ * b ∈ Subgroup.center SL(2, ZMod r) := by
        rw [← QuotientGroup.ker_mk' (Subgroup.center SL(2, ZMod r)), MonoidHom.mem_ker, map_mul,
          map_inv, h1, inv_mul_cancel]
      rcases eq_one_or_eq_sl2NegOne_of_mem_center h2 with h3 | h3
      · apply Subtype.ext
        have : (a : SL(2, ZMod r)) = b := inv_mul_eq_one.1 h3
        exact this
      · exfalso
        have hmem : (a : SL(2, ZMod r))⁻¹ * b ∈ K := K.mul_mem (K.inv_mem a.2) b.2
        have h4 := hK _ hmem
        rw [h3] at h4
        obtain ⟨m, hm⟩ : Odd p := hp.out.odd_of_ne_two hp2
        have hneg : sl2NegOne r ^ p = sl2NegOne r := by
          rw [hm, pow_succ, pow_mul, sq, sl2NegOne_mul_self, one_pow, one_mul]
        rw [hneg] at h4
        have : Fact (1 < r) := ⟨hr1⟩
        exact sl2NegOne_ne_one hr2 h4
    exact (Nat.card_le_card_of_injective f hf).trans hK'card
  ·
    have hr35 : r = 3 ∨ r = 5 := by
      have hr7' : r < 7 := by omega
      interval_cases r
      · simp_all
      · left; rfl
      · exact absurd (Fact.out : Nat.Prime 4) (by decide)
      · right; rfl
      · exact absurd (Fact.out : Nat.Prime 6) (by decide)
    have hdvd : Nat.card K ∣ r * (r ^ 2 - 1) := by
      rw [← card_SL2_zmod]
      exact Subgroup.card_subgroup_dvd_card K
    rcases hr35 with rfl | rfl
    · have hcop3 : Nat.Coprime p 3 := hcopr
      have hc : Nat.Coprime (Nat.card K) 24 := by
        rw [hj]
        exact Nat.Coprime.pow_left j (by
          rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num]
          exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 hcop2) hcop3)
      have : Nat.card K = 1 :=
        Nat.Coprime.eq_one_of_dvd hc (by simpa using hdvd)
      rw [this]; exact hp.out.one_lt.le
    · by_cases hp3 : p = 3
      · subst hp3
        have hdvd' : 3 ^ j ∣ 120 := by rw [← hj]; simpa using hdvd
        have hj1 : j ≤ 1 := by
          by_contra hj2
          push Not at hj2
          have : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 hj2
          have := this.trans hdvd'
          omega
        rw [hj]
        calc 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
          _ = 3 := pow_one 3
      · have hcop3 : Nat.Coprime p 3 := (Nat.coprime_primes hp.out Nat.prime_three).2 hp3
        have hc : Nat.Coprime (Nat.card K) 120 := by
          rw [hj]
          exact Nat.Coprime.pow_left j (by
            rw [show (120 : ℕ) = 2 ^ 3 * 3 * 5 by norm_num]
            exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 hcop2)
              hcop3) hcopr)
        have : Nat.card K = 1 :=
          Nat.Coprime.eq_one_of_dvd hc (by simpa using hdvd)
        rw [this]; exact hp.out.one_lt.le

end A1c

end CFSG.Quasithin
