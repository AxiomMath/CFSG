module

public import CFSG.Quasithin.Vol2.Asc94.TSModel5
public import CFSG.Quasithin.Vol2.Asc94.TSModel8
public import CFSG.Quasithin.Vol2.Asc94.TSModel11

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

theorem blk_pow7 : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B 1 0 = 0 → B 2 0 = 0 → B ^ 7 = 1 →
    B = 1 := by decide +kernel

@[expose] def x3 : Hc := mkH !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0;
    0, 0, 0, 0, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem x3_mem : x3 ∈ NH1 := ⟨by decide +kernel, by decide +kernel⟩

theorem x3_cube : x3 ^ 3 = 1 := by
  apply cm_injective
  show cm (x3 ^ 3) = cm 1
  rw [pow_three', cm_mul, cm_mul, cm_one]
  decide +kernel

theorem x3_ne_one : x3 ≠ 1 := by
  intro h
  have h' := congrArg cm h
  rw [cm_one] at h'
  exact absurd h' (by decide +kernel)

theorem orderOf_x3 : orderOf x3 = 3 := orderOf_eq_prime x3_cube x3_ne_one

theorem Qh_le_Tm : Qh ≤ Tm := by
  intro x hx
  rw [← SetLike.mem_coe, Qh_eq_U1_mul_U2] at hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.1 hx
  exact Tm.mul_mem (U1_le_Tm hu) (U2_le_Tm hv)

theorem card_NH1 : Nat.card NH1 = 3072 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdvd : Nat.card NH1 ∣ 21504 := by
    rw [← card_Hc]
    exact Subgroup.card_subgroup_dvd_card NH1
  obtain ⟨k, hk⟩ : 1024 ∣ Nat.card NH1 := by
    have := Subgroup.card_dvd_of_le Tm_le_NH1
    rw [card_Tm] at this
    simpa using this
  have h3 : 3 ∣ Nat.card NH1 := by
    have h := orderOf_dvd_natCard (⟨x3, x3_mem⟩ : NH1)
    rwa [← Subgroup.orderOf_coe, orderOf_x3] at h
  have h7 : ¬ 7 ∣ Nat.card NH1 := by
    intro h7
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥NH1) 7 h7
    set y : Hc := (x : Hc) with hy
    have hyo : orderOf y = 7 := by rw [hy, Subgroup.orderOf_coe]; exact hx
    have hyN : y ∈ NH1 := x.2
    have hpow : (blk (cm y)) ^ 7 = 1 := by
      have hy7 : y ^ 7 = 1 := by
        rw [← hyo]
        exact pow_orderOf_eq_one y
      have h1 : (piHom y) ^ 7 = 1 := by
        rw [← map_pow, hy7, map_one]
      have h2 := congrArg Units.val h1
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h2
      exact h2
    have h10 : blk (cm y) 1 0 = 0 := hyN.1
    have h20 : blk (cm y) 2 0 = 0 := hyN.2
    have hB : blk (cm y) = 1 := blk_pow7 _ h10 h20 hpow
    have hyQ : y ∈ Qh := by
      rw [Qh, MonoidHom.mem_ker]
      exact Units.ext hB
    have h4 := Qh_pow_four hyQ
    have := orderOf_dvd_of_pow_eq_one h4
    rw [hyo] at this
    omega
  rw [hk] at hdvd h3 h7 ⊢
  have hk21 : k ∣ 21 := by
    have : 1024 * k ∣ 1024 * 21 := hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hk3 : k ∈ Nat.divisors 21 := Nat.mem_divisors.2 ⟨hk21, by norm_num⟩
  have hdiv21 : Nat.divisors 21 = {1, 3, 7, 21} := by decide
  rw [hdiv21] at hk3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk3
  omega

end CFSG.Quasithin.A94.L52
