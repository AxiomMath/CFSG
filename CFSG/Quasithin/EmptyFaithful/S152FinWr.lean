module

public import Certificates.Certificate17020

public section

namespace CFSG.Quasithin

namespace S152Fin

theorem Wr_cube_comm : ∀ x y : Wr, x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x :=
  Certificates.certificate17020.1

theorem Wr_cube_conj : ∀ x : Wr, x ^ 3 = 1 → x ≠ 1 →
    ∃ g : Wr, g * x * g⁻¹ ≠ 1 ∧ g * x * g⁻¹ ≠ x ∧ g * x * g⁻¹ ≠ x ^ 2 :=
  Certificates.certificate17020.2.1

theorem Wr_card_cube : Fintype.card {x : Wr // x ^ 3 = 1} = 9 :=
  Certificates.certificate17020.2.2

def Wr3 : Subgroup Wr where
  carrier := {x | x ^ 3 = 1}
  one_mem' := one_pow 3
  mul_mem' := fun {x y} hx hy => by
    have hc : Commute x y := Wr_cube_comm x y hx hy
    show (x * y) ^ 3 = 1
    rw [hc.mul_pow]
    have hx' : x ^ 3 = 1 := hx
    have hy' : y ^ 3 = 1 := hy
    rw [hx', hy', one_mul]
  inv_mem' := fun {x} hx => by
    show x⁻¹ ^ 3 = 1
    have hx' : x ^ 3 = 1 := hx
    rw [inv_pow, hx', inv_one]

theorem Wr3_card : Nat.card Wr3 = 9 := by
  show Nat.card {x : Wr // x ^ 3 = 1} = 9
  rw [Nat.card_eq_fintype_card]
  exact Wr_card_cube

instance instNormalWr3 : Wr3.Normal where
  conj_mem := fun n hn g => by
    show (g * n * g⁻¹) ^ 3 = 1
    have hn' : n ^ 3 = 1 := hn
    rw [conj_pow, hn']
    group

theorem not_exists_surj_Wr_perm3 :
    ¬ ∃ f : Wr →* Equiv.Perm (Fin 3), Function.Surjective f := by
  rintro ⟨f, hf⟩
  have hN : f.ker.Normal := f.normal_ker
  have hcardN : Nat.card f.ker = 12 := by
    have h1 := f.ker.card_mul_index
    rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf, Subgroup.card_top, card_Wr] at h1
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_perm]; simp [Nat.factorial]
    rw [h6] at h1
    omega
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 3 (by rw [hcardN]; norm_num)
  have hx3 : (x : Wr) ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  have hx1 : (x : Wr) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    omega
  obtain ⟨g, hg1, hg2, hg3⟩ := Wr_cube_conj x hx3 hx1
  have hxY : (x : Wr) ∈ f.ker ⊓ Wr3 := ⟨x.2, hx3⟩
  have hyY : g * (x : Wr) * g⁻¹ ∈ f.ker ⊓ Wr3 := by
    refine ⟨hN.conj_mem _ x.2 g, ?_⟩
    show (g * (x : Wr) * g⁻¹) ^ 3 = 1
    rw [conj_pow, hx3]; group
  have hz : Subgroup.zpowers (x : Wr) ≤ f.ker ⊓ Wr3 := by
    rw [Subgroup.zpowers_le]; exact hxY
  have hzcard : Nat.card (Subgroup.zpowers (x : Wr)) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hnot : g * (x : Wr) * g⁻¹ ∉ Subgroup.zpowers (x : Wr) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk3 : (x : Wr) ^ k = (x : Wr) ^ (k % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
      have : ((x : Wr) ^ (3 : ℤ)) = 1 := by simpa using hx3
      rw [this, one_zpow, mul_one]
    have hm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hm with hm | hm | hm
    · rw [hm] at hk3; simp at hk3; exact hg1 (hk.symm.trans hk3)
    · rw [hm] at hk3; simp at hk3; exact hg2 (hk.symm.trans hk3)
    · rw [hm] at hk3
      have : (x : Wr) ^ (2 : ℤ) = (x : Wr) ^ 2 := by simp
      rw [this] at hk3
      exact hg3 (hk.symm.trans hk3)
  have hY9 : Nat.card (f.ker ⊓ Wr3 : Subgroup Wr) ∣ 9 :=
    Wr3_card ▸ Subgroup.card_dvd_of_le inf_le_right
  have hY12 : Nat.card (f.ker ⊓ Wr3 : Subgroup Wr) ∣ 12 :=
    hcardN ▸ Subgroup.card_dvd_of_le inf_le_left
  have hY3 : 3 < Nat.card (f.ker ⊓ Wr3 : Subgroup Wr) := by
    by_contra hle
    push Not at hle
    have := Subgroup.eq_of_le_of_card_ge hz (by omega)
    exact hnot (this ▸ hyY)
  have : Nat.card (f.ker ⊓ Wr3 : Subgroup Wr) ∣ 3 := by
    have := Nat.dvd_gcd hY9 hY12
    simpa using this
  have := Nat.le_of_dvd (by norm_num) this
  omega

end S152Fin

end CFSG.Quasithin
