module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13

theorem sylow_image_cv {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal] (R : Subgroup X)
    (hR2 : IsPGroup 2 R) (hRodd : ¬ 2 ∣ R.index) :
    IsPGroup 2 (R.map (QuotientGroup.mk' N)) ∧ ¬ 2 ∣ (R.map (QuotientGroup.mk' N)).index := by
  refine ⟨IsPGroup.map hR2 (QuotientGroup.mk' N), fun h => hRodd ?_⟩
  exact dvd_trans h (Subgroup.index_map_dvd R (QuotientGroup.mk'_surjective N))

theorem card_two_subgroup_of_card_cv {X : Type} [Group X] [Finite X] (S : Subgroup X)
    (hS : IsPGroup 2 S) (hodd : ¬ 2 ∣ S.index) {e m : ℕ} (hX : Nat.card X = 2 ^ e * m)
    (hm : ¬ 2 ∣ m) : Nat.card S = 2 ^ e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hmul : 2 ^ k * S.index = 2 ^ e * m := by
    rw [← hk, ← hX, Subgroup.card_mul_index]
  have hcopm : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm)
  have hk_dvd : 2 ^ k ∣ 2 ^ e := by
    apply Nat.Coprime.dvd_of_dvd_mul_right hcopm
    exact ⟨S.index, hmul.symm⟩
  have hcopi : Nat.Coprime (2 ^ e) S.index :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have he_dvd : 2 ^ e ∣ 2 ^ k := by
    apply Nat.Coprime.dvd_of_dvd_mul_right hcopi
    exact ⟨m, hmul⟩
  have hke : k ≤ e := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hk_dvd
  have hek : e ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp he_dvd
  rw [hk, le_antisymm hke hek]

theorem false_of_two_commuting_three_cv {P Y : Type} [Group P] [Finite P] [Group Y]
    (ψ : P →* Y) (hP9 : ¬ 9 ∣ Nat.card P) {a b : P}
    (ha : orderOf (ψ a) = 3) (hb : orderOf (ψ b) = 3)
    (hc : Commute (ψ a) (ψ b)) (hn : ψ b ∉ Subgroup.zpowers (ψ a)) : False := by
  set x : Y := ψ a with hx
  set y : Y := ψ b with hy
  have hI : ∀ t : Y, t ∈ Subgroup.zpowers x → t ∈ Subgroup.zpowers y → t = 1 := by
    intro t htx hty
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 htx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hty
    have hmod : y ^ (k % 3) = y ^ k := by
      have h := zpow_mod_orderOf y k
      rw [hb] at h
      exact_mod_cast h
    by_cases hk3 : k % 3 = 0
    · rw [← hk, ← hmod, hk3, zpow_zero]
    · exfalso
      have hk12 : k % 3 = 1 ∨ k % 3 = 2 := by omega
      have hkk : (k * k) % 3 = 1 := by
        rw [Int.mul_emod]
        rcases hk12 with h | h <;> rw [h] <;> norm_num
      have hyy : y = (y ^ k) ^ k := by
        have hm2 : y ^ (k * k % 3) = y ^ (k * k) := by
          have h := zpow_mod_orderOf y (k * k)
          rw [hb] at h
          exact_mod_cast h
        rw [← zpow_mul, ← hm2, hkk, zpow_one]
      apply hn
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨j * k, ?_⟩
      rw [zpow_mul, ← hk, ← hyy]
  have hcomm : ∀ u ∈ Subgroup.zpowers x, ∀ v ∈ Subgroup.zpowers y, Commute u v := by
    intro u hu v hv
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact Commute.zpow_zpow hc j k
  have key : ∀ a1 a2 b1 b2 : Y, b1 * a2 = a2 * b1 →
      a1 * b1 * (a2 * b2) = a1 * a2 * (b1 * b2) := by
    intro a1 a2 b1 b2 h
    calc a1 * b1 * (a2 * b2) = a1 * (b1 * a2) * b2 := by simp only [mul_assoc]
      _ = a1 * (a2 * b1) * b2 := by rw [h]
      _ = a1 * a2 * (b1 * b2) := by simp only [mul_assoc]
  let F : (↥(Subgroup.zpowers x)) × (↥(Subgroup.zpowers y)) →* Y :=
    { toFun := fun p => (p.1 : Y) * (p.2 : Y)
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        exact key _ _ _ _ (hcomm _ q.1.2 _ p.2.2).eq }
  have hF : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ huv
    change u * v = 1 at huv
    have hu1 : u = 1 := by
      apply hI u hu
      have hvinv : u = v⁻¹ := eq_inv_of_mul_eq_one_left huv
      rw [hvinv]
      exact inv_mem hv
    have hv1 : v = 1 := by
      rw [hu1, one_mul] at huv
      exact huv
    subst hu1
    subst hv1
    rfl
  have hcardF : Nat.card F.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hF).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, ha, hb]
  have hxr : x ∈ ψ.range := MonoidHom.mem_range.mpr ⟨a, rfl⟩
  have hyr : y ∈ ψ.range := MonoidHom.mem_range.mpr ⟨b, rfl⟩
  have hle : F.range ≤ ψ.range := by
    rintro _ ⟨p, rfl⟩
    exact mul_mem (Subgroup.zpowers_le.mpr hxr p.1.2) (Subgroup.zpowers_le.mpr hyr p.2.2)
  have h9 : Nat.card F.range ∣ Nat.card ψ.range := Subgroup.card_dvd_of_le hle
  rw [hcardF] at h9
  have hPdvd : Nat.card ψ.range ∣ Nat.card P := by
    rw [← Subgroup.card_ker_mul_card_range ψ]
    exact dvd_mul_left _ _
  exact hP9 (dvd_trans h9 hPdvd)

theorem exists_three_power_cv {H A : Type} [Group H] [Finite H] [Group A] (ψ : H →* A) (d : H)
    (hd : orderOf (ψ d) = 3) (hJ : ∀ g : H, ψ g = 1 → ¬ 3 ∣ orderOf g) :
    ∃ y : H, y ∈ Subgroup.zpowers d ∧ y ^ 3 = 1 ∧ orderOf (ψ y) = 3 ∧ ∃ k : ℕ, ψ (y ^ k) = ψ d := by
  obtain ⟨a, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos d).ne' 3 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm3 (dvd_zero 3)
  have hmd : m ∣ orderOf d := Dvd.intro_left _ hnm.symm
  obtain ⟨y, hy⟩ : ∃ y : H, y = d ^ m := ⟨_, rfl⟩
  have hordy : orderOf y = 3 ^ a := by
    rw [hy, orderOf_pow_of_dvd hm0 hmd, hnm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have h3 : ψ d ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (ψ d)
    rwa [hd] at h
  have hψz : ψ (y ^ 3) = 1 := by
    rw [hy, map_pow, map_pow, ← pow_mul, mul_comm, pow_mul, h3, one_pow]
  have hy3 : y ^ 3 = 1 := by
    by_contra hne
    have hdvd : orderOf (y ^ 3) ∣ 3 ^ a := by
      rw [← hordy]
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have hne1 : orderOf (y ^ 3) ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hne1 (by rw [hi, pow_zero])
    apply hJ (y ^ 3) hψz
    rw [hi]
    exact dvd_pow_self 3 hi0
  have hyd : y ∈ Subgroup.zpowers d := by
    rw [hy]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) m
  have hψy : ψ y = ψ d ^ m := by
    rw [hy, map_pow]
  have hcop : Nat.Coprime (orderOf (ψ d)) m := by
    rw [hd]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3
  have hordψy : orderOf (ψ y) = 3 := by
    rw [hψy, Nat.Coprime.orderOf_pow hcop, hd]
  have hmm : m * m % 3 = 1 := by
    have hm12 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rw [Nat.mul_mod]
    rcases hm12 with h | h <;> rw [h] <;> norm_num
  have hk : ψ (y ^ m) = ψ d := by
    have h1 := pow_mod_orderOf (ψ d) (m * m)
    rw [hd, hmm, pow_one] at h1
    rw [map_pow, hψy, ← pow_mul]
    exact h1.symm
  exact ⟨y, hyd, hy3, hordψy, m, hk⟩

end CFSG.Quasithin.H13
