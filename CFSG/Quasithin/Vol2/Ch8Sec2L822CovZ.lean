module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13

theorem pow_three_pow_two_eq_one_cv {G : Type} [Group G] {g : G} {n : ℕ} (h3 : g ^ 3 = 1)
    (h2 : g ^ 2 ^ n = 1) : g = 1 := by
  have hg : Nat.gcd 3 (2 ^ n) = 1 := Nat.Coprime.pow_right n (by norm_num)
  have h := pow_gcd_eq_one.2 ⟨h3, h2⟩
  rw [hg, pow_one] at h
  exact h

theorem central_image_of_hat_cv {B N₀ : Type} [Group B] [Finite B] [Group N₀] [Finite N₀]
    (ρ : B →* N₀) (O : Subgroup B) [hOn : O.Normal] (hO2 : IsPGroup 2 O)
    (hker : ∀ b ∈ ρ.ker, b ∈ O)
    (hZ3 : Nat.card (Subgroup.center (B ⧸ O)) = 3)
    (h27 : 27 ∣ Nat.card B)
    (hN27 : ¬ 27 ∣ Nat.card (N₀ ⧸ Subgroup.center N₀))
    (u : B) (hu3 : u ^ 3 = 1)
    (hu : (QuotientGroup.mk u : B ⧸ O) ∈ Subgroup.center (B ⧸ O))
    (hu1 : u ∉ O) :
    ρ u ∈ Subgroup.center N₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOpow : ∀ x ∈ O, ∃ n : ℕ, x ^ (2 ^ n) = 1 := by
    intro x hx
    obtain ⟨n, hn⟩ := hO2 ⟨x, hx⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have h3not2 : ∀ n : ℕ, ¬ 3 ∣ 2 ^ n := fun n h => by
    have h' := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h'
  have hk3 : ¬ 3 ∣ Nat.card ρ.ker := by
    intro h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h
    obtain ⟨n, hn⟩ := hOpow (x : B) (hker _ x.2)
    have hdvd : orderOf (x : B) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    rw [Subgroup.orderOf_coe, hx] at hdvd
    exact h3not2 n hdvd
  have hcopk : Nat.Coprime 27 (Nat.card ρ.ker) := by
    have h3c : Nat.Coprime 3 (Nat.card ρ.ker) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hk3
    have h27c := Nat.Coprime.pow_left 3 h3c
    rwa [show (3 : ℕ) ^ 3 = 27 from rfl] at h27c
  have hRdvd : 27 ∣ Nat.card ρ.range := by
    have hprod : Nat.card ρ.ker * Nat.card ρ.range = Nat.card B := by
      rw [← Subgroup.index_ker ρ, Subgroup.card_mul_index]
    rw [← hprod] at h27
    exact Nat.Coprime.dvd_of_dvd_mul_left hcopk h27
  let f : ↥ρ.range →* N₀ ⧸ Subgroup.center N₀ :=
    (QuotientGroup.mk' (Subgroup.center N₀)).comp ρ.range.subtype
  have hfprod : Nat.card f.ker * Nat.card f.range = Nat.card ρ.range := by
    rw [← Subgroup.index_ker f, Subgroup.card_mul_index]
  have hfrange : ¬ 27 ∣ Nat.card f.range := fun h =>
    hN27 (dvd_trans h (Subgroup.card_subgroup_dvd_card f.range))
  have hf3 : 3 ∣ Nat.card f.ker := by
    by_contra h3
    have h3c : Nat.Coprime 3 (Nat.card f.ker) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    have hc27 : Nat.Coprime 27 (Nat.card f.ker) := by
      have h27c := Nat.Coprime.pow_left 3 h3c
      rwa [show (3 : ℕ) ^ 3 = 27 from rfl] at h27c
    have hdvd : 27 ∣ Nat.card f.ker * Nat.card f.range := by
      rw [hfprod]
      exact hRdvd
    exact hfrange (Nat.Coprime.dvd_of_dvd_mul_left hc27 hdvd)
  obtain ⟨d, hd3, hdZ, hdR⟩ :
      ∃ d : N₀, orderOf d = 3 ∧ d ∈ Subgroup.center N₀ ∧ d ∈ ρ.range := by
    obtain ⟨c', hc'⟩ := exists_prime_orderOf_dvd_card' 3 hf3
    refine ⟨((c' : ↥ρ.range) : N₀), ?_, ?_, (c' : ↥ρ.range).2⟩
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc']
    · have h1 : QuotientGroup.mk' (Subgroup.center N₀) ((c' : ↥ρ.range) : N₀) = 1 :=
        MonoidHom.mem_ker.1 c'.2
      exact (QuotientGroup.eq_one_iff _).1 h1
  have hd1 : d ^ 3 = 1 := by
    rw [← hd3]
    exact pow_orderOf_eq_one d
  obtain ⟨c₀, hc₀⟩ := MonoidHom.mem_range.1 hdR
  have hc₀3 : c₀ ^ 3 ∈ O := by
    apply hker
    rw [MonoidHom.mem_ker, map_pow, hc₀, hd1]
  obtain ⟨k, hk⟩ := hOpow (c₀ ^ 3) hc₀3
  obtain ⟨c, hcdef⟩ : ∃ c : B, c = c₀ ^ 2 ^ k := ⟨_, rfl⟩
  have hc3 : c ^ 3 = 1 := by
    rw [hcdef, pow_right_comm, hk]
  have hρc : ρ c = d ^ 2 ^ k := by
    rw [hcdef, map_pow, hc₀]
  have hdk : d ^ 2 ^ k ≠ 1 := by
    intro h
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hd3] at h'
    exact h3not2 k h'
  have hρc1 : ρ c ≠ 1 := by
    rw [hρc]
    exact hdk
  have hZc : ρ c ∈ Subgroup.center N₀ := by
    rw [hρc]
    exact pow_mem hdZ _
  have hρc3 : ρ c ^ 3 = 1 := by
    rw [← map_pow, hc3, map_one]
  have hcO : c ∉ O := by
    intro hcO
    obtain ⟨n, hn⟩ := hOpow c hcO
    apply hρc1
    rw [pow_three_pow_two_eq_one_cv (n := n) hc3 hn, map_one]
  have hmkc : (QuotientGroup.mk c : B ⧸ O) ∈ Subgroup.center (B ⧸ O) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
    have hzb : ρ c * ρ b = ρ b * ρ c := (Subgroup.mem_center_iff.1 hZc (ρ b)).symm
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    apply hker
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    rw [hzb, inv_mul_cancel]
  have hmkc_ne : (QuotientGroup.mk c : B ⧸ O) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hcO
  have hmkc3 : (QuotientGroup.mk c : B ⧸ O) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hc3, QuotientGroup.mk_one]
  have hord : orderOf (QuotientGroup.mk c : B ⧸ O) = 3 := orderOf_eq_prime hmkc3 hmkc_ne
  have hzp : Subgroup.zpowers (QuotientGroup.mk c : B ⧸ O) = Subgroup.center (B ⧸ O) := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hmkc
    · exact le_of_eq (by rw [hZ3, Nat.card_zpowers, hord])
  have hu' : (QuotientGroup.mk u : B ⧸ O) ∈ Subgroup.zpowers (QuotientGroup.mk c : B ⧸ O) := by
    rw [hzp]
    exact hu
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hu'
  rw [← QuotientGroup.mk_zpow] at hj
  have hoO : (c ^ j)⁻¹ * u ∈ O := QuotientGroup.eq.1 hj
  obtain ⟨o, hoO', hu_eq⟩ : ∃ o ∈ O, u = c ^ j * o :=
    ⟨(c ^ j)⁻¹ * u, hoO, (mul_inv_cancel_left _ _).symm⟩
  have hXZ : ρ c ^ j ∈ Subgroup.center N₀ := zpow_mem hZc j
  have hX3 : (ρ c ^ j) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρc3, one_zpow]
  have hcomm : Commute (ρ c ^ j) (ρ o) := (Subgroup.mem_center_iff.1 hXZ (ρ o)).symm
  have hρu : ρ u = ρ c ^ j * ρ o := by
    rw [hu_eq, map_mul, map_zpow]
  have hY3 : ρ o ^ 3 = 1 := by
    have h : (ρ c ^ j * ρ o) ^ 3 = 1 := by
      rw [← hρu, ← map_pow, hu3, map_one]
    rw [hcomm.mul_pow, hX3, one_mul] at h
    exact h
  obtain ⟨n, hn⟩ := hOpow o hoO'
  have hY : ρ o = 1 := by
    apply pow_three_pow_two_eq_one_cv (n := n) hY3
    rw [← map_pow, hn, map_one]
  rw [hρu, hY, mul_one]
  exact hXZ

end CFSG.Quasithin.H13
