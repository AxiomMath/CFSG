module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin

public section

namespace CFSG.Quasithin.F53

open Equiv

theorem mem_of_orderOf_prime {K : Type*} [Group K] [Finite K] (p : ℕ) [hp : Fact p.Prime]
    (hp2 : ¬ p ^ 2 ∣ Nat.card K) (N : Subgroup K) [N.Normal] {x y : K} (hx : orderOf x = p)
    (hy : orderOf y = p) (hyN : y ∈ N) : x ∈ N := by
  have key : ∀ z : K, orderOf z = p → ∃ S : Sylow p K, (S : Subgroup K) = Subgroup.zpowers z := by
    intro z hz
    have hP : IsPGroup p (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
    have hidx : ¬ p ∣ (Subgroup.zpowers z).index := by
      intro hd
      apply hp2
      have h1 := (Subgroup.zpowers z).card_mul_index
      rw [Nat.card_zpowers, hz] at h1
      rw [← h1, pow_two]
      exact Nat.mul_dvd_mul_left p hd
    exact ⟨hP.toSylow hidx, rfl⟩
  obtain ⟨S1, hS1⟩ := key y hy
  obtain ⟨S2, hS2⟩ := key x hx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S1 S2
  have hx' : x ∈ (S2 : Subgroup K) := by rw [hS2]; exact Subgroup.mem_zpowers x
  rw [← hg, Sylow.coe_subgroup_smul, hS1, Subgroup.mem_smul_pointwise_iff_exists] at hx'
  obtain ⟨s, hs, rfl⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have : y ^ i ∈ N := N.zpow_mem hyN i
  have h2 := (inferInstance : N.Normal).conj_mem _ this g
  simpa [MulAut.conj_apply] using h2

theorem alt5_le_of_dvd (K : Subgroup (Perm (Fin 5))) (h : 15 ∣ Nat.card K) :
    alternatingGroup (Fin 5) ≤ K := by
  set A := alternatingGroup (Fin 5) with hA
  have hsimple : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  have h1 : A.relIndex K ∣ 2 := by
    have := Subgroup.relIndex_dvd_index_of_normal A K
    rwa [hA, alternatingGroup.index_eq_two] at this
  have h2 : A.relIndex K * Nat.card (A ⊓ K :) = Nat.card K := Subgroup.relIndex_mul_card A K
  have h15 : 15 ∣ Nat.card (A ⊓ K :) := by
    have hc : Nat.Coprime 15 (A.relIndex K) := by
      have : A.relIndex K = 1 ∨ A.relIndex K = 2 := (Nat.dvd_prime Nat.prime_two).mp h1
      rcases this with h | h <;> rw [h] <;> decide
    rw [← h2] at h
    exact hc.dvd_of_dvd_mul_left h
  have h3 : K.relIndex A * Nat.card (K ⊓ A :) = Nat.card A := Subgroup.relIndex_mul_card K A
  have hcommA : Nat.card (K ⊓ A :) = Nat.card (A ⊓ K :) := by rw [inf_comm]
  have hA60 : Nat.card A = 60 := card_alt5
  have hm : K.relIndex A ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have hpos : 15 ≤ Nat.card (K ⊓ A :) := by
      rw [hcommA]; exact Nat.le_of_dvd Nat.card_pos h15
    nlinarith
  set K' := K.subgroupOf A with hK'
  have hidx : K'.index = K.relIndex A := rfl
  have hne : K.relIndex A ≠ 0 := by
    intro h0; rw [h0] at h3; omega
  have : K'.FiniteIndex := ⟨by rw [hidx]; exact hne⟩
  have hdvd := K'.index_normalCore_dvd_factorial_index
  have hN : K'.normalCore.Normal := K'.normalCore_normal
  rcases hsimple.eq_bot_or_eq_top_of_normal K'.normalCore with hb | ht
  · exfalso
    rw [hb, Subgroup.index_bot, hA60, hidx] at hdvd
    have hf : (K.relIndex A).factorial ≤ 24 := by
      calc (K.relIndex A).factorial ≤ (4 : ℕ).factorial := Nat.factorial_le hm
        _ = 24 := rfl
    have := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
    omega
  · have hle : K' = ⊤ := top_le_iff.mp (ht ▸ K'.normalCore_le)
    intro x hx
    have : (⟨x, hx⟩ : A) ∈ K' := by rw [hle]; exact Subgroup.mem_top _
    exact this

theorem perm5_pow_sixty : ∀ x : Perm (Fin 5), x ^ 60 = 1 := by decide +kernel

theorem perm5_pow : ∀ x : Perm (Fin 5), x ^ 15 = 1 → x ^ 3 = 1 ∨ x ^ 5 = 1 := by decide +kernel

theorem perm3_pow_six : ∀ x : Perm (Fin 3), x ^ 6 = 1 := by decide +kernel

theorem perm5_odd_order {x : Perm (Fin 5)} (h : Odd (orderOf x)) : x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  have h1 : orderOf x ∣ 60 := orderOf_dvd_of_pow_eq_one (perm5_pow_sixty x)
  have h2 : orderOf x ∣ 15 := by
    have hc : Nat.Coprime (orderOf x) 4 := by
      rw [show (4:ℕ) = 2 ^ 2 from rfl]
      refine Nat.Coprime.pow_right 2 ?_
      refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
      intro hd
      exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr hd)
    have : (60 : ℕ) = 4 * 15 := rfl
    rw [this] at h1
    exact hc.dvd_of_dvd_mul_left h1
  exact perm5_pow x (by rw [← orderOf_dvd_iff_pow_eq_one]; exact h2)


theorem mem_alt_of_odd_order {n : ℕ} {x : Perm (Fin n)} (h : Odd (orderOf x)) :
    x ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h1 : Equiv.Perm.sign x ^ orderOf x = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h2 | h2
  · exact h2
  · rw [h2, h.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem exists_order_three_or_five (N : Subgroup (Perm (Fin 5))) (h2 : ¬ IsPGroup 2 N) :
    ∃ y ∈ N, orderOf y = 3 ∨ orderOf y = 5 := by
  have hdvd : Nat.card N ∣ 120 := card_perm5 ▸ Subgroup.card_subgroup_dvd_card N
  by_cases h3 : 3 ∣ Nat.card N
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := Fintype.ofFinite N
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := ↥N) 3 (by rwa [← Nat.card_eq_fintype_card])
    exact ⟨y, y.2, Or.inl (by rw [Subgroup.orderOf_coe]; exact hy)⟩
  by_cases h5 : 5 ∣ Nat.card N
  · have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have := Fintype.ofFinite N
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := ↥N) 5 (by rwa [← Nat.card_eq_fintype_card])
    exact ⟨y, y.2, Or.inr (by rw [Subgroup.orderOf_coe]; exact hy)⟩
  exfalso
  apply h2
  have hc : Nat.Coprime (Nat.card N) 15 := by
    have c3 : Nat.Coprime (Nat.card N) 3 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    have c5 : Nat.Coprime (Nat.card N) 5 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5)
    exact Nat.Coprime.mul_right c3 c5
  have h8 : Nat.card N ∣ 8 := by
    have : (120 : ℕ) = 8 * 15 := rfl
    rw [this] at hdvd
    exact hc.dvd_of_dvd_mul_right hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card N ∣ 2 ^ 3 by simpa using h8)
  exact IsPGroup.of_card hk


theorem mem_of_normal_mixed (K N : Subgroup (Perm (Fin 5))) (hnorm : ∀ k ∈ K, ∀ y ∈ N, k * y * k⁻¹ ∈ N)
    {x y : Perm (Fin 5)} (hxK : x ∈ K) (hyN : y ∈ N) (hNK : N ≤ K)
    (hx : orderOf x = 3 ∨ orderOf x = 5) (hy : orderOf y = 3 ∨ orderOf y = 5)
    (hne : orderOf x ≠ orderOf y) : x ∈ N := by
  set A := alternatingGroup (Fin 5) with hA
  have hsimple : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  have hdx : orderOf x ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hxK
  have hdy : orderOf y ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K (hNK hyN)
  have h15 : 15 ∣ Nat.card K := by
    have h3 : 3 ∣ Nat.card K := by
      rcases hx with h | h
      · rwa [h] at hdx
      · rcases hy with h' | h'
        · rwa [h'] at hdy
        · exact absurd (h.trans h'.symm) hne
    have h5 : 5 ∣ Nat.card K := by
      rcases hx with h | h
      · rcases hy with h' | h'
        · exact absurd (h.trans h'.symm) hne
        · rwa [h'] at hdy
      · rwa [h] at hdx
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5
  have hAK : A ≤ K := alt5_le_of_dvd K h15
  have hxo : Odd (orderOf x) := by rcases hx with h | h <;> rw [h] <;> decide
  have hyo : Odd (orderOf y) := by rcases hy with h | h <;> rw [h] <;> decide
  have hxA : x ∈ A := mem_alt_of_odd_order hxo
  have hyA : y ∈ A := mem_alt_of_odd_order hyo
  have hN' : (N.subgroupOf A).Normal := ⟨fun n hn g => by
    have := hnorm g (hAK g.2) n (by simpa [Subgroup.mem_subgroupOf] using hn)
    simpa [Subgroup.mem_subgroupOf] using this⟩
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with hb | ht
  · exfalso
    have : (⟨y, hyA⟩ : A) ∈ N.subgroupOf A := by simpa [Subgroup.mem_subgroupOf] using hyN
    rw [hb, Subgroup.mem_bot] at this
    have hy1 : y = 1 := congrArg Subtype.val this
    rw [hy1, orderOf_one] at hy
    omega
  · have : (⟨x, hxA⟩ : A) ∈ N.subgroupOf A := by rw [ht]; exact Subgroup.mem_top _
    simpa [Subgroup.mem_subgroupOf] using this

theorem mem_of_normal_odd_five (K N : Subgroup (Perm (Fin 5))) (hNK : N ≤ K)
    (hnorm : ∀ k ∈ K, ∀ y ∈ N, k * y * k⁻¹ ∈ N) (h2 : ¬ IsPGroup 2 N) :
    ∀ x ∈ K, Odd (orderOf x) → x ∈ N := by
  intro x hxK hxo
  obtain ⟨y, hyN, hy⟩ := exists_order_three_or_five N h2
  have hyo : Odd (orderOf y) := by rcases hy with h | h <;> rw [h] <;> decide
  by_cases hx1 : x = 1
  · rw [hx1]; exact N.one_mem
  have hx35 : orderOf x = 3 ∨ orderOf x = 5 := by
    rcases perm5_odd_order hxo with h | h
    · exact Or.inl (orderOf_eq_prime h hx1 (hp := ⟨Nat.prime_three⟩))
    · exact Or.inr (orderOf_eq_prime h hx1 (hp := ⟨Nat.prime_five⟩))
  have hcardK : Nat.card K ∣ 120 := card_perm5 ▸ Subgroup.card_subgroup_dvd_card K
  let N' : Subgroup K := N.subgroupOf K
  have hN' : N'.Normal := ⟨fun n hn g => by
    have := hnorm g g.2 n (by simpa [N', Subgroup.mem_subgroupOf] using hn)
    simpa [N', Subgroup.mem_subgroupOf] using this⟩
  have hxK' : (⟨x, hxK⟩ : K) = ⟨x, hxK⟩ := rfl
  have hord : ∀ (z : K), orderOf (z : Perm (Fin 5)) = orderOf z := fun z => (Subgroup.orderOf_coe z)
  rcases hx35 with hx3 | hx5 <;> rcases hy with hy3 | hy5
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hp2 : ¬ 3 ^ 2 ∣ Nat.card K := by
      intro hd
      have := (Nat.dvd_trans hd hcardK)
      omega
    have := mem_of_orderOf_prime (K := K) 3 hp2 N' (x := ⟨x, hxK⟩) (y := ⟨y, hNK hyN⟩)
      (by rw [← hord]; exact hx3) (by rw [← hord]; exact hy3) (by simpa [N', Subgroup.mem_subgroupOf] using hyN)
    simpa [N', Subgroup.mem_subgroupOf] using this
  · exact mem_of_normal_mixed K N hnorm hxK hyN hNK (Or.inl hx3) (Or.inr hy5) (by rw [hx3, hy5]; decide)
  · exact mem_of_normal_mixed K N hnorm hxK hyN hNK (Or.inr hx5) (Or.inl hy3) (by rw [hx5, hy3]; decide)
  · have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hp2 : ¬ 5 ^ 2 ∣ Nat.card K := by
      intro hd
      have := (Nat.dvd_trans hd hcardK)
      omega
    have := mem_of_orderOf_prime (K := K) 5 hp2 N' (x := ⟨x, hxK⟩) (y := ⟨y, hNK hyN⟩)
      (by rw [← hord]; exact hx5) (by rw [← hord]; exact hy5) (by simpa [N', Subgroup.mem_subgroupOf] using hyN)
    simpa [N', Subgroup.mem_subgroupOf] using this


theorem card_perm3 : Nat.card (Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm]; simp [Nat.factorial]

theorem mem_of_normal_odd_three (K N : Subgroup (Perm (Fin 3))) (hNK : N ≤ K)
    (hnorm : ∀ k ∈ K, ∀ y ∈ N, k * y * k⁻¹ ∈ N) (h2 : ¬ IsPGroup 2 N) :
    ∀ x ∈ K, Odd (orderOf x) → x ∈ N := by
  intro x hxK hxo
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hx1 : x = 1
  · rw [hx1]; exact N.one_mem
  have hx3 : orderOf x = 3 := by
    have h1 : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one (perm3_pow_six x)
    have h3 : orderOf x ∣ 3 := by
      have hc : Nat.Coprime (orderOf x) 2 := by
        refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
        intro hd
        exact (Nat.not_even_iff_odd.mpr hxo) (even_iff_two_dvd.mpr hd)
      have : (6 : ℕ) = 2 * 3 := rfl
      rw [this] at h1
      exact hc.dvd_of_dvd_mul_left h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hcardN : Nat.card N ∣ 6 := card_perm3 ▸ Subgroup.card_subgroup_dvd_card N
  have h3N : 3 ∣ Nat.card N := by
    by_contra h3
    apply h2
    have hc : Nat.Coprime (Nat.card N) 3 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    have h2' : Nat.card N ∣ 2 := by
      have : (6 : ℕ) = 2 * 3 := rfl
      rw [this] at hcardN
      exact hc.dvd_of_dvd_mul_right hcardN
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card N ∣ 2 ^ 1 by simpa using h2')
    exact IsPGroup.of_card hk
  have := Fintype.ofFinite N
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := ↥N) 3 (by rwa [← Nat.card_eq_fintype_card])
  have hy3 : orderOf (y : Perm (Fin 3)) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hcardK : Nat.card K ∣ 6 := card_perm3 ▸ Subgroup.card_subgroup_dvd_card K
  let N' : Subgroup K := N.subgroupOf K
  have hN' : N'.Normal := ⟨fun n hn g => by
    have := hnorm g g.2 n (by simpa [N', Subgroup.mem_subgroupOf] using hn)
    simpa [N', Subgroup.mem_subgroupOf] using this⟩
  have hp2 : ¬ 3 ^ 2 ∣ Nat.card K := by
    intro hd
    have := (Nat.dvd_trans hd hcardK)
    omega
  have hord : ∀ (z : K), orderOf (z : Perm (Fin 3)) = orderOf z := fun z => (Subgroup.orderOf_coe z)
  have := mem_of_orderOf_prime (K := K) 3 hp2 N' (x := ⟨x, hxK⟩) (y := ⟨y, hNK y.2⟩)
      (by rw [← hord]; exact hx3) (by rw [← hord]; exact hy3) (by simp [N', Subgroup.mem_subgroupOf])
  simpa [N', Subgroup.mem_subgroupOf] using this

theorem mem_of_normal_odd {n : ℕ} (hn : n = 3 ∨ n = 5) (K N : Subgroup (Perm (Fin n)))
    (hNK : N ≤ K) (hnorm : ∀ k ∈ K, ∀ y ∈ N, k * y * k⁻¹ ∈ N) (h2 : ¬ IsPGroup 2 N) :
    ∀ x ∈ K, Odd (orderOf x) → x ∈ N := by
  rcases hn with rfl | rfl
  · exact mem_of_normal_odd_three K N hNK hnorm h2
  · exact mem_of_normal_odd_five K N hNK hnorm h2

end CFSG.Quasithin.F53
