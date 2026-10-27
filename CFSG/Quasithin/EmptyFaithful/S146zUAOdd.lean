module

public import CFSG.Quasithin.EmptyFaithful.S146zRPair

public section

namespace CFSG.Quasithin.S146zU.UA

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped Pointwise

section TwoPower

variable {G : Type*} [Group G]

theorem mul_mem_of_two_power {K : Subgroup G} {k r : G} (hk : k ∈ K)
    (hr : r ∈ Subgroup.normalizer (K : Set G)) {e : ℕ} (hre : r ^ 2 ^ e = 1)
    (hodd : Odd (orderOf (k * r))) : k * r ∈ K := by
  obtain ⟨k', hk', h⟩ := A4.exists_pow_mul_eq hk hr (2 ^ e)
  rw [hre, mul_one] at h
  have hcop : Nat.Coprime (2 ^ e) (orderOf (k * r)) :=
    Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)
  have h2 := A4.mem_zpowers_pow_of_coprime hcop
  rw [h] at h2
  exact (Subgroup.zpowers_le.mpr hk') h2

end TwoPower

section Prod

variable {X : Type*} [Group X] {N N' : Subgroup X}

theorem comp_pow_eq_one (hc : ∀ a ∈ N, ∀ b ∈ N', a * b = b * a) (hd : N ⊓ N' = ⊥) {n n' : X}
    (hn : n ∈ N) (hn' : n' ∈ N') {k : ℕ} (hk : (n * n') ^ k = 1) : n ^ k = 1 ∧ n' ^ k = 1 := by
  rw [(show Commute n n' from hc n hn n' hn').mul_pow] at hk
  have h1 : n ^ k = (n' ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk
  have h2 : n ^ k ∈ N ⊓ N' := ⟨N.pow_mem hn k, by rw [h1]; exact N'.inv_mem (N'.pow_mem hn' k)⟩
  rw [hd, Subgroup.mem_bot] at h2
  refine ⟨h2, ?_⟩
  have h3 : (n' ^ k)⁻¹ = 1 := by rw [← h1, h2]
  exact inv_eq_one.mp h3

theorem comp_comm_of_comm (hc : ∀ a ∈ N, ∀ b ∈ N', a * b = b * a) (hd : N ⊓ N' = ⊥) {n m : X}
    (hn : n ∈ N) (hm : m ∈ N) {n' m' : X} (hn' : n' ∈ N') (hm' : m' ∈ N')
    (h : (n * n') * (m * m') = (m * m') * (n * n')) : n * m = m * n ∧ n' * m' = m' * n' := by
  have e1 : (n * m) * (n' * m') = (m * n) * (m' * n') := by
    have h1 : n * n' * (m * m') = n * m * (n' * m') := by
      calc n * n' * (m * m') = n * (n' * m) * m' := by simp only [mul_assoc]
        _ = n * (m * n') * m' := by rw [← hc m hm n' hn']
        _ = n * m * (n' * m') := by simp only [mul_assoc]
    have h2 : m * m' * (n * n') = m * n * (m' * n') := by
      calc m * m' * (n * n') = m * (m' * n) * n' := by simp only [mul_assoc]
        _ = m * (n * m') * n' := by rw [← hc n hn m' hm']
        _ = m * n * (m' * n') := by simp only [mul_assoc]
    rw [← h1, ← h2]
    exact h
  have e2 : (m * n)⁻¹ * (n * m) = (m' * n') * (n' * m')⁻¹ := by
    have h1 : (m * n)⁻¹ * (n * m * (n' * m')) = m' * n' := by
      rw [e1]
      exact inv_mul_cancel_left _ _
    rw [← mul_assoc] at h1
    exact eq_mul_inv_of_mul_eq h1
  have hN : (m * n)⁻¹ * (n * m) ∈ N := N.mul_mem (N.inv_mem (N.mul_mem hm hn)) (N.mul_mem hn hm)
  have hN' : (m * n)⁻¹ * (n * m) ∈ N' := by
    rw [e2]
    exact N'.mul_mem (N'.mul_mem hm' hn') (N'.inv_mem (N'.mul_mem hn' hm'))
  have h0 : (m * n)⁻¹ * (n * m) ∈ N ⊓ N' := ⟨hN, hN'⟩
  rw [hd, Subgroup.mem_bot] at h0
  have h3 : n * m = m * n := by
    have := inv_mul_eq_one.mp h0
    exact this.symm
  refine ⟨h3, ?_⟩
  rw [h0, eq_comm, mul_inv_eq_one] at e2
  exact e2.symm

end Prod

section Pair

variable {G : Type} [Group G] {G₁ A B : Subgroup G}

structure CompPair (G₁ A B : Subgroup G) : Prop where
  left_le : A ≤ G₁
  right_le : B ≤ G₁
  norm_left : B ≤ Subgroup.normalizer (A : Set G)
  norm_right : A ≤ Subgroup.normalizer (B : Set G)
  comm : ∀ a ∈ imageOTwoQuot G₁ A, ∀ b ∈ imageOTwoQuot G₁ B, a * b = b * a
  disj : imageOTwoQuot G₁ A ⊓ imageOTwoQuot G₁ B = ⊥

theorem CompPair.symm (P : CompPair G₁ A B) : CompPair G₁ B A :=
  ⟨P.right_le, P.left_le, P.norm_right, P.norm_left, fun a ha b hb => (P.comm b hb a ha).symm,
    by rw [inf_comm]; exact P.disj⟩

theorem CompPair.of_cComp [Finite G] (hA : A ∈ cComp G₁) (hB : B ∈ cComp G₁) (hne : A ≠ B)
    (hs : IsSimpleGroup ↥(imageOTwoQuot G₁ A)) : CompPair G₁ A B := by
  have h12 : B ≤ Subgroup.normalizer (A : Set G) :=
    le_sup_right.trans (SBc16.sup_le_normalizer_of_mem_cComp hA hB)
  have h21 : A ≤ Subgroup.normalizer (B : Set G) :=
    le_sup_right.trans (SBc16.sup_le_normalizer_of_mem_cComp hB hA)
  obtain ⟨hcomm, hdisj⟩ := q_pair_comm_disjoint hA hB hne hs h12 h21
  exact ⟨le_of_mem_cComp hA, le_of_mem_cComp hB, h12, h21, hcomm, hdisj⟩

variable [Finite G]

theorem mem_left_of_split (P : CompPair G₁ A B) {w : G} (hwG : w ∈ G₁) (hw : w ∈ A ⊔ B)
    (hodd : Odd (orderOf w)) {n c : OTwoQuot G₁} (hn : n ∈ imageOTwoQuot G₁ A) {e : ℕ}
    (hce : c ^ 2 ^ e = 1) (hnc : qPi G₁ ⟨w, hwG⟩ = n * c) : w ∈ A := by
  have hmul : (↑(A ⊔ B) : Set G) = ↑A * ↑B :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B P.norm_left
  have hw' : w ∈ (↑A * ↑B : Set G) := by
    rw [← hmul]
    exact hw
  obtain ⟨k, hk, k', hk', rfl⟩ := Set.mem_mul.mp hw'
  have hkG : k ∈ G₁ := P.left_le hk
  have hk'G : k' ∈ G₁ := P.right_le hk'
  set u : OTwoQuot G₁ := qPi G₁ ⟨k, hkG⟩ with hu_def
  set u' : OTwoQuot G₁ := qPi G₁ ⟨k', hk'G⟩ with hu'_def
  have hu : u ∈ imageOTwoQuot G₁ A := ⟨⟨k, hkG⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hu' : u' ∈ imageOTwoQuot G₁ B := ⟨⟨k', hk'G⟩, Subgroup.mem_subgroupOf.mpr hk', rfl⟩
  have hww : qPi G₁ ⟨k * k', hwG⟩ = u * u' := by
    have : (⟨k * k', hwG⟩ : ↥G₁) = ⟨k, hkG⟩ * ⟨k', hk'G⟩ := rfl
    rw [this, map_mul]
  rw [hww] at hnc
  set m : OTwoQuot G₁ := n⁻¹ * u with hm_def
  have hmN : m ∈ imageOTwoQuot G₁ A :=
    (imageOTwoQuot G₁ A).mul_mem ((imageOTwoQuot G₁ A).inv_mem hn) hu
  have hcm : m * u' = c := by rw [hm_def, mul_assoc, hnc, inv_mul_cancel_left]
  have hc2 : u' ^ 2 ^ e = 1 := by
    have h1 : (m * u') ^ 2 ^ e = 1 := by rw [hcm]; exact hce
    rw [(show Commute m u' from P.comm m hmN u' hu').mul_pow] at h1
    have h2 : u' ^ 2 ^ e ∈ imageOTwoQuot G₁ A ⊓ imageOTwoQuot G₁ B := by
      refine ⟨?_, (imageOTwoQuot G₁ B).pow_mem hu' _⟩
      have h3 : u' ^ 2 ^ e = (m ^ 2 ^ e)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h3]
      exact (imageOTwoQuot G₁ A).inv_mem ((imageOTwoQuot G₁ A).pow_mem hmN _)
    rw [P.disj, Subgroup.mem_bot] at h2
    exact h2
  have hcM : u' ^ orderOf (k * k') = 1 := by
    have h1 : (u * u') ^ orderOf (k * k') = 1 := by
      rw [← hww, ← map_pow]
      have : (⟨k * k', hwG⟩ : ↥G₁) ^ orderOf (k * k') = 1 := by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact pow_orderOf_eq_one _
      rw [this, map_one]
    exact (comp_pow_eq_one P.comm P.disj hu hu' h1).2
  have hu'1 : u' = 1 := by
    have hcop : Nat.Coprime (2 ^ e) (orderOf (k * k')) :=
      Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)
    have hd : orderOf u' ∣ Nat.gcd (2 ^ e) (orderOf (k * k')) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc2) (orderOf_dvd_of_pow_eq_one hcM)
    rw [hcop.gcd_eq_one, Nat.dvd_one] at hd
    exact orderOf_eq_one_iff.mp hd
  have hk'p : (⟨k', hk'G⟩ : ↥G₁) ∈ CFSG.Open.pCore 2 ↥G₁ := by
    have h : (QuotientGroup.mk (⟨k', hk'G⟩ : ↥G₁) : OTwoQuot G₁) = 1 := hu'1
    exact (QuotientGroup.eq_one_iff _).mp h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥G₁)) ⟨_, hk'p⟩
  have hf' : k' ^ 2 ^ f = 1 := by
    have := congrArg (fun z : CFSG.Open.pCore 2 ↥G₁ => ((z : ↥G₁) : G)) hf
    simpa using this
  exact mul_mem_of_two_power hk (P.norm_left hk') hf' hodd

theorem oTwoUpper_le_of_rotation (P : CompPair G₁ A B) {H Hi : Subgroup G} (hHi : Hi ≤ H)
    (hHG : H ≤ G₁) (hz : oTwoUpper H ≤ A ⊔ B) (φ : ↥Hi →* DihedralGroup 5)
    (hker : ∀ y : ↥Hi, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {x : G} (hx : x ∈ Hi)
    (hφx : φ ⟨x, hx⟩ = DihedralGroup.r 1)
    (hxA : qPi G₁ ⟨x, hHG (hHi hx)⟩ ∈ imageOTwoQuot G₁ A) : oTwoUpper Hi ≤ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.closure_le A).mpr ?_
  rintro z ⟨hzH, hodd⟩
  have hzG : z ∈ G₁ := hHG (hHi hzH)
  have hzK : z ∈ A ⊔ B := hz (mem_oTwoUpper_of_odd (hHi hzH) hodd)
  have hzpow : (⟨z, hzH⟩ : ↥Hi) ^ orderOf z = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact pow_orderOf_eq_one _
  have hφz : φ ⟨z, hzH⟩ ^ orderOf z = 1 := by rw [← map_pow, hzpow, map_one]
  obtain ⟨j, hj⟩ := dih_rot_of_pow hodd hφz
  set q : G := (x ^ j.val)⁻¹ * z with hq_def
  have hqH : q ∈ Hi := Hi.mul_mem (Hi.inv_mem (Hi.pow_mem hx _)) hzH
  have hφq : φ ⟨q, hqH⟩ = 1 := by
    have e : (⟨q, hqH⟩ : ↥Hi) = (⟨x, hx⟩ ^ j.val)⁻¹ * ⟨z, hzH⟩ := rfl
    rw [e, map_mul, map_inv, map_pow, hφx, hj, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val,
      inv_mul_cancel]
  have hqQ : q ∈ pCoreOf 2 H := (hker _).mp hφq
  have hqG : q ∈ G₁ := hHG (hHi hqH)
  obtain ⟨e, he⟩ := (pCoreOf_isPGroup (r := 2) (G := G) H) ⟨q, hqQ⟩
  have hqe : q ^ 2 ^ e = 1 := by
    have := congrArg (fun z : pCoreOf 2 H => (z : G)) he
    simpa using this
  have hce : (qPi G₁ ⟨q, hqG⟩) ^ 2 ^ e = 1 := by
    rw [← map_pow]
    have : (⟨q, hqG⟩ : ↥G₁) ^ 2 ^ e = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hqe
    rw [this, map_one]
  have hnc : qPi G₁ ⟨z, hzG⟩ = (qPi G₁ ⟨x, hHG (hHi hx)⟩) ^ j.val * qPi G₁ ⟨q, hqG⟩ := by
    have e : (⟨z, hzG⟩ : ↥G₁) = ⟨x, hHG (hHi hx)⟩ ^ j.val * ⟨q, hqG⟩ := by
      apply Subtype.ext
      show z = x ^ j.val * q
      rw [hq_def]
      group
    rw [e, map_mul, map_pow]
  exact mem_left_of_split P hzG hzK hodd ((imageOTwoQuot G₁ A).pow_mem hxA _) hce hnc

end Pair

section Qpi

variable {G : Type} [Group G] [Finite G] {G₁ : Subgroup G}

omit [Finite G] in
theorem qPi_mem_image {K : Subgroup G} {k : G} (hk : k ∈ K) (hkG : k ∈ G₁) :
    qPi G₁ ⟨k, hkG⟩ ∈ imageOTwoQuot G₁ K :=
  ⟨⟨k, hkG⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩

omit [Finite G] in
theorem qPi_pow {a : G} (ha : a ∈ G₁) (n : ℕ) :
    qPi G₁ ⟨a ^ n, G₁.pow_mem ha n⟩ = qPi G₁ ⟨a, ha⟩ ^ n := by
  rw [← map_pow]
  rfl

theorem eq_one_of_qPi_eq_one {z : G} (hz : z ∈ G₁) (hπ : qPi G₁ ⟨z, hz⟩ = 1) {n : ℕ}
    (hn : Odd n) (hzn : z ^ n = 1) : z = 1 := by
  have hp : (⟨z, hz⟩ : ↥G₁) ∈ CFSG.Open.pCore 2 ↥G₁ := by
    have h : (QuotientGroup.mk (⟨z, hz⟩ : ↥G₁) : OTwoQuot G₁) = 1 := hπ
    exact (QuotientGroup.eq_one_iff _).mp h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥G₁)) ⟨_, hp⟩
  have hzf : z ^ 2 ^ f = 1 := by
    have := congrArg (fun w : CFSG.Open.pCore 2 ↥G₁ => ((w : ↥G₁) : G)) hf
    simpa using this
  have hcop : Nat.Coprime (2 ^ f) n := Nat.Coprime.pow_left f (Nat.coprime_two_left.mpr hn)
  have hd : orderOf z ∣ Nat.gcd (2 ^ f) n :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzf) (orderOf_dvd_of_pow_eq_one hzn)
  rw [hcop.gcd_eq_one, Nat.dvd_one] at hd
  exact orderOf_eq_one_iff.mp hd

end Qpi

end CFSG.Quasithin.S146zU.UA
