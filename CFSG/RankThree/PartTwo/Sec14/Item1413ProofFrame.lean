module

public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofTools
public import CFSG.RankThree.PartTwo.KFacts.K73Lines

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Proof1413

variable {G : Type} [Group G] [Finite G]

structure Frame (L : Subgroup G) (c b d : G) : Prop where
  hcb : Commute c b
  hcd : Commute c d
  hbd : Commute b d
  hc : orderOf c = 3
  hcL : c ∉ L
  hbL : b ∈ L
  hdL : d ∈ L
  hb3 : b ^ 3 = 1
  hd : orderOf d = 3
  hbdz : b ∉ Subgroup.zpowers d

namespace Frame

variable {L : Subgroup G} {c b d : G} (hF : Frame L c b d)
include hF

omit [Finite G] in
theorem hc3 : c ^ 3 = 1 := by rw [← hF.hc]; exact pow_orderOf_eq_one c

omit [Finite G] in
theorem hd3 : d ^ 3 = 1 := by rw [← hF.hd]; exact pow_orderOf_eq_one d

theorem eq_mod {i j k i' j' k' : ℕ} (h : nf c b d i j k = nf c b d i' j' k') :
    i % 3 = i' % 3 ∧ j % 3 = j' % 3 ∧ k % 3 = k' % 3 :=
  nf_eq_mod hF.hcb hF.hcd hF.hbd hF.hc hF.hcL hF.hbL hF.hdL hF.hb3 hF.hd hF.hbdz h

omit [Finite G] hF in
theorem mul_pow_eq_nf (i : ℕ) : b * d ^ i = nf c b d 0 1 i := by simp [nf]

theorem mul_pow_not_mem_closure (i : ℕ) : b * d ^ i ∉ Subgroup.closure ({c, d} : Set G) := by
  intro h
  obtain ⟨m, n, -, -, hmn⟩ :=
    KFacts.exists_pow_mul_pow_of_mem_closure_pair hF.hcd.eq hF.hc3 hF.hd3 h
  have h' : nf c b d 0 1 i = nf c b d m 0 n := by
    rw [← mul_pow_eq_nf, hmn]
    simp [nf]
  have := hF.eq_mod h'
  omega

theorem mul_pow_ne_one (i : ℕ) : b * d ^ i ≠ 1 := by
  intro h
  have h' : nf c b d 0 1 i = nf c b d 0 0 0 := by
    rw [← mul_pow_eq_nf, h]
    simp [nf]
  have := hF.eq_mod h'
  omega

theorem orderOf_mul_pow (i : ℕ) : orderOf (b * d ^ i) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ (hF.mul_pow_ne_one i)
  rw [(hF.hbd.pow_right i).mul_pow, hF.hb3, ← pow_mul, mul_comm, pow_mul, hF.hd3, one_pow,
    one_mul]

theorem zpowers_ne {i j : ℕ} (hij : i % 3 ≠ j % 3) :
    Subgroup.zpowers (b * d ^ i) ≠ Subgroup.zpowers (b * d ^ j) := by
  intro h
  have hj : b * d ^ j ∈ Subgroup.zpowers (b * d ^ i) := h ▸ Subgroup.mem_zpowers _
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hj)
  have h' : nf c b d 0 1 j = nf c b d 0 n (i * n) := by
    rw [← mul_pow_eq_nf, ← hn, mul_pow_eq_nf, nf_pow hF.hcb hF.hcd hF.hbd]
    simp
  obtain ⟨-, h1, h2⟩ := hF.eq_mod h'
  have h3 : (i * n) % 3 = i % 3 := by
    rw [Nat.mul_mod, ← h1]
    simp
  omega

theorem not_mem_closure_mul : d ∉ Subgroup.closure ({c, b * d} : Set G) := by
  intro h
  have hcbd : c * (b * d) = (b * d) * c := ((hF.hcb.mul_right hF.hcd).eq)
  have hbd3 : (b * d) ^ 3 = 1 := by
    have h1 := hF.orderOf_mul_pow 1
    rw [pow_one] at h1
    rw [← h1]
    exact pow_orderOf_eq_one _
  obtain ⟨m, n, -, -, hmn⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hcbd hF.hc3 hbd3 h
  have h' : nf c b d 0 0 1 = nf c b d m n n := by
    have e1 : (b * d) ^ n = nf c b d 0 n n := by
      rw [show b * d = nf c b d 0 1 1 by simp [nf], nf_pow hF.hcb hF.hcd hF.hbd]
      simp
    calc nf c b d 0 0 1 = d := by simp [nf]
      _ = c ^ m * (b * d) ^ n := hmn
      _ = nf c b d m 0 0 * nf c b d 0 n n := by rw [e1]; simp [nf]
      _ = nf c b d m n n := by rw [nf_mul hF.hcb hF.hcd hF.hbd]; simp
  have := hF.eq_mod h'
  omega

omit [Finite G] in
theorem e_not_mem : c * (b * d) ∉ L := by
  intro h
  apply hF.hcL
  have : c = c * (b * d) * (b * d)⁻¹ := by group
  rw [this]
  exact mul_mem h (inv_mem (mul_mem hF.hbL hF.hdL))

theorem f_not_mem : c ^ 2 * (b * d) ∉ L := by
  intro h
  have h2 : c ^ 2 ∈ L := by
    have : c ^ 2 = c ^ 2 * (b * d) * (b * d)⁻¹ := by group
    rw [this]
    exact mul_mem h (inv_mem (mul_mem hF.hbL hF.hdL))
  have := three_dvd_of_pow_mem hF.hc hF.hcL h2
  omega

theorem e_not_mem_zpowers : c * (b * d) ∉ Subgroup.zpowers c := by
  intro h
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr h)
  have h' : nf c b d 1 1 1 = nf c b d n 0 0 := by
    rw [show nf c b d 1 1 1 = c * (b * d) by simp [nf, mul_assoc], ← hn]
    simp [nf]
  have := hF.eq_mod h'
  omega

theorem f_not_mem_zpowers : c ^ 2 * (b * d) ∉ Subgroup.zpowers c := by
  intro h
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr h)
  have h' : nf c b d 2 1 1 = nf c b d n 0 0 := by
    rw [show nf c b d 2 1 1 = c ^ 2 * (b * d) by simp [nf, mul_assoc], ← hn]
    simp [nf]
  have := hF.eq_mod h'
  omega

theorem mem_of_mem_closure {d' : G} (hbd' : Commute b d') (hd'3 : d' ^ 3 = 1)
    (h : d ∈ Subgroup.closure ({b, d'} : Set G)) : d' ∈ L := by
  obtain ⟨m, n, -, hn, hmn⟩ :=
    KFacts.exists_pow_mul_pow_of_mem_closure_pair hbd'.eq hF.hb3 hd'3 h
  have hd'n : d' ^ n ∈ L := by
    have : d' ^ n = (b ^ m)⁻¹ * d := by rw [hmn]; group
    rw [this]
    exact mul_mem (inv_mem (Subgroup.pow_mem _ hF.hbL m)) hF.hdL
  interval_cases n
  ·
    have h' : nf c b d 0 0 1 = nf c b d 0 m 0 := by
      calc nf c b d 0 0 1 = d := by simp [nf]
        _ = b ^ m * d' ^ 0 := hmn
        _ = nf c b d 0 m 0 := by simp [nf]
    have := hF.eq_mod h'
    omega
  · simpa using hd'n
  · have : d' = (d' ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hd'3, one_mul, pow_one]
    rw [this]
    exact Subgroup.pow_mem _ hd'n 2

omit [Finite G] in
theorem cd_not_mem : c * d ∉ L := by
  intro h
  apply hF.hcL
  have : c = c * d * d⁻¹ := by group
  rw [this]
  exact mul_mem h (inv_mem hF.hdL)

theorem c2d_not_mem : c ^ 2 * d ∉ L := by
  intro h
  have h2 : c ^ 2 ∈ L := by
    have : c ^ 2 = c ^ 2 * d * d⁻¹ := by group
    rw [this]
    exact mul_mem h (inv_mem hF.hdL)
  have := three_dvd_of_pow_mem hF.hc hF.hcL h2
  omega

theorem not_mem_closure_cd : c ^ 2 * d ∉ Subgroup.closure ({b, c * d} : Set G) := by
  intro h
  have hbcd : b * (c * d) = (c * d) * b := ((hF.hcb.symm.mul_right hF.hbd).eq)
  have hcd3 : (c * d) ^ 3 = 1 := by
    rw [hF.hcd.mul_pow, hF.hc3, hF.hd3, one_mul]
  obtain ⟨m, n, -, -, hmn⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hbcd hF.hb3 hcd3 h
  have h' : nf c b d 2 0 1 = nf c b d n m n := by
    have e1 : (c * d) ^ n = nf c b d n 0 n := by
      rw [show c * d = nf c b d 1 0 1 by simp [nf], nf_pow hF.hcb hF.hcd hF.hbd]
      simp
    calc nf c b d 2 0 1 = c ^ 2 * d := by simp [nf]
      _ = b ^ m * (c * d) ^ n := hmn
      _ = nf c b d 0 m 0 * nf c b d n 0 n := by rw [e1]; simp [nf]
      _ = nf c b d n m n := by rw [nf_mul hF.hcb hF.hcd hF.hbd]; simp
  have := hF.eq_mod h'
  omega

omit [Finite G] in
theorem e_eq : c * (b * d) = b * (c * d) := by
  rw [← mul_assoc, hF.hcb.eq, mul_assoc]

omit [Finite G] in
theorem f_eq : c ^ 2 * (b * d) = b * (c ^ 2 * d) := by
  rw [← mul_assoc, (hF.hcb.pow_left 2).eq, mul_assoc]

end Frame

end Proof1413

end CFSG.RankThree.PartTwo.Sec14
