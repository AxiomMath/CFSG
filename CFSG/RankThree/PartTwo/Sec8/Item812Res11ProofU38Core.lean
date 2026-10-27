module

public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofTools
import CFSG.RankThree.PartTwo.KFacts.K71Coprime

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction)

namespace Item812Res11

theorem sq_eq_one_of_pow_two_pow {M : Type*} [Group M] {C : Subgroup M}
    (hC : ∀ z ∈ C, z ^ 4 = 1 → z ^ 2 = 1) {x : M} (hx : x ∈ C) :
    ∀ e : ℕ, x ^ 2 ^ e = 1 → x ^ 2 = 1
  | 0, h => by
    rw [pow_zero, pow_one] at h
    rw [h, one_pow]
  | 1, h => by rwa [pow_one] at h
  | e + 2, h => by
    apply sq_eq_one_of_pow_two_pow hC hx (e + 1)
    have h1 : (x ^ 2 ^ e) ^ 4 = 1 := by
      rw [← pow_mul, show 2 ^ e * 4 = 2 ^ (e + 2) by ring]
      exact h
    have h2 := hC _ (C.pow_mem hx _) h1
    rwa [← pow_mul, show 2 ^ e * 2 = 2 ^ (e + 1) by ring] at h2

variable {G : Type} [Group G] [Finite G]

theorem sec8I_le_L {L : Subgroup G} {a : G} :
    sec8I L a ≤ L := by
  unfold sec8I
  split_ifs
  · exact (Subgroup.closure_le _).mpr fun y hy => hy.1.1
  · exact (Subgroup.map_subtype_le _).trans inf_le_left

theorem exists_mem_sec8I_of_pow_four {L : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    (hU : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3)
    {z : L ⧸ aschbacherSolvableCore 3 L} (hz : z ∈ barCentralizer (Subgroup.zpowers a) L)
    (hz4 : z ^ 4 = 1) :
    ∃ x : sec8I L a, Item87Proof.modThetaHom sec8I_le_L x = z := by
  classical
  rw [← KFacts.imageModTheta_centralizer_eq haN ⟨1, by rw [pow_one]; exact ha3⟩] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hw' : (w : G) ∈ L ⊓ Subgroup.centralizer {a} := Subgroup.mem_subgroupOf.mp hw
  obtain ⟨e, u, hu, ho⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (w : G)).ne'
  have hxmem : (w : G) ^ (u ^ 2) ∈ L ⊓ Subgroup.centralizer {a} := Subgroup.pow_mem _ hw' _
  have hx2 : ((w : G) ^ (u ^ 2)) ^ 2 ^ e = 1 := by
    rw [← pow_mul, show u ^ 2 * 2 ^ e = 2 ^ e * u * u by ring, pow_mul, ← ho,
      pow_orderOf_eq_one, one_pow]
  have hxI : (w : G) ^ (u ^ 2) ∈ sec8I L a := by
    simp only [sec8I, hU, ↓reduceIte]
    exact Subgroup.subset_closure ⟨hxmem, e, hx2⟩
  refine ⟨⟨_, hxI⟩, ?_⟩
  have hwz : Item87Proof.modThetaHom sec8I_le_L ⟨_, hxI⟩ =
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) w ^ (u ^ 2) := by
    rw [← map_pow]
    rfl
  rw [hwz]
  obtain ⟨k, rfl⟩ := hu
  rw [show (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 by ring, pow_succ, pow_mul]
  have h4 : (QuotientGroup.mk' (aschbacherSolvableCore 3 L) w) ^ 4 = 1 := hz4
  rw [h4, one_pow, one_mul]

theorem exists_not_mem_theta_of_witness {L I : Subgroup G} {b : G} (hIL : I ≤ L)
    (hbL : b ∈ Subgroup.normalizer (L : Set G)) (hbI : b ∈ Subgroup.normalizer (I : Set G))
    (hb3 : b ^ 3 = 1) (t s : I)
    (ht4 : Item87Proof.modThetaHom hIL t ^ 4 = 1)
    (hw3 : (Item87Proof.modThetaHom hIL t ^ 2 * (Item87Proof.modThetaHom hIL s *
      Item87Proof.modThetaHom hIL t ^ 2 * (Item87Proof.modThetaHom hIL s)⁻¹)) ^ 3 = 1)
    (hw1 : Item87Proof.modThetaHom hIL t ^ 2 * (Item87Proof.modThetaHom hIL s *
      Item87Proof.modThetaHom hIL t ^ 2 * (Item87Proof.modThetaHom hIL s)⁻¹) ≠ 1)
    (hB : ∀ z ∈ barCentralizer (Subgroup.zpowers b) L, z ^ 4 = 1 → z ^ 2 = 1) :
    ∃ i ∈ I, b * i * b⁻¹ * i⁻¹ ∉ ((aschbacherSolvableCore 3 I).map I.subtype : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hall
  push Not at hall
  set φI := Item87Proof.modThetaHom hIL with hφI
  set N := aschbacherSolvableCore 3 I with hN
  have hNn : N.Normal := inferInstance
  have hN3 : ¬ 3 ∣ Nat.card N := KFacts.not_three_dvd_card_aschbacherSolvableCore I
  set bI : Subgroup.normalizer (I : Set G) := ⟨b, hbI⟩ with hbIdef
  have hτ : thetaQuotMulAut I (compAction I bI) = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [Sec4.thetaQuotMulAut_mk, MulAut.one_apply, QuotientGroup.eq]
      obtain ⟨n, hn, hne⟩ := hall x x.2
      have hne' : (n : G) = b * x * b⁻¹ * (x : G)⁻¹ := hne
      have e1 : (compAction I bI x : I)⁻¹ * x = x⁻¹ * n⁻¹ * x⁻¹⁻¹ := by
        apply Subtype.ext
        change (b * (x : G) * b⁻¹)⁻¹ * x = (x : G)⁻¹ * (n : G)⁻¹ * (x : G)⁻¹⁻¹
        rw [hne']
        group
      rw [e1]
      exact hNn.conj_mem _ (N.inv_mem hn) x⁻¹
  have hbP : IsPGroup 3 (Subgroup.zpowers bI) := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have h1 : (bI ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      have : bI ^ 3 = 1 := Subtype.ext (by simpa [hbIdef] using hb3)
      rw [this, one_zpow]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one
      (show (⟨bI ^ k, hg⟩ : Subgroup.zpowers bI) ^ 3 ^ 1 = 1 from
        Subtype.ext (by rw [pow_one]; exact h1)))
    exact ⟨i, hi⟩
  set φ : Subgroup.zpowers bI →* MulAut I := (compAction I).comp (Subgroup.zpowers bI).subtype
    with hφ
  have hφN : ∀ g, ∀ n ∈ N, φ g n ∈ N := by
    intro g n hn
    have h : N.map ((φ g : MulAut I) : I →* I) = N := Sec4.map_aschbacherSolvableCore (φ g)
    rw [← h]
    exact ⟨n, hn, rfl⟩
  have hy : ∀ g, ((φ g t : I) : I ⧸ N) = (t : I ⧸ N) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    change ((compAction I (bI ^ k) t : I) : I ⧸ N) = _
    rw [← Sec4.thetaQuotMulAut_mk, map_zpow, map_zpow, hτ, one_zpow, MulAut.one_apply]
  obtain ⟨t', ht'eq, ht'fix⟩ := KFacts.exists_fixed_of_coprime hbP φ N hN3 hφN t hy
  obtain ⟨n, hn, ht'⟩ : ∃ n ∈ N, t' = t * n :=
    ⟨t⁻¹ * t', QuotientGroup.eq.mp ht'eq.symm, by group⟩
  subst ht'
  have hbt' : b * ((t * n : I) : G) * b⁻¹ = (t * n : I) := by
    have h1 := congrArg Subtype.val (ht'fix ⟨bI, Subgroup.mem_zpowers bI⟩)
    exact h1
  set z := φI (t * n) with hz
  have hzC : z ∈ barCentralizer (Subgroup.zpowers b) L := by
    rw [KFacts.mem_barCentralizer_zpowers_iff hbL]
    change thetaQuotMulAut L (compAction L ⟨b, hbL⟩)
      ((⟨(t * n : I), hIL (t * n).2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = _
    rw [Sec4.thetaQuotMulAut_mk]
    congr 1
    exact Subtype.ext hbt'
  have hpow : ∀ j : ℕ, ∃ m ∈ N, z ^ j = φI t ^ j * φI m := by
    intro j
    induction j with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨m, hm, hmj⟩ := ih
      refine ⟨t⁻¹ * m * t * n, N.mul_mem ?_ hn, ?_⟩
      · have := hNn.conj_mem m hm t⁻¹
        rwa [inv_inv] at this
      · rw [pow_succ, hmj, hz]
        simp only [map_mul, map_inv, pow_succ]
        group
  obtain ⟨e, u, hu, ho⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  have hzu : (z ^ u) ^ 2 ^ e = 1 := by
    rw [← pow_mul, mul_comm, ← ho, pow_orderOf_eq_one]
  have hz2u : z ^ (2 * u) = 1 := by
    have := sq_eq_one_of_pow_two_pow hB (Subgroup.pow_mem _ hzC u) e hzu
    rwa [← pow_mul, mul_comm] at this
  obtain ⟨m, hm, hmz⟩ := hpow (2 * u)
  have htu : φI t ^ (2 * u) = φI t ^ 2 := by
    obtain ⟨k, rfl⟩ := hu
    rw [show 2 * (2 * k + 1) = 4 * k + 2 by ring, pow_add, pow_mul, ht4, one_pow, one_mul]
  rw [hz2u, htu] at hmz
  have ht2m : φI t ^ 2 = φI m⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left hmz.symm
  set n₀ : I := m⁻¹ * (s * m⁻¹ * s⁻¹) with hn₀
  have hn₀N : n₀ ∈ N := N.mul_mem (N.inv_mem hm) (hNn.conj_mem _ (N.inv_mem hm) s)
  have hw : φI t ^ 2 * (φI s * φI t ^ 2 * (φI s)⁻¹) = φI n₀ := by
    rw [ht2m, hn₀]
    simp only [map_mul, map_inv]
  rw [hw] at hw3 hw1
  have h1 : orderOf (φI n₀) ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
  have h2 : orderOf (φI n₀) ∣ Nat.card N := by
    refine (orderOf_map_dvd φI n₀).trans ?_
    have := Subgroup.orderOf_dvd_natCard N hn₀N
    exact this
  have hcop : Nat.Coprime 3 (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
  exact hw1 (orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2))

end Item812Res11

end CFSG.RankThree.PartTwo.Sec8
