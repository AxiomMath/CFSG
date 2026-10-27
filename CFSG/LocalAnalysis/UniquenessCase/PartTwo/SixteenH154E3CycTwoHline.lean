module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoExp3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AABBAAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

open scoped Pointwise

variable {X : Type} [CommGroup X] {Mb : Subgroup (MulAut X)} {ψ z : MulAut X} {U : Subgroup X}

private lemma s16h_e3_CycTwoHline_conj_zp_mem (F : s16h_CycFrame Mb ψ z U) {n : MulAut X}
    (hn : n ∈ s16h_CycN Mb z) :
    n * (ψ * z * ψ⁻¹) * n⁻¹ ∈ Subgroup.zpowers (ψ * z * ψ⁻¹) := by
  have hmN : ψ⁻¹ * n * ψ ∈ s16h_CycN Mb z := F.conj_inv_mem F.psi_mem hn
  have hmz : (ψ⁻¹ * n * ψ) * z * (ψ⁻¹ * n * ψ)⁻¹ ∈ Subgroup.zpowers z := by
    have hnorm : ψ⁻¹ * n * ψ ∈
        Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut X)) :=
      (inf_le_right : s16h_CycN Mb z ≤
        Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut X))) hmN
    exact (Subgroup.mem_normalizer_iff.1 hnorm z).mp (Subgroup.mem_zpowers z)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmz
  refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
  have hconj_pow : (ψ * z * ψ⁻¹) ^ i = ψ * z ^ i * ψ⁻¹ := by
    have h := map_zpow (MulAut.conj ψ) z i
    rw [MulAut.conj_apply, MulAut.conj_apply] at h
    exact h.symm
  calc (ψ * z * ψ⁻¹) ^ i
      = ψ * z ^ i * ψ⁻¹ := hconj_pow
    _ = ψ * ((ψ⁻¹ * n * ψ) * z * (ψ⁻¹ * n * ψ)⁻¹) * ψ⁻¹ := by rw [← hi]
    _ = n * (ψ * z * ψ⁻¹) * n⁻¹ := by group

private lemma s16h_e3_CycTwoHline_N_le_normalizer (F : s16h_CycFrame Mb ψ z U) :
    s16h_CycN Mb z ≤
      Subgroup.normalizer (Subgroup.zpowers (ψ * z * ψ⁻¹) : Set (MulAut X)) := by
  rw [Subgroup.le_normalizer_iff]
  intro n hn k hk
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hconj := s16h_e3_CycTwoHline_conj_zp_mem F hn
  have he : n * (ψ * z * ψ⁻¹) ^ j * n⁻¹ = (n * (ψ * z * ψ⁻¹) * n⁻¹) ^ j := by
    have h := map_zpow (MulAut.conj n) (ψ * z * ψ⁻¹) j
    rw [MulAut.conj_apply, MulAut.conj_apply] at h
    exact h
  rw [he]
  exact Subgroup.zpow_mem _ hconj j

theorem s16h_e3_CycTwoHline_not_fixed
    [Finite X] [Finite (MulAut X)] (F : s16h_CycFrame Mb ψ z U)
    {u₀ : X} (hu₀ : u₀ ∈ U)
    (hK : ∀ R : Subgroup (MulAut X), R ≤ Mb → IsElemAbelian 3 R →
      (∀ r ∈ R, r u₀ = u₀) → Nat.card ↥R ≤ 3)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (autSub (s16h_CycN Mb z) U)) :
    ∀ b ∈ autSub (s16h_CycN Mb z) U, b ≠ 1 → orderOf b = 3 →
      b ⟨u₀, hu₀⟩ ≠ ⟨u₀, hu₀⟩ := by
  classical
  intro b hb hb_ne hb_ord hfix
  rw [← F.rho_range] at hb
  obtain ⟨n₀, rfl⟩ := hb
  have ho_pos : 0 < orderOf (n₀ : MulAut X) := orderOf_pos _
  obtain ⟨a, m, hm_notdvd, ho⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.pos_iff_ne_zero.mp ho_pos) 3 (by norm_num)
  let n₁ : MulAut X := (n₀ : MulAut X) ^ m
  have hn₁_mem : n₁ ∈ s16h_CycN Mb z := (s16h_CycN Mb z).pow_mem n₀.2 m
  have hm_ne0 : m ≠ 0 := by
    intro hm0
    exact (Nat.pos_iff_ne_zero.mp ho_pos) (by rw [ho, hm0, mul_zero])
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne0
  have hn1_ord : orderOf n₁ = 3 ^ a := by
    have hm_dvd : m ∣ orderOf (n₀ : MulAut X) := by
      rw [ho]; exact dvd_mul_left m (3 ^ a)
    change orderOf ((n₀ : MulAut X) ^ m) = 3 ^ a
    rw [orderOf_pow_of_dvd hm_ne0 hm_dvd, ho, mul_comm (3 ^ a) m,
      Nat.mul_div_cancel_left _ hm_pos]
  have hrho_n1 : F.rho ⟨n₁, hn₁_mem⟩ = (F.rho n₀) ^ m := by
    have he : (⟨n₁, hn₁_mem⟩ : ↥(s16h_CycN Mb z)) = n₀ ^ m := Subtype.ext rfl
    rw [he, map_pow]
  have hbm_ne : (F.rho n₀) ^ m ≠ 1 := by
    intro h
    have hdvd : orderOf (F.rho n₀) ∣ m := orderOf_dvd_of_pow_eq_one h
    rw [hb_ord] at hdvd
    exact hm_notdvd hdvd
  have hg_rho : ∃ k : ℕ, orderOf (F.rho ⟨n₁, hn₁_mem⟩) = 3 ^ k := by
    have hdvd : orderOf (F.rho ⟨n₁, hn₁_mem⟩) ∣ 3 ^ a := by
      have h := orderOf_map_dvd F.rho (⟨n₁, hn₁_mem⟩ : ↥(s16h_CycN Mb z))
      rwa [Subgroup.orderOf_mk n₁ hn₁_mem, hn1_ord] at h
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact ⟨k, hk⟩
  have hpow_rho : (F.rho ⟨n₁, hn₁_mem⟩) ^ 3 = 1 :=
    s16h_e3_CycTwoExp3_pow_three (W := ↥U)
      (fun w : ↥U => Subtype.ext (F.exp2 (w : X))) F.card_u h2 hg_rho
  let n₁' : MulAut X := ψ⁻¹ * n₁ * ψ
  have hn₁'_mem : n₁' ∈ s16h_CycN Mb z := F.conj_inv_mem F.psi_mem hn₁_mem
  have hn1'_ord : orderOf n₁' = orderOf n₁ := by
    have hsc : SemiconjBy ψ⁻¹ n₁ n₁' := by
      show ψ⁻¹ * n₁ = (ψ⁻¹ * n₁ * ψ) * ψ⁻¹
      group
    exact (SemiconjBy.orderOf_eq ψ⁻¹ hsc).symm
  have hg_rho' : ∃ k : ℕ, orderOf (F.rho ⟨n₁', hn₁'_mem⟩) = 3 ^ k := by
    have hdvd : orderOf (F.rho ⟨n₁', hn₁'_mem⟩) ∣ 3 ^ a := by
      have h := orderOf_map_dvd F.rho (⟨n₁', hn₁'_mem⟩ : ↥(s16h_CycN Mb z))
      rwa [Subgroup.orderOf_mk n₁' hn₁'_mem, hn1'_ord, hn1_ord] at h
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact ⟨k, hk⟩
  have hpow_rho' : (F.rho ⟨n₁', hn₁'_mem⟩) ^ 3 = 1 :=
    s16h_e3_CycTwoExp3_pow_three (W := ↥U)
      (fun w : ↥U => Subtype.ext (F.exp2 (w : X))) F.card_u h2 hg_rho'
  have hn1_cube : n₁ ^ 3 = 1 := by
    refine F.eq_one_of_rho_eq_one ((s16h_CycN Mb z).pow_mem hn₁_mem 3) ?_ ?_
    · have he : (⟨n₁ ^ 3, (s16h_CycN Mb z).pow_mem hn₁_mem 3⟩ : ↥(s16h_CycN Mb z)) =
          ⟨n₁, hn₁_mem⟩ ^ 3 := Subtype.ext rfl
      rw [he, map_pow, hpow_rho]
    · have he : (⟨ψ⁻¹ * n₁ ^ 3 * ψ,
            F.conj_inv_mem F.psi_mem ((s16h_CycN Mb z).pow_mem hn₁_mem 3)⟩ :
            ↥(s16h_CycN Mb z)) = ⟨n₁', hn₁'_mem⟩ ^ 3 := by
        apply Subtype.ext
        show ψ⁻¹ * n₁ ^ 3 * ψ = (ψ⁻¹ * n₁ * ψ) ^ 3
        have h := map_pow (MulAut.conj ψ⁻¹) n₁ 3
        rw [MulAut.conj_apply, MulAut.conj_apply] at h
        simpa using h
      rw [he, map_pow, hpow_rho']
  have hrho_n1_ne : F.rho ⟨n₁, hn₁_mem⟩ ≠ 1 := by
    rw [hrho_n1]; exact hbm_ne
  have hn1_ne_one : n₁ ≠ 1 := by
    intro h
    exact hrho_n1_ne (by
      have hsub : (⟨n₁, hn₁_mem⟩ : ↥(s16h_CycN Mb z)) = 1 := Subtype.ext h
      rw [hsub, map_one])
  have hn1_ord3 : orderOf n₁ = 3 := orderOf_eq_prime hn1_cube hn1_ne_one
  have hz'_ord : orderOf (ψ * z * ψ⁻¹) = 3 := by
    have hsc : SemiconjBy ψ z (ψ * z * ψ⁻¹) := by
      show ψ * z = (ψ * z * ψ⁻¹) * ψ
      group
    exact (SemiconjBy.orderOf_eq ψ hsc).symm.trans F.z_ord
  have hcomm : Commute n₁ (ψ * z * ψ⁻¹) :=
    s16h_e3_CycTwoP3M4AA2AABBAAA_three_centralizes_z (W := X)
      (A := s16h_CycN Mb z) hz'_ord (s16h_e3_CycTwoHline_N_le_normalizer F) hn₁_mem hn1_ord3
  have hpow_fix_all : ∀ k : ℕ, ((F.rho n₀) ^ k) ⟨u₀, hu₀⟩ = ⟨u₀, hu₀⟩ := by
    intro k
    induction k with
    | zero => rfl
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hfix, ih]
  have hpow_fix := hpow_fix_all m
  have hn1_fix : n₁ u₀ = u₀ := by
    have h : F.rho ⟨n₁, hn₁_mem⟩ ⟨u₀, hu₀⟩ = ⟨u₀, hu₀⟩ := by
      rw [hrho_n1]; exact hpow_fix
    have h2 := congrArg (fun v : ↥U => (v : X)) h
    rw [F.rho_apply] at h2
    simpa using h2
  have hz'_fix : (ψ * z * ψ⁻¹) u₀ = u₀ := F.zp_fix u₀ hu₀
  let R : Subgroup (MulAut X) := Subgroup.zpowers n₁ ⊔ Subgroup.zpowers (ψ * z * ψ⁻¹)
  have hR_le_Mb : R ≤ Mb := by
    change Subgroup.zpowers n₁ ⊔ Subgroup.zpowers (ψ * z * ψ⁻¹) ≤ Mb
    refine sup_le ?_ ?_
    · exact (Subgroup.zpowers_le.mpr hn₁_mem).trans F.N_le
    · exact (Subgroup.zpowers_le.mpr F.zp_mem_N).trans F.N_le
  have hnorm : Subgroup.zpowers (ψ * z * ψ⁻¹) ≤
      Subgroup.normalizer (Subgroup.zpowers n₁ : Set (MulAut X)) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hc : Commute ((ψ * z * ψ⁻¹) ^ i) (n₁ ^ j) := hcomm.symm.zpow_zpow i j
    have he : (ψ * z * ψ⁻¹) ^ i * n₁ ^ j * ((ψ * z * ψ⁻¹) ^ i)⁻¹ = n₁ ^ j := by
      rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [he]
    exact Subgroup.zpow_mem_zpowers n₁ j
  have hR_pow : ∀ x ∈ R, x ^ 3 = 1 := by
    intro x hx
    have hx' : x ∈ (Subgroup.zpowers n₁ : Set (MulAut X)) *
        (Subgroup.zpowers (ψ * z * ψ⁻¹) : Set (MulAut X)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers n₁)
        (Subgroup.zpowers (ψ * z * ψ⁻¹)) hnorm]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hc : Commute (n₁ ^ i) ((ψ * z * ψ⁻¹) ^ j) := hcomm.zpow_zpow i j
    rw [hc.mul_pow 3]
    have h1 : (n₁ ^ i) ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact hn1_ord3 ▸ orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers n₁ i)
    have h2 : ((ψ * z * ψ⁻¹) ^ j) ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact hz'_ord ▸
        orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers (ψ * z * ψ⁻¹) j)
    rw [h1, h2, mul_one]
  have hn1_notin : n₁ ∉ Subgroup.zpowers (ψ * z * ψ⁻¹) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : F.rho ⟨n₁, hn₁_mem⟩ = 1 := by
      have he : (⟨n₁, hn₁_mem⟩ : ↥(s16h_CycN Mb z)) =
          ⟨ψ * z * ψ⁻¹, F.zp_mem_N⟩ ^ k := by
        apply Subtype.ext
        exact hk.symm
      rw [he, map_zpow, F.rho_zp, one_zpow]
    exact hrho_n1_ne h1
  have hdisj : Disjoint (Subgroup.zpowers n₁) (Subgroup.zpowers (ψ * z * ψ⁻¹)) := by
    rw [disjoint_iff]
    refine Subgroup.eq_bot_of_card_le
      (H := Subgroup.zpowers n₁ ⊓ Subgroup.zpowers (ψ * z * ψ⁻¹)) ?_
    have hdvd : Nat.card ↥(Subgroup.zpowers n₁ ⊓
        Subgroup.zpowers (ψ * z * ψ⁻¹)) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_left : Subgroup.zpowers n₁ ⊓ Subgroup.zpowers (ψ * z * ψ⁻¹) ≤
          Subgroup.zpowers n₁)
      rwa [Nat.card_zpowers, hn1_ord3] at h
    have hne : Nat.card ↥(Subgroup.zpowers n₁ ⊓
        Subgroup.zpowers (ψ * z * ψ⁻¹)) ≠ 3 := by
      intro h3
      have heq : Subgroup.zpowers n₁ ⊓ Subgroup.zpowers (ψ * z * ψ⁻¹) =
          Subgroup.zpowers n₁ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left
          (by rw [h3, Nat.card_zpowers, hn1_ord3])
      have hmem : n₁ ∈ Subgroup.zpowers n₁ ⊓ Subgroup.zpowers (ψ * z * ψ⁻¹) := by
        rw [heq]; exact Subgroup.mem_zpowers n₁
      exact hn1_notin (Subgroup.mem_inf.1 hmem).2
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact le_of_eq h1
    · exact absurd h3 hne
  have hR_card : Nat.card ↥R = 9 := by
    change Nat.card ↥(Subgroup.zpowers n₁ ⊔ Subgroup.zpowers (ψ * z * ψ⁻¹)) = 9
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers n₁) (Subgroup.zpowers (ψ * z * ψ⁻¹)) hnorm hdisj,
      Nat.card_zpowers, Nat.card_zpowers, hn1_ord3, hz'_ord]
  have hR_abel : IsElemAbelian 3 R := by
    refine ⟨?_, hR_pow⟩
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := ↥R) (p := 3)
      (by rw [hR_card]; norm_num)
  have hR_fix : ∀ r ∈ R, r u₀ = u₀ := by
    have hle : R ≤ MulAction.stabilizer (MulAut X) u₀ :=
      sup_le (Subgroup.zpowers_le.mpr hn1_fix) (Subgroup.zpowers_le.mpr hz'_fix)
    intro r hr
    simpa using hle hr
  have hle := hK R hR_le_Mb hR_abel hR_fix
  rw [hR_card] at hle
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
