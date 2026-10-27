module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res2ProofL3
import CFSG.RankThree.PartTwo.Sec19.Item19ResProofAutCent
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Function

section Nine

variable {Y : Type} [Group Y]

theorem mulAut_pow_apply (σ : MulAut Y) (n : ℕ) (y : Y) : (σ ^ n) y = (⇑σ)^[n] y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, ih, iterate_succ_apply]

theorem pow_three_apply_of_card_nine [Finite Y] {S : Subgroup Y} (hS9 : Nat.card S = 9)
    (σ : MulAut Y) (hσS : ∀ s ∈ S, σ s ∈ S) {k : ℕ} (hσ : σ ^ 3 ^ k = 1) :
    ∀ y ∈ S, (σ ^ 3) y = y := by
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1, map_one]
  have hper : IsPeriodicPt (⇑σ) (3 ^ k) y := by
    change (⇑σ)^[3 ^ k] y = y
    rw [← mulAut_pow_apply, hσ]
    rfl
  have hm0 : 0 < minimalPeriod (⇑σ) y := hper.minimalPeriod_pos (by positivity)
  have hmdvd : minimalPeriod (⇑σ) y ∣ 3 ^ k := hper.minimalPeriod_dvd
  have hsub : (fun n => (⇑σ)^[n] y) '' Set.Iio (minimalPeriod (⇑σ) y) ⊆ (S : Set Y) \ {1} := by
    rintro _ ⟨n, -, rfl⟩
    have hmem : ∀ n : ℕ, (⇑σ)^[n] y ∈ S ∧ (⇑σ)^[n] y ≠ 1 := by
      intro n
      induction n with
      | zero => exact ⟨hy, hy1⟩
      | succ n ih =>
        rw [iterate_succ_apply']
        exact ⟨hσS _ ih.1, fun h => ih.2 (σ.injective (h.trans (map_one σ).symm))⟩
    exact ⟨(hmem n).1, (hmem n).2⟩
  have hcard : minimalPeriod (⇑σ) y ≤ 8 := by
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.InjOn.ncard_image iterate_injOn_Iio_minimalPeriod, Set.ncard_Iio,
      Nat.card_Iio] at h1
    have h2 : ((S : Set Y) \ {1}).ncard = 8 := by
      rw [Set.ncard_sdiff_singleton_of_mem (one_mem S), ← Nat.card_coe_set_eq]
      change Nat.card S - 1 = 8
      rw [hS9]
    omega
  obtain ⟨j, -, hmj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hmdvd
  have hj1 : j ≤ 1 := by
    by_contra h
    have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h3 : minimalPeriod (⇑σ) y ∣ 3 := by
    rw [hmj]
    interval_cases j <;> norm_num
  rw [mulAut_pow_apply]
  exact isPeriodicPt_iff_minimalPeriod_dvd.mpr h3

theorem pow_eq_pow_mod_three {y : Y} (hy : y ^ 3 = 1) (n : ℕ) : y ^ n = y ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hy, one_pow, mul_one]

theorem eq_of_pow_mul_pow_eq {y z : Y} (hy : orderOf y = 3)
    (hz : z ^ 3 = 1) (hzy : z ∉ Subgroup.zpowers y) {a b a' b' : ℕ} (ha : a < 3) (hb : b < 3)
    (ha' : a' < 3) (hb' : b' < 3) (h : y ^ a * z ^ b = y ^ a' * z ^ b') : a = a' ∧ b = b' := by
  have hbb : b = b' := by
    by_contra hne
    set d : ℤ := (b : ℤ) - b' with hd
    have hzd : z ^ d ∈ Subgroup.zpowers y := by
      have h1 : z ^ d = y ^ ((a' : ℤ) - a) := by
        have h2 : y ^ (a : ℤ) * z ^ (b : ℤ) = y ^ (a' : ℤ) * z ^ (b' : ℤ) := by
          simpa only [zpow_natCast] using h
        rw [hd, zpow_sub, zpow_sub]
        calc z ^ (b : ℤ) * (z ^ (b' : ℤ))⁻¹
            = (y ^ (a : ℤ))⁻¹ * (y ^ (a : ℤ) * z ^ (b : ℤ)) * (z ^ (b' : ℤ))⁻¹ := by group
          _ = (y ^ (a : ℤ))⁻¹ * (y ^ (a' : ℤ) * z ^ (b' : ℤ)) * (z ^ (b' : ℤ))⁻¹ := by rw [h2]
          _ = y ^ (a' : ℤ) * (y ^ (a : ℤ))⁻¹ := by
              rw [show (y ^ (a : ℤ))⁻¹ = y ^ (-(a : ℤ)) by rw [zpow_neg]]
              calc y ^ (-(a : ℤ)) * (y ^ (a' : ℤ) * z ^ (b' : ℤ)) * (z ^ (b' : ℤ))⁻¹
                  = y ^ (-(a : ℤ)) * y ^ (a' : ℤ) := by group
                _ = y ^ (a' : ℤ) * y ^ (-(a : ℤ)) := by
                    rw [← zpow_add, ← zpow_add, add_comm]
      rw [h1]
      exact Subgroup.zpow_mem_zpowers y _
    have hdd : ∃ t : ℤ, d * d = 1 + 3 * t := by
      have : d = 1 ∨ d = 2 ∨ d = -1 ∨ d = -2 := by omega
      rcases this with h | h | h | h <;> rw [h]
      · exact ⟨0, by norm_num⟩
      · exact ⟨1, by norm_num⟩
      · exact ⟨0, by norm_num⟩
      · exact ⟨1, by norm_num⟩
    obtain ⟨t, ht⟩ := hdd
    apply hzy
    have : z = (z ^ d) ^ d := by
      rw [← zpow_mul, ht, zpow_add, zpow_one, zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl,
        zpow_natCast, hz, one_zpow, mul_one]
    rw [this]
    exact Subgroup.zpow_mem _ hzd d
  subst hbb
  refine ⟨?_, rfl⟩
  have h2 : y ^ a = y ^ a' := mul_right_cancel h
  exact pow_injOn_Iio_orderOf (by rw [hy]; exact ha) (by rw [hy]; exact ha') h2

theorem norm_eq_one_of_card_nine [Finite Y] {S : Subgroup Y} (hS9 : Nat.card S = 9)
    (hS3 : ∀ s ∈ S, s ^ 3 = 1) (hSab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (σ : MulAut Y)
    (hσS : ∀ s ∈ S, σ s ∈ S) (hσ3 : ∀ s ∈ S, (σ ^ 3) s = s) :
    ∀ y ∈ S, y * σ y * σ (σ y) = 1 := by
  intro y hy
  have hσy : σ (σ (σ y)) = y := by
    have := hσ3 y hy
    rwa [pow_three, MulAut.mul_apply, MulAut.mul_apply] at this
  by_cases hy1 : y = 1
  · rw [hy1]
    simp
  have hzS : σ y ∈ S := hσS y hy
  have hy3 : y ^ 3 = 1 := hS3 y hy
  have hz3 : σ y ^ 3 = 1 := hS3 _ hzS
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyz : y * σ y = σ y * y := hSab y hy _ hzS
  by_cases hzy : σ y ∈ Subgroup.zpowers y
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hzy
    obtain ⟨n, hn⟩ := exists_pow_eq_zpow_of_pow_three hy3 i
    have hz : σ y = y ^ (n % 3) := by rw [← hi, hn, pow_eq_pow_mod_three hy3]
    have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : n % 3
    · exfalso
      apply hy1
      apply σ.injective
      rw [hz, pow_zero, map_one]
    · rw [pow_one] at hz
      rw [hz, hz, ← pow_three', hy3]
    · exfalso
      have h1 : σ (σ y) = y := by
        rw [hz, map_pow, hz, ← pow_mul, pow_eq_pow_mod_three hy3]
        norm_num
      rw [h1, hz] at hσy
      apply hy1
      calc y = y ^ 2 * y⁻¹ := by group
        _ = y * y⁻¹ := by rw [hσy]
        _ = 1 := by group
  ·
    have hz1 : σ y ≠ 1 := fun h => hzy (h ▸ one_mem _)
    have hzo : orderOf (σ y) = 3 := orderOf_eq_prime hz3 hz1
    have hcard : Nat.card (Subgroup.zpowers y ⊔ Subgroup.zpowers (σ y) : Subgroup Y) = 9 := by
      rw [Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hzo hzy
        (by rintro _ ⟨k, rfl⟩; exact (Commute.zpow_left hyz k).eq), Nat.card_zpowers, hyo]
    have hle : Subgroup.zpowers y ⊔ Subgroup.zpowers (σ y) ≤ S :=
      sup_le (Subgroup.zpowers_le.mpr hy) (Subgroup.zpowers_le.mpr hzS)
    have hSeq : Subgroup.zpowers y ⊔ Subgroup.zpowers (σ y) = S :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hS9])
    have hwS : σ (σ y) ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers (σ y) := by
      rw [hSeq]; exact hσS _ hzS
    obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup hyz hwS
    obtain ⟨a, ha⟩ := exists_pow_eq_zpow_of_pow_three hy3 i
    obtain ⟨b, hb⟩ := exists_pow_eq_zpow_of_pow_three hz3 j
    rw [ha, hb, pow_eq_pow_mod_three hy3 a, pow_eq_pow_mod_three hz3 b] at hij
    have hcomm : ∀ m n : ℕ, Commute (y ^ m) (σ y ^ n) := fun m n => (Commute.pow_pow hyz m n)
    have key : ∀ a' b' : ℕ, a' < 3 → b' < 3 → σ (σ y) = y ^ a' * σ y ^ b' →
        y * σ y * σ (σ y) = 1 := by
      intro a' b' ha3 hb3 hij
      have h3 : y = y ^ (a' * b') * σ y ^ (a' + b' * b') := by
        have e1 : σ (σ (σ y)) = σ y ^ a' * (y ^ a' * σ y ^ b') ^ b' := by
          rw [hij, map_mul, map_pow, map_pow, hij]
        rw [hσy, (hcomm a' b').mul_pow, ← pow_mul, ← pow_mul] at e1
        refine e1.trans ?_
        calc σ y ^ a' * (y ^ (a' * b') * σ y ^ (b' * b'))
            = (σ y ^ a' * y ^ (a' * b')) * σ y ^ (b' * b') := by rw [mul_assoc]
          _ = (y ^ (a' * b') * σ y ^ a') * σ y ^ (b' * b') := by rw [(hcomm _ _).symm.eq]
          _ = y ^ (a' * b') * σ y ^ (a' + b' * b') := by rw [mul_assoc, ← pow_add]
      have h4 : y ^ 1 * σ y ^ 0 = y ^ ((a' * b') % 3) * σ y ^ ((a' + b' * b') % 3) := by
        rw [pow_one, pow_zero, mul_one, ← pow_eq_pow_mod_three hy3, ← pow_eq_pow_mod_three hz3]
        exact h3
      obtain ⟨h5, h6⟩ := eq_of_pow_mul_pow_eq hyo hz3 hzy (by norm_num) (by norm_num)
        (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h4
      have hab : a' = 2 ∧ b' = 2 := by
        clear h3 h4 hij
        interval_cases a' <;> interval_cases b' <;> omega
      rw [hij, hab.1, hab.2]
      have hzy2 : σ y * y ^ 2 = y ^ 2 * σ y := by
        have := (hcomm 2 1).eq
        rw [pow_one] at this
        exact this.symm
      calc y * σ y * (y ^ 2 * σ y ^ 2) = y * (σ y * y ^ 2) * σ y ^ 2 := by simp only [mul_assoc]
        _ = y * (y ^ 2 * σ y) * σ y ^ 2 := by rw [hzy2]
        _ = (y * y ^ 2) * (σ y * σ y ^ 2) := by simp only [mul_assoc]
        _ = 1 := by rw [← pow_succ', ← pow_succ', hy3, hz3, one_mul]
    exact key _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) hij

end Nine

section Complement

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_conj_sylow_of_sup_eq_top {S : Subgroup Y} [S.Normal] (Q : Sylow 2 Y)
    (hSQ : S ⊔ (Q : Subgroup Y) = ⊤) (α : MulAut Y) :
    ∃ s ∈ S, ∀ u ∈ (Q : Subgroup Y), s⁻¹ * α u * s ∈ (Q : Subgroup Y) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q (α • Q)
  have hg' : g ∈ ((S ⊔ (Q : Subgroup Y) : Subgroup Y) : Set Y) := by
    rw [hSQ]
    exact Subgroup.mem_top g
  rw [Subgroup.normal_mul, Set.mem_mul] at hg'
  obtain ⟨s, hs, t, ht, rfl⟩ := hg'
  have htQ : t • Q = Q := Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer ht)
  have hsQ : s • Q = α • Q := by rw [← hg, mul_smul, htQ]
  refine ⟨s, hs, fun u hu => ?_⟩
  have h1 : α u ∈ ((α • Q : Sylow 2 Y) : Subgroup Y) := by
    rw [Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨u, hu, rfl⟩
  rw [← hsQ, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨u', hu', hu'e⟩ := h1
  rw [MulAut.smul_def, MulAut.conj_apply] at hu'e
  rw [← hu'e]
  simpa [mul_assoc] using hu'

end Complement

section Two

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)

theorem u32_structure {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi X p e) (hq2 : p ^ e = 2) (S : Sylow 3 X) :
    Nat.card X = 72 ∧ Nat.card (S : Subgroup X) = 9 ∧ (∀ s ∈ (S : Subgroup X), s ^ 3 = 1) ∧
      (S : Subgroup X).Normal ∧
      ∀ x ∈ (S : Subgroup X), x ≠ 1 → ∀ t : X, t * x = x * t → t ∈ (S : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h91 : p ^ e % 9 ≠ 1 := by rw [hq2]; norm_num
  have h98 : p ^ e % 9 ≠ 8 := by rw [hq2]; norm_num
  obtain ⟨hS9, hS3⟩ := Sec19.Step1915WProof.ks1917Lie3Sylow X p e he hiso h91 h98 S
  have hSab : ∀ a ∈ (S : Subgroup X), ∀ b ∈ (S : Subgroup X), a * b = b * a := by
    intro a ha b hb
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := (S : Subgroup X))
      (by rw [hS9]; norm_num)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h
  have hX72 : Nat.card X = 72 := by
    obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
    have hc := Sec13.card_projImage_slPi_mul_three hK hq
    rw [← Nat.card_congr φ.toEquiv, hq2] at hc
    cases π
    · norm_num at hc
      omega
    · exfalso
      change p ^ e % 3 = 1 at hq
      rw [hq2] at hq
      norm_num at hq
  have htr := Sec19.Item19ResProof.transitive_sylow he hiso h91 h98 S
  set N := Subgroup.normalizer ((S : Subgroup X) : Set X) with hN
  let _ : MulAction N X := MulAction.compHom X ((MulAut.conj : X →* MulAut X).comp N.subtype)
  have hsmul : ∀ (n : N) (y : X), n • y = (n : X) * y * (n : X)⁻¹ := fun _ _ => rfl
  have hSN : (S : Subgroup X) ≤ N := Subgroup.le_normalizer
  have hSsub9 : Nat.card ((S : Subgroup X).subgroupOf N) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv, hS9]
  have hNle : Nat.card N ≤ 72 := by
    have := Subgroup.card_le_of_le (le_top : N ≤ ⊤)
    rwa [Subgroup.card_top, hX72] at this
  have hcard8 : (((S : Subgroup X) : Set X) \ {1}).ncard = 8 := by
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem (S : Subgroup X)), ← Nat.card_coe_set_eq]
    change Nat.card (S : Subgroup X) - 1 = 8
    rw [hS9]
  have hloc : ∀ x ∈ (S : Subgroup X), x ≠ 1 →
      Nat.card N = 72 ∧ (S : Subgroup X).subgroupOf N = MulAction.stabilizer N x := by
    intro x hxS hx1
    have horb : ((S : Subgroup X) : Set X) \ {1} ⊆ MulAction.orbit N x := by
      rintro y ⟨hyS, hy1⟩
      obtain ⟨n, hn, hny⟩ := htr x hxS hx1 y hyS hy1
      refine ⟨⟨n, hn⟩, ?_⟩
      change (⟨n, hn⟩ : N) • x = y
      rw [hsmul]
      exact hny
    have horb8 : 8 ≤ (MulAction.orbit N x).ncard :=
      hcard8 ▸ Set.ncard_le_ncard horb (Set.toFinite _)
    have hidx := MulAction.index_stabilizer N x
    have hSstab : (S : Subgroup X).subgroupOf N ≤ MulAction.stabilizer N x := by
      intro n hn
      rw [MulAction.mem_stabilizer_iff, hsmul, hSab _ (Subgroup.mem_subgroupOf.mp hn) x hxS]
      group
    have hstab9 : 9 ≤ Nat.card (MulAction.stabilizer N x) :=
      hSsub9 ▸ Subgroup.card_le_of_le hSstab
    have hNcard := Subgroup.card_mul_index (MulAction.stabilizer N x)
    have hst : Nat.card (MulAction.stabilizer N x) = 9 := by
      rw [hidx] at hNcard
      nlinarith
    have hN72 : Nat.card N = 72 := by
      rw [hidx] at hNcard
      nlinarith
    exact ⟨hN72, Subgroup.eq_of_le_of_card_ge hSstab (by rw [hst, hSsub9])⟩
  obtain ⟨x₀, hx₀S, hx₀1⟩ : ∃ x ∈ (S : Subgroup X), x ≠ 1 := by
    by_contra h
    push Not at h
    have : (S : Subgroup X) = ⊥ := eq_bot_iff.mpr fun y hy => Subgroup.mem_bot.mpr (h y hy)
    rw [this, Subgroup.card_bot] at hS9
    omega
  have hNtop : N = ⊤ := Subgroup.eq_top_of_card_eq N (by rw [(hloc x₀ hx₀S hx₀1).1, hX72])
  refine ⟨hX72, hS9, hS3, Subgroup.normalizer_eq_top_iff.mp hNtop, ?_⟩
  intro x hxS hx1 t ht
  have htN : t ∈ N := hNtop ▸ Subgroup.mem_top t
  have hmem : (⟨t, htN⟩ : N) ∈ MulAction.stabilizer N x := by
    rw [MulAction.mem_stabilizer_iff, hsmul]
    change t * x * t⁻¹ = x
    rw [ht]
    group
  rw [← (hloc x hxS hx1).2] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

end Two

theorem pow_three_eq_one_of_eq_two {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) (hq2 : p ^ e = 2) (σ : MulAut X) (k : ℕ)
    (hσ : σ ^ 3 ^ k = 1) : σ ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 X) := inferInstance
  obtain ⟨hX72, hS9, hS3, hSn, hC⟩ := u32_structure he hiso hq2 S
  have hSab : ∀ a ∈ (S : Subgroup X), ∀ b ∈ (S : Subgroup X), a * b = b * a := by
    intro a ha b hb
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := (S : Subgroup X))
      (by rw [hS9]; norm_num)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h
  obtain ⟨x₀, hx₀S, hx₀1⟩ : ∃ x ∈ (S : Subgroup X), x ≠ 1 := by
    by_contra h
    push Not at h
    have : (S : Subgroup X) = ⊥ := eq_bot_iff.mpr fun y hy => Subgroup.mem_bot.mpr (h y hy)
    rw [this, Subgroup.card_bot] at hS9
    omega
  obtain ⟨Q⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hQ8 : Nat.card (Q : Subgroup X) = 8 := by
    rw [Sylow.card_eq_multiplicity, hX72, Sec19.Item19ResProof.factorization_seventyTwo_two]
    norm_num
  have hSQ : (S : Subgroup X) ⊔ (Q : Subgroup X) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 : 9 ∣ Nat.card ((S : Subgroup X) ⊔ (Q : Subgroup X) : Subgroup X) :=
      hS9 ▸ Subgroup.card_dvd_of_le le_sup_left
    have h2 : 8 ∣ Nat.card ((S : Subgroup X) ⊔ (Q : Subgroup X) : Subgroup X) :=
      hQ8 ▸ Subgroup.card_dvd_of_le le_sup_right
    have h3 : 72 ∣ Nat.card ((S : Subgroup X) ⊔ (Q : Subgroup X) : Subgroup X) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
    have h4 : Nat.card ((S : Subgroup X) ⊔ (Q : Subgroup X) : Subgroup X) ≤ 72 :=
      hX72 ▸ (Subgroup.card_le_of_le le_top).trans (by rw [Subgroup.card_top])
    have h5 := Nat.le_of_dvd (Nat.card_pos) h3
    omega
  have hSQbot : ∀ t ∈ (S : Subgroup X), t ∈ (Q : Subgroup X) → t = 1 := by
    intro t htS htQ
    have h9 : orderOf t ∣ 9 := by
      have := orderOf_dvd_natCard (⟨t, htS⟩ : (S : Subgroup X))
      rwa [Subgroup.orderOf_mk, hS9] at this
    have h8 : orderOf t ∣ 8 := by
      have := orderOf_dvd_natCard (⟨t, htQ⟩ : (Q : Subgroup X))
      rwa [Subgroup.orderOf_mk, hQ8] at this
    have h1 : orderOf t ∣ 1 := (Nat.dvd_gcd h9 h8).trans (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hCQ : ∀ t ∈ (Q : Subgroup X), (∀ s ∈ (S : Subgroup X), t * s = s * t) → t = 1 :=
    fun t htQ hts => hSQbot t (hC x₀ hx₀S hx₀1 t (hts x₀ hx₀S)) htQ
  have hCS : ∀ s ∈ (S : Subgroup X), (∀ q ∈ (Q : Subgroup X), s * q = q * s) → s = 1 := by
    intro s hs hsq
    by_contra hs1
    have hle : (S : Subgroup X) ⊔ (Q : Subgroup X) ≤ Subgroup.centralizer {s} := by
      refine sup_le (fun a ha => ?_) (fun q hq => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hSab s hs a ha).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hsq q hq).symm
    rw [hSQ] at hle
    have hall : ∀ t : X, t ∈ (S : Subgroup X) := fun t =>
      hC s hs hs1 t (Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top t)))
    have : (⊤ : Subgroup X) ≤ S := fun t _ => hall t
    have h := Subgroup.card_le_of_le this
    rw [Subgroup.card_top, hX72, hS9] at h
    omega
  have hσS : ∀ s ∈ (S : Subgroup X), σ s ∈ (S : Subgroup X) := by
    intro s hs
    have hmap : IsPGroup 3 ((S : Subgroup X).map σ.toMonoidHom) := S.isPGroup'.map _
    obtain ⟨P, hP⟩ := hmap.exists_le_sylow
    have hSP : (S : Subgroup X) ≤ P := IsPGroup.le_sylow_of_normal S.isPGroup' P
    have hPS : (P : Subgroup X) = S := (Subgroup.eq_of_le_of_card_ge hSP (by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity])).symm
    exact hPS ▸ hP ⟨s, hs, rfl⟩
  have hσ3S := pow_three_apply_of_card_nine hS9 σ hσS hσ
  obtain ⟨s, hs, hse⟩ := Sec19.Item19ResProof.eq_conj_of_fix_normal hSab Q hSQ hCQ (σ ^ 3) hσ3S
  obtain ⟨x, hx, hxQ⟩ := exists_conj_sylow_of_sup_eq_top Q hSQ σ
  set β : MulAut X := (MulAut.conj x)⁻¹ * σ with hβ
  have hβapp : ∀ y, β y = x⁻¹ * σ y * x := fun y => by
    rw [hβ, MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv]
  have hβQ : ∀ u ∈ (Q : Subgroup X), β u ∈ (Q : Subgroup X) := fun u hu => by
    rw [hβapp]; exact hxQ u hu
  have hσβ : σ = MulAut.conj x * β := by rw [hβ]; group
  have hσx : σ x ∈ (S : Subgroup X) := hσS x hx
  have hσσx : σ (σ x) ∈ (S : Subgroup X) := hσS _ hσx
  have hβx : β x = σ x := by
    rw [hβapp, mul_assoc, ← hSab x hx _ hσx]
    group
  have hβσx : β (σ x) = σ (σ x) := by
    rw [hβapp, mul_assoc, ← hSab x hx _ hσσx]
    group
  have hN := norm_eq_one_of_card_nine hS9 hS3 hSab σ hσS hσ3S x hx
  have hσ3β : σ ^ 3 = β ^ 3 := by
    have h1 : β * MulAut.conj x = MulAut.conj (σ x) * β := by
      rw [← hβx]
      have := KFacts.mul_mulAutConj_mul_inv β x
      calc β * MulAut.conj x = β * MulAut.conj x * β⁻¹ * β := by group
        _ = MulAut.conj (β x) * β := by rw [this]
    have h2 : β * MulAut.conj (σ x) = MulAut.conj (σ (σ x)) * β := by
      rw [← hβσx]
      have := KFacts.mul_mulAutConj_mul_inv β (σ x)
      calc β * MulAut.conj (σ x) = β * MulAut.conj (σ x) * β⁻¹ * β := by group
        _ = MulAut.conj (β (σ x)) * β := by rw [this]
    calc σ ^ 3 = MulAut.conj x * β * (MulAut.conj x * β) * (MulAut.conj x * β) := by
          rw [hσβ, pow_three]; simp only [mul_assoc]
      _ = MulAut.conj x * (β * MulAut.conj x) * β * (MulAut.conj x * β) := by group
      _ = MulAut.conj x * (MulAut.conj (σ x) * β) * β * (MulAut.conj x * β) := by rw [h1]
      _ = MulAut.conj x * MulAut.conj (σ x) * (β * (β * MulAut.conj x)) * β := by group
      _ = MulAut.conj x * MulAut.conj (σ x) * (β * (MulAut.conj (σ x) * β)) * β := by rw [h1]
      _ = MulAut.conj x * MulAut.conj (σ x) * ((β * MulAut.conj (σ x)) * β) * β := by group
      _ = MulAut.conj x * MulAut.conj (σ x) * ((MulAut.conj (σ (σ x)) * β) * β) * β := by
          rw [h2]
      _ = MulAut.conj (x * σ x * σ (σ x)) * β ^ 3 := by
          rw [map_mul, map_mul, pow_three]; group
      _ = β ^ 3 := by rw [hN, map_one, one_mul]
  have hsQ : ∀ q ∈ (Q : Subgroup X), s * q = q * s := by
    intro q hq
    have h1 : s * q * s⁻¹ ∈ (Q : Subgroup X) := by
      have : (σ ^ 3) q = s * q * s⁻¹ := by rw [hse, MulAut.conj_apply]
      rw [← this, hσ3β, pow_three, MulAut.mul_apply, MulAut.mul_apply]
      exact hβQ _ (hβQ _ (hβQ _ hq))
    have h2 : s * q * s⁻¹ * q⁻¹ ∈ (S : Subgroup X) := by
      have : s * q * s⁻¹ * q⁻¹ = s * (q * s⁻¹ * q⁻¹) := by group
      rw [this]
      exact mul_mem hs (hSn.conj_mem _ (inv_mem hs) q)
    have h3 := hSQbot _ h2 (mul_mem h1 (inv_mem hq))
    calc s * q = s * q * s⁻¹ * q⁻¹ * q * s := by group
      _ = q * s := by rw [h3, one_mul]
  rw [hse, hCS s hs hsQ, map_one]

end CFSG.RankThree.PartTwo.Sec17.Proof17Res2

namespace CFSG.RankThree.PartTwo.Sec17

theorem ks1721AutThreeU32 : KS1721AutThreeU32 :=
  fun _ _ _ _ _ _ he hiso hq2 σ k hσ => Proof17Res2.pow_three_eq_one_of_eq_two he hiso hq2 σ k hσ

theorem ks1721AutThreeL3 : KS1721AutThreeL3 := ks1721AutThreeL3_of_u32 ks1721AutThreeU32

end CFSG.RankThree.PartTwo.Sec17
