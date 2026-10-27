module

public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Final1128ProofCore
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

namespace Item1117Res6Proof

section Group

variable {G : Type} [Group G]

theorem mul_pow_three_of_central {y z k : G} (hzy : z * y = k * y * z) (hky : y * k = k * y)
    (hkz : z * k = k * z) (hk3 : k ^ 3 = 1) : (y * z) ^ 3 = y ^ 3 * z ^ 3 := by
  have h1 : ∀ t, z * (y * t) = k * (y * (z * t)) := fun t => by
    rw [← mul_assoc, hzy]; simp only [mul_assoc]
  have h2 : ∀ t, y * (k * t) = k * (y * t) := fun t => by rw [← mul_assoc, hky, mul_assoc]
  have h3 : ∀ t, z * (k * t) = k * (z * t) := fun t => by rw [← mul_assoc, hkz, mul_assoc]
  have h4 : ∀ t, k * (k * (k * t)) = t := fun t => by
    rw [← mul_assoc, ← mul_assoc, ← pow_two, ← pow_succ, hk3, one_mul]
  simp only [pow_three, mul_assoc, h1, h2, h3, h4]

variable {P : Subgroup G} {d : G}

theorem commute_of_mem_zpowers (hd : ∀ w ∈ P, d * w = w * d) {z : G}
    (hz : z ∈ Subgroup.zpowers d) {w : G} (hw : w ∈ P) : z * w = w * z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact (Commute.zpow_left (hd w hw) n).eq

theorem commute_zpowers {z z' : G} (hz : z ∈ Subgroup.zpowers d)
    (hz' : z' ∈ Subgroup.zpowers d) : z * z' = z' * z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
  exact (Commute.zpow_zpow_self d n m).eq

theorem pow_three_of_mem_zpowers (hd3 : d ^ 3 = 1) {z : G} (hz : z ∈ Subgroup.zpowers d) :
    z ^ 3 = 1 := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]

variable (hP : ∀ y ∈ P, ∀ w ∈ P, ⁅y, w⁆ ∈ Subgroup.zpowers d) (hd : ∀ w ∈ P, d * w = w * d)
include hP hd

theorem commutator_mul_right_eq {v w₁ w₂ : G} (hv : v ∈ P) (hw₁ : w₁ ∈ P) (hw₂ : w₂ ∈ P) :
    ⁅v, w₁ * w₂⁆ = ⁅v, w₁⁆ * ⁅v, w₂⁆ := by
  have hc := commute_of_mem_zpowers hd (hP v hv w₂ hw₂) hw₁
  rw [Final1128Proof.commutatorElement_mul_right', ← hc, mul_inv_cancel_right]

theorem commutator_mul_left_eq {y₁ y₂ w : G} (hy₁ : y₁ ∈ P) (hy₂ : y₂ ∈ P) (hw : w ∈ P) :
    ⁅y₁ * y₂, w⁆ = ⁅y₁, w⁆ * ⁅y₂, w⁆ := by
  have hc := commute_of_mem_zpowers hd (hP y₂ hy₂ w hw) hy₁
  rw [Final1128Proof.commutatorElement_mul_left', ← hc, mul_inv_cancel_right]
  exact commute_zpowers (hP y₂ hy₂ w hw) (hP y₁ hy₁ w hw)

theorem commutator_inv_right_eq {v w : G} (hv : v ∈ P) (hw : w ∈ P) : ⁅v, w⁻¹⁆ = ⁅v, w⁆⁻¹ := by
  have h1 := commutator_mul_right_eq hP hd hv hw (P.inv_mem hw)
  rw [mul_inv_cancel, commutatorElement_one_right] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem commutator_inv_left_eq {v w : G} (hv : v ∈ P) (hw : w ∈ P) : ⁅v⁻¹, w⁆ = ⁅v, w⁆⁻¹ := by
  have h1 := commutator_mul_left_eq hP hd (P.inv_mem hv) hv hw
  rw [inv_mul_cancel, commutatorElement_one_left] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem mul_pow_three_eq (hd3 : d ^ 3 = 1) {y z : G} (hy : y ∈ P) (hz : z ∈ P) :
    (y * z) ^ 3 = y ^ 3 * z ^ 3 := by
  have hk := hP z hz y hy
  refine mul_pow_three_of_central (k := ⁅z, y⁆) ?_ ?_ ?_ (pow_three_of_mem_zpowers hd3 hk)
  · rw [commutatorElement_def]; group
  · exact (commute_of_mem_zpowers hd hk hy).symm
  · exact (commute_of_mem_zpowers hd hk hz).symm

theorem pow_three_commute (hd3 : d ^ 3 = 1) {y w : G} (hy : y ∈ P) (hw : w ∈ P) :
    y ^ 3 * w = w * y ^ 3 := by
  have hk := hP w hw y hy
  have hcomm : Commute ⁅w, y⁆ y := commute_of_mem_zpowers hd hk hy
  have h1 : w * y ^ 3 * w⁻¹ = y ^ 3 := by
    rw [← conj_pow, Final1128Proof.conj_eq_commutatorElement_mul, hcomm.mul_pow,
      pow_three_of_mem_zpowers hd3 hk, one_mul]
  calc y ^ 3 * w = (w * y ^ 3 * w⁻¹) * w := by rw [h1]
    _ = w * y ^ 3 := by group

theorem mul_pow_of_three_dvd (hd3 : d ^ 3 = 1) {n : ℕ} (hn : 3 ∣ n) {y z : G} (hy : y ∈ P)
    (hz : z ∈ P) : (y * z) ^ n = y ^ n * z ^ n := by
  obtain ⟨m, rfl⟩ := hn
  have hc : Commute (y ^ 3) (z ^ 3) := pow_three_commute hP hd hd3 hy (P.pow_mem hz 3)
  rw [pow_mul, mul_pow_three_eq hP hd hd3 hy hz, hc.mul_pow, ← pow_mul, ← pow_mul]

omit hP hd in
theorem commutator_mem_of_eq (hPP : ⁅P, P⁆ = Subgroup.zpowers d) :
    ∀ y ∈ P, ∀ w ∈ P, ⁅y, w⁆ ∈ Subgroup.zpowers d := fun _ hy _ hw =>
  hPP ▸ Subgroup.commutator_mem_commutator hy hw

end Group

section Data


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem mem_R_of_commute_c (h : Sec11Data G A c L a R Y d x s r g) {y : G}
    (hy : y ∈ sec11P R g) (hyc : y * c = c * y) : y ∈ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : R ≤ sec11P R g ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    le_inf (Item1119Proof.R_le_P R g) h.isSylowOf.le
  have heq := h.isSylowOf.eq_of_le hle inf_le_right (h.isPGroup_sec11P.to_le inf_le_left)
  have hyH : y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
    rw [hyc, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c
  rw [← heq]
  exact ⟨hy, hyH⟩

theorem mem_zpowers_x_cube_of_central (h45 : Sec4.Item4_5) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (hgx3 : g * x ^ 3 * g⁻¹ = x ^ 3) {y : G} (hy : y ∈ sec11P R g)
    (hcen : ∀ w ∈ sec11P R g, y * w = w * y) : y ∈ Subgroup.zpowers (x ^ 3) := by
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1116Proof.mem_R h).2.1
  have hAP : A ≤ sec11P R g := (le_R_of_hyp91 h.toHyp91).trans (Item1119Proof.R_le_P R g)
  have hgP : g ∈ sec11P R g := Item1119Proof.g_mem_P R g
  have hyR : y ∈ R := mem_R_of_commute_c h hy (hcen c (hAP h.mem_A))
  obtain ⟨m, u, hu, rfl⟩ := Item1117Proof.exists_eq_zpow_mul h hsc hrs hyR
  have hxa : x ^ m * a = a * x ^ m := by
    have h1 := hcen a (hAP h.a_mem)
    have hua : u * a = a * u := Item1117Proof.commute_of_mem_A h hu h.a_mem
    have h2 : x ^ m * a * u = a * x ^ m * u := by
      calc x ^ m * a * u = x ^ m * (u * a) := by rw [hua]; group
        _ = x ^ m * u * a := by group
        _ = a * (x ^ m * u) := h1
        _ = a * x ^ m * u := by group
    exact mul_right_cancel h2
  obtain ⟨z₀, hz₀, hax⟩ := Item1117Proof.exists_conj_x_of_mem_A h h.a_mem
  have hz₀1 : z₀ ≠ 1 := by
    intro h1
    apply h.toSec11Std.mul_ne_mul h45 h.inf_eq h.closure_eq h.inf_L_eq
    rw [h1, mul_one] at hax
    calc a * x = (a * x * a⁻¹) * a := by group
      _ = x * a := by rw [hax]
  have hz₀3 : orderOf z₀ = 3 := by
    have h1 := orderOf_dvd_of_mem_zpowers hz₀
    rw [Item1117Proof.orderOf_d h] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hz₀1
    · exact h1
  have hxz := Item1117Proof.commute_x_of_mem_zpowers_d h hz₀
  have hm : ((3 : ℕ) : ℤ) ∣ m := by
    have h1 : a * x ^ m * a⁻¹ = x ^ m * z₀ ^ m := by rw [← conj_zpow, hax, hxz.mul_zpow]
    have h2 : a * x ^ m * a⁻¹ = x ^ m := by rw [← hxa, mul_inv_cancel_right]
    have h3 : z₀ ^ m = 1 := by
      have h4 : x ^ m * z₀ ^ m = x ^ m * 1 := by rw [← h1, h2, mul_one]
      exact mul_left_cancel h4
    rw [← hz₀3]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h3
  obtain ⟨m', rfl⟩ := hm
  have hxm : x ^ ((3 : ℕ) * m' : ℤ) = (x ^ 3) ^ m' := by
    rw [zpow_mul, zpow_natCast]
  have hux : x * u = u * x := by
    have h1 := hcen x hxP
    have hxx : x ^ ((3 : ℕ) * m' : ℤ) * x = x * x ^ ((3 : ℕ) * m' : ℤ) :=
      (Commute.zpow_left (Commute.refl x) _).eq
    have h2 : x ^ ((3 : ℕ) * m' : ℤ) * (u * x) = x ^ ((3 : ℕ) * m' : ℤ) * (x * u) := by
      calc x ^ ((3 : ℕ) * m' : ℤ) * (u * x) = x ^ ((3 : ℕ) * m' : ℤ) * u * x := by group
        _ = x * (x ^ ((3 : ℕ) * m' : ℤ) * u) := h1
        _ = x ^ ((3 : ℕ) * m' : ℤ) * (x * u) := by rw [← mul_assoc, ← hxx, mul_assoc]
    exact (mul_left_cancel h2).symm
  have hucd : u ∈ Subgroup.closure ({c, d} : Set G) := by
    by_contra hucd
    exact Item1117StepsProof.not_commute_x_e h45 h hu hucd hux
  have hgu : g * u * g⁻¹ = u := by
    have h1 := hcen g hgP
    have hgxm : g * x ^ ((3 : ℕ) * m' : ℤ) * g⁻¹ = x ^ ((3 : ℕ) * m' : ℤ) := by
      rw [hxm, ← conj_zpow, hgx3]
    have h2 : x ^ ((3 : ℕ) * m' : ℤ) * (g * u * g⁻¹) = x ^ ((3 : ℕ) * m' : ℤ) * u := by
      calc x ^ ((3 : ℕ) * m' : ℤ) * (g * u * g⁻¹)
          = (g * x ^ ((3 : ℕ) * m' : ℤ) * g⁻¹) * (g * u * g⁻¹) := by rw [hgxm]
        _ = g * (x ^ ((3 : ℕ) * m' : ℤ) * u) * g⁻¹ := by group
        _ = x ^ ((3 : ℕ) * m' : ℤ) * u := by rw [← h1, mul_inv_cancel_right]
    exact mul_left_cancel h2
  have hdA := Item1117Proof.d_mem_A h
  have hcd : c * d = d * c := Item1117Proof.commute_of_mem_A h h.mem_A hdA
  obtain ⟨i, j, hi, -, rfl⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hcd
    (Item1117Proof.pow_three_of_mem_A h h.mem_A) (Item1117Proof.pow_three_of_mem_A h hdA) hucd
  set w₀ := g * c * g⁻¹ * c⁻¹ with hw₀
  have hw₀d : w₀ ∈ Subgroup.zpowers d := Item1117Proof.conj_g_c_mem h117 h
  have hw₀A : w₀ ∈ A := Subgroup.zpowers_le.mpr hdA hw₀d
  have hgc : g * c * g⁻¹ = w₀ * c := by rw [hw₀]; group
  have hw₀c : Commute w₀ c := Item1117Proof.commute_of_mem_A h hw₀A h.mem_A
  have hconj : g * (c ^ i * d ^ j) * g⁻¹ = w₀ ^ i * (c ^ i * d ^ j) := by
    have e : g * (c ^ i * d ^ j) * g⁻¹ = (g * c * g⁻¹) ^ i * (g * d * g⁻¹) ^ j := by
      rw [conj_pow, conj_pow]; group
    rw [e, hgc, Item1117Proof.conj_g_d h117 h, hw₀c.mul_pow, mul_assoc]
  have hwi : w₀ ^ i = 1 := by
    have h1 : w₀ ^ i * (c ^ i * d ^ j) = 1 * (c ^ i * d ^ j) := by rw [← hconj, hgu, one_mul]
    exact mul_right_cancel h1
  have hw₀1 : w₀ ≠ 1 := by
    intro h1
    apply h.g_not_mem
    refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
    rw [hgc, h1, one_mul]
    exact Subgroup.mem_zpowers c
  have hw₀3 : orderOf w₀ = 3 := by
    have h1 := orderOf_dvd_of_mem_zpowers hw₀d
    rw [Item1117Proof.orderOf_d h] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hw₀1
    · exact h1
  have hi0 : i = 0 := by
    have := orderOf_dvd_of_pow_eq_one hwi
    rw [hw₀3] at this
    omega
  subst hi0
  rw [pow_zero, one_mul, hxm]
  refine Subgroup.mul_mem _ (Subgroup.zpow_mem_zpowers _ _) ?_
  exact Subgroup.pow_mem _ (Item1117Proof.d_mem_zpowers_x_cube h) j

theorem mem_zpowers_d_of_central (h45 : Sec4.Item4_5) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (hgx3 : g * x ^ 3 * g⁻¹ = x ^ 3) {y : G} (hy : y ∈ sec11P R g)
    (hcen : ∀ w ∈ sec11P R g, y * w = w * y) (hy3 : y ^ 3 = 1) : y ∈ Subgroup.zpowers d := by
  have h1 := mem_zpowers_x_cube_of_central h45 h117 h hsc hrs hgx3 hy hcen
  have h2 : y ∈ Subgroup.zpowers x :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 3) h1
  exact Item1117Proof.mem_zpowers_of_pow_three_eq_one (Item1117Proof.d_mem_zpowers_x h)
    (Item1117Proof.orderOf_d h) h2 hy3

theorem three_dvd_orderOf_div (h : Sec11Data G A c L a R Y d x s r g) :
    3 ∣ orderOf x / 3 := by
  obtain ⟨t, ht⟩ := Item1117Proof.nine_dvd_orderOf_x h
  rw [ht]
  exact ⟨t, by omega⟩

theorem pow_div_ne_one (h : Sec11Data G A c L a R Y d x s r g) : x ^ (orderOf x / 3) ≠ 1 := by
  obtain ⟨t, ht⟩ := Item1117Proof.nine_dvd_orderOf_x h
  have hpos : 0 < orderOf x := orderOf_pos_iff.mpr (isOfFinOrder_of_finite x)
  refine pow_ne_one_of_lt_orderOf ?_ ?_ <;> omega

theorem pow_div_mem (h : Sec11Data G A c L a R Y d x s r g) :
    x ^ (orderOf x / 3) ∈ Subgroup.zpowers d := by
  obtain ⟨t, ht⟩ := Item1117Proof.nine_dvd_orderOf_x h
  refine Item1117Proof.mem_zpowers_of_pow_three_eq_one (Item1117Proof.d_mem_zpowers_x h)
    (Item1117Proof.orderOf_d h) (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _) ?_
  rw [← pow_mul, show orderOf x / 3 * 3 = orderOf x by omega, pow_orderOf_eq_one]

variable (h45 : Sec4.Item4_5) (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g)
  (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
  (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
  (hgx3 : g * x ^ 3 * g⁻¹ = x ^ 3) (hPP : ⁅sec11P R g, sec11P R g⁆ = Subgroup.zpowers d)

include h117 h hsc hrs in
theorem d_central : ∀ w ∈ sec11P R g, d * w = w * d := fun _ hw =>
  (Subgroup.mem_centralizer_singleton_iff.mp
    (Item1117StepsProof.sec11P_le_centralizer_d h117 h hsc hrs hw)).symm

include h45 h117 h hsc hrs hgx3 hPP in
theorem pow_mem_zpowers_d {w : G} (hw : w ∈ sec11P R g) :
    w ^ (orderOf x / 3) ∈ Subgroup.zpowers d := by
  have hP := commutator_mem_of_eq hPP
  have hd := d_central h117 h hsc hrs
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h (Item1117Proof.d_mem_A h)
  have hw3 : w ^ 3 ∈ Subgroup.zpowers (x ^ 3) :=
    mem_zpowers_x_cube_of_central h45 h117 h hsc hrs hgx3 ((sec11P R g).pow_mem hw 3)
      fun w' hw' => pow_three_commute hP hd hd3 hw hw'
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hw3
  obtain ⟨t, ht⟩ := Item1117Proof.nine_dvd_orderOf_x h
  have hN : orderOf x / 3 = 3 * t := by omega
  have e : w ^ (orderOf x / 3) = (x ^ (orderOf x / 3)) ^ j := by
    rw [hN, pow_mul, ← hj, ← zpow_natCast ((x ^ 3) ^ j) t, ← zpow_mul, ← zpow_natCast x 3,
      ← zpow_mul, ← zpow_natCast x (3 * t), ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [e]
  exact Subgroup.zpow_mem _ (pow_div_mem h) j

include h45 h117 h hsc hrs hgx3 hPP in
theorem exists_canonical :
    ∃ v ∈ A, (∀ w ∈ sec11P R g, ⁅v, w⁆ = w ^ (orderOf x / 3)) ∧ x * v ≠ v * x := by
  have hP := commutator_mem_of_eq hPP
  have hd := d_central h117 h hsc hrs
  have hdA := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h hdA
  have hAP : A ≤ sec11P R g := (le_R_of_hyp91 h.toHyp91).trans (Item1119Proof.R_le_P R g)
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1116Proof.mem_R h).2.1
  have hgP : g ∈ sec11P R g := Item1119Proof.g_mem_P R g
  have h3N := three_dvd_orderOf_div h
  set N := orderOf x / 3 with hNdef
  have hθ₁ : ⁅a, x⁆ ∈ Subgroup.zpowers d := by
    rw [commutatorElement_def]; exact Item1117Proof.commutator_a_x_mem h
  have hθ₁1 : ⁅a, x⁆ ≠ 1 := fun h1 =>
    h.toSec11Std.mul_ne_mul h45 h.inf_eq h.closure_eq h.inf_L_eq
      (commutatorElement_eq_one_iff_mul_comm.mp h1)
  have hθ₂ : ⁅c, g⁆ ∈ Subgroup.zpowers d := by
    rw [← commutatorElement_inv, commutatorElement_def]
    exact Subgroup.inv_mem _ (Item1117Proof.conj_g_c_mem h117 h)
  have hθ₂1 : ⁅c, g⁆ ≠ 1 := by
    intro h1
    apply h.g_not_mem
    refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
    rw [(commutatorElement_eq_one_iff_mul_comm.mp h1).symm, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c
  obtain ⟨q, hq⟩ := Final1128Proof.exists_pow_eq_of_orderOf_eq_three (Item1117Proof.orderOf_d h)
    hθ₁ hθ₁1 (pow_div_mem h)
  obtain ⟨u, hu⟩ := Final1128Proof.exists_pow_eq_of_orderOf_eq_three (Item1117Proof.orderOf_d h)
    hθ₂ hθ₂1 (pow_mem_zpowers_d h45 h117 h hsc hrs hgx3 hPP hgP)
  have hvA : a ^ q * c ^ u ∈ A := A.mul_mem (A.pow_mem h.a_mem q) (A.pow_mem h.mem_A u)
  have hvP : a ^ q * c ^ u ∈ sec11P R g := hAP hvA
  have haqP : a ^ q ∈ sec11P R g := hAP (A.pow_mem h.a_mem q)
  have hcuP : c ^ u ∈ sec11P R g := hAP (A.pow_mem h.mem_A u)
  have hpowA : ∀ y ∈ A, y ^ N = 1 := fun y hy => by
    obtain ⟨t, ht⟩ := h3N
    rw [ht, pow_mul, Item1117Proof.pow_three_of_mem_A h hy, one_pow]
  have hcx : c * x = x * c := (Subgroup.mem_centralizer_singleton_iff.mp
    (Item1117Proof.R_le_centralizer_c h (Item1116Proof.mem_R h).2.1)).symm
  have hag : a * g = g * a := (Item1117Proof.commute_g_a h).symm
  have hgen : ∀ w ∈ ({a, x, c, g} : Set G), ⁅a ^ q * c ^ u, w⁆ = w ^ N := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · rw [hpowA _ h.a_mem, commutatorElement_eq_one_iff_mul_comm]
      exact Item1117Proof.commute_of_mem_A h hvA h.a_mem
    · rw [commutator_mul_left_eq hP hd haqP hcuP hxP,
        Final1128Proof.commutatorElement_pow_left_of_commute
          (commute_of_mem_zpowers hd hθ₁ (hAP h.a_mem)).symm,
        commutatorElement_eq_one_iff_mul_comm.mpr (Commute.pow_left hcx u).eq, mul_one, hq]
    · rw [hpowA _ h.mem_A, commutatorElement_eq_one_iff_mul_comm]
      exact Item1117Proof.commute_of_mem_A h hvA h.mem_A
    · rw [commutator_mul_left_eq hP hd haqP hcuP hgP,
        commutatorElement_eq_one_iff_mul_comm.mpr (Commute.pow_left hag q).eq, one_mul,
        Final1128Proof.commutatorElement_pow_left_of_commute
          (commute_of_mem_zpowers hd hθ₂ (hAP h.mem_A)).symm, hu]
  have hPcl := Item1117Proof.sec11P_eq_closure h hsc hrs
  have hall : ∀ w ∈ sec11P R g, ⁅a ^ q * c ^ u, w⁆ = w ^ N := by
    intro w hw
    rw [hPcl] at hw
    induction hw using Subgroup.closure_induction with
    | mem w hw => exact hgen w hw
    | one => rw [commutatorElement_one_right, one_pow]
    | mul w₁ w₂ hw₁ hw₂ ih₁ ih₂ =>
      rw [← hPcl] at hw₁ hw₂
      rw [commutator_mul_right_eq hP hd hvP hw₁ hw₂, ih₁, ih₂,
        mul_pow_of_three_dvd hP hd hd3 h3N hw₁ hw₂]
    | inv w hw ih =>
      rw [← hPcl] at hw
      rw [commutator_inv_right_eq hP hd hvP hw, ih, inv_pow]
  refine ⟨a ^ q * c ^ u, hvA, hall, fun hxv => ?_⟩
  apply pow_div_ne_one h
  rw [← hall x hxP, commutatorElement_eq_one_iff_mul_comm]
  exact hxv.symm

include h45 h117 h hsc hrs hgx3 hPP in
theorem conj_canonical_mem {v : G} (hvA : v ∈ A)
    (hcan : ∀ w ∈ sec11P R g, ⁅v, w⁆ = w ^ (orderOf x / 3)) {n : G}
    (hn : n ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G)) :
    v⁻¹ * (n * v * n⁻¹) ∈ Subgroup.zpowers d := by
  have hP := commutator_mem_of_eq hPP
  have hd := d_central h117 h hsc hrs
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h (Item1117Proof.d_mem_A h)
  have hAP : A ≤ sec11P R g := (le_R_of_hyp91 h.toHyp91).trans (Item1119Proof.R_le_P R g)
  have hvP := hAP hvA
  have hyP : n * v * n⁻¹ ∈ sec11P R g := (Subgroup.mem_normalizer_iff.mp hn v).mp hvP
  have hy : ∀ w ∈ sec11P R g, ⁅n * v * n⁻¹, w⁆ = ⁅v, w⁆ := by
    intro w hw
    have hw' : n⁻¹ * w * n ∈ sec11P R g := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) w).mp hw
      rwa [inv_inv] at this
    rw [hcan w hw]
    calc ⁅n * v * n⁻¹, w⁆ = n * ⁅v, n⁻¹ * w * n⁆ * n⁻¹ := by
          rw [Final1128Proof.conj_commutatorElement]; group
      _ = n * (n⁻¹ * w * n) ^ (orderOf x / 3) * n⁻¹ := by rw [hcan _ hw']
      _ = w ^ (orderOf x / 3) := by
          have e := conj_pow (a := n⁻¹) (b := w) (i := orderOf x / 3)
          rw [inv_inv] at e
          rw [e]; group
  have hzP : v⁻¹ * (n * v * n⁻¹) ∈ sec11P R g := (sec11P R g).mul_mem (inv_mem hvP) hyP
  refine mem_zpowers_d_of_central h45 h117 h hsc hrs hgx3 hzP (fun w hw => ?_) ?_
  · rw [← commutatorElement_eq_one_iff_mul_comm,
      commutator_mul_left_eq hP hd (inv_mem hvP) hyP hw, commutator_inv_left_eq hP hd hvP hw,
      hy w hw, inv_mul_cancel]
  · rw [mul_pow_three_eq hP hd hd3 (inv_mem hvP) hyP, inv_pow, conj_pow,
      Item1117Proof.pow_three_of_mem_A h hvA]
    group

include h hPP in
theorem isEmpty_wreath :
    ∀ (K : Subgroup (sec11P R g)) [K.Normal], IsEmpty (sec11P R g ⧸ K ≃* W33) := by
  intro K _
  refine ⟨fun φ => ?_⟩
  set π : sec11P R g →* W33 := φ.toMonoidHom.comp (QuotientGroup.mk' K) with hπ
  have hπs : Function.Surjective π := φ.surjective.comp (QuotientGroup.mk'_surjective K)
  set C : Subgroup (sec11P R g) :=
    ⁅(⊤ : Subgroup (sec11P R g)), (⊤ : Subgroup (sec11P R g))⁆ with hC
  have h1 : C.map π = ⁅(⊤ : Subgroup W33), (⊤ : Subgroup W33)⁆ := by
    rw [hC, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπs]
  have h2 : C.map (sec11P R g).subtype = ⁅sec11P R g, sec11P R g⁆ := by
    rw [hC, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h3 : Nat.card C = 3 := by
    rw [← Subgroup.card_map_of_injective (sec11P R g).subtype_injective, h2, hPP,
      Nat.card_zpowers, Item1117Proof.orderOf_d h]
  have h4 := Subgroup.card_map_dvd (H := C) π
  rw [h1, KFacts.card_commutator_wreath, h3] at h4
  norm_num at h4

include h45 h117 h hsc hrs hgx3 hPP in
theorem false_of_isSylowOf (hS : IsSylowOf 3 (sec11P R g) ⊤) : False := by
  obtain ⟨v, hvA, hcan, hxv⟩ := exists_canonical h45 h117 h hsc hrs hgx3 hPP
  have hAP : A ≤ sec11P R g := (le_R_of_hyp91 h.toHyp91).trans (Item1119Proof.R_le_P R g)
  have hY := rank3II_11_31 h hS (isEmpty_wreath h hPP)
  have hind : ¬ 3 ∣ (sec11P R g).relIndex
      (Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G)) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 := (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2
    intro h3
    apply h1
    rw [← Subgroup.relIndex_mul_relIndex (sec11P R g) _ ⊤ Subgroup.le_normalizer le_top]
    exact h3.mul_right _
  have hmem := Final1128Proof.mem_commutator_of_forall_conj h.isPGroup_sec11P hind hY (hAP hvA)
    (Item1117Proof.pow_three_of_mem_A h hvA) fun n hn => by
      rw [hPP]
      exact conj_canonical_mem h45 h117 h hsc hrs hgx3 hPP hvA hcan hn
  rw [hPP] at hmem
  exact hxv (Item1117Proof.commute_x_of_mem_zpowers_d h hmem).eq

include h45 h117 h hsc hrs hgx3 hPP in
theorem isSylowOf_top_of_canonical {v : G} (hvA : v ∈ A)
    (hcan : ∀ w ∈ sec11P R g, ⁅v, w⁆ = w ^ (orderOf x / 3)) (hxv : x * v ≠ v * x)
    {K : Subgroup G} (hK : Subgroup.centralizer {v} ≤ K)
    (hC : IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer {v}) K) :
    IsSylowOf 3 (sec11P R g) ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd := d_central h117 h hsc hrs
  have hdA := Item1117Proof.d_mem_A h
  have hd3o := Item1117Proof.orderOf_d h
  have hAP : A ≤ sec11P R g := (le_R_of_hyp91 h.toHyp91).trans (Item1119Proof.R_le_P R g)
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1116Proof.mem_R h).2.1
  set P := sec11P R g with hPdef
  set N := Subgroup.normalizer (P : Set G) with hNdef
  have hP3 : IsPGroup 3 P := h.isPGroup_sec11P
  have hPN : P ≤ N := Subgroup.le_normalizer
  obtain ⟨Q, hQ⟩ := (hP3.comap_subtype (K := N)).exists_le_sylow
  set S := (Q : Subgroup N).map N.subtype with hS
  have hPS : P ≤ S := fun y hy => ⟨⟨y, hPN hy⟩, hQ (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hSN : S ≤ N := Subgroup.map_subtype_le _
  have hS3 : IsPGroup 3 S := Q.isPGroup'.map N.subtype
  have hSd : S ≤ Subgroup.centralizer ({d} : Set G) := by
    intro y hy
    obtain ⟨k, hk⟩ := hS3 ⟨y, hy⟩
    have hyk : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hyN := hSN hy
    have hdyP : y * d * y⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hyN d).mp (hAP hdA)
    have hcen : ∀ z ∈ P, (y * d * y⁻¹) * z = z * (y * d * y⁻¹) := by
      intro z hz
      have hz' : y⁻¹ * z * y⁻¹⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) z).mp hz
      have h1 := hd _ hz'
      calc (y * d * y⁻¹) * z = y * (d * (y⁻¹ * z * y⁻¹⁻¹)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * z * y⁻¹⁻¹) * d) * y⁻¹ := by rw [h1]
        _ = z * (y * d * y⁻¹) := by group
    have hdy3 : (y * d * y⁻¹) ^ 3 = 1 := by
      rw [conj_pow, Item1117Proof.pow_three_of_mem_A h hdA]; group
    have hmem := mem_zpowers_d_of_central h45 h117 h hsc hrs hgx3 hdyP hcen hdy3
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Sec12.commute_of_conj_mem_zpowers hd3o hmem hyk)
  have hSdv : S ≤ Subgroup.normalizer ((Subgroup.closure {d, v} : Subgroup G) : Set G) := by
    intro y hy
    have hyv := conj_canonical_mem h45 h117 h hsc hrs hgx3 hPP hvA hcan (hSN hy)
    refine Item1117Proof.mem_normalizer_closure_pair ?_ ?_
    · have hyd : y * d = d * y := Subgroup.mem_centralizer_singleton_iff.mp (hSd hy)
      rw [hyd, mul_inv_cancel_right]
      exact Subgroup.subset_closure (by simp)
    · have e : y * v * y⁻¹ = v * (v⁻¹ * (y * v * y⁻¹)) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hyv)
  have hvd : v ∉ Subgroup.zpowers d := fun hv =>
    hxv (Item1117Proof.commute_x_of_mem_zpowers_d h hv).eq
  have hfr := exists_pow_inv_mul_mem_centralizer hS3 (hPS hxP)
    (Item1117Proof.commute_of_mem_A h hvA hdA) (Item1117Proof.pow_three_of_mem_A h hvA)
    (Item1117Proof.pow_three_of_mem_A h hdA) hvd hSdv hSd hxv
  have hCS : S ⊓ Subgroup.centralizer ({v} : Set G) = P ⊓ Subgroup.centralizer {v} :=
    hC.eq_of_le (inf_le_inf_right _ hPS) (inf_le_right.trans hK) (hS3.to_le inf_le_left)
  have hSP : S ≤ P := by
    intro y hy
    obtain ⟨n, hn⟩ := hfr y hy
    have hz : (x ^ n)⁻¹ * y ∈ S ⊓ Subgroup.centralizer ({v} : Set G) :=
      ⟨S.mul_mem (S.inv_mem (S.pow_mem (hPS hxP) n)) hy, hn⟩
    rw [hCS] at hz
    have e1 : y = x ^ n * ((x ^ n)⁻¹ * y) := by group
    rw [e1]
    exact P.mul_mem (P.pow_mem hxP n) hz.1
  have hPS' : P = S := le_antisymm hPS hSP
  have hPsyl : IsSylowOf 3 P N := by
    rw [hPS']
    exact ⟨Q, rfl⟩
  exact Sec12.isSylowOf_of_normalizer_le hPsyl le_top inf_le_right

end Data

end Item1117Res6Proof

end CFSG.RankThree.PartTwo.Sec11
