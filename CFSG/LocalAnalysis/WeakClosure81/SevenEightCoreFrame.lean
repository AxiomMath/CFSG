module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement Pointwise

variable {Q : Type*} [Group Q] [Finite Q]

private lemma seven_eight_core_frame_zpow_involution {a : Q} (ha : a * a = 1) (n : ℤ) :
    a ^ n = 1 ∨ a ^ n = a := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul, show a ^ (2 : ℤ) = 1 by rw [zpow_two, ha], one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, show a ^ (2 : ℤ) = 1 by rw [zpow_two, ha],
      one_zpow, zpow_one, one_mul]

private lemma seven_eight_core_frame_inv_commutator_self {a x : Q} (ha : a * a = 1) :
    a * ⁅x, a⁆ * a⁻¹ = ⁅x, a⁆⁻¹ := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [commutatorElement_def, hai]
  have hL : a * (x * a * x⁻¹ * a) * a = a * x * a * x⁻¹ := by
    rw [show a * (x * a * x⁻¹ * a) * a = a * x * a * x⁻¹ * (a * a) by group,
      ha, mul_one]
  have hR : (x * a * x⁻¹ * a)⁻¹ = a * x * a * x⁻¹ := by
    rw [show (x * a * x⁻¹ * a)⁻¹ = a⁻¹ * x * a⁻¹ * x⁻¹ by group, hai]
  rw [hL, hR]

private lemma seven_eight_core_frame_exists_sq_eq_of_odd {X : Type*} [Monoid X] {u : X}
    (hu : Odd (orderOf u)) : ∃ k : ℕ, (u ^ k) ^ 2 = u := by
  obtain ⟨k, hk⟩ := hu
  exact ⟨k + 1, by
    rw [← pow_mul, show (k + 1) * 2 = (2 * k + 1) + 1 by ring, pow_succ, ← hk,
      pow_orderOf_eq_one, one_mul]⟩

private lemma seven_eight_core_frame_eq_one_of_sq_eq_one_of_odd {G : Type*} [Group G]
    {H : Subgroup G} (hH : Odd (Nat.card H)) {x : G} (hx : x ∈ H) (hx2 : x ^ 2 = 1) :
    x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h2 : orderOf x ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hx
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h2
    exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hH)

private lemma seven_eight_core_frame_commutator_le_of_mem_normalizer {Xb : Subgroup Q} {a : Q}
    (haX : a ∈ Subgroup.normalizer (Xb : Set Q)) : ⁅Xb, Subgroup.zpowers a⁆ ≤ Xb := by
  rw [Subgroup.commutator_le]
  intro g1 hg1 g2 hg2
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg2
  have hnorm : a ^ n ∈ Subgroup.normalizer (Xb : Set Q) :=
    (Subgroup.normalizer (Xb : Set Q)).zpow_mem haX n
  have hconj : a ^ n * g1⁻¹ * (a ^ n)⁻¹ ∈ Xb :=
    (Subgroup.mem_normalizer_iff.mp hnorm g1⁻¹).mp (Xb.inv_mem hg1)
  have hcommutator : ⁅g1, a ^ n⁆ = g1 * (a ^ n * g1⁻¹ * (a ^ n)⁻¹) := by
    rw [commutatorElement_def]; group
  rw [hcommutator]
  exact Xb.mul_mem hg1 hconj

theorem conj_eq_inv_of_mem_commutator_zpowers {Xb : Subgroup Q} {a : Q} (ha : a * a = 1)
    (hab : ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, ∀ m' ∈ ⁅Xb, Subgroup.zpowers a⁆, m * m' = m' * m) :
    ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, a * m * a⁻¹ = m⁻¹ := by
  intro m hm
  rw [Subgroup.commutator_def] at hm
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨x1, hx1, x2, hx2, rfl⟩ := hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx2
      rcases seven_eight_core_frame_zpow_involution ha n with h | h
      · rw [h]; simp
      · rw [h]; exact seven_eight_core_frame_inv_commutator_self ha
  | one => simp
  | mul x y hx hy ihx ihy =>
      have hcomm : x * y = y * x := hab x hx y hy
      rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group,
        ihx, ihy, hcomm, mul_inv_rev]
  | inv x hx ihx =>
      rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group, ihx]

theorem exists_mul_eq_of_commutator_zpowers {Xb : Subgroup Q} (hodd : Odd (Nat.card Xb)) {a : Q}
    (ha : a * a = 1) (haX : a ∈ Subgroup.normalizer (Xb : Set Q))
    (hab : ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, ∀ m' ∈ ⁅Xb, Subgroup.zpowers a⁆, m * m' = m' * m) :
    ∀ x ∈ Xb, ∃ m ∈ ⁅Xb, Subgroup.zpowers a⁆, ∃ c ∈ Xb, a * c = c * a ∧ x = m * c := by
  have hMX : ⁅Xb, Subgroup.zpowers a⁆ ≤ Xb :=
    seven_eight_core_frame_commutator_le_of_mem_normalizer haX
  intro x hx
  set y : Q := ⁅x, a⁆ with hy_def
  have hyM : y ∈ ⁅Xb, Subgroup.zpowers a⁆ := by
    rw [hy_def]
    exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers a)
  have hyX : y ∈ Xb := hMX hyM
  have hy_odd : Odd (orderOf y) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard Xb hyX)
  obtain ⟨k, hk⟩ := seven_eight_core_frame_exists_sq_eq_of_odd hy_odd
  set m : Q := y ^ k with hm_def
  have hmM : m ∈ ⁅Xb, Subgroup.zpowers a⁆ := by
    rw [hm_def]; exact Subgroup.pow_mem _ hyM k
  have hm_sq : m ^ 2 = y := by rw [hm_def]; exact hk
  set c : Q := m⁻¹ * x with hc_def
  have hcX : c ∈ Xb := by
    rw [hc_def]; exact Xb.mul_mem (Xb.inv_mem (hMX hmM)) hx
  have hm_conj : a * m * a⁻¹ = m⁻¹ :=
    conj_eq_inv_of_mem_commutator_zpowers ha hab m hmM
  have hm_conj_inv : a * m⁻¹ * a⁻¹ = m := by
    calc a * m⁻¹ * a⁻¹ = (a * m * a⁻¹)⁻¹ := by group
      _ = (m⁻¹)⁻¹ := by rw [hm_conj]
      _ = m := inv_inv m
  have hay : a * x * a⁻¹ = y⁻¹ * x := by
    rw [hy_def, commutatorElement_def]
    group
  have hc_conj : a * c * a⁻¹ = c := by
    rw [hc_def]
    rw [show a * (m⁻¹ * x) * a⁻¹ = (a * m⁻¹ * a⁻¹) * (a * x * a⁻¹) by group,
      hm_conj_inv, hay, ← hm_sq]
    group
  have hcomm_c : a * c = c * a := by
    calc a * c = (a * c * a⁻¹) * a := by group
      _ = c * a := by rw [hc_conj]
  refine ⟨m, hmM, c, hcX, hcomm_c, ?_⟩
  rw [hc_def]
  group

theorem commute_of_mul_commute {Xb : Subgroup Q} (hodd : Odd (Nat.card Xb)) {a f : Q}
    (ha : a * a = 1) (haX : a ∈ Subgroup.normalizer (Xb : Set Q)) (haf : a * f = f * a)
    (hab : ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, ∀ m' ∈ ⁅Xb, Subgroup.zpowers a⁆, m * m' = m' * m)
    (hf : ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, f * m = m * f) :
    ∀ x ∈ Xb, a * f * x = x * (a * f) → a * x = x * a := by
  have hMX : ⁅Xb, Subgroup.zpowers a⁆ ≤ Xb :=
    seven_eight_core_frame_commutator_le_of_mem_normalizer haX
  intro x hx hcomm_x
  obtain ⟨m, hmM, c, hcX, hac, hx_eq⟩ :=
    exists_mul_eq_of_commutator_zpowers hodd ha haX hab x hx
  have hmX : m ∈ Xb := hMX hmM
  have hm2X : m ^ 2 ∈ Xb := Xb.pow_mem hmX 2
  have hm_conj : a * m * a⁻¹ = m⁻¹ :=
    conj_eq_inv_of_mem_commutator_zpowers ha hab m hmM
  have hm2_conj : a * m ^ 2 * a⁻¹ = (m ^ 2)⁻¹ :=
    conj_eq_inv_of_mem_commutator_zpowers ha hab (m ^ 2) (Subgroup.pow_mem _ hmM 2)
  set c' : Q := f * c * f⁻¹ with hc'_def
  have hfm : f * m * f⁻¹ = m := by rw [hf m hmM]; group
  have haf_conj : a * f * a⁻¹ = f := by rw [haf]; group
  have haf_inv_conj : a * f⁻¹ * a⁻¹ = f⁻¹ := by
    calc a * f⁻¹ * a⁻¹ = (a * f * a⁻¹)⁻¹ := by group
      _ = f⁻¹ := by rw [haf_conj]
  have hac_inv : a * c⁻¹ * a⁻¹ = c⁻¹ := by
    calc a * c⁻¹ * a⁻¹ = (a * c * a⁻¹)⁻¹ := by group
      _ = c⁻¹ := by rw [hac]; group
  have hc'_conj : a * c' * a⁻¹ = c' := by
    rw [hc'_def]
    calc a * (f * c * f⁻¹) * a⁻¹ = (a * f) * c * (f⁻¹ * a⁻¹) := by group
      _ = (f * a) * c * (f⁻¹ * a⁻¹) := by rw [haf]
      _ = f * (a * c) * (f⁻¹ * a⁻¹) := by group
      _ = f * (c * a) * (f⁻¹ * a⁻¹) := by rw [hac]
      _ = (f * c) * (a * f⁻¹ * a⁻¹) := by group
      _ = (f * c) * f⁻¹ := by rw [haf_inv_conj]
      _ = f * c * f⁻¹ := by group
  have hcent_cc : a * (c' * c⁻¹) * a⁻¹ = c' * c⁻¹ := by
    rw [show a * (c' * c⁻¹) * a⁻¹ = (a * c' * a⁻¹) * (a * c⁻¹ * a⁻¹) by group,
      hc'_conj, hac_inv]
  have hfix : (a * f) * x * (a * f)⁻¹ = x := by rw [hcomm_x]; group
  have hdecomp : (a * f) * x * (a * f)⁻¹ = (a * m * a⁻¹) * (a * c' * a⁻¹) := by
    rw [hx_eq]
    rw [show (a * f) * (m * c) * (a * f)⁻¹
        = ((a * f) * m * (a * f)⁻¹) * ((a * f) * c * (a * f)⁻¹) by group]
    rw [show (a * f) * m * (a * f)⁻¹ = a * m * a⁻¹ by
          rw [show (a * f) * m * (a * f)⁻¹ = a * (f * m * f⁻¹) * a⁻¹ by group, hfm]]
    rw [show (a * f) * c * (a * f)⁻¹ = a * c' * a⁻¹ by rw [hc'_def]; group]
  have heq : m⁻¹ * c' = m * c := by
    calc m⁻¹ * c' = (a * m * a⁻¹) * (a * c' * a⁻¹) := by rw [hm_conj, hc'_conj]
      _ = (a * f) * x * (a * f)⁻¹ := hdecomp.symm
      _ = x := hfix
      _ = m * c := hx_eq
  have heq2 : c' * c⁻¹ = m ^ 2 := by
    have h : c' = m * (m * c) := by
      calc c' = m * (m⁻¹ * c') := by group
        _ = m * (m * c) := by rw [heq]
    rw [h, pow_two]; group
  have hm2_eq_inv : m ^ 2 = (m ^ 2)⁻¹ := by
    have h := hcent_cc
    rw [heq2] at h
    rw [hm2_conj] at h
    exact h.symm
  have hm4 : (m ^ 2) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [hm2_eq_inv]
    exact inv_mul_cancel (m ^ 2)
  have hm2_eq_one : m ^ 2 = 1 :=
    seven_eight_core_frame_eq_one_of_sq_eq_one_of_odd hodd hm2X hm4
  have hm_eq_one : m = 1 :=
    seven_eight_core_frame_eq_one_of_sq_eq_one_of_odd hodd hmX hm2_eq_one
  rw [hx_eq, hm_eq_one, one_mul]
  exact hac

theorem inf_eq_bot_and_sup_eq_of_iSup_eq {Xb : Subgroup Q} (hodd : Odd (Nat.card Xb))
    (hXab : ∀ x ∈ Xb, ∀ y ∈ Xb, x * y = y * x) {ι : Type*} (a : ι → Q)
    (hinv : ∀ i, a i * a i = 1) (hnorm : ∀ i, a i ∈ Subgroup.normalizer (Xb : Set Q))
    (hcent : ∀ i j, i ≠ j → ∀ m ∈ ⁅Xb, Subgroup.zpowers (a j)⁆, a i * m = m * a i)
    (hgen : (⨆ j, ⁅Xb, Subgroup.zpowers (a j)⁆) = Xb) (i : ι) :
    ⁅Xb, Subgroup.zpowers (a i)⁆ ⊓ (⨆ j, ⨆ (_ : j ≠ i), ⁅Xb, Subgroup.zpowers (a j)⁆) = ⊥ ∧
      ⁅Xb, Subgroup.zpowers (a i)⁆ ⊔ (⨆ j, ⨆ (_ : j ≠ i), ⁅Xb, Subgroup.zpowers (a j)⁆) = Xb ∧
      ∀ x ∈ Xb, a i * x = x * a i → x ∈ ⨆ j, ⨆ (_ : j ≠ i), ⁅Xb, Subgroup.zpowers (a j)⁆ := by
  set Mi : Subgroup Q := ⁅Xb, Subgroup.zpowers (a i)⁆ with hMi_def
  set C : Subgroup Q := ⨆ j, ⨆ (_ : j ≠ i), ⁅Xb, Subgroup.zpowers (a j)⁆ with hC_def
  have hMile : Mi ≤ Xb := by
    rw [hMi_def]
    exact seven_eight_core_frame_commutator_le_of_mem_normalizer (hnorm i)
  have hCle : C ≤ Xb := by
    rw [hC_def]
    apply iSup_le
    intro j
    apply iSup_le
    intro _
    exact seven_eight_core_frame_commutator_le_of_mem_normalizer (hnorm j)
  have hleC : C ≤ Subgroup.centralizer ({a i} : Set Q) := by
    rw [hC_def]
    apply iSup_le
    intro j
    apply iSup_le
    intro h
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hcent i j h.symm m hm
  have hcentC : ∀ c ∈ C, a i * c = c * a i := fun c hc =>
    (Subgroup.mem_centralizer_iff.mp (hleC hc)) (a i) (Set.mem_singleton _)
  have hhab_i : ∀ m ∈ Mi, ∀ m' ∈ Mi, m * m' = m' * m :=
    fun m hm m' hm' => hXab m (hMile hm) m' (hMile hm')
  have hinf : Mi ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxm : x ∈ Mi := hx.1
    have hxc : x ∈ C := hx.2
    have h1 : a i * x * (a i)⁻¹ = x⁻¹ :=
      conj_eq_inv_of_mem_commutator_zpowers (hinv i) hhab_i x hxm
    have h2 : a i * x * (a i)⁻¹ = x := by rw [hcentC x hxc]; group
    have hxinv : x⁻¹ = x := by rw [← h1, h2]
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← hxinv]
      exact inv_mul_cancel x
    simpa using seven_eight_core_frame_eq_one_of_sq_eq_one_of_odd hodd (hMile hxm) hx2
  have hsup : Mi ⊔ C = Xb := by
    have h := iSup_split_single (fun j => ⁅Xb, Subgroup.zpowers (a j)⁆) i
    rw [hgen] at h
    simpa [hMi_def, hC_def] using h.symm
  have hdecomp : ∀ y ∈ Mi ⊔ C, ∃ m ∈ Mi, ∃ c ∈ C, y = m * c := by
    intro y hy
    rw [Subgroup.sup_eq_closure] at hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
        rcases hz with hz | hz
        · exact ⟨z, hz, 1, C.one_mem, by rw [mul_one]⟩
        · exact ⟨1, Mi.one_mem, z, hz, by rw [one_mul]⟩
    | one => exact ⟨1, Mi.one_mem, 1, C.one_mem, by rw [mul_one]⟩
    | mul y z hy hz ihy ihz =>
        obtain ⟨m₁, hm₁, c₁, hc₁, rfl⟩ := ihy
        obtain ⟨m₂, hm₂, c₂, hc₂, rfl⟩ := ihz
        refine ⟨m₁ * m₂, Mi.mul_mem hm₁ hm₂, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
        rw [show (m₁ * c₁) * (m₂ * c₂) = (m₁ * m₂) * (c₁ * c₂) by
              calc (m₁ * c₁) * (m₂ * c₂) = m₁ * (c₁ * m₂) * c₂ := by group
                _ = m₁ * (m₂ * c₁) * c₂ := by rw [hXab m₂ (hMile hm₂) c₁ (hCle hc₁)]
                _ = (m₁ * m₂) * (c₁ * c₂) := by group]
    | inv z hz ihz =>
        obtain ⟨m, hm, c, hc, rfl⟩ := ihz
        refine ⟨m⁻¹, Mi.inv_mem hm, c⁻¹, C.inv_mem hc, ?_⟩
        rw [show (m * c)⁻¹ = m⁻¹ * c⁻¹ by
              rw [hXab m (hMile hm) c (hCle hc)]; group]
  refine ⟨hinf, hsup, ?_⟩
  intro x hxX hxcomm
  have hxsup : x ∈ Mi ⊔ C := by rw [hsup]; exact hxX
  obtain ⟨m, hm, c, hc, rfl⟩ := hdecomp x hxsup
  have hm_conj : a i * m * (a i)⁻¹ = m⁻¹ :=
    conj_eq_inv_of_mem_commutator_zpowers (hinv i) hhab_i m hm
  have hc_fix : a i * c * (a i)⁻¹ = c := by rw [hcentC c hc]; group
  have hxconj : a i * (m * c) * (a i)⁻¹ = m⁻¹ * c := by
    rw [show a i * (m * c) * (a i)⁻¹
        = (a i * m * (a i)⁻¹) * (a i * c * (a i)⁻¹) by group, hm_conj, hc_fix]
  have hfix : a i * (m * c) * (a i)⁻¹ = m * c := by rw [hxcomm]; group
  have hm_eq_inv : m⁻¹ = m := by
    apply mul_right_cancel (b := c)
    rw [← hxconj, hfix]
  have hm2 : m ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← hm_eq_inv]
    exact inv_mul_cancel m
  have hm1 : m = 1 :=
    seven_eight_core_frame_eq_one_of_sq_eq_one_of_odd hodd (hMile hm) hm2
  rw [hm1, one_mul]
  exact hc

theorem orderOf_mul_not_odd_and_ne_two_pow {a a' m : Q} (ha : a * a = 1) (ha' : a' * a' = 1)
    (hcomm : a * a' = a' * a) (hne : a ≠ a') (hm : Odd (orderOf m)) (hm1 : m ≠ 1)
    (hinv : a * m * a⁻¹ = m⁻¹) (hc : a * a' * m = m * (a * a')) :
    ¬ Odd (orderOf (m⁻¹ * a * m * a')) ∧ ∀ n : ℕ, orderOf (m⁻¹ * a * m * a') ≠ 2 ^ n := by
  have ham : a * m = m⁻¹ * a := by
    calc a * m = a * m * a⁻¹ * a := by group
      _ = m⁻¹ * a := by rw [hinv]
  have hX : m⁻¹ * a * m * a' = (m⁻¹ ^ 2) * (a * a') := by
    calc m⁻¹ * a * m * a' = m⁻¹ * (a * m) * a' := by group
      _ = m⁻¹ * (m⁻¹ * a) * a' := by rw [ham]
      _ = (m⁻¹ ^ 2) * (a * a') := by rw [pow_two]; group
  have hcop : (orderOf m).Coprime 2 := hm.coprime_two_right
  have hgcd : Nat.gcd (orderOf m) 2 = 1 := hcop
  have hs_order : orderOf (m⁻¹ ^ 2) = orderOf m := by
    rw [orderOf_pow, orderOf_inv, hgcd, Nat.div_one]
  have ht_ne : a * a' ≠ 1 := by
    intro h
    have haa' : a' = a := (eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right ha)
    exact hne haa'.symm
  have ht2 : (a * a') ^ 2 = 1 := by
    rw [pow_two]
    calc (a * a') * (a * a') = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [← hcomm]
      _ = (a * a) * (a' * a') := by group
      _ = 1 := by rw [ha, ha', mul_one]
  have ht_order : orderOf (a * a') = 2 := orderOf_eq_prime ht2 ht_ne
  have hcomm_st : Commute (m⁻¹ ^ 2) (a * a') := (Commute.symm hc).inv_left.pow_left 2
  have hcoprime : (orderOf (m⁻¹ ^ 2)).Coprime (orderOf (a * a')) := by
    rw [hs_order, ht_order]
    exact hcop
  have hst : orderOf ((m⁻¹ ^ 2) * (a * a')) = orderOf m * 2 := by
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm_st hcoprime, hs_order, ht_order]
  rw [hX]
  constructor
  · intro hodd
    rw [hst] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (by rw [Nat.mul_comm]; exact even_two_mul (orderOf m))
  · intro n hn
    rw [hst] at hn
    have hdvd : orderOf m ∣ 2 ^ n := by
      rw [← hn]; exact dvd_mul_right (orderOf m) 2
    have hcop2 : (orderOf m).Coprime (2 ^ n) := hcop.pow_right n
    exact hm1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop2 (dvd_refl _) hdvd))

end CFSG.LocalAnalysis.WeakClosure81
