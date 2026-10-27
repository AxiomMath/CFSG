module

public import CFSG.Walter.J1Recog.Gens

public section

namespace CFSG.Walter.J1Recog

open CFSG.Walter.J1

namespace Setup

variable {G : Type} [Group G] [Finite G] (X : Setup G)

omit [Finite G] in
theorem conj_comm_of_conj {g a b : G} (hab : a * b = b * a) (hb : g * b * g⁻¹ = b) :
    (g * a * g⁻¹) * b = b * (g * a * g⁻¹) := by
  have := conj_commute (g := g) hab
  rwa [hb] at this

omit [Finite G] in
theorem comm_of_comm_inv {a b : G} (h : a * b⁻¹ = b⁻¹ * a) : a * b = b * a := by
  calc a * b = b * (b⁻¹ * a) * b := by group
    _ = b * (a * b⁻¹) * b := by rw [h]
    _ = b * a := by group

omit [Finite G] in
theorem inv_conj_of_conj {g a : G} (h : g * a * g⁻¹ = a⁻¹) : g * a⁻¹ * g⁻¹ = a := by
  rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group, h, inv_inv]

include X in
theorem exists_q {p y z : G} (hp5 : p ^ 5 = 1) (hp1 : p ≠ 1) (hy : orderOf y = 2)
    (hyp : y * p = p * y) (hz : z * p * z⁻¹ = p⁻¹) :
    ∃ q : G, q ^ 3 = 1 ∧ q ≠ 1 ∧ q * p = p * q ∧ y * q * y⁻¹ = q⁻¹ ∧
      (z * q * z⁻¹ = q ∨ z * q * z⁻¹ = q⁻¹) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpo : orderOf p = 5 := orderOf_eq_prime hp5 hp1
  have hP : Nat.card (Subgroup.zpowers p) = 5 := by rw [Nat.card_zpowers, hpo]
  have hPy : Subgroup.zpowers p ≤ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hyp.symm)
  obtain ⟨A, hAC, hPA, hAy, hA, hodd, habel, -⟩ := X.exists_A (Or.inr rfl) hP hy hPy
  obtain ⟨q₀, hq₀⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (by rw [hA]; norm_num)
  obtain ⟨q, hqdef⟩ : ∃ q : G, q = q₀ := ⟨_, rfl⟩
  have hqo : orderOf q = 3 := by rw [hqdef, Subgroup.orderOf_coe, hq₀]
  have hq3 : q ^ 3 = 1 := by rw [← hqo]; exact pow_orderOf_eq_one q
  have hq1 : q ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hqo; omega
  have hqA : q ∈ A := hqdef ▸ q₀.2
  have hqp : q * p = p * q := (mem_centralizer_zpowers_iff' _ _).mp (hAC hqA)
  have hpow : ∀ w : G, w * p = p * w → orderOf w = 3 → w = q ∨ w = q⁻¹ ∨ w = 1 := by
    intro w hwp hwo
    have hwA : w ∈ A := hodd w ((mem_centralizer_zpowers_iff' _ _).mpr hwp) (by
      rw [hwo]; decide)
    have hw3 : w ^ 3 = 1 := by rw [← hwo]; exact pow_orderOf_eq_one w
    have hmem := mem_zpowers_of_comm habel Nat.prime_three (by rw [hA]; norm_num) hwA hqA hw3
      hq3 hq1
    obtain ⟨j, hj3, rfl⟩ := exists_pow_of_mem_zpowers (n := 3) (by norm_num) hq3 hmem
    interval_cases j
    · exact Or.inr (Or.inr (pow_zero q))
    · exact Or.inl (pow_one q)
    · refine Or.inr (Or.inl ?_)
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hq3]
  have hconj_o : ∀ g : G, orderOf (g * q * g⁻¹) = 3 := fun g => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hqo]
  have hconj_ne : ∀ g : G, g * q * g⁻¹ ≠ 1 := fun g h1 => by
    have := hconj_o g; rw [h1, orderOf_one] at this; omega
  refine ⟨q, hq3, hq1, hqp, ?_, ?_⟩
  ·
    have hyq : (y * q * y⁻¹) * p = p * (y * q * y⁻¹) := by
      have h1 : y * p * y⁻¹ = p := by rw [hyp, mul_inv_cancel_right]
      exact conj_comm_of_conj hqp h1
    rcases hpow _ hyq (hconj_o y) with h | h | h
    · exfalso
      have hqy : q ∈ Subgroup.centralizer ({y} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (mul_inv_eq_iff_eq_mul.mp h).symm
      have hqP : q ∈ Subgroup.zpowers p := by rw [← hAy]; exact ⟨hqA, hqy⟩
      have hq5 : q ^ 5 = 1 := by
        obtain ⟨k, hk⟩ := hqP
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp5, one_zpow]
      apply hq1
      calc q = q ^ 6 * (q ^ 5)⁻¹ := by group
        _ = 1 := by rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hq3, one_pow, hq5, inv_one,
          mul_one]
    · exact h
    · exact absurd h (hconj_ne y)
  ·
    have hzq : (z * q * z⁻¹) * p = p * (z * q * z⁻¹) := by
      have h1 := conj_commute (g := z) hqp
      rw [hz] at h1
      exact comm_of_comm_inv h1
    rcases hpow _ hzq (hconj_o z) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hconj_ne z)

omit [Finite G] in
theorem conj_conj_comm {g a b : G} (hab : a * b = b * a) :
    (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) := conj_commute hab

omit [Finite G] in
theorem conj_inv_of {g a b : G} (h : a * b * a⁻¹ = b⁻¹) :
    (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ = (g * b * g⁻¹)⁻¹ := by
  calc (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ = g * (a * b * a⁻¹) * g⁻¹ := by group
    _ = (g * b * g⁻¹)⁻¹ := by rw [h]; group

include X in
theorem transfer {s u : G} (hs : orderOf s = 2) (hsm : s * X.m = X.m * s) (hst : s ≠ X.t)
    (hu : orderOf u = 2) (hut : u * X.t = X.t * u) (hus : u * s = s * u)
    (hum : u * X.m * u⁻¹ = X.m⁻¹) {r q p y g : G} (hq3 : q ^ 3 = 1) (hq1 : q ≠ 1)
    (hrq : r * q = q * r) (hp5 : p ^ 5 = 1) (hp1 : p ≠ 1) (hqp : q * p = p * q)
    (hyr : y * r = r * y) (hyp : y * p = p * y) (hyq : y * q * y⁻¹ = q⁻¹)
    (hg : g * r * g⁻¹ = X.t) :
    g * y * g⁻¹ ∈ X.F ↔ u ∈ X.F := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set q₁ := g * q * g⁻¹ with hq₁
  have hq₁t : q₁ * X.t = X.t * q₁ := by rw [← hg]; exact conj_conj_comm hrq.symm
  have hq₁3 : q₁ ^ 3 = 1 := by rw [hq₁, conj_pow, hq3]; group
  have hq₁1 : q₁ ≠ 1 := fun h1 => hq1 (by
    have : q = g⁻¹ * q₁ * g := by rw [hq₁]; group
    rw [this, h1]; group)
  have hq₁o : orderOf q₁ = 3 := orderOf_eq_prime hq₁3 hq₁1
  have hq₁F : q₁ ∈ X.F := X.h.mem_F_of_odd (Subgroup.mem_centralizer_singleton_iff.mpr hq₁t)
    (by rw [hq₁o]; decide)
  obtain ⟨f, hfF, hfq⟩ := A5Sub.conj_three X.h.iso hq₁F X.m_mem_F hq₁3 hq₁1 X.m_pow_three
    X.m_ne_one
  have hft : f * X.t * f⁻¹ = X.t := by
    rw [X.h.commute_of_mem_F hfF, mul_inv_cancel_right]
  set g₂ := f * g with hg₂
  have hconj : ∀ a : G, g₂ * a * g₂⁻¹ = f * (g * a * g⁻¹) * f⁻¹ := fun a => by
    rw [hg₂]; group
  have hg₂r : g₂ * r * g₂⁻¹ = X.t := by rw [hconj, hg, hft]
  have hg₂q : g₂ * q * g₂⁻¹ = X.m := by rw [hconj, ← hq₁, hfq]
  set x₅ := g₂ * p * g₂⁻¹ with hx₅
  have hx₅5 : x₅ ^ 5 = 1 := by rw [hx₅, conj_pow, hp5]; group
  have hx₅1 : x₅ ≠ 1 := fun h1 => hp1 (by
    have : p = g₂⁻¹ * x₅ * g₂ := by rw [hx₅]; group
    rw [this, h1]; group)
  have hx₅m : x₅ * X.m = X.m * x₅ := by
    rw [← hg₂q, hx₅]; exact conj_conj_comm hqp.symm
  obtain ⟨hts5, hts1⟩ := X.pow_five hs hsm hst
  obtain ⟨A, -, -, -, hA, hodd, habel, -⟩ := X.exists_A (Or.inl rfl) X.card_zpowers_m
    X.h.orderOf_t X.zpowers_m_le
  have htsm : X.t * s * X.m = X.m * (X.t * s) := by
    rw [mul_assoc, hsm, ← mul_assoc, ← X.m_t, mul_assoc]
  have htsA : X.t * s ∈ A := hodd _ ((mem_centralizer_zpowers_iff' _ _).mpr htsm)
    (by rw [orderOf_eq_prime hts5 hts1]; decide)
  have hx₅A : x₅ ∈ A := hodd _ ((mem_centralizer_zpowers_iff' _ _).mpr hx₅m)
    (by rw [orderOf_eq_prime hx₅5 hx₅1]; decide)
  have hx₅mem : x₅ ∈ Subgroup.zpowers (X.t * s) := mem_zpowers_of_comm habel (p := 5)
    (by norm_num) (by rw [hA]; norm_num) hx₅A htsA hx₅5 hts5 hts1
  have htsmem : X.t * s ∈ Subgroup.zpowers x₅ := by
    have hcard : Nat.card (Subgroup.zpowers (X.t * s)) = 5 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hts5 hts1]
    rw [← eq_zpowers_of_card_prime (by norm_num) hcard hx₅mem hx₅1]
    exact Subgroup.mem_zpowers _
  set y' := g₂ * y * g₂⁻¹ with hy'
  have hy't : y' * X.t = X.t * y' := by rw [← hg₂r, hy']; exact conj_conj_comm hyr
  have hy'm : y' * X.m * y'⁻¹ = X.m⁻¹ := by rw [← hg₂q, hy']; exact conj_inv_of hyq
  have hy'x : y' * x₅ = x₅ * y' := by rw [hy', hx₅]; exact conj_conj_comm hyp
  have hy'ts : y' * (X.t * s) = (X.t * s) * y' := by
    obtain ⟨k, hk⟩ := htsmem
    rw [← hk]
    exact (Commute.zpow_right (show Commute y' x₅ from hy'x) k).eq
  have hy's : y' * s = s * y' := by
    have hs' : s = X.t * (X.t * s) := by rw [← mul_assoc, X.t_mul_t, one_mul]
    rw [hs', ← mul_assoc, hy't, mul_assoc, hy'ts]
    simp only [mul_assoc]
  have hu2 : u * u = 1 := (orderOf_eq_two_iff.mp hu).1
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  set z := y' * u with hz
  have hzm : z * X.m = X.m * z := by
    have : z * X.m * z⁻¹ = X.m := by
      calc z * X.m * z⁻¹ = y' * (u * X.m * u⁻¹) * y'⁻¹ := by rw [hz]; group
        _ = (y' * X.m * y'⁻¹)⁻¹ := by rw [hum]; group
        _ = X.m := by rw [hy'm, inv_inv]
    exact mul_inv_eq_iff_eq_mul.mp this
  have hzt : z * X.t = X.t * z := by
    rw [hz, mul_assoc, hut, ← mul_assoc, hy't, mul_assoc]
  have hzs : z * s = s * z := by
    rw [hz, mul_assoc, hus, ← mul_assoc, hy's, mul_assoc]
  have hzF : z ∈ X.F := by
    rcases X.h.mem_centralizer_t.mp (Subgroup.mem_centralizer_singleton_iff.mpr hzt) with h | h
    · exact h
    · exfalso
      have htzm : X.t * z * X.m = X.m * (X.t * z) := by
        rw [mul_assoc, hzm, ← mul_assoc, ← X.m_t, mul_assoc]
      have hmem := CFSG.Walter.J1.A5Sub.mem_zpowers_of_commute_three X.h.iso X.m_mem_F h
        X.m_pow_three X.m_ne_one htzm.symm
      have htzs : X.t * z * s = s * (X.t * z) := by
        obtain ⟨k, hk⟩ := hmem
        rw [← hk]
        exact (Commute.zpow_left (show Commute X.m s from hsm.symm) k).eq
      have hts : X.t * s = s * X.t := by
        have : X.t * s * z = s * X.t * z := by
          rw [mul_assoc, ← hzs, ← mul_assoc, htzs, mul_assoc]
        exact mul_right_cancel this
      apply hts1
      have hts2 : (X.t * s) * (X.t * s) = 1 := by
        rw [mul_assoc, ← mul_assoc s, ← hts, mul_assoc, ← mul_assoc X.t, X.t_mul_t, one_mul,
          (orderOf_eq_two_iff.mp hs).1]
      obtain ⟨w, hw⟩ : ∃ w, w = X.t * s := ⟨_, rfl⟩
      rw [← hw] at hts5 hts2 ⊢
      calc w = w ^ 5 * (w * w)⁻¹ ^ 2 := by group
        _ = 1 := by rw [hts5, hts2, inv_one, one_pow, one_mul]
  have hy'eq : y' = z * u := by rw [hz, mul_assoc, hu2, mul_one]
  have hy'F : y' ∈ X.F ↔ u ∈ X.F := by
    constructor
    · intro h
      have : u = z⁻¹ * y' := by rw [hy'eq]; group
      rw [this]
      exact X.F.mul_mem (X.F.inv_mem hzF) h
    · intro h
      rw [hy'eq]
      exact X.F.mul_mem hzF h
  rw [← hy'F, hy', hconj]
  constructor
  · intro h
    exact X.F.mul_mem (X.F.mul_mem hfF h) (X.F.inv_mem hfF)
  · intro h
    have : g * y * g⁻¹ = f⁻¹ * (f * (g * y * g⁻¹) * f⁻¹) * f := by group
    rw [this]
    exact X.F.mul_mem (X.F.mul_mem (X.F.inv_mem hfF) h) hfF

theorem e6_eq : X.n * X.t * X.n⁻¹ = X.e 6 := by
  have := ee_inv_eq X.t X.n X.n_pow_seven 1 (by norm_num)
  simpa using this

theorem e1_eq : X.e 1 = X.n⁻¹ * X.t * X.n := by simp [e, ee]

theorem e5_eq : X.e 5 = X.t * X.e 1 := by rw [← X.rel05, X.e_zero]

theorem e4_eq : X.e 4 = X.t * X.e 6 := by rw [← X.rel04, X.e_zero]

theorem n4_e4 : X.n ^ 4 * X.e 4 * (X.n ^ 4)⁻¹ = X.t := by simp only [e, ee]; group

theorem n4_e6 : X.n ^ 4 * X.e 6 * (X.n ^ 4)⁻¹ = X.e 2 := by simp only [e, ee]; group

theorem n4_t : X.n ^ 4 * X.t * (X.n ^ 4)⁻¹ = X.e 3 := by
  have := ee_inv_eq X.t X.n X.n_pow_seven 4 (by norm_num)
  simpa using this

theorem ninv_e6 : X.n⁻¹ * X.e 6 * X.n⁻¹⁻¹ = X.t := by rw [← X.e6_eq]; group

theorem e_inv (i : ℕ) : (X.e i)⁻¹ = X.e i := inv_eq_of_mul_eq_one_right (X.e_mul_self i)

theorem orderOf_e (i : ℕ) : orderOf (X.e i) = 2 :=
  orderOf_eq_two_iff.mpr ⟨X.e_mul_self i, X.e_ne_one i⟩

theorem e_comm_t (i : ℕ) : X.e i * X.t = X.t * X.e i := by
  rw [← X.e_zero]; exact X.e_comm i 0

omit [Finite G] in
theorem conj_pow_five {x : G} (g : G) (h5 : x ^ 5 = 1) (h1 : x ≠ 1) :
    (g * x * g⁻¹) ^ 5 = 1 ∧ g * x * g⁻¹ ≠ 1 := by
  refine ⟨by rw [conj_pow, h5]; group, fun h => h1 ?_⟩
  have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [this, h]; group

omit [Finite G] in
theorem comm_of_mem_pow {q b c : G} (hqb : q * b = b * q) (hc : c = q ∨ c = q ^ 2) :
    c * b = b * c := by
  rcases hc with rfl | rfl
  · exact hqb
  · exact (Commute.pow_left (show Commute q b from hqb) 2).eq

omit [Finite G] in
theorem comm_of_split {b c y d q : G} (hy2 : y * y = 1) (hyb : y * b = b * y)
    (hqb : q * b = b * q) (hd : d = c * y) (hdq : d = q ∨ d = q ^ 2) : b * c = c * b := by
  have hdb := comm_of_mem_pow hqb hdq
  have hc : c = d * y := by rw [hd, mul_assoc, hy2, mul_one]
  rw [hc, ← mul_assoc, ← hdb, mul_assoc, ← hyb, ← mul_assoc]

theorem conj_tn_eq {c : G} (hct : c * X.t = X.t * c) :
    (X.n⁻¹ * X.t * X.n)⁻¹ * c * (X.n⁻¹ * X.t * X.n) = X.e 5 * c * (X.e 5)⁻¹ := by
  rw [← X.e1_eq, X.e5_eq, X.e_inv 1]
  have h1 : X.e 1 * c * X.e 1 * X.t = X.t * (X.e 1 * c * X.e 1) := by
    calc X.e 1 * c * X.e 1 * X.t = X.e 1 * c * (X.e 1 * X.t) := by group
      _ = X.e 1 * (c * X.t) * X.e 1 := by rw [X.e_comm_t]; group
      _ = X.e 1 * X.t * c * X.e 1 := by rw [hct]; group
      _ = X.t * (X.e 1 * c * X.e 1) := by rw [X.e_comm_t]; group
  rw [mul_inv_rev, X.e_inv 1, X.h.t_inv]
  calc X.e 1 * c * X.e 1 = X.e 1 * c * X.e 1 * X.t * X.t := by
        rw [mul_assoc _ X.t, X.t_mul_t, mul_one]
    _ = X.t * (X.e 1 * c * X.e 1) * X.t := by rw [h1]
    _ = X.t * X.e 1 * c * (X.e 1 * X.t) := by group

theorem conj_e5_mul (c : G) (i : ℕ) :
    X.e 5 * (c * X.e i) * (X.e 5)⁻¹ = X.e 5 * c * (X.e 5)⁻¹ * X.e i := by
  rw [X.e_inv 5]
  calc X.e 5 * (c * X.e i) * X.e 5 = X.e 5 * c * (X.e i * X.e 5) := by group
    _ = X.e 5 * c * X.e 5 * X.e i := by rw [X.e_comm i 5]; group

theorem involution_conj_m {x : G} (hx2 : x * x = 1) (hxm : x * X.m * x⁻¹ = X.m⁻¹) :
    (X.m * x) ^ 2 = 1 := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  rw [pow_two]
  calc X.m * x * (X.m * x) = X.m * (x * X.m * x⁻¹) := by rw [hxinv]; group
    _ = 1 := by rw [hxm, mul_inv_cancel]

theorem m_mul_ne_one {x : G} (hx : orderOf x = 2) : X.m * x ≠ 1 := by
  intro h1
  have : x = X.m⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [this, orderOf_inv, X.orderOf_m] at hx
  omega

theorem split_O1 {s u : G} (hs : orderOf s = 2) (hsn : s * X.n * s⁻¹ = X.n⁻¹)
    (hsm : s * X.m = X.m * s) (hu : orderOf u = 2) (hut : u * X.t = X.t * u)
    (hus : u * s = s * u) (hum : u * X.m * u⁻¹ = X.m⁻¹) (huF : u ∈ X.F) (hpat : X.Pattern u) :
    (X.n * X.t * u * X.n⁻¹) * (X.m * u) = (X.m * u) * (X.n * X.t * u * X.n⁻¹) ∨
      (X.n * X.t * u * X.n⁻¹) * ((X.n⁻¹ * X.t * X.n)⁻¹ * (X.m * u) * (X.n⁻¹ * X.t * X.n)) =
        ((X.n⁻¹ * X.t * X.n)⁻¹ * (X.m * u) * (X.n⁻¹ * X.t * X.n)) * (X.n * X.t * u * X.n⁻¹) := by
  have hst : s ≠ X.t := by rintro rfl; exact X.t_not_inv_n hsn
  have hu2 : u * u = 1 := (orderOf_eq_two_iff.mp hu).1
  have htinv : X.t⁻¹ = X.t := X.h.t_inv
  have hct : X.m * u * X.t = X.t * (X.m * u) := by
    rw [mul_assoc, hut, ← mul_assoc, X.m_t, mul_assoc]
  rw [X.conj_tn_eq hct]
  obtain ⟨b, hb⟩ : ∃ b, b = X.n * X.t * u * X.n⁻¹ := ⟨_, rfl⟩
  rw [← hb]
  obtain ⟨p, hp⟩ : ∃ p, p = X.t * b := ⟨_, rfl⟩
  have hpn : p = X.n * (X.e 5 * u) * X.n⁻¹ := by
    have h1 : X.n * X.e 5 * X.n⁻¹ = X.e 6 * X.t := by
      rw [X.e5_eq, X.e1_eq, ← X.e6_eq]; group
    calc p = X.t * X.e 6 * (X.n * u * X.n⁻¹) := by rw [hp, hb, ← X.e6_eq]; group
      _ = X.e 6 * X.t * (X.n * u * X.n⁻¹) := by rw [X.e_comm_t]
      _ = X.n * (X.e 5 * u) * X.n⁻¹ := by rw [← h1]; group
  have he5u : X.e 5 * u = X.e 5 * (u * X.e 5) * (X.e 5)⁻¹ := by group
  obtain ⟨hp5, hp1⟩ : p ^ 5 = 1 ∧ p ≠ 1 := by
    obtain ⟨h5, h1⟩ := conj_pow_five (X.e 5) hpat.1.1 hpat.1.2
    rw [← he5u] at h5 h1
    rw [hpn]
    exact conj_pow_five X.n h5 h1
  have htu2 : X.t * u * (X.t * u) = 1 := by
    calc X.t * u * (X.t * u) = X.t * (u * X.t) * u := by group
      _ = 1 := by rw [hut, ← mul_assoc, X.t_mul_t, one_mul, hu2]
  have hb2 : b * b = 1 := by
    rw [hb]
    calc X.n * X.t * u * X.n⁻¹ * (X.n * X.t * u * X.n⁻¹) =
        X.n * (X.t * u * (X.t * u)) * X.n⁻¹ := by group
      _ = 1 := by rw [htu2]; group
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hyb : X.e 6 * b = b * X.e 6 := by
    rw [hb, ← X.e6_eq]
    have h1 : X.t * u * X.t = X.t * X.t * u := by rw [mul_assoc, hut, ← mul_assoc]
    calc X.n * X.t * X.n⁻¹ * (X.n * X.t * u * X.n⁻¹) = X.n * (X.t * X.t * u) * X.n⁻¹ := by
          group
      _ = X.n * (X.t * u * X.t) * X.n⁻¹ := by rw [h1]
      _ = X.n * X.t * u * X.n⁻¹ * (X.n * X.t * X.n⁻¹) := by group
  have hyp : X.e 6 * p = p * X.e 6 := by
    rw [hp, ← mul_assoc, X.e_comm_t, mul_assoc, hyb, ← mul_assoc]
  have htp : X.t * p * X.t⁻¹ = p⁻¹ := by
    rw [hp, mul_inv_rev, hbinv, htinv, ← mul_assoc, X.t_mul_t, one_mul]
  obtain ⟨q, hq3, hq1, hqp, hyq, htq⟩ := X.exists_q hp5 hp1 (X.orderOf_e 6) hyp htp
  rcases htq with htq | htq
  ·
    have hqt : q * X.t = X.t * q := (mul_inv_eq_iff_eq_mul.mp htq).symm
    have hqF : q ∈ X.F := X.h.mem_F_of_odd (Subgroup.mem_centralizer_singleton_iff.mpr hqt)
      (by rw [orderOf_eq_prime hq3 hq1]; decide)
    have hqb : q * b = b * q := by
      have hb' : b = X.t * p := by rw [hp, ← mul_assoc, X.t_mul_t, one_mul]
      rw [hb', ← mul_assoc, hqt, mul_assoc, hqp, mul_assoc]
    have hsplit := A5Sub.split_fact X.h.iso (x := X.e 6) (a := X.m * u) (w := X.e 5) (q := q)
      X.e6_mem_F (X.F.mul_mem X.m_mem_F huF) X.e5_mem_F hqF
      (by rw [pow_two]; exact X.e_mul_self 6) (X.e_ne_one 6) (X.involution_conj_m hu2 hum)
      (X.m_mul_ne_one hu) hpat.2.2.2.1 hpat.2.2.2.2 (by rw [pow_two]; exact X.e_mul_self 5)
      (X.e_ne_one 5) (X.e_comm 5 6) (X.e_ne (by norm_num) (by norm_num)) hq3 hq1 hyq
    have hy2 := X.e_mul_self 6
    rcases hsplit with h | h | h | h
    · exact Or.inl (comm_of_split hy2 hyb hqb rfl (Or.inl h))
    · exact Or.inl (comm_of_split hy2 hyb hqb rfl (Or.inr h))
    · exact Or.inr (comm_of_split hy2 hyb hqb (X.conj_e5_mul _ 6) (Or.inl h))
    · exact Or.inr (comm_of_split hy2 hyb hqb (X.conj_e5_mul _ 6) (Or.inr h))
  ·
    exfalso
    have hrq : X.t * X.e 6 * q = q * (X.t * X.e 6) := by
      have h1 : (X.t * X.e 6) * q * (X.t * X.e 6)⁻¹ = q := by
        calc (X.t * X.e 6) * q * (X.t * X.e 6)⁻¹ = X.t * (X.e 6 * q * (X.e 6)⁻¹) * X.t⁻¹ := by
              group
          _ = q := by rw [hyq]; exact inv_conj_of_conj htq
      exact mul_inv_eq_iff_eq_mul.mp h1
    have hyr : X.e 6 * (X.t * X.e 6) = (X.t * X.e 6) * X.e 6 := by
      rw [← mul_assoc, X.e_comm_t]
    have hg : X.n ^ 4 * (X.t * X.e 6) * (X.n ^ 4)⁻¹ = X.t := by rw [← X.e4_eq, X.n4_e4]
    have htr := X.transfer hs hsm hst hu hut hus hum hq3 hq1 hrq hp5 hp1 hqp hyr hyp hyq hg
    rw [X.n4_e6] at htr
    exact X.e2_not_mem_F (htr.mpr huF)

theorem split_O2 {s u : G} (hs : orderOf s = 2) (hsn : s * X.n * s⁻¹ = X.n⁻¹)
    (hsm : s * X.m = X.m * s) (hu : orderOf u = 2) (hut : u * X.t = X.t * u)
    (hus : u * s = s * u) (hum : u * X.m * u⁻¹ = X.m⁻¹) (hxF : X.t * u ∈ X.F)
    (hpat : X.Pattern (X.t * u)) :
    ((X.m * X.n ^ 4)⁻¹ * (X.t * u) * (X.m * X.n ^ 4)) * (X.m * u) =
        (X.m * u) * ((X.m * X.n ^ 4)⁻¹ * (X.t * u) * (X.m * X.n ^ 4)) ∨
      ((X.m * X.n ^ 4)⁻¹ * (X.t * u) * (X.m * X.n ^ 4)) *
          ((X.n⁻¹ * X.t * X.n)⁻¹ * (X.m * u) * (X.n⁻¹ * X.t * X.n)) =
        ((X.n⁻¹ * X.t * X.n)⁻¹ * (X.m * u) * (X.n⁻¹ * X.t * X.n)) *
          ((X.m * X.n ^ 4)⁻¹ * (X.t * u) * (X.m * X.n ^ 4)) := by
  have hst : s ≠ X.t := by rintro rfl; exact X.t_not_inv_n hsn
  have hu2 : u * u = 1 := (orderOf_eq_two_iff.mp hu).1
  have htinv : X.t⁻¹ = X.t := X.h.t_inv
  have hct : X.m * u * X.t = X.t * (X.m * u) := by
    rw [mul_assoc, hut, ← mul_assoc, X.m_t, mul_assoc]
  rw [X.conj_tn_eq hct]
  obtain ⟨x, hx⟩ : ∃ x, x = X.t * u := ⟨_, rfl⟩
  rw [← hx] at hxF hpat ⊢
  have hx2 : x * x = 1 := by
    rw [hx]
    calc X.t * u * (X.t * u) = X.t * (u * X.t) * u := by group
      _ = 1 := by rw [hut, ← mul_assoc, X.t_mul_t, one_mul, hu2]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxm : x * X.m * x⁻¹ = X.m⁻¹ := by
    have htmt : X.t * X.m * X.t⁻¹ = X.m := by rw [← X.m_t, mul_inv_cancel_right]
    rw [hx]
    calc X.t * u * X.m * (X.t * u)⁻¹ = X.t * (u * X.m * u⁻¹) * X.t⁻¹ := by group
      _ = X.m⁻¹ := by rw [hum, ← inv_inj, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv,
        ← mul_assoc, htmt]
  have hxo : orderOf x = 2 := orderOf_eq_two_iff.mpr ⟨hx2, fun h1 => by
    have : u = X.t := by
      have h2 : u = X.t * (X.t * u) := by rw [← mul_assoc, X.t_mul_t, one_mul]
      rw [h2, ← hx, h1, mul_one]
    rw [this, ← X.m_t, mul_inv_cancel_right] at hum
    apply X.m_ne_one
    have hm2 : X.m * X.m = 1 := by
      calc X.m * X.m = X.m * X.m⁻¹ := by rw [← hum]
        _ = 1 := mul_inv_cancel _
    calc X.m = X.m ^ 3 * (X.m * X.m)⁻¹ := by group
      _ = 1 := by rw [X.m_pow_three, hm2, inv_one, one_mul]⟩
  obtain ⟨g, hg⟩ : ∃ g, g = X.m * X.n ^ 4 := ⟨_, rfl⟩
  rw [← hg]
  have hmt : X.m⁻¹ * X.t * X.m = X.t := by
    rw [mul_assoc, ← X.m_t, ← mul_assoc, inv_mul_cancel, one_mul]
  have hge4 : g⁻¹ * X.t * g = X.e 4 := by
    rw [hg]
    calc (X.m * X.n ^ 4)⁻¹ * X.t * (X.m * X.n ^ 4) =
        (X.n ^ 4)⁻¹ * (X.m⁻¹ * X.t * X.m) * X.n ^ 4 := by group
      _ = X.e 4 := by rw [hmt]; rfl
  have hgt : g * X.t * g⁻¹ = X.e 5 := by
    rw [hg]
    calc X.m * X.n ^ 4 * X.t * (X.m * X.n ^ 4)⁻¹ = X.m * (X.n ^ 4 * X.t * (X.n ^ 4)⁻¹) * X.m⁻¹ :=
          by group
      _ = X.e 5 := by rw [X.n4_t, X.m_e_inv, ← X.e_mod, show 4 * 3 % 7 = 5 from rfl]
  obtain ⟨b, hb⟩ : ∃ b, b = g⁻¹ * x * g := ⟨_, rfl⟩
  rw [← hb]
  obtain ⟨p, hp⟩ : ∃ p, p = X.t * b := ⟨_, rfl⟩
  have hpn : p = g⁻¹ * (X.e 5 * x) * g := by
    rw [hp, hb, ← hgt]; group
  have he5x : X.e 5 * x = X.e 5 * (x * X.e 5) * (X.e 5)⁻¹ := by group
  obtain ⟨hp5, hp1⟩ : p ^ 5 = 1 ∧ p ≠ 1 := by
    obtain ⟨h5, h1⟩ := conj_pow_five (X.e 5) hpat.1.1 hpat.1.2
    rw [← he5x] at h5 h1
    rw [hpn]
    have := conj_pow_five g⁻¹ h5 h1
    rwa [inv_inv] at this
  have hxt : x * X.t = X.t * x := by
    rw [hx, mul_assoc, hut]
  have hb2 : b * b = 1 := by
    rw [hb]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hx2]; group
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hyb : X.e 4 * b = b * X.e 4 := by
    rw [← hge4, hb]
    calc g⁻¹ * X.t * g * (g⁻¹ * x * g) = g⁻¹ * (X.t * x) * g := by group
      _ = g⁻¹ * (x * X.t) * g := by rw [hxt]
      _ = g⁻¹ * x * g * (g⁻¹ * X.t * g) := by group
  have hyp : X.e 4 * p = p * X.e 4 := by
    rw [hp, ← mul_assoc, X.e_comm_t, mul_assoc, hyb, ← mul_assoc]
  have htp : X.t * p * X.t⁻¹ = p⁻¹ := by
    rw [hp, mul_inv_rev, hbinv, htinv, ← mul_assoc, X.t_mul_t, one_mul]
  obtain ⟨q, hq3, hq1, hqp, hyq, htq⟩ := X.exists_q hp5 hp1 (X.orderOf_e 4) hyp htp
  have he6 : X.e 6 = X.t * X.e 4 := by rw [X.e4_eq, ← mul_assoc, X.t_mul_t, one_mul]
  rcases htq with htq | htq
  ·
    have hqt : q * X.t = X.t * q := (mul_inv_eq_iff_eq_mul.mp htq).symm
    have hqF : q ∈ X.F := X.h.mem_F_of_odd (Subgroup.mem_centralizer_singleton_iff.mpr hqt)
      (by rw [orderOf_eq_prime hq3 hq1]; decide)
    have hqb : q * b = b * q := by
      have hb' : b = X.t * p := by rw [hp, ← mul_assoc, X.t_mul_t, one_mul]
      rw [hb', ← mul_assoc, hqt, mul_assoc, hqp, mul_assoc]
    have he6q : X.e 6 * q * (X.e 6)⁻¹ = q⁻¹ := by
      rw [he6]
      calc X.t * X.e 4 * q * (X.t * X.e 4)⁻¹ = X.t * (X.e 4 * q * (X.e 4)⁻¹) * X.t⁻¹ := by group
        _ = q⁻¹ := by rw [hyq, show X.t * q⁻¹ * X.t⁻¹ = (X.t * q * X.t⁻¹)⁻¹ by group, htq]
    have hd : X.m * x * X.e 6 = X.m * u * X.e 4 := by
      rw [hx, he6]
      calc X.m * (X.t * u) * (X.t * X.e 4) = X.m * (X.t * u * X.t) * X.e 4 := by group
        _ = X.m * u * X.e 4 := by
          rw [mul_assoc X.t u X.t, hut, ← mul_assoc X.t X.t u, X.t_mul_t, one_mul]
    have hsplit := A5Sub.split_fact X.h.iso (x := X.e 6) (a := X.m * x) (w := X.e 5) (q := q)
      X.e6_mem_F (X.F.mul_mem X.m_mem_F hxF) X.e5_mem_F hqF
      (by rw [pow_two]; exact X.e_mul_self 6) (X.e_ne_one 6) (X.involution_conj_m hx2 hxm)
      (X.m_mul_ne_one hxo) hpat.2.2.2.1 hpat.2.2.2.2 (by rw [pow_two]; exact X.e_mul_self 5)
      (X.e_ne_one 5) (X.e_comm 5 6) (X.e_ne (by norm_num) (by norm_num)) hq3 hq1 he6q
    have hy2 := X.e_mul_self 4
    have hd' : X.e 5 * (X.m * x * X.e 6) * (X.e 5)⁻¹ = X.e 5 * (X.m * u) * (X.e 5)⁻¹ * X.e 4 := by
      rw [hd, X.conj_e5_mul]
    rcases hsplit with h | h | h | h
    · exact Or.inl (comm_of_split hy2 hyb hqb hd (Or.inl h))
    · exact Or.inl (comm_of_split hy2 hyb hqb hd (Or.inr h))
    · exact Or.inr (comm_of_split hy2 hyb hqb hd' (Or.inl h))
    · exact Or.inr (comm_of_split hy2 hyb hqb hd' (Or.inr h))
  ·
    exfalso
    have hrq : X.e 6 * q = q * X.e 6 := by
      have h1 : X.e 6 * q * (X.e 6)⁻¹ = q := by
        rw [he6]
        calc X.t * X.e 4 * q * (X.t * X.e 4)⁻¹ = X.t * (X.e 4 * q * (X.e 4)⁻¹) * X.t⁻¹ := by
              group
          _ = q := by rw [hyq]; exact inv_conj_of_conj htq
      exact mul_inv_eq_iff_eq_mul.mp h1
    have hyr : X.e 4 * X.e 6 = X.e 6 * X.e 4 := X.e_comm 4 6
    have htr := X.transfer hs hsm hst hu hut hus hum hq3 hq1 hrq hp5 hp1 hqp hyr hyp hyq
      X.ninv_e6
    have hne4 : X.n⁻¹ * X.e 4 * X.n⁻¹⁻¹ = X.e 5 := by
      calc X.n⁻¹ * X.e 4 * X.n⁻¹⁻¹ = X.e 1 * X.t := by
            rw [X.e4_eq, X.e1_eq, ← X.e6_eq]; group
        _ = X.e 5 := by rw [X.e_comm_t, X.e5_eq]
    rw [hne4] at htr
    have huF := htr.mp X.e5_mem_F
    apply X.t_not_mem_F
    have : X.t = x * u⁻¹ := by rw [hx, mul_inv_cancel_right]
    rw [this]
    exact X.F.mul_mem hxF (X.F.inv_mem huF)

end Setup

end CFSG.Walter.J1Recog
