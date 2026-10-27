module

public import CFSG.Quasithin.Vol2.KGFactC31NoM22FusBurnside
public import Mathlib.FieldTheory.Finite.Basic

public section

open scoped Pointwise

namespace CFSG.Quasithin.KGC31

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} {x : G} {r : ℕ}
    (hx : x ^ (p ^ r) = 1) : IsPGroup p (Subgroup.zpowers x) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨r, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, hx, one_zpow]

theorem normalizer_of_conj_le {K : Type*} [Group K] [Finite K] (H : Subgroup K) (b : K)
    (hb : ∀ h ∈ H, b * h * b⁻¹ ∈ H) : b ∈ Subgroup.normalizer (H : Set K) := by
  have hpow : ∀ t : ℕ, ∀ h ∈ H, b ^ t * h * (b ^ t)⁻¹ ∈ H := by
    intro t
    induction t with
    | zero => intro h hh; simpa using hh
    | succ t ih =>
      intro h hh
      rw [show b ^ (t + 1) * h * (b ^ (t + 1))⁻¹ = b * (b ^ t * h * (b ^ t)⁻¹) * b⁻¹ by
        rw [pow_succ']; group]
      exact hb _ (ih h hh)
  have hb1 : b ^ (orderOf b - 1) = b⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos b), pow_orderOf_eq_one]
  have hinv : ∀ h ∈ H, b⁻¹ * h * b⁻¹⁻¹ ∈ H := by
    intro h hh
    have := hpow (orderOf b - 1) h hh
    rwa [hb1] at this
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hb h hh
  · intro hh
    have := hinv _ hh
    simpa [mul_assoc] using this

theorem normalizer_map_subtype {G : Type*} [Group G] {A : Subgroup G} {Q : Subgroup A} {x : A}
    (hx : x ∈ Subgroup.normalizer (Q : Set A)) :
    (x : G) ∈ Subgroup.normalizer ((Subgroup.map A.subtype Q : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨x * z * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx z).1 hz, ?_⟩
    simp
  · intro hw
    obtain ⟨z, hz, hzw⟩ := Subgroup.mem_map.1 hw
    have hmem : x⁻¹ * z * x ∈ Q := by
      refine (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * z * x)).2 ?_
      rw [show x * (x⁻¹ * z * x) * x⁻¹ = z by group]
      exact hz
    refine Subgroup.mem_map.2 ⟨x⁻¹ * z * x, hmem, ?_⟩
    have hzw' : (z : G) = (x : G) * w * (x : G)⁻¹ := by
      rw [← hzw]
      rfl
    simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hzw']
    group

theorem frattini_elem {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (H : Subgroup K) (b : K) (hb : ∀ h ∈ H, b * h * b⁻¹ ∈ H)
    (q : K) (hq : q ∈ H) (r : ℕ) (hqr : q ^ (p ^ r) = 1) :
    ∃ Q : Subgroup K, IsPGroup p Q ∧ q ∈ Q ∧
      ∃ x y : K, x ∈ Subgroup.normalizer (Q : Set K) ∧ y ∈ H ∧ b = x * y := by
  have hbN : b ∈ Subgroup.normalizer (H : Set K) := normalizer_of_conj_le H b hb
  have hqL : q ∈ Subgroup.normalizer (H : Set K) := Subgroup.le_normalizer hq
  obtain ⟨qN, hqNq⟩ : ∃ qN : ↥(H.subgroupOf (Subgroup.normalizer (H : Set K))),
      ((qN : Subgroup.normalizer (H : Set K)) : K) = q :=
    ⟨⟨⟨q, hqL⟩, by rw [Subgroup.mem_subgroupOf]; exact hq⟩, rfl⟩
  have hqNpow : qN ^ (p ^ r) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp [Subgroup.coe_pow, hqNq, hqr]
  obtain ⟨P, hPle⟩ := (isPGroup_zpowers_of_pow_eq_one hqNpow).exists_le_sylow
  have hqP : qN ∈ (P : Subgroup ↥(H.subgroupOf (Subgroup.normalizer (H : Set K)))) :=
    hPle (Subgroup.mem_zpowers qN)
  have hfr := Sylow.normalizer_sup_eq_top P
  have hbtop : (⟨b, hbN⟩ : Subgroup.normalizer (H : Set K)) ∈
      (⊤ : Subgroup (Subgroup.normalizer (H : Set K))) := Subgroup.mem_top _
  rw [← hfr, Subgroup.mem_sup_of_normal_right] at hbtop
  obtain ⟨x', hx', y', hy', hxy⟩ := hbtop
  have hxy' : (x' : K) * (y' : K) = b := by
    have := congrArg Subtype.val hxy
    simpa using this
  refine ⟨Subgroup.map (Subgroup.normalizer (H : Set K)).subtype
    (Subgroup.map (H.subgroupOf (Subgroup.normalizer (H : Set K))).subtype
      (P : Subgroup ↥(H.subgroupOf (Subgroup.normalizer (H : Set K))))), ?_, ?_,
    (x' : K), (y' : K), ?_, ?_, hxy'.symm⟩
  · exact IsPGroup.map (IsPGroup.map P.isPGroup' _) _
  · refine Subgroup.mem_map.2 ⟨(H.subgroupOf (Subgroup.normalizer (H : Set K))).subtype qN,
      Subgroup.mem_map.2 ⟨qN, hqP, rfl⟩, ?_⟩
    exact hqNq
  · exact normalizer_map_subtype hx'
  · exact Subgroup.mem_subgroupOf.1 hy'

theorem exists_pPart_of_orderOf {K X : Type*} [Group K] [Finite K] [Group X] {p : ℕ}
    [hp : Fact p.Prime] (φ : K →* X) (a : K) (j : ℕ) (hj : orderOf (φ a) = p ^ j) :
    ∃ q : K, φ q = φ a ∧ ∃ r : ℕ, q ^ (p ^ r) = 1 := by
  obtain ⟨r, s, hps, hN⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos a).ne' p hp.out.ne_one
  have hcop : Nat.Coprime s (p ^ j) :=
    Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hps).symm
  have htot : 0 < Nat.totient (p ^ j) := Nat.totient_pos.2 (pow_pos hp.out.pos j)
  have hmod : s ^ Nat.totient (p ^ j) ≡ 1 [MOD p ^ j] := Nat.ModEq.pow_totient hcop
  have hsdvd : s ∣ s ^ Nat.totient (p ^ j) := dvd_pow_self s htot.ne'
  refine ⟨a ^ (s ^ Nat.totient (p ^ j)), ?_, r, ?_⟩
  · rw [map_pow]
    have h1 : φ a ^ (s ^ Nat.totient (p ^ j)) = φ a ^ 1 := by
      apply pow_eq_pow_iff_modEq.2
      rw [hj]
      exact hmod
    rw [h1, pow_one]
  · rw [← pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.1
    rw [hN, mul_comm (s ^ Nat.totient (p ^ j))]
    exact mul_dvd_mul_left (p ^ r) hsdvd

theorem section_fusion {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x)
    {m : ℕ} (hm : ∀ u ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
      u ^ m ∈ Subgroup.centralizer ((P : Subgroup G) : Set G))
    {A : Subgroup G} {X : Type*} [Group X] (φ : A →* X) (a b : A)
    (ha : ∃ n : ℕ, orderOf (φ a) = p ^ n) {k : ℕ} (hk : φ b * φ a * (φ b)⁻¹ = φ a ^ k) :
    φ a ^ (k ^ m) = φ a := by
  obtain ⟨j, hj⟩ := ha
  obtain ⟨q₀, hq₀, r, hqr⟩ := exists_pPart_of_orderOf φ a j hj
  obtain ⟨H, hH⟩ : ∃ H : Subgroup A, H = Subgroup.comap φ (Subgroup.zpowers (φ a)) :=
    ⟨_, rfl⟩
  have memH : ∀ h : A, h ∈ H ↔ φ h ∈ Subgroup.zpowers (φ a) := fun h => by
    rw [hH, Subgroup.mem_comap]
  have hb : ∀ h ∈ H, b * h * b⁻¹ ∈ H := by
    intro h hh
    rw [memH] at hh ⊢
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [map_mul, map_mul, map_inv, ← hi, ← conj_zpow, hk]
    exact Subgroup.mem_zpowers_iff.2 ⟨(k : ℤ) * i, by rw [zpow_mul, zpow_natCast]⟩
  have hqH : q₀ ∈ H := (memH q₀).2 (by rw [hq₀]; exact Subgroup.mem_zpowers _)
  obtain ⟨Q, hQp, hq₀Q, x, y, hxN, hyH, hbxy⟩ := frattini_elem H b hb q₀ hqH r hqr
  have hQG : IsPGroup p (Subgroup.map A.subtype Q) := hQp.map A.subtype
  have hxG := normalizer_map_subtype hxN
  have hq₀G : (q₀ : G) ∈ Subgroup.map A.subtype Q := Subgroup.mem_map.2 ⟨q₀, hq₀Q, rfl⟩
  have key := pow_centralizes_pgroup P hP hm (Subgroup.map A.subtype Q) hQG (x : G) hxG
    (q₀ : G) hq₀G
  have hcommA : x ^ m * q₀ = q₀ * x ^ m := Subtype.ext (by simpa using key)
  have hφcomm : φ x ^ m * φ a = φ a * φ x ^ m := by
    have := congrArg φ hcommA
    simpa [map_mul, map_pow, hq₀] using this
  have hyz : φ y ∈ Subgroup.zpowers (φ a) := (memH y).1 hyH
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hyz
  have hcomm_y : φ a * φ y = φ y * φ a := by
    rw [← hi]
    exact ((Commute.refl (φ a)).zpow_right i).eq
  have hxa : φ x * φ a * (φ x)⁻¹ = φ a ^ k := by
    have hx : φ x = φ b * (φ y)⁻¹ := by
      rw [hbxy, map_mul]
      group
    have hconjy : (φ y)⁻¹ * φ a * φ y = φ a := by
      rw [mul_assoc, hcomm_y, inv_mul_cancel_left]
    rw [hx]
    calc φ b * (φ y)⁻¹ * φ a * (φ b * (φ y)⁻¹)⁻¹
        = φ b * ((φ y)⁻¹ * φ a * φ y) * (φ b)⁻¹ := by group
      _ = φ b * φ a * (φ b)⁻¹ := by rw [hconjy]
      _ = φ a ^ k := hk
  have hxa' : φ x * φ a = φ a ^ k * φ x := by
    calc φ x * φ a = (φ x * φ a * (φ x)⁻¹) * φ x := by group
      _ = φ a ^ k * φ x := by rw [hxa]
  have hpowcomm : ∀ e : ℕ, φ x * φ a ^ e = φ a ^ (k * e) * φ x := by
    intro e
    induction e with
    | zero => simp
    | succ e ih =>
      calc φ x * φ a ^ (e + 1) = (φ x * φ a ^ e) * φ a := by rw [pow_succ, ← mul_assoc]
        _ = (φ a ^ (k * e) * φ x) * φ a := by rw [ih]
        _ = φ a ^ (k * e) * (φ x * φ a) := by rw [mul_assoc]
        _ = φ a ^ (k * e) * (φ a ^ k * φ x) := by rw [hxa']
        _ = φ a ^ (k * (e + 1)) * φ x := by
          rw [← mul_assoc, ← pow_add, show k * e + k = k * (e + 1) by ring]
  have hiter : ∀ t : ℕ, φ x ^ t * φ a = φ a ^ (k ^ t) * φ x ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      calc φ x ^ (t + 1) * φ a = φ x * (φ x ^ t * φ a) := by rw [pow_succ', mul_assoc]
        _ = φ x * (φ a ^ (k ^ t) * φ x ^ t) := by rw [ih]
        _ = (φ x * φ a ^ (k ^ t)) * φ x ^ t := by rw [mul_assoc]
        _ = φ a ^ (k * k ^ t) * φ x * φ x ^ t := by rw [hpowcomm, mul_assoc]
        _ = φ a ^ (k ^ (t + 1)) * φ x ^ (t + 1) := by
          rw [pow_succ' k t, pow_succ' (φ x) t, mul_assoc]
  have h1 : φ a ^ (k ^ m) * φ x ^ m = φ a * φ x ^ m := by
    rw [← hiter m]
    exact hφcomm
  exact mul_right_cancel h1

end CFSG.Quasithin.KGC31

end
