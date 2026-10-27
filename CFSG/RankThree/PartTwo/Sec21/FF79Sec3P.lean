module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3T
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.S3

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn

local notation "Z3" => ZMod 3 × ZMod 3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_zpowers_of_pow {p : ℕ} [hp : Fact p.Prime] {x : G} {m : ℕ}
    (hx : x ^ (p ^ m) = 1) : IsPGroup p (Subgroup.zpowers x) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hx)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

namespace Ctx

variable {b : G} {J B : Subgroup G} {u v r₁ r₂ w : G} (C : Ctx b J B u v r₁ r₂ w)
include C

theorem B_pgroup : IsPGroup 3 B := IsPGroup.of_card (n := 3) C.D.hE.2

theorem exists_P : ∃ P : Subgroup G, IsSylowOf 3 P (Nor B) ∧ B ≤ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_sylowOf_le Subgroup.le_normalizer C.B_pgroup

variable {P : Subgroup G}

theorem P_le_T (hP : IsSylowOf 3 P (Nor B)) : P ≤ T b B (R u v) := C.pgroup_le_T hP.2.1 hP.1

theorem P_syl_T (hP : IsSylowOf 3 P (Nor B)) : IsSylowOf 3 P (T b B (R u v)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isSylowOf_mono hP (C.P_le_T hP) C.T_le_N

theorem pelt_of_P (hP : IsSylowOf 3 P (Nor B)) {x : G} (hx : x ∈ P) :
    ∃ m : ℕ, x ^ (3 ^ m) = 1 := by
  obtain ⟨m, hm⟩ := hP.2.1 ⟨x, hx⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

theorem mem_B_of_cen {x : G} (hxN : x ∈ Nor B) (hxb : x * b = b * x) {m : ℕ}
    (hm : x ^ (3 ^ m) = 1) : x ∈ B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact mem_of_pelt C.B_pgroup C.D.hB.1 C.D.hB.2.2
    (Subgroup.mem_centralizer_singleton_iff.mpr hxb) hxN hm

theorem P_cen (hP : IsSylowOf 3 P (Nor B)) {x : G} (hx : x ∈ P) (hxb : x * b = b * x) :
    x ∈ B := by
  obtain ⟨m, hm⟩ := C.pelt_of_P hP hx
  exact C.mem_B_of_cen (hP.1 hx) hxb hm

theorem θ_eq_one_mem_B (hP : IsSylowOf 3 P (Nor B)) {x : G} (hx : x ∈ P) (h : θ b x = 1) :
    x ∈ B := by
  refine C.P_cen hP hx ?_
  have : x * b * x⁻¹ * b⁻¹ = 1 := h
  calc x * b = (x * b * x⁻¹ * b⁻¹) * b * x := by group
    _ = b * x := by rw [this, one_mul]

theorem bpow_T (k : ℕ) : b ^ k ∈ T b B (R u v) := (C.cenB_le_T) (Subgroup.pow_mem _ (by
  rw [Subgroup.mem_centralizer_iff]; intro y hy; exact C.comm_B hy C.bB) k)

theorem θ_bpow (k : ℕ) : θ b (b ^ k) = 1 := by unfold θ; group

theorem θ_surj_P (hP : IsSylowOf 3 P (Nor B)) {t : G} (ht : t ∈ R u v) :
    ∃ x ∈ P, θ b x = t := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs, hst⟩ := C.θ_surj ht
  obtain ⟨a, m', hm', hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos s).ne' 3 (by norm_num)
  have hx₀T : s ^ (m' ^ 2) ∈ T b B (R u v) := Subgroup.pow_mem _ hs _
  have hx₀3 : (s ^ (m' ^ 2)) ^ (3 ^ a) = 1 := by
    rw [← pow_mul, show m' ^ 2 * 3 ^ a = orderOf s * m' by rw [hn]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  have hθx₀ : θ b (s ^ (m' ^ 2)) = t := by
    rw [C.θ_pow hs, hst, pow_eq_pow_mod _ (C.pow3_R ht)]
    have h1 : m' % 3 = 1 ∨ m' % 3 = 2 := by omega
    have : m' ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod]; rcases h1 with h | h <;> rw [h]
    rw [this, pow_one]
  obtain ⟨k, hk, hkx⟩ := L41.exists_conj_le_sylowOf_p (C.P_syl_T hP)
    ((Subgroup.zpowers_le).mpr hx₀T) (isPGroup_zpowers_of_pow hx₀3)
  exact ⟨_, hkx _ (Subgroup.mem_zpowers _), by rw [C.θ_conj_T hk hx₀T, hθx₀]⟩

theorem realize (hP : IsSylowOf 3 P (Nor B)) {j : G} (hj : j ∈ Nor B) {n : ℕ}
    (hjb : j * b * j⁻¹ = b ^ n) :
    ∃ m ∈ Nor P, m ∈ Nor B ∧ m * b * m⁻¹ = b ^ n ∧
      ∀ x ∈ R u v, m * x * m⁻¹ = j * x * j⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hjT : j ∈ Nor (T b B (R u v)) := L41.mem_nor_of_forall fun y hy => C.T_normal hj hy
  obtain ⟨k, hk, hkj⟩ := exists_frattini (C.P_syl_T hP) hjT
  have e1 : (k * j) * b * (k * j)⁻¹ = θ b k ^ n * b ^ n := by
    calc (k * j) * b * (k * j)⁻¹ = k * (j * b * j⁻¹) * k⁻¹ := by group
      _ = (k * b * k⁻¹) ^ n := by rw [hjb, conj_pow]
      _ = (θ b k * b) ^ n := by rw [C.conj_b_T hk]
      _ = θ b k ^ n * b ^ n := (Commute.mul_pow (C.comm_bR (C.θ_mem hk)).symm _)
  obtain ⟨q, hq, hθq⟩ := C.θ_surj_P hP (Subgroup.inv_mem _ (C.θ_mem hk))
  have hqT := C.P_le_T hP hq
  refine ⟨q * (k * j), Subgroup.mul_mem _ (Subgroup.le_normalizer hq) hkj,
    Subgroup.mul_mem _ (C.T_le_N hqT) (Subgroup.mul_mem _ (C.T_le_N hk) hj), ?_, ?_⟩
  · calc q * (k * j) * b * (q * (k * j))⁻¹ = q * ((k * j) * b * (k * j)⁻¹) * q⁻¹ := by group
      _ = (q * θ b k ^ n * q⁻¹) * (q * b * q⁻¹) ^ n := by rw [e1, conj_pow]; group
      _ = θ b k ^ n * (θ b q * b) ^ n := by
          rw [C.T_cen hqT (Subgroup.pow_mem _ (C.θ_mem hk) _), C.conj_b_T hqT]
      _ = θ b k ^ n * (θ b q ^ n * b ^ n) := by
          rw [(Commute.mul_pow (C.comm_bR (C.θ_mem hqT)).symm _)]
      _ = b ^ n := by rw [hθq, inv_pow, ← mul_assoc, mul_inv_cancel, one_mul]
  · intro x hx
    have h1 := C.nor0 hj hx
    calc q * (k * j) * x * (q * (k * j))⁻¹ = q * (k * (j * x * j⁻¹) * k⁻¹) * q⁻¹ := by group
      _ = j * x * j⁻¹ := by rw [C.T_cen hk h1, C.T_cen hqT h1]

theorem key_det (hP : IsSylowOf 3 P (Nor B)) {x₀ y₀ β₁ β₂ : G} (hx₀ : x₀ ∈ P) (hy₀ : y₀ ∈ P)
    (hβ₁ : β₁ ∈ B) (hβ₂ : β₂ ∈ B) (hc : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ ∈ B) :
    (x₀⁻¹ * β₁) * (y₀ * β₂) * (x₀⁻¹ * β₁)⁻¹ * (y₀ * β₂)⁻¹ * (x₀ * y₀ * x₀⁻¹ * y₀⁻¹) ∈
      R u v := by
  set c := x₀ * y₀ * x₀⁻¹ * y₀⁻¹ with hcdef
  have hx₀T := C.P_le_T hP hx₀
  have hy₀T := C.P_le_T hP hy₀
  set s₁ := y₀⁻¹ * β₁ * y₀⁻¹⁻¹ * β₁⁻¹ with hs₁
  set s₂ := x₀⁻¹ * β₂ * x₀⁻¹⁻¹ * β₂⁻¹ with hs₂
  set s₃ := x₀⁻¹ * c⁻¹ * x₀⁻¹⁻¹ * c⁻¹⁻¹ with hs₃
  have h1 : s₁ ∈ R u v := C.T_comm_B (Subgroup.inv_mem _ hy₀T) hβ₁
  have h2 : s₂ ∈ R u v := C.T_comm_B (Subgroup.inv_mem _ hx₀T) hβ₂
  have h3 : s₃ ∈ R u v := C.T_comm_B (Subgroup.inv_mem _ hx₀T) (Subgroup.inv_mem _ hc)
  have cen : ∀ {g : G}, g ∈ T b B (R u v) → ∀ {s : G}, s ∈ R u v → s * g = g * s :=
    fun hg _ hs => Subgroup.mem_centralizer_iff.mp hg.2.1 _ hs
  have hβ : β₂ * β₁⁻¹ = β₁⁻¹ * β₂ := C.comm_B hβ₂ (Subgroup.inv_mem _ hβ₁)
  have e1 : β₁ * y₀ * β₁⁻¹ = y₀ * s₁ := by rw [hs₁]; group
  have e2 : β₂ * x₀ * β₂⁻¹ = x₀ * s₂ := by rw [hs₂]; group
  have hs1x : s₁ * x₀ = x₀ * s₁ := cen hx₀T h1
  have hs2y : s₂ * y₀⁻¹ = y₀⁻¹ * s₂ := cen (Subgroup.inv_mem _ hy₀T) h2
  have hs1y : s₁ * y₀⁻¹ = y₀⁻¹ * s₁ := cen (Subgroup.inv_mem _ hy₀T) h1
  have hs2c : s₂ * c = c * s₂ := C.comm_B (C.R_le_B h2) hc
  have hs1c : s₁ * c = c * s₁ := C.comm_B (C.R_le_B h1) hc
  have key : (x₀⁻¹ * β₁) * (y₀ * β₂) * (x₀⁻¹ * β₁)⁻¹ * (y₀ * β₂)⁻¹ * c = s₃ * s₁ * s₂ := by
    calc (x₀⁻¹ * β₁) * (y₀ * β₂) * (x₀⁻¹ * β₁)⁻¹ * (y₀ * β₂)⁻¹ * c
        = x₀⁻¹ * β₁ * y₀ * (β₂ * β₁⁻¹) * x₀ * β₂⁻¹ * y₀⁻¹ * c := by group
      _ = x₀⁻¹ * β₁ * y₀ * (β₁⁻¹ * β₂) * x₀ * β₂⁻¹ * y₀⁻¹ * c := by rw [hβ]
      _ = x₀⁻¹ * (β₁ * y₀ * β₁⁻¹) * (β₂ * x₀ * β₂⁻¹) * y₀⁻¹ * c := by group
      _ = x₀⁻¹ * (y₀ * s₁) * (x₀ * s₂) * y₀⁻¹ * c := by rw [e1, e2]
      _ = x₀⁻¹ * y₀ * (s₁ * x₀) * (s₂ * y₀⁻¹) * c := by group
      _ = x₀⁻¹ * y₀ * (x₀ * s₁) * (y₀⁻¹ * s₂) * c := by rw [hs1x, hs2y]
      _ = x₀⁻¹ * y₀ * x₀ * (s₁ * y₀⁻¹) * (s₂ * c) := by group
      _ = x₀⁻¹ * y₀ * x₀ * (y₀⁻¹ * s₁) * (c * s₂) := by rw [hs1y, hs2c]
      _ = x₀⁻¹ * y₀ * x₀ * y₀⁻¹ * (s₁ * c) * s₂ := by group
      _ = x₀⁻¹ * y₀ * x₀ * y₀⁻¹ * (c * s₁) * s₂ := by rw [hs1c]
      _ = s₃ * s₁ * s₂ := by rw [hs₃, hcdef]; group
  rw [key]
  exact (R u v).mul_mem ((R u v).mul_mem h3 h1) h2

theorem bpow_comm_T {g : G} (hg : g ∈ T b B (R u v)) (l : ℕ) :
    b ^ l * g = g * (θ b g)⁻¹ ^ l * b ^ l := by
  have h1 : g⁻¹ * b * g = (θ b g)⁻¹ * b := by
    have := C.conj_b_T hg
    calc g⁻¹ * b * g = g⁻¹ * (θ b g)⁻¹ * (g * b * g⁻¹) * g := by rw [this]; group
      _ = (g⁻¹ * (θ b g)⁻¹ * g) * b := by group
      _ = (θ b g)⁻¹ * b := by
          rw [show g⁻¹ * (θ b g)⁻¹ * g = (θ b g)⁻¹ by
            have := C.T_cen (Subgroup.inv_mem _ hg) (Subgroup.inv_mem _ (C.θ_mem hg))
            simpa using this]
  have h2 : g⁻¹ * b ^ l * g = (θ b g)⁻¹ ^ l * b ^ l := by
    have : g⁻¹ * b ^ l * g = (g⁻¹ * b * g) ^ l := by
      rw [show g⁻¹ * b * g = g⁻¹ * b * g⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
    rw [this, h1]
    exact Commute.mul_pow (C.comm_bR (Subgroup.inv_mem _ (C.θ_mem hg))).symm _
  calc b ^ l * g = g * (g⁻¹ * b ^ l * g) := by group
    _ = g * (θ b g)⁻¹ ^ l * b ^ l := by rw [h2]; group

theorem exists_comm_pair (hP : IsSylowOf 3 P (Nor B)) (hBP : B ≤ P) :
    ∃ x' ∈ P, ∃ y' ∈ P, θ b x' = u ∧ θ b y' = v ∧ x' * y' = y' * x' := by
  obtain ⟨x₀, hx₀, hθx⟩ := C.θ_surj_P hP C.uR
  obtain ⟨y₀, hy₀, hθy⟩ := C.θ_surj_P hP C.vR
  have hx₀T := C.P_le_T hP hx₀
  have hy₀T := C.P_le_T hP hy₀
  set c := x₀ * y₀ * x₀⁻¹ * y₀⁻¹ with hcdef
  have hcP : c ∈ P := P.mul_mem (P.mul_mem (P.mul_mem hx₀ hy₀) (P.inv_mem hx₀)) (P.inv_mem hy₀)
  have hcT := C.P_le_T hP hcP
  have huv : u * v = v * u := C.comm_R C.uR C.vR
  have hθc : θ b c = 1 := by
    have t1 := C.θ_mul ((T b B (R u v)).mul_mem ((T b B (R u v)).mul_mem hx₀T hy₀T)
      ((T b B (R u v)).inv_mem hx₀T)) ((T b B (R u v)).inv_mem hy₀T)
    have t2 := C.θ_mul ((T b B (R u v)).mul_mem hx₀T hy₀T) ((T b B (R u v)).inv_mem hx₀T)
    have t3 := C.θ_mul hx₀T hy₀T
    rw [hcdef, t1, t2, t3, C.θ_inv hx₀T, C.θ_inv hy₀T, hθx, hθy, huv]; group
  have hcB : c ∈ B := C.θ_eq_one_mem_B hP hcP hθc
  obtain ⟨m, hmP, hmB, hmb, hmR⟩ := C.realize hP C.r₁N (n := 1)
    (by rw [pow_one]; exact C.conj_b_of_J C.r₁J)
  rw [pow_one] at hmb
  have hconjP : ∀ {x : G}, x ∈ P → m * x * m⁻¹ ∈ P := fun hx =>
    (Subgroup.mem_normalizer_iff.mp hmP _).mp hx
  have hr₁u : r₁ * u * r₁⁻¹ = u ^ 2 := by rw [C.nd.r₁a]; group
  have hr₁v : r₁ * v * r₁⁻¹ = v := by rw [C.nd.r₁b]; group
  set x₁ := m * x₀ * m⁻¹ with hx₁
  set y₁ := m * y₀ * m⁻¹ with hy₁
  have hx₁P : x₁ ∈ P := hconjP hx₀
  have hy₁P : y₁ ∈ P := hconjP hy₀
  have hθx₁ : θ b x₁ = u ^ 2 := by
    rw [hx₁, C.θ_conj_of_cen m x₀ hmb, hθx, hmR u C.uR, hr₁u]
  have hθy₁ : θ b y₁ = v := by
    rw [hy₁, C.θ_conj_of_cen m y₀ hmb, hθy, hmR v C.vR, hr₁v]
  have hβ₁P : x₀ * x₁ ∈ P := P.mul_mem hx₀ hx₁P
  have hβ₁B : x₀ * x₁ ∈ B := by
    refine C.θ_eq_one_mem_B hP hβ₁P ?_
    rw [C.θ_mul hx₀T (C.P_le_T hP hx₁P), hθx, hθx₁, ← pow_succ', C.pow3_R C.uR]
  have hβ₂P : y₀⁻¹ * y₁ ∈ P := P.mul_mem (P.inv_mem hy₀) hy₁P
  have hβ₂B : y₀⁻¹ * y₁ ∈ B := by
    refine C.θ_eq_one_mem_B hP hβ₂P ?_
    rw [C.θ_mul ((T b B (R u v)).inv_mem hy₀T) (C.P_le_T hP hy₁P), C.θ_inv hy₀T, hθy, hθy₁,
      inv_mul_cancel]
  have hk1 : m * c * m⁻¹ * c ∈ R u v := by
    have := C.key_det hP hx₀ hy₀ hβ₁B hβ₂B (hcdef ▸ hcB)
    have e : m * c * m⁻¹ = (x₀⁻¹ * (x₀ * x₁)) * (y₀ * (y₀⁻¹ * y₁)) * (x₀⁻¹ * (x₀ * x₁))⁻¹ *
        (y₀ * (y₀⁻¹ * y₁))⁻¹ := by rw [hcdef, hx₁, hy₁]; group
    rw [e]; exact this
  have hk2 : m * c * m⁻¹ * c⁻¹ ∈ R u v := by
    obtain ⟨k, q, hkq⟩ := (C.mem_B_iff).mp hcB
    have hq := ψ_mem C.E q
    have hmq := C.nor0 hmB hq
    have hbk : m * b ^ k.val * m⁻¹ = b ^ k.val := by rw [← conj_pow, hmb]
    have e : m * c * m⁻¹ * c⁻¹ = b ^ k.val * ((m * ψ u v q * m⁻¹) * (ψ u v q)⁻¹) *
        (b ^ k.val)⁻¹ := by
      rw [hkq]
      calc m * (b ^ k.val * ψ u v q) * m⁻¹ * (b ^ k.val * ψ u v q)⁻¹ =
          (m * b ^ k.val * m⁻¹) * (m * ψ u v q * m⁻¹) * (ψ u v q)⁻¹ * (b ^ k.val)⁻¹ := by group
        _ = _ := by rw [hbk]; group
    have hr : (m * ψ u v q * m⁻¹) * (ψ u v q)⁻¹ ∈ R u v := (R u v).mul_mem hmq ((R u v).inv_mem hq)
    rw [e, (Commute.pow_left (C.comm_bR hr) k.val).eq]
    simpa using hr
  have hcc : c * c ∈ R u v := by
    have : c * c = (m * c * m⁻¹ * c⁻¹)⁻¹ * (m * c * m⁻¹ * c) := by group
    rw [this]; exact (R u v).mul_mem ((R u v).inv_mem hk2) hk1
  have hcR : c ∈ R u v := by
    have h3 := C.pow3_B hcB
    have : (c * c) * (c * c) = c := by
      calc (c * c) * (c * c) = c ^ 3 * c := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = c := by rw [h3, one_mul]
    rw [← this]; exact (R u v).mul_mem hcc hcc
  obtain ⟨q, hq⟩ := exists_ψ C.E hcR
  have hkey : ∀ q : Z3, q + q.2.val • (-((0 : ZMod 3), (1 : ZMod 3))) =
      (-q.1).val • (-((1 : ZMod 3), (0 : ZMod 3))) := by decide
  set l := q.2.val
  set k := (-q.1).val
  have hbP : ∀ n : ℕ, b ^ n ∈ P := fun n => P.pow_mem (hBP C.bB) n
  refine ⟨x₀ * b ^ l, P.mul_mem hx₀ (hbP l), y₀ * b ^ k, P.mul_mem hy₀ (hbP k), ?_, ?_, ?_⟩
  · rw [C.θ_mul hx₀T (C.bpow_T l), C.θ_bpow, hθx, mul_one]
  · rw [C.θ_mul hy₀T (C.bpow_T k), C.θ_bpow, hθy, mul_one]
  · have hc' : x₀ * y₀ = c * (y₀ * x₀) := by rw [hcdef]; group
    have hcy : c * (y₀ * x₀) = (y₀ * x₀) * c :=
      Subgroup.mem_centralizer_iff.mp ((T b B (R u v)).mul_mem hy₀T hx₀T).2.1 _ hcR
    have hψeq : c * v⁻¹ ^ l = u⁻¹ ^ k := by
      have hv : v⁻¹ ^ l = ψ u v (l • (-((0 : ZMod 3), (1 : ZMod 3)))) := by
        rw [ψ_nsmul C.E, ψ_neg C.E, ψ_01]
      have hu : u⁻¹ ^ k = ψ u v (k • (-((1 : ZMod 3), (0 : ZMod 3)))) := by
        rw [ψ_nsmul C.E, ψ_neg C.E, ψ_10]
      rw [hq, hv, hu, ← ψ_add C.E, hkey q]
    calc x₀ * b ^ l * (y₀ * b ^ k) = x₀ * (b ^ l * y₀) * b ^ k := by group
      _ = x₀ * (y₀ * (θ b y₀)⁻¹ ^ l * b ^ l) * b ^ k := by rw [C.bpow_comm_T hy₀T]
      _ = (x₀ * y₀) * v⁻¹ ^ l * (b ^ l * b ^ k) := by rw [hθy]; group
      _ = (y₀ * x₀) * (c * v⁻¹ ^ l) * (b ^ l * b ^ k) := by rw [hc', hcy]; group
      _ = (y₀ * x₀) * u⁻¹ ^ k * (b ^ k * b ^ l) := by rw [hψeq, pow_mul_comm]
      _ = y₀ * (b ^ k * x₀) * b ^ l := by rw [C.bpow_comm_T hx₀T, hθx]; group
      _ = y₀ * b ^ k * (x₀ * b ^ l) := by group

end Ctx

end CFSG.RankThree.PartTwo.Sec21.FF79.S3
