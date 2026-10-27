module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3EF3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3E

open GoldAmL3

open scoped commutatorElement

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

omit [Finite D] in
theorem zpw_even {x : D} (hx : x * x = 1) (k : ℕ) : x ^ (2 * k) = 1 := by
  rw [pow_mul, pow_two, hx, one_pow]

omit [Finite D] in
theorem zpw_odd {x : D} (hx : x * x = 1) (k : ℕ) : x ^ (2 * k + 1) = x := by
  rw [pow_succ, pow_mul, pow_two, hx, one_pow, one_mul]

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

include g in
theorem KL_A {θ₂ r₀ r₁ r₂ : D} (h2 : θ₂ ∈ V)
    (hnf : ∃ e₀ e₁ e₂ : ℕ, r₀ = g.z₂ ^ e₁ * g.z₁ ^ e₂ ∧ r₁ = g.z₂ ^ e₀ * z ^ e₂ ∧
      r₂ = g.z₁ ^ e₀ * z ^ e₁)
    (E0 : g.a * θ₂ * g.a⁻¹ = r₀ * 1) (E1 : g.a * (1 : D) * g.a⁻¹ = r₁ * 1)
    (E2 : g.a * (1 : D) * g.a⁻¹ = r₂ * θ₂) : θ₂ = 1 := by
  obtain ⟨e₀, e₁, e₂, hr₀, hr₁, hr₂⟩ := hnf
  have s0 := c.z_sq
  have s1 := g.z₁_mul_z₁
  have s2 := g.z₂_mul_z₂
  subst hr₀ hr₁ hr₂
  rcases g.V_cases h2 with rfl | rfl | rfl | rfl <;>
  obtain ⟨k₀, rfl | rfl⟩ := Nat.even_or_odd' e₀ <;>
  obtain ⟨k₁, rfl | rfl⟩ := Nat.even_or_odd' e₁ <;>
  obtain ⟨k₂, rfl | rfl⟩ := Nat.even_or_odd' e₂ <;>
  simp [zpw_even s0, zpw_even s1, zpw_even s2, zpw_odd s0, zpw_odd s1, zpw_odd s2, g.a_conj_z,
    g.a_conj_z₁, g.a_conj_z₂, g.z_mul_z₁, g.z₂_mul_z,
    g.z₂_mul_z₁, g.z₁_ne_one, g.z₂_ne_one, c.z_ne_one, g.one_ne_z₁, g.one_ne_z₂, c.one_ne_z,
    g.z_ne_z₁, g.z_ne_z₂, g.z₁_ne_z₂, g.z₁_ne_z, g.z₂_ne_z, g.z₂_ne_z₁] at E0 E1 E2 ⊢

include g in
theorem KL_B {θ r₀ r₁ r₂ : D} (h : θ ∈ V)
    (hnf : ∃ e₀ e₁ e₂ : ℕ, r₀ = g.z₂ ^ e₁ * g.z₁ ^ e₂ ∧ r₁ = g.z₂ ^ e₀ * z ^ e₂ ∧
      r₂ = g.z₁ ^ e₀ * z ^ e₁)
    (E0 : g.a * θ * g.a⁻¹ = r₀ * 1) (E1 : g.a * (1 : D) * g.a⁻¹ = r₁ * θ)
    (E2 : g.a * θ * g.a⁻¹ = r₂ * θ) : θ = 1 := by
  obtain ⟨e₀, e₁, e₂, hr₀, hr₁, hr₂⟩ := hnf
  have s0 := c.z_sq
  have s1 := g.z₁_mul_z₁
  have s2 := g.z₂_mul_z₂
  subst hr₀ hr₁ hr₂
  rcases g.V_cases h with rfl | rfl | rfl | rfl <;>
  obtain ⟨k₀, rfl | rfl⟩ := Nat.even_or_odd' e₀ <;>
  obtain ⟨k₁, rfl | rfl⟩ := Nat.even_or_odd' e₁ <;>
  obtain ⟨k₂, rfl | rfl⟩ := Nat.even_or_odd' e₂ <;>
  simp [zpw_even s0, zpw_even s1, zpw_even s2, zpw_odd s0, zpw_odd s1, zpw_odd s2, g.a_conj_z,
    g.a_conj_z₁, g.a_conj_z₂, g.z₂_mul_z, g.z₂_mul_z₁, g.z₁_mul_z₂, g.z₁_mul_z, g.z_mul_z₂,
    g.z₁_ne_one, g.z₂_ne_one,
    c.z_ne_one, g.one_ne_z₁, g.one_ne_z₂, c.one_ne_z, g.z_ne_z₁, g.z_ne_z₂, g.z₁_ne_z₂,
    g.z₁_ne_z, g.z₂_ne_z, g.z₂_ne_z₁] at E0 E1 E2 ⊢

include g in
theorem A_eqs {q : D} (hq : q ∈ pCoreOf 2 A) :
    ∃ w ∈ Wsub A B V, g.a * ⁅g.u₂, q⁆ * g.a⁻¹ = ⁅g.u₀, w⁆ * ⁅g.u₀, q⁆ ∧
      g.a * ⁅g.u₀, q⁆ * g.a⁻¹ = ⁅g.u₁, w⁆ * ⁅g.u₁, q⁆ ∧
      g.a * ⁅g.u₁, q⁆ * g.a⁻¹ = ⁅g.u₂, w⁆ * ⁅g.u₂, q⁆ := by
  obtain ⟨w, hw, m, hm, hx⟩ := c.exists_mul_of_mem_sup (g.A_step g.a_mem hq)
  refine ⟨w, hw, ?_⟩
  have hwQ := c.W_le_Q hw
  have hmQ : m ∈ pCoreOf 2 A := (c.mem_M_iff.mp hm).1
  have hq' : g.a * q * g.a⁻¹ = (w * m) * q := by
    calc g.a * q * g.a⁻¹ = (g.a * q * g.a⁻¹ * q⁻¹) * q := by group
      _ = (w * m) * q := by rw [hx]
  have key : ∀ x ∈ Wsub A B V, ⁅x, g.a * q * g.a⁻¹⁆ = ⁅x, w⁆ * ⁅x, q⁆ := fun x hx' => by
    rw [hq', c.comm_mul_W hx' ((pCoreOf 2 A).mul_mem hwQ hmQ) hq, c.comm_mul_W hx' hwQ hmQ,
      c.comm_W_M hx' hm, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [← key _ g.u₀_mem_W, ← g.a_conj_u₂]
    exact conj_comm g.a g.u₂ q
  · rw [← key _ g.u₁_mem_W, ← g.a_conj_u₀]
    exact conj_comm g.a g.u₀ q
  · rw [← key _ g.u₂_mem_W, ← g.a_conj_u₁]
    exact conj_comm g.a g.u₁ q

include g in
theorem theta2_eq_one {q : D} (hq : q ∈ pCoreOf 2 A) (h0 : ⁅g.u₀, q⁆ = 1)
    (h1 : ⁅g.u₁, q⁆ = 1) : ⁅g.u₂, q⁆ = 1 := by
  obtain ⟨w, hw, E0, E1, E2⟩ := g.A_eqs hq
  rw [h0] at E0 E1
  rw [h1] at E1 E2
  exact g.KL_A (c.comm_W_Q g.u₂_mem_W hq) (g.nf_of_mem_W hw) E0 E1 E2

include g in
theorem theta1_eq_one {q : D} (hq : q ∈ pCoreOf 2 A) (h0 : ⁅g.u₀, q⁆ = 1)
    (h12 : ⁅g.u₁, q⁆ = ⁅g.u₂, q⁆) : ⁅g.u₁, q⁆ = 1 := by
  obtain ⟨w, hw, E0, E1, E2⟩ := g.A_eqs hq
  rw [h0] at E0 E1
  rw [← h12] at E0
  rw [← h12] at E2
  exact g.KL_B (c.comm_W_Q g.u₁_mem_W hq) (g.nf_of_mem_W hw) E0 E1 E2

include g in
theorem inf_conjSub_le_M : Ksub A B ⊓ conjSub g.a (Ksub A B) ≤ Msub A B V := by
  intro q hq
  obtain ⟨hqK, hqK'⟩ := hq
  have hqK'' : g.a⁻¹ * q * g.a ∈ Ksub A B := mem_conjSub.mp hqK'
  have hqQ : q ∈ pCoreOf 2 A := c.K_le_Q hqK
  have h0 : ⁅g.u₀, q⁆ = 1 :=
    comm_eq_one_iff.mpr (c.hyp.comm_of_mem_coreIn hqK g.u₀ g.u₀_mem)
  have h0' : ⁅g.u₀, g.a⁻¹ * q * g.a⁆ = 1 :=
    comm_eq_one_iff.mpr (c.hyp.comm_of_mem_coreIn hqK'' g.u₀ g.u₀_mem)
  have h1 : ⁅g.u₁, q⁆ = 1 := by
    have e := conj_comm g.a g.u₀ (g.a⁻¹ * q * g.a)
    rw [h0', g.a_conj_u₀] at e
    have e2 : g.a * (g.a⁻¹ * q * g.a) * g.a⁻¹ = q := by group
    rw [e2] at e
    simpa using e.symm
  have h2 := g.theta2_eq_one hqQ h0 h1
  exact g.mem_M_of_comm hqQ h0 h1 h2

end Gen

end GoldAmL3E

end F6

end CFSG.Quasithin
