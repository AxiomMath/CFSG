module

public import CFSG.Quasithin.EmptyFaithful.S143KA
public import CFSG.Quasithin.EmptyFaithful.S143IF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

theorem isBasis_of_conditions {G : Type*} [Group G] {A : Subgroup G} {e0 e1 e2 e3 : G}
    (mem0 : e0 ∈ A) (mem1 : e1 ∈ A) (mem2 : e2 ∈ A) (mem3 : e3 ∈ A)
    (comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (sq : ∀ a ∈ A, a * a = 1) (card : Nat.card ↥A = 16)
    (c0 : e0 ≠ 1) (c1 : ∀ b0 : Bool, e1 ≠ (if b0 = true then e0 else 1))
    (c2 : ∀ b0 b1 : Bool, e2 ≠ (if b0 = true then e0 else 1) * (if b1 = true then e1 else 1))
    (c3 : ∀ b0 b1 b2 : Bool, e3 ≠ (if b0 = true then e0 else 1) * (if b1 = true then e1 else 1) *
      (if b2 = true then e2 else 1)) :
    IsBasis A e0 e1 e2 e3 := by
  refine ⟨mem0, mem1, mem2, mem3, comm, sq, card, ?_⟩
  have key : ∀ X e : G, X * X = 1 → X * e = 1 → e = X := fun X e hXX hXe => by
    rw [eq_inv_of_mul_eq_one_right hXe]
    exact inv_eq_of_mul_eq_one_right hXX
  have hite : ∀ (b : Bool) (e : G), e ∈ A → (if b = true then e else 1) ∈ A := by
    intro b e he; cases b <;> simp [he]
  rintro ⟨v0, v1, v2, v3⟩ hv
  unfold embV at hv
  simp only at hv
  have m0 := hite v0 e0 mem0
  have m1 := hite v1 e1 mem1
  have m2 := hite v2 e2 mem2
  have m3 := hite v3 e3 mem3
  have P2 := A.mul_mem m0 m1
  have P3 := A.mul_mem P2 m2
  cases v3
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hv
    cases v2
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hv
      cases v1
      · simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hv
        cases v0
        · rfl
        · exact absurd (by simpa using hv) c0
      · simp only [↓reduceIte] at hv
        exact absurd (key _ _ (sq _ m0) hv) (c1 v0)
    · simp only [↓reduceIte] at hv
      exact absurd (key _ _ (sq _ P2) hv) (c2 v0 v1)
  · simp only [↓reduceIte] at hv
    exact absurd (key _ _ (sq _ P3) hv) (c3 v0 v1 v2)

section X

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.exists_x : ∃ x ∈ yOfL22 T M, orderOf x = 3 := by
  have hR2 : IsPGroup 2 ↥(rOf T M) := c.hyp.sylow.1.to_le (rOf_le_T_of_hyp c.h1281)
  have hg3 : g * g * g ∈ rOf T M := by
    rw [rOf_eq_pCoreOf_sup c]
    exact c.h1281.mul_mul_mem_pCoreOf_sup c.nonab c.goodElt
  have hg3' : g ^ 3 ∈ rOf T M := by rw [pow_three']; exact hg3
  obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hR2) ⟨g ^ 3, hg3'⟩
  have hord : orderOf (g ^ 3) = 2 ^ i := (Subgroup.orderOf_mk _ _).symm.trans hi
  have hdvd : orderOf g ∣ 3 * 2 ^ i := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, ← hord, pow_orderOf_eq_one]
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hm3 : m ∣ 3 := by
    rw [hn] at hdvd
    have h2 : m ∣ 3 * 2 ^ i := (Dvd.intro_left _ rfl).trans hdvd
    exact (Nat.Coprime.pow_right i (Nat.coprime_two_right.mpr hm)).dvd_of_dvd_mul_right h2
  rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with rfl | rfl
  · exfalso
    have hcop : Nat.Coprime 3 (orderOf g) := by
      rw [hn, mul_one]
      exact Nat.Coprime.pow_right a (by norm_num)
    have hgR : g ∈ rOf T M :=
      (Subgroup.zpowers_le.mpr hg3') (A4.mem_zpowers_pow_of_coprime hcop)
    exact c.g_nmem (rOf_le_mcOf c hgR)
  · refine ⟨g ^ 2 ^ a, Subgroup.pow_mem _ c.g_mem _, ?_⟩
    have h2a : (2 ^ a : ℕ) ≠ 0 := by positivity
    rw [orderOf_pow' _ h2a, hn, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]

variable {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include hrW hrV hr2

theorem Counter.trace_eq_one {x : G} (hxI : x ∈ iTwo T M) (hx3 : x * x * x = 1)
    (hfpf : ∀ ρ ∈ rOf T M, x * ρ * x⁻¹ = ρ → ρ = 1) {e : G} (he : e ∈ c.Ac hrW hrV hr2) :
    e * (x * e * x⁻¹) * (x * x * e * (x * x)⁻¹) = 1 := by
  have hA : ∀ {γ y : G}, γ ∈ iTwo T M → y ∈ c.Ac hrW hrV hr2 → γ * y * γ⁻¹ ∈ c.Ac hrW hrV hr2 :=
    fun hγ hy => c.Ac_conj_mem hrW hrV hr2 hγ hy
  have hcomm : ∀ a ∈ c.Ac hrW hrV hr2, ∀ b ∈ c.Ac hrW hrV hr2, a * b = b * a := fun a ha b hb =>
    mul_comm_of_sq_eq_one (fun y hy => c.sq_Ac hrW hrV hr2 hy) ha hb
  have h1 : x * e * x⁻¹ ∈ c.Ac hrW hrV hr2 := hA hxI he
  have h2 : x * x * e * (x * x)⁻¹ ∈ c.Ac hrW hrV hr2 := by
    have := hA hxI h1
    have e' : x * (x * e * x⁻¹) * x⁻¹ = x * x * e * (x * x)⁻¹ := by group
    rwa [e'] at this
  have hfA : e * (x * e * x⁻¹) * (x * x * e * (x * x)⁻¹) ∈ c.Ac hrW hrV hr2 :=
    (c.Ac hrW hrV hr2).mul_mem ((c.Ac hrW hrV hr2).mul_mem he h1) h2
  apply hfpf _ (c.Ac_le_rOf hrW hrV hr2 hfA)
  have h3 : x * (x * x * e * (x * x)⁻¹) * x⁻¹ = e := by
    have : x * (x * x * e * (x * x)⁻¹) * x⁻¹ = (x * x * x) * e * (x * x * x)⁻¹ := by group
    rw [this, hx3]; group
  calc x * (e * (x * e * x⁻¹) * (x * x * e * (x * x)⁻¹)) * x⁻¹
      = (x * e * x⁻¹) * (x * (x * e * x⁻¹) * x⁻¹) * (x * (x * x * e * (x * x)⁻¹) * x⁻¹) := by
        group
    _ = (x * e * x⁻¹) * (x * x * e * (x * x)⁻¹) * e := by
        rw [h3]
        congr 2
        group
    _ = e * (x * e * x⁻¹) * (x * x * e * (x * x)⁻¹) := by
        rw [mul_assoc, hcomm _ h2 e he, ← mul_assoc, hcomm _ h1 e he]

theorem Counter.not_conj_eq {x : G} (hxI : x ∈ iTwo T M) (hx3 : x * x * x = 1)
    (hfpf : ∀ ρ ∈ rOf T M, x * ρ * x⁻¹ = ρ → ρ = 1) {e : G} (he : e ∈ VZ T M) :
    x * r * x⁻¹ ≠ e * r := by
  intro h
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := c.iTwo_le_normalizer_VZ hxI
  have hwV : x * e * x⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hxN e).mp he
  have heA : e ∈ c.Ac hrW hrV hr2 := c.VZ_le_Ac hrW hrV hr2 he
  have hwA : x * e * x⁻¹ ∈ c.Ac hrW hrV hr2 := c.VZ_le_Ac hrW hrV hr2 hwV
  have hrA : r ∈ c.Ac hrW hrV hr2 := c.r_mem_Ac hrW hrV hr2
  have hcomm : ∀ a ∈ c.Ac hrW hrV hr2, ∀ b ∈ c.Ac hrW hrV hr2, a * b = b * a := fun a ha b hb =>
    mul_comm_of_sq_eq_one (fun y hy => c.sq_Ac hrW hrV hr2 hy) ha hb
  have htr := c.trace_eq_one hrW hrV hr2 hxI hx3 hfpf heA
  have hx2 : x * x * e * (x * x)⁻¹ = x * (x * e * x⁻¹) * x⁻¹ := by group
  rw [hx2] at htr
  set w := x * e * x⁻¹ with hw
  set u := x * w * x⁻¹ with hu_def
  have heu : e * u = w := by
    have h1 : w * (e * u) = 1 := by
      rw [← mul_assoc, hcomm w hwA e heA]
      exact htr
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_eq_of_mul_eq_one_right (c.sq_Ac hrW hrV hr2 hwA)
  have hfix : x * (r * w) * x⁻¹ = r * w := by
    calc x * (r * w) * x⁻¹ = (x * r * x⁻¹) * (x * w * x⁻¹) := by group
      _ = (e * r) * u := by rw [h]
      _ = (r * e) * u := by rw [hcomm e heA r hrA]
      _ = r * (e * u) := by rw [mul_assoc]
      _ = r * w := by rw [heu]
  have hf : r * w = 1 := hfpf _ ((rOf T M).mul_mem (c.Ac_le_rOf hrW hrV hr2 hrA)
    (c.Ac_le_rOf hrW hrV hr2 hwA)) hfix
  apply hrV
  have : r = w := by
    rw [eq_inv_of_mul_eq_one_left hf]
    exact inv_eq_of_mul_eq_one_right (c.sq_Ac hrW hrV hr2 hwA)
  rw [this]
  exact hwV

end X

section Setup

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

structure Setup (x z a r1 : G) : Prop where
  x_mem : x ∈ yOfL22 T M
  x_ord : orderOf x = 3
  x_fpf : ∀ ρ ∈ rOf T M, x * ρ * x⁻¹ = ρ → ρ = 1
  z_mem : z ∈ quasithinOmegaOneCenter T
  z_ne : z ≠ 1
  a_def : a = x * z * x⁻¹
  r1_def : r1 = x * r * x⁻¹
  basis : IsBasis (c.Ac hrW hrV hr2) z a r r1
  V_cases : ∀ w ∈ VZ T M, w = 1 ∨ w = z ∨ w = a ∨ w = z * a

include c hrW hrV hr2

theorem Counter.exists_setup (c18a : Concl18a T M g) :
    ∃ x z a r1 : G, Setup c hrW hrV hr2 x z a r1 := by
  obtain ⟨x, hxL, hx3⟩ := c.exists_x
  have hxI : x ∈ iTwo T M := by
    rw [iTwo_eq c.h1281 c.nonab]; exact Subgroup.mem_sup_left hxL
  have hfpf := c18a.r_fpf x hxI hx3
  have hx3' : x * x * x = 1 := by
    rw [← pow_three', ← hx3]; exact pow_orderOf_eq_one x
  obtain ⟨z, a_g, hzZ, hz1, -, -, -, hzz, -, -, -, -, hcases⟩ :=
    exists_three_cycle c.h1281 c.goodElt
  have hzV : z ∈ VZ T M := Hyp1281Two.omegaOneCenter_le_VZ T M hzZ
  have hzA : z ∈ c.Ac hrW hrV hr2 := c.VZ_le_Ac hrW hrV hr2 hzV
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := c.iTwo_le_normalizer_VZ hxI
  have haV : x * z * x⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hxN z).mp hzV
  have haA : x * z * x⁻¹ ∈ c.Ac hrW hrV hr2 := c.VZ_le_Ac hrW hrV hr2 haV
  have hzR : z ∈ rOf T M := c.Ac_le_rOf hrW hrV hr2 hzA
  have ha1 : x * z * x⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this, h]; group
  have haz : x * z * x⁻¹ ≠ z := fun h => hz1 (hfpf z hzR h)
  have hV4 : ∀ w ∈ VZ T M, w = 1 ∨ w = z ∨ w = x * z * x⁻¹ ∨ w = z * (x * z * x⁻¹) := by
    intro w hw
    have hwc := hcases w hw
    rcases hcases _ haV with h1 | h1 | h1 | h1
    · exact absurd h1 ha1
    · exact absurd h1 haz
    · rw [← h1] at hwc; exact hwc
    · have hag : a_g = z * (x * z * x⁻¹) := by rw [h1, ← mul_assoc, hzz, one_mul]
      rcases hwc with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (h.trans hag)))
      · exact Or.inr (Or.inr (Or.inl (h.trans h1.symm)))
  have hmemV : ∀ b0 b1 : Bool, (if b0 = true then z else 1) * (if b1 = true then x * z * x⁻¹ else 1)
      ∈ VZ T M := by
    intro b0 b1
    refine (VZ T M).mul_mem ?_ ?_
    · cases b0 <;> simp [hzV]
    · cases b1 <;> simp [haV]
  have hrA : r ∈ c.Ac hrW hrV hr2 := c.r_mem_Ac hrW hrV hr2
  have hr1A : x * r * x⁻¹ ∈ c.Ac hrW hrV hr2 := c.Ac_conj_mem hrW hrV hr2 hxI hrA
  have hxinvN : x⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) := (Subgroup.normalizer _).inv_mem hxN
  refine ⟨x, z, x * z * x⁻¹, x * r * x⁻¹, ⟨hxL, hx3, hfpf, hzZ, hz1, rfl, rfl, ?_, hV4⟩⟩
  refine isBasis_of_conditions hzA haA hrA hr1A
    (fun a ha b hb => mul_comm_of_sq_eq_one (fun y hy => c.sq_Ac hrW hrV hr2 hy) ha hb)
    (fun y hy => c.sq_Ac hrW hrV hr2 hy) (c.card_Ac hrW hrV hr2) hz1 ?_ ?_ ?_
  · intro b0
    cases b0
    · simpa using ha1
    · simpa using haz
  · intro b0 b1 h
    apply hrV
    rw [h]
    exact hmemV b0 b1
  · intro b0 b1 b2 h
    cases b2
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at h
      apply hrV
      have hr : r = x⁻¹ * (x * r * x⁻¹) * x := by group
      have hmem : x⁻¹ * (x * r * x⁻¹) * x⁻¹⁻¹ ∈ VZ T M := by
        refine (Subgroup.mem_normalizer_iff.mp hxinvN _).mp ?_
        rw [h]; exact hmemV b0 b1
      rw [hr]
      simpa using hmem
    · simp only [↓reduceIte] at h
      exact c.not_conj_eq hrW hrV hr2 hxI hx3' hfpf (hmemV b0 b1) h

end Setup

end S143

end CFSG.Quasithin
