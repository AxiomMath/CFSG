module

public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.RankThree.PartOne.CTP.U5Span

open CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

theorem no_proper_divisor {f d e : ℕ} (hf : 6 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) (he : 2 ≤ e)
    (hde : d * e = 2 * f) (hdvd : (2 ^ f + 1) / 5 ∣ 2 ^ d - 1) : False := by
  obtain ⟨m, hm⟩ := h5
  have hmpos : (2 ^ f + 1) / 5 = m := by omega
  rw [hmpos] at hdvd
  have h64 : 64 ≤ 2 ^ f := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hm13 : 13 ≤ m := by omega
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; omega
    · exact h
  have hdf : d ≤ f := by nlinarith
  by_cases hdf' : d ∣ f
  · obtain ⟨k, hk⟩ := hdf'
    have h1 : 2 ^ d - 1 ∣ 2 ^ f - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (2 ^ d) 1 k
      simpa [← pow_mul, ← hk] using this
    have h2 : m ∣ 2 ^ f - 1 := hdvd.trans h1
    have h3 : m ∣ 2 ^ f + 1 := ⟨5, by omega⟩
    have h4 : m ∣ 2 := by
      have := Nat.dvd_sub h3 h2
      have e2 : 2 ^ f + 1 - (2 ^ f - 1) = 2 := by omega
      rwa [e2] at this
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  · have hodd : e % 2 = 1 := by
      by_contra hev
      obtain ⟨e', he'⟩ : ∃ e', e = 2 * e' := ⟨e / 2, by omega⟩
      exact hdf' ⟨e', by nlinarith⟩
    have he3 : 3 ≤ e := by omega
    have h3d : 3 * d ≤ 2 * f := by nlinarith
    have hle : m ≤ 2 ^ d - 1 := Nat.le_of_dvd (by
      have : 2 ≤ 2 ^ d := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hdpos
      omega) hdvd
    have hx : 2 ^ (3 * d) ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) h3d
    by_cases hd4 : d ≤ 4
    · have h16 : 2 ^ d ≤ 16 := by
        calc 2 ^ d ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hd4
          _ = 16 := by norm_num
      have hf6 : f = 6 := by
        by_contra hne
        have hf7 : 7 ≤ f := by omega
        have : 128 ≤ 2 ^ f := by
          calc 128 = 2 ^ 7 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf7
        omega
      subst hf6
      have hm13' : m = 13 := by omega
      subst hm13'
      interval_cases d <;> omega
    · have hd5 : 5 ≤ d := by omega
      have h32 : 32 ≤ 2 ^ d := by
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd5
      have hx3 : (2 ^ d) ^ 3 ≤ (2 ^ f) ^ 2 := by
        rw [← pow_mul, ← pow_mul, mul_comm d 3, mul_comm f 2]
        exact hx
      have h5x : 5 * 2 ^ d ≤ 2 ^ f := by
        by_contra hlt
        push Not at hlt
        have h1 : (2 ^ f) ^ 2 < (5 * 2 ^ d) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
        have h2 : 25 * (2 ^ d) ^ 2 ≤ (2 ^ d) ^ 3 := by
          have := Nat.mul_le_mul_right ((2 ^ d) ^ 2) (show 25 ≤ 2 ^ d by omega)
          calc 25 * (2 ^ d) ^ 2 ≤ 2 ^ d * (2 ^ d) ^ 2 := this
            _ = (2 ^ d) ^ 3 := by ring
        have h3 : (5 * 2 ^ d) ^ 2 = 25 * (2 ^ d) ^ 2 := by ring
        omega
      omega

section Field

variable {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K]

theorem adjoin_eq_top_of_orderOf {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 6 ≤ f)
    (h5 : 5 ∣ 2 ^ f + 1) {ρ : K} (hρ : orderOf ρ = (2 ^ f + 1) / 5) :
    IntermediateField.adjoin (ZMod 2) {ρ} = ⊤ := by
  classical
  have := Fintype.ofFinite K
  set E : IntermediateField (ZMod 2) K := IntermediateField.adjoin (ZMod 2) {ρ} with hE
  have hρE : ρ ∈ E := IntermediateField.mem_adjoin_simple_self (ZMod 2) ρ
  have hKcard : Fintype.card K = 2 ^ (2 * f) := by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm]
  have hfinK : Module.finrank (ZMod 2) K = 2 * f := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [hKcard, ZMod.card] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hfinE : Fintype.card E = 2 ^ Module.finrank (ZMod 2) E := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := E)
    rwa [ZMod.card] at h
  have htower := Module.finrank_mul_finrank (ZMod 2) E K
  rw [hfinK] at htower
  set d := Module.finrank (ZMod 2) E with hd
  set e := Module.finrank E K with he
  have h64 : 64 ≤ 2 ^ f := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hρpow : ρ ^ (2 ^ d - 1) = 1 := by
    have hne : (⟨ρ, hρE⟩ : E) ≠ 0 := by
      intro h
      have h0 : ρ = 0 := congrArg Subtype.val h
      rw [h0, orderOf_zero] at hρ
      omega
    have := FiniteField.pow_card_sub_one_eq_one (⟨ρ, hρE⟩ : E) hne
    rw [hfinE] at this
    exact congrArg Subtype.val this
  have hdvd : (2 ^ f + 1) / 5 ∣ 2 ^ d - 1 := by
    rw [← hρ]
    exact orderOf_dvd_of_pow_eq_one hρpow
  by_cases he1 : e = 1
  · rw [he1, mul_one] at htower
    refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
    rw [IntermediateField.finrank_top', hfinK]
    exact htower
  · exfalso
    have he0 : e ≠ 0 := by
      have : 0 < e := Module.finrank_pos
      omega
    exact no_proper_divisor hf h5 (by omega) htower hdvd

end Field

section Span

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

variable (K f) in
@[expose] def G5 : Set K :=
  {ρ | ∃ η : K, unitaryInvolution K 2 f η * η = 1 ∧ ρ = (η ^ 5)⁻¹}

variable (K f) in
@[expose] def L5 : AddSubgroup K := AddSubgroup.closure {x | ∃ ρ ∈ G5 K f, x = ρ + 1}

variable (K f) in
@[expose] def P5 : Set K := {p | ∃ ρ ∈ G5 K f, ∃ z ∈ G5 K f, p = (ρ + 1) * (z + 1)}

variable (K f) in
@[expose] def B5 : AddSubgroup K :=
  AddSubgroup.closure {x | ∃ p ∈ P5 K f, ∃ p' ∈ P5 K f,
    x = unitaryInvolution K 2 f p * p' + unitaryInvolution K 2 f p' * p}

theorem mul_mem_G5 {ρ ρ' : K} (hρ : ρ ∈ G5 K f) (hρ' : ρ' ∈ G5 K f) : ρ * ρ' ∈ G5 K f := by
  obtain ⟨η, hη, rfl⟩ := hρ
  obtain ⟨η', hη', rfl⟩ := hρ'
  refine ⟨η * η', ?_, ?_⟩
  · rw [map_mul]
    linear_combination (unitaryInvolution K 2 f η' * η') * hη + hη'
  · rw [mul_pow, mul_inv]

theorem exists_mem_G5_orderOf (hK : Nat.card K = (2 ^ f) ^ 2) (h5 : 5 ∣ 2 ^ f + 1) :
    ∃ ρ ∈ G5 K f, orderOf ρ = (2 ^ f + 1) / 5 := by
  have hq : 1 < 2 ^ f := one_lt_pow_of_card (p := 2) hK
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (2 ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_units_of_card hK]
  have hgK : orderOf (g : K) = (2 ^ f) ^ 2 - 1 := by rw [orderOf_units, hord]
  set q := 2 ^ f with hqdef
  have hω : orderOf ((g : K) ^ (q - 1)) = q + 1 := by
    rw [orderOf_pow' _ (by omega : q - 1 ≠ 0), hgK, sq_sub_one_eq q hq.le]
    have : Nat.gcd ((q + 1) * (q - 1)) (q - 1) = q - 1 := Nat.gcd_eq_right (dvd_mul_left _ _)
    rw [this]
    exact Nat.mul_div_cancel _ (by omega)
  have hnorm : unitaryInvolution K 2 f ((g : K) ^ (q - 1)) * (g : K) ^ (q - 1) = 1 := by
    rw [unitaryInvolution_apply, ← pow_succ]
    have := pow_orderOf_eq_one ((g : K) ^ (q - 1))
    rwa [hω] at this
  refine ⟨((((g : K) ^ (q - 1))⁻¹) ^ 5)⁻¹, ⟨((g : K) ^ (q - 1))⁻¹, ?_, rfl⟩, ?_⟩
  · rw [map_inv₀, ← mul_inv, hnorm, inv_one]
  · rw [inv_pow, inv_inv, orderOf_pow' _ (by norm_num : 5 ≠ 0), hω]
    have : Nat.gcd (q + 1) 5 = 5 := Nat.gcd_eq_right h5
    rw [this]

theorem mul_mem_L5 {ρ : K} (hρ : ρ ∈ G5 K f) {ℓ : K} (hℓ : ℓ ∈ L5 K f) : ρ * ℓ ∈ L5 K f := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  induction hℓ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨ρ', hρ', rfl⟩ := hx
    have : ρ * (ρ' + 1) = (ρ * ρ' + 1) + (ρ + 1) := by linear_combination (-1) * h2
    rw [this]
    exact add_mem (AddSubgroup.subset_closure ⟨ρ * ρ', mul_mem_G5 hρ hρ', rfl⟩)
      (AddSubgroup.subset_closure ⟨ρ, hρ, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact add_mem hx hy
  | neg x _ hx =>
    rw [mul_neg]
    exact neg_mem hx

theorem L5_eq_top (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 6 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) :
    L5 K f = ⊤ := by
  classical
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨ρ₀, hρ₀, hord⟩ := exists_mem_G5_orderOf hK h5
  have hE := adjoin_eq_top_of_orderOf hK hf h5 hord
  have halg : IsAlgebraic (ZMod 2) ρ₀ := by
    have : Module.Finite (ZMod 2) K := Module.Finite.of_finite
    exact Algebra.IsAlgebraic.isAlgebraic ρ₀
  have hmul : ∀ x : K, ∀ ℓ ∈ L5 K f, x * ℓ ∈ L5 K f := by
    intro x ℓ hℓ
    have hx : x ∈ Algebra.adjoin (ZMod 2) {ρ₀} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg, hE]
      trivial
    induction hx using Algebra.adjoin_induction generalizing ℓ with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact mul_mem_L5 hρ₀ hℓ
    | algebraMap r =>
      rcases (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) r with rfl | rfl
      · simp
      · simpa using hℓ
    | add y z _ _ hy hz =>
      rw [add_mul]
      exact add_mem (hy ℓ hℓ) (hz ℓ hℓ)
    | mul y z _ _ hy hz =>
      rw [mul_assoc]
      exact hy _ (hz ℓ hℓ)
  have hne : ρ₀ + 1 ≠ 0 := by
    intro h
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h1 : ρ₀ = 1 := by linear_combination h - h2
    rw [h1, orderOf_one] at hord
    have h64 : 64 ≤ 2 ^ f := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨m, hm⟩ := h5
    omega
  have hmem : ρ₀ + 1 ∈ L5 K f := AddSubgroup.subset_closure ⟨ρ₀, hρ₀, rfl⟩
  rw [eq_top_iff]
  intro x _
  have := hmul (x * (ρ₀ + 1)⁻¹) _ hmem
  rwa [mul_assoc, inv_mul_cancel₀ hne, mul_one] at this

theorem mul_mem_closure_P5 {u v : K} (hu : u ∈ L5 K f) (hv : v ∈ L5 K f) :
    u * v ∈ AddSubgroup.closure (P5 K f) := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨ρ, hρ, rfl⟩ := hx
    induction hv using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨ρ, hρ, z, hz, rfl⟩
    | zero => simp
    | add y y' _ _ hy hy' =>
      rw [mul_add]
      exact add_mem hy hy'
    | neg y _ hy =>
      rw [mul_neg]
      exact neg_mem hy
  | zero => simp
  | add x x' _ _ hx hx' =>
    rw [add_mul]
    exact add_mem hx hx'
  | neg x _ hx =>
    rw [neg_mul]
    exact neg_mem hx

theorem closure_P5_eq_top (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 6 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) :
    AddSubgroup.closure (P5 K f) = ⊤ := by
  have hL := L5_eq_top hK hf h5
  rw [eq_top_iff]
  intro x _
  have h1 : x ∈ L5 K f := by rw [hL]; trivial
  have h2 : (1 : K) ∈ L5 K f := by rw [hL]; trivial
  simpa using mul_mem_closure_P5 h1 h2

theorem mem_B5_of_fixed (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 6 ≤ f) (h5 : 5 ∣ 2 ^ f + 1)
    {b : K} (hb : unitaryInvolution K 2 f b = b) : b ∈ B5 K f := by
  set σ := unitaryInvolution K 2 f with hσ
  have hP := closure_P5_eq_top hK hf h5
  have key : ∀ u v : K, σ u * v + σ v * u ∈ B5 K f := by
    intro u v
    have hu : u ∈ AddSubgroup.closure (P5 K f) := by rw [hP]; trivial
    have hv : v ∈ AddSubgroup.closure (P5 K f) := by rw [hP]; trivial
    induction hu using AddSubgroup.closure_induction with
    | mem x hx =>
      induction hv using AddSubgroup.closure_induction with
      | mem y hy => exact AddSubgroup.subset_closure ⟨x, hx, y, hy, rfl⟩
      | zero => simp
      | add y y' _ _ hy hy' =>
        have : σ x * (y + y') + σ (y + y') * x = (σ x * y + σ y * x) + (σ x * y' + σ y' * x) := by
          rw [map_add]; ring
        rw [this]
        exact add_mem hy hy'
      | neg y _ hy =>
        have : σ x * (-y) + σ (-y) * x = -(σ x * y + σ y * x) := by rw [map_neg]; ring
        rw [this]
        exact neg_mem hy
    | zero => simp
    | add x x' _ _ hx hx' =>
      have : σ (x + x') * v + σ v * (x + x') = (σ x * v + σ v * x) + (σ x' * v + σ v * x') := by
        rw [map_add]; ring
      rw [this]
      exact add_mem hx hx'
    | neg x _ hx =>
      have : σ (-x) * v + σ v * (-x) = -(σ x * v + σ v * x) := by rw [map_neg]; ring
      rw [this]
      exact neg_mem hx
  have hσi := isUnitaryInvolution_unitaryInvolution (p := 2) (f := f) hK
  obtain ⟨c, hc⟩ := hσi.trace_surj b hb
  have := key 1 c
  rw [map_one, one_mul, mul_one] at this
  rw [← hc]
  exact this

end Span

end CFSG.RankThree.PartOne.CTP.U5Span
