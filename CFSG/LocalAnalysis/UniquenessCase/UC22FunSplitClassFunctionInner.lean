module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.RootSL2.Adjust

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Dickson.Sec6.I1431.RootSL2
open scoped MatrixGroups

theorem ringEquiv_apply_eq_of_sq_of_odd {K : Type*} [Field K] (σ : K ≃+* K) {m : ℕ}
    (hm : Odd m) (hσm : σ ^ m = 1) {x : K} (hx : σ (σ x) = x) : σ x = x := by
  obtain ⟨k, hk⟩ := hm
  have h2 : (σ ^ 2) x = x := by
    rw [pow_two]
    exact hx
  have h2pow : ∀ j : ℕ, ((σ ^ 2) ^ j) x = x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      change ((σ ^ 2) ^ j) ((σ ^ 2) x) = x
      rw [h2, ih]
  have hσpow : (σ ^ 2) ^ (k + 1) = σ := by
    rw [← pow_mul]
    have h2k : 2 * (k + 1) = m + 1 := by omega
    rw [h2k, pow_succ, hσm, one_mul]
  have := h2pow (k + 1)
  rwa [hσpow] at this

theorem ringEquiv_eq_id_of_trace_of_odd {K : Type*} [Field K] (c : ℕ) (σ : K ≃+* K)
    {m : ℕ} (hm : Odd m) (hσm : σ ^ m = 1)
    (hg : ∀ t : K, t ≠ 0 →
      (t + t⁻¹) ^ 2 + (c : K) * (t + t⁻¹) =
        (σ t + (σ t)⁻¹) ^ 2 + (c : K) * (σ t + (σ t)⁻¹)) :
    ∀ x, σ x = x := by
  have key : ∀ t : K, t ≠ 0 → σ (t + t⁻¹) = t + t⁻¹ := by
    intro t ht
    have hs : σ (t + t⁻¹) = σ t + (σ t)⁻¹ := by rw [map_add, map_inv₀]
    have h := hg t ht
    set u := t + t⁻¹ with hu
    set s := σ u with hsdef
    have hs' : s = σ t + (σ t)⁻¹ := hs
    rw [← hs'] at h
    have hfac : (u - s) * (u + s + (c : K)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 hfac with h1 | h1
    · exact (sub_eq_zero.1 h1).symm
    · have hs2 : s = -(c : K) - u := by linear_combination h1
      have hss : σ s = u := by
        rw [hs2, map_sub, map_neg, map_natCast, ← hsdef]
        linear_combination (-1 : K) * hs2
      have hfix : σ (σ u) = u := by simpa [hsdef] using hss
      have hu : σ u = u := ringEquiv_apply_eq_of_sq_of_odd σ hm hσm hfix
      exact hsdef.trans hu
  intro x
  by_cases hx : x = 0
  · rw [hx, map_zero]
  have hk := key x hx
  rw [map_add, map_inv₀] at hk
  have hy : σ x ≠ 0 := (map_ne_zero σ).2 hx
  have hfac : (σ x - x) * (1 - (x * σ x)⁻¹) = 0 := by
    have e : (σ x - x) * (1 - (x * σ x)⁻¹) = (σ x + (σ x)⁻¹) - (x + x⁻¹) := by
      field_simp
      ring
    rw [e, hk, sub_self]
  rcases mul_eq_zero.1 hfac with h1 | h1
  · exact sub_eq_zero.1 h1
  · have h2 : x * σ x = 1 := by
      have : (x * σ x)⁻¹ = 1 := by linear_combination -h1
      exact inv_eq_one.1 this
    have h3' : σ x = x⁻¹ := eq_inv_of_mul_eq_one_right h2
    have h4 : σ (σ x) = x := by rw [h3', map_inv₀, h3', inv_inv]
    have hxfix : σ x = x := ringEquiv_apply_eq_of_sq_of_odd σ hm hσm h4
    exact hxfix

private noncomputable def normProd {G : Type*} [Group G] (η : MulAut G) (v : G) : ℕ → G
  | 0 => 1
  | n + 1 => normProd η v n * ((η ^ n) v)

private theorem pow_apply_mem {G : Type*} [Group G] {J : Subgroup G} {η : MulAut G}
    {v : G} (hv : v ∈ J) (hηJ : ∀ y ∈ J, η y ∈ J) : ∀ n : ℕ, ((η ^ n) v) ∈ J := by
  intro n
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ']
    exact hηJ _ ih

private theorem normProd_mem {G : Type*} [Group G] {J : Subgroup G} {η : MulAut G}
    {v : G} (hv : v ∈ J) (hηJ : ∀ y ∈ J, η y ∈ J) : ∀ n : ℕ, normProd η v n ∈ J := by
  intro n
  induction n with
  | zero => exact J.one_mem
  | succ n ih =>
    rw [normProd]
    exact J.mul_mem ih (pow_apply_mem hv hηJ n)

private theorem conj_mul_eta {G : Type*} [Group G] (η : MulAut G) (v : G) :
    η * MulAut.conj v = MulAut.conj (η v) * η := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

private theorem pow_conj_mul_normProd {G : Type*} [Group G] (η : MulAut G) (v : G) :
    ∀ n : ℕ, (MulAut.conj v * η) ^ n =
      MulAut.conj (normProd η v n) * η ^ n := by
  intro n
  induction n with
  | zero => simp [normProd]
  | succ n ih =>
    rw [pow_succ, ih, normProd]
    calc
      (MulAut.conj (normProd η v n) * η ^ n) * (MulAut.conj v * η)
          = MulAut.conj (normProd η v n) * (η ^ n * MulAut.conj v) * η := by group
      _ = MulAut.conj (normProd η v n) * (MulAut.conj ((η ^ n) v) * η ^ n) * η := by
            rw [conj_mul_eta]
      _ = (MulAut.conj (normProd η v n) * MulAut.conj ((η ^ n) v)) * (η ^ n * η) := by group
      _ = MulAut.conj (normProd η v n * (η ^ n) v) * η ^ (n + 1) := by
            rw [← map_mul, pow_succ]

private noncomputable def iterSMul {K : Type*} [Field K] (a : Kˣ) (σ : K ≃+* K) :
    ℕ → K → K
  | 0 => id
  | n + 1 => fun c => (a : K) * σ (iterSMul a σ n c)

private noncomputable def scalarNorm {K : Type*} [Field K] (a : Kˣ) (σ : K ≃+* K) :
    ℕ → K
  | 0 => 1
  | n + 1 => (a : K) * σ (scalarNorm a σ n)

private theorem iterSMul_eq_scalarNorm_mul {K : Type*} [Field K] (a : Kˣ) (σ : K ≃+* K) :
    ∀ (n : ℕ) (c : K), iterSMul a σ n c =
      scalarNorm a σ n * ((σ ^ n) c) := by
  intro n
  induction n with
  | zero => intro c; simp [iterSMul, scalarNorm]
  | succ n ih =>
    intro c
    change (a : K) * σ (iterSMul a σ n c) =
      scalarNorm a σ (n + 1) * ((σ ^ (n + 1)) c)
    rw [scalarNorm]
    rw [ih c, map_mul]
    have hpow : σ ((σ ^ n) c) = (σ ^ (n + 1)) c := by
      rw [pow_succ']
      rfl
    rw [hpow]
    ring

private theorem scalarNorm_eq_pow_of_eq_one {K : Type*} [Field K] (a : Kˣ) {σ : K ≃+* K}
    (hσ : σ = 1) : ∀ n : ℕ, scalarNorm a σ n = (a : K) ^ n := by
  intro n
  induction n with
  | zero => simp [scalarNorm]
  | succ n ih =>
    rw [scalarNorm, ih, hσ]
    simp [pow_succ']

theorem excres_normalizer_inner_of_odd
    {K : Type} [Field K] [Finite K] {G : Type} [Group G] [Finite G]
    {ρ : SL(2, K) →* G}
    (hker : ∀ g : SL(2, K), ρ g = 1 → ∃ l : Kˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K))
    {E : Type} [Field E] (ε : K →+* E) (c : ℕ) (c₀ : E) (χ : G → E)
    (hχ : ∀ g h : G, χ (h * g * h⁻¹) = χ g)
    (hχd : ∀ t : Kˣ, χ (ρ (sl2Diag K t)) =
      ε (((t : K) + (t : K)⁻¹) ^ 2 + (c : K) * ((t : K) + (t : K)⁻¹)) + c₀)
    {y₀ : G} (hyo : Odd (orderOf y₀))
    (hJ : ρ.range.map (MulAut.conj y₀).toMonoidHom = ρ.range) :
    ∃ w ∈ ρ.range, ∀ j ∈ ρ.range, y₀ * j * y₀⁻¹ = w * j * w⁻¹ := by
  classical
  set η : MulAut G := MulAut.conj y₀ with hηdef
  set m : ℕ := orderOf y₀ with hm
  have hyo' : Odd m := by rw [hm]; exact hyo
  have hηpow : η ^ m = 1 := by
    have hpow := map_pow (MulAut.conj : G →* MulAut G) y₀ m
    have hy0m : y₀ ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one y₀
    rw [hy0m, map_one] at hpow
    simpa [hηdef] using hpow.symm
  obtain ⟨v, hv, hα⟩ := exists_pairAut_adjust hker hJ
  obtain ⟨f, hf⟩ : ∃ f : K → K, ∀ c, (MulAut.conj v * η) (ρ (sl2Upper K c)) =
      ρ (sl2Upper K (f c)) := by
    choose f hf using exists_sl2Upper_param hα
    exact ⟨f, hf⟩
  obtain ⟨g, hg⟩ : ∃ g : K → K, ∀ c, (MulAut.conj v * η) (ρ (sl2Lower K c)) =
      ρ (sl2Lower K (g c)) := by
    choose g hg using exists_sl2Lower_param hα
    exact ⟨g, hg⟩
  obtain ⟨a, σ, hfa, hga, hd⟩ := exists_semilinear_params hker hα hf hg
  set α : MulAut G := MulAut.conj v * η with hαdef
  have hJη : ∀ y ∈ ρ.range, η y ∈ ρ.range := fun y hy => by
    have : η y ∈ ρ.range.map η.toMonoidHom := Subgroup.mem_map_of_mem _ hy
    rwa [hJ] at this
  set e : G := normProd η v m with hedef
  have he : e ∈ ρ.range := by
    rw [hedef]
    exact normProd_mem hv hJη m
  have hαm_eq : α ^ m = MulAut.conj e := by
    rw [hαdef, pow_conj_mul_normProd, hηpow, mul_one, ← hedef]
  have hαm : ∀ x, (α ^ m) x = e * x * e⁻¹ := by
    intro x
    rw [hαm_eq, MulAut.conj_apply]
  have hpowUpper : ∀ (n : ℕ) (c : K),
      (α ^ n) (ρ (sl2Upper K c)) = ρ (sl2Upper K (iterSMul a σ n c)) := by
    intro n
    induction n with
    | zero => intro c; simp [iterSMul]
    | succ n ih =>
      intro c
      rw [pow_succ']
      change α ((α ^ n) (ρ (sl2Upper K c))) = _
      rw [ih, hf, hfa]
      rfl
  have hXm : ∀ c, e * ρ (sl2Upper K c) * e⁻¹ =
      ρ (sl2Upper K (iterSMul a σ m c)) := by
    intro c
    rw [← hαm]
    exact hpowUpper m c
  obtain ⟨p, hp⟩ := exists_sq_of_conj_upper hker he
    (μ := fun c => iterSMul a σ m c) hXm
  have hN : scalarNorm a σ m = (p : K) ^ 2 := by
    have h1 := hp 1
    rw [iterSMul_eq_scalarNorm_mul a σ m 1] at h1
    simpa using h1
  have hσm_fun : ∀ c : K, (σ ^ m) c = c := by
    intro c
    have h1 := hp c
    rw [iterSMul_eq_scalarNorm_mul a σ m c, hN] at h1
    exact mul_left_cancel₀ (pow_ne_zero 2 p.ne_zero) h1
  have hσm : σ ^ m = 1 := RingEquiv.ext hσm_fun
  have hσodd : Odd (orderOf σ) := Odd.of_dvd_nat hyo' (orderOf_dvd_of_pow_eq_one hσm)
  have hconj : ∀ t : Kˣ, χ (ρ (sl2Diag K (Units.map σ.toMonoidHom t))) =
      χ (ρ (sl2Diag K t)) := by
    intro t
    rw [← hd t]
    simp only [hαdef, MulAut.mul_apply, MulAut.conj_apply, hηdef]
    rw [hχ _ v]
    simpa using hχ (ρ (sl2Diag K t)) y₀
  have htrace : ∀ t : Kˣ,
      ((t : K) + (t : K)⁻¹) ^ 2 + (c : K) * ((t : K) + (t : K)⁻¹) =
        (σ (t : K) + (σ (t : K))⁻¹) ^ 2 + (c : K) * (σ (t : K) + (σ (t : K))⁻¹) := by
    intro t
    have h1 := hconj t
    rw [hχd, hχd] at h1
    have h2 := add_right_cancel h1
    have h3 := ε.injective h2
    simp only [Units.coe_map] at h3
    exact h3.symm
  have hσ : ∀ x, σ x = x :=
    ringEquiv_eq_id_of_trace_of_odd c σ hyo' hσm fun t ht => by
      simpa using htrace (Units.mk0 t ht)
  have hσeq : σ = 1 := RingEquiv.ext hσ
  have hNm : (a : K) ^ m = (p : K) ^ 2 := by
    have hscalar : scalarNorm a σ m = (a : K) ^ m := scalarNorm_eq_pow_of_eq_one a hσeq m
    rw [← hscalar]
    exact hN
  obtain ⟨k, hk⟩ := hyo'
  let r : Kˣ := a ^ (k + 1) * p⁻¹
  have hNm_units : a ^ m = p ^ 2 := by
    apply Units.ext
    simpa using hNm
  have hr2_units : r ^ 2 = a := by
    dsimp [r]
    rw [mul_pow, ← pow_mul]
    have h2k : (k + 1) * 2 = m + 1 := by omega
    have hp2 : p ^ 2 * (p⁻¹) ^ 2 = 1 := by group
    rw [h2k, pow_succ, hNm_units]
    rw [mul_comm (p ^ 2) a, mul_assoc, hp2, mul_one]
  have hr2 : (r : K) ^ 2 = (a : K) := by
    simpa using congrArg (fun u : Kˣ => (u : K)) hr2_units
  have hx' : ∀ c, α (ρ (sl2Upper K c)) = ρ (sl2Upper K ((r : K) ^ 2 * c)) := by
    intro c
    rw [hf, hfa, hσ, hr2]
  have hy' : ∀ c, α (ρ (sl2Lower K c)) =
      ρ (sl2Lower K (((r⁻¹ : Kˣ) : K) ^ 2 * c)) := by
    intro c
    rw [hg, hga, hσ]
    congr 2
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_pow, hr2]
  have hconjd := eq_conj_diag (ρ := ρ) (α := α) (r := r) hx' hy'
  refine ⟨v⁻¹ * ρ (sl2Diag K r), mul_mem (inv_mem hv) ⟨_, rfl⟩, fun j hj => ?_⟩
  have h1 := hconjd j hj
  have h2 : α j = v * η j * v⁻¹ := rfl
  rw [h2] at h1
  have h3 : η j = y₀ * j * y₀⁻¹ := rfl
  rw [h3] at h1
  calc y₀ * j * y₀⁻¹ = v⁻¹ * (v * (y₀ * j * y₀⁻¹) * v⁻¹) * v := by group
    _ = v⁻¹ * (ρ (sl2Diag K r) * j * (ρ (sl2Diag K r))⁻¹) * v := by rw [h1]
    _ = (v⁻¹ * ρ (sl2Diag K r)) * j * (v⁻¹ * ρ (sl2Diag K r))⁻¹ := by group

end CFSG.HardMathSupport.Dickson.Sec6.I1431
