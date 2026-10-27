module

public import CFSG.Walter.Ree.Thompson3.Base

public section

namespace CFSG.Walter.Ree.T2

variable {k : Type} [Field k] [CharP k 3]

theorem two_ne_zero' : (2 : k) ≠ 0 := by
  intro h
  have h3 := three_eq_zero' (k := k)
  exact one_ne_zero (by linear_combination h3 - h)

theorem ppv_mul_J (σ : k ≃+* k) (v : k × k × k) :
    coords (ppv σ v * ThompsonN.J σ) = (-v.1, v.2.1, -v.2.2) := by
  simp [coords, ThompsonN.J, ThompsonN.mul_def, thompsonMul, pp]

omit [CharP k 3] in
theorem units_sq_eq_one {t : kˣ} (h : t * t = 1) : t = 1 ∨ t = -1 := by
  have h' : ((t : k) - 1) * ((t : k) + 1) = 0 := by
    have := congrArg Units.val h
    simp only [Units.val_mul, Units.val_one] at this
    linear_combination this
  rcases mul_eq_zero.mp h' with h1 | h1
  · left; exact Units.ext (by simpa using sub_eq_zero.mp h1)
  · right; exact Units.ext (by simpa using eq_neg_of_add_eq_zero_left h1)

theorem thompsonN_invol_form {σ : k ≃+* k} {n : ThompsonN k σ} (h : n * n = 1) (h1 : n ≠ 1) :
    n.κ = -1 ∧ n.β = 0 := by
  have hk : n.κ * n.κ = 1 := by simpa using congrArg ThompsonN.κ h
  have h2 := two_ne_zero' (k := k)
  rcases units_sq_eq_one hk with hk1 | hk1
  · exfalso
    apply h1
    have hα : n.α = 0 := by
      have := congrArg ThompsonN.α h
      simp [ThompsonN.mul_def, thompsonMul, hk1] at this
      have : 2 * n.α = 0 := by linear_combination this
      exact (mul_eq_zero.mp this).resolve_left h2
    have hβ : n.β = 0 := by
      have := congrArg ThompsonN.β h
      simp [ThompsonN.mul_def, thompsonMul, hk1, hα] at this
      have : 2 * n.β = 0 := by linear_combination this
      exact (mul_eq_zero.mp this).resolve_left h2
    have hγ : n.γ = 0 := by
      have := congrArg ThompsonN.γ h
      simp [ThompsonN.mul_def, thompsonMul, hk1, hα, hβ] at this
      have : 2 * n.γ = 0 := by linear_combination this
      exact (mul_eq_zero.mp this).resolve_left h2
    ext <;> simp [hk1, hα, hβ, hγ]
  · refine ⟨hk1, ?_⟩
    have := congrArg ThompsonN.β h
    simp [ThompsonN.mul_def, thompsonMul, hk1] at this
    have : 2 * n.β = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_left h2

theorem conj_J_pp (σ : k ≃+* k) (x y z : k) :
    (pp σ x y z)⁻¹ * ThompsonN.J σ * pp σ x y z =
      ⟨-1, -x, 0, x * y + σ x * x ^ 2 - z⟩ := by
  have h3 := three_eq_zero' (k := k)
  rw [ThompsonN.inv_def]
  ext
  · simp [ThompsonN.J, ThompsonN.mul_def, thompsonMul, pp]
  · simp [ThompsonN.J, ThompsonN.mul_def, thompsonMul, pp]; linear_combination x * h3
  · simp [ThompsonN.J, ThompsonN.mul_def, thompsonMul, pp]; ring
  · simp [ThompsonN.J, ThompsonN.mul_def, thompsonMul, pp]
    linear_combination (z - x * y) * h3

theorem thompsonN_invol {σ : k ≃+* k} {n : ThompsonN k σ} (h : n * n = 1) (h1 : n ≠ 1) :
    ∃ c : ThompsonN k σ, n = c⁻¹ * ThompsonN.J σ * c := by
  obtain ⟨hk, hb⟩ := thompsonN_invol_form h h1
  refine ⟨pp σ (-n.α) 0 (σ (-n.α) * (-n.α) ^ 2 - n.γ), ?_⟩
  rw [conj_J_pp]
  ext
  · simp [hk]
  · simp
  · simp [hb]
  · simp only; ring

namespace RType

variable [Finite k] {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

@[expose] def fixSet
    (x : G) : Set (Option (k × k × k)) := {ω | R.act ω x = ω}

theorem mem_fixSet
    {x : G} {ω : Option (k × k × k)} : ω ∈ R.fixSet x ↔ R.act ω x = ω := Iff.rfl

theorem fixSet_conj (x g : G) :
    R.fixSet (g⁻¹ * x * g) = (fun ω => R.act ω g) '' R.fixSet x := by
  ext ω
  simp only [mem_fixSet, Set.mem_image]
  constructor
  · intro h
    refine ⟨R.act ω g⁻¹, ?_, R.act_inv_act ω g⟩
    have := congrArg (fun z => R.act z g⁻¹) h
    simp only [act_mul, act_act_inv] at this
    exact this
  · rintro ⟨ω', h, rfl⟩
    rw [act_mul, act_mul, act_act_inv, h]

theorem ncard_fixSet_conj (x g : G) :
    (R.fixSet (g⁻¹ * x * g)).ncard = (R.fixSet x).ncard := by
  rw [fixSet_conj]
  exact Set.ncard_image_of_injective _ (R.act_injective g)

theorem act_J
    (v : k × k × k) : R.act (some v) R.Jg = some (-v.1, v.2.1, -v.2.2) := by
  rw [Jg, act_ι, ppv_mul_J]

theorem act_none_J :
    R.act none R.Jg = none := R.act_none_ι _

theorem fixSet_J :
    R.fixSet R.Jg = insert none (Set.range fun y : k => some (0, y, 0)) := by
  ext ω
  rcases ω with _ | ⟨a, b, c⟩
  · simp [mem_fixSet, act_none_J]
  · simp only [mem_fixSet, act_J, Set.mem_insert_iff, reduceCtorEq, Set.mem_range,
      Option.some.injEq, Prod.mk.injEq, false_or]
    have h2 := two_ne_zero' (k := k)
    constructor
    · rintro ⟨ha, -, hc⟩
      refine ⟨b, ?_, rfl, ?_⟩
      · have : 2 * a = 0 := by linear_combination -ha
        exact ((mul_eq_zero.mp this).resolve_left h2).symm
      · have : 2 * c = 0 := by linear_combination -hc
        exact ((mul_eq_zero.mp this).resolve_left h2).symm
    · rintro ⟨y, rfl, rfl, rfl⟩
      simp

theorem ncard_fixSet_J :
    (R.fixSet R.Jg).ncard = Nat.card k + 1 := by
  rw [fixSet_J, Set.ncard_insert_of_notMem (by simp),
    Set.ncard_range_of_injective (fun y y' h => by simpa using h)]

theorem act_none_inv_of_act_eq_none
    {ω : Option (k × k × k)} {g : G} (h : R.act ω g = none) :
    R.act none g⁻¹ = ω := by
  rw [← h, act_act_inv]

theorem fix_iff_mem_N
    (ω : Option (k × k × k)) (x : G) :
    R.act ω x = ω ↔ R.rep ω * x * (R.rep ω)⁻¹ ∈ R.N := by
  rw [← act_none_eq_none_iff, act_mul, act_mul, act_none_rep]
  constructor
  · intro h; rw [h, act_rep_inv]
  · intro h
    have := congrArg (fun z => R.act z (R.rep ω)) h
    simp only [act_inv_act, act_none_rep] at this
    exact this

theorem fixes_two_iff_of
    {ω₁ ω₂ : Option (k × k × k)} {g : G} (h1 : R.act ω₁ g = none)
    (h2 : R.act ω₂ g = some (0, 0, 0)) (x : G) :
    (R.act ω₁ x = ω₁ ∧ R.act ω₂ x = ω₂) ↔ ∃ t : kˣ, g⁻¹ * x * g = R.ι (ThompsonN.torus σ t) := by
  rw [← R.fix_none_zero_iff]
  have e1 : R.act none g⁻¹ = ω₁ := R.act_none_inv_of_act_eq_none h1
  have e2 : R.act (some (0, 0, 0)) g⁻¹ = ω₂ := by rw [← h2, act_act_inv]
  simp only [act_mul, e1, e2]
  constructor
  · rintro ⟨a, b⟩; rw [a, b, h1, h2]; exact ⟨rfl, rfl⟩
  · rintro ⟨a, b⟩
    refine ⟨?_, ?_⟩
    · have := congrArg (fun z => R.act z g⁻¹) a
      simpa only [act_act_inv, e1] using this
    · have := congrArg (fun z => R.act z g⁻¹) b
      simpa only [act_act_inv, e2] using this

theorem fixes_two_iff
    {ω₁ ω₂ : Option (k × k × k)} (h : ω₁ ≠ ω₂) :
    ∃ g : G, ∀ x : G, (R.act ω₁ x = ω₁ ∧ R.act ω₂ x = ω₂) ↔
      ∃ t : kˣ, g⁻¹ * x * g = R.ι (ThompsonN.torus σ t) := by
  obtain ⟨g, h1, h2⟩ := R.exists_two h
  exact ⟨g, R.fixes_two_iff_of h1 h2⟩

omit [Finite k] in
theorem ι_torus_injective : Function.Injective fun t : kˣ => R.ι (ThompsonN.torus σ t) :=
  R.ι_injective.comp ThompsonN.torus_injective

theorem invol_of_fixes_two
    {ω₁ ω₂ : Option (k × k × k)} {g : G}
    (hg : ∀ x : G, (R.act ω₁ x = ω₁ ∧ R.act ω₂ x = ω₂) ↔
      ∃ t : kˣ, g⁻¹ * x * g = R.ι (ThompsonN.torus σ t))
    {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) (h1 : R.act ω₁ x = ω₁) (h2 : R.act ω₂ x = ω₂) :
    g⁻¹ * x * g = R.Jg := by
  obtain ⟨t, ht⟩ := (hg x).mp ⟨h1, h2⟩
  have htt : t * t = 1 := by
    apply R.ι_torus_injective
    simp only [map_mul, ← ht, map_one]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hx]; group
  rcases units_sq_eq_one htt with rfl | rfl
  · exfalso; apply hx1
    have : g⁻¹ * x * g = 1 := by rw [ht, map_one, map_one]
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  · rw [ht]; rfl

theorem invol_unique
    {ω₁ ω₂ : Option (k × k × k)} (h : ω₁ ≠ ω₂) {x y : G}
    (hx : x * x = 1) (hx1 : x ≠ 1) (hx₁ : R.act ω₁ x = ω₁) (hx₂ : R.act ω₂ x = ω₂)
    (hy : y * y = 1) (hy1 : y ≠ 1) (hy₁ : R.act ω₁ y = ω₁) (hy₂ : R.act ω₂ y = ω₂) : x = y := by
  obtain ⟨g, hg⟩ := R.fixes_two_iff h
  have e1 := R.invol_of_fixes_two hg hx hx1 hx₁ hx₂
  have e2 := R.invol_of_fixes_two hg hy hy1 hy₁ hy₂
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [e1, e2]
    _ = y := by group

theorem exists_invol_fixes_two
    {ω₁ ω₂ : Option (k × k × k)} (h : ω₁ ≠ ω₂) :
    ∃ x : G, x * x = 1 ∧ x ≠ 1 ∧ R.act ω₁ x = ω₁ ∧ R.act ω₂ x = ω₂ := by
  obtain ⟨g, hg⟩ := R.fixes_two_iff h
  refine ⟨g * R.Jg * g⁻¹, ?_, ?_, ?_⟩
  · have : R.Jg * R.Jg = 1 := by
      rw [Jg, ← map_mul]
      have : ThompsonN.J σ * ThompsonN.J σ = 1 := by
        rw [ThompsonN.J, ← map_mul]; simp
      rw [this, map_one]
    calc g * R.Jg * g⁻¹ * (g * R.Jg * g⁻¹) = g * (R.Jg * R.Jg) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  · intro h1
    have : R.Jg = 1 := by
      calc R.Jg = g⁻¹ * (g * R.Jg * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have h2 := congrArg (fun z => R.act (some (1, 0, 0)) z) this
    simp only [act_J, act_one, Option.some.injEq, Prod.mk.injEq] at h2
    exact two_ne_zero' (by linear_combination -h2.1)
  · exact (hg _).mpr ⟨-1, by rw [show g⁻¹ * (g * R.Jg * g⁻¹) * g = R.Jg by group]; rfl⟩

theorem eq_torus_mul_K_of_swap
    {x : G} (h1 : R.act none x = some (0, 0, 0))
    (h2 : R.act (some (0, 0, 0)) x = none) : ∃ t : kˣ, x = R.ι (ThompsonN.torus σ t) * R.K := by
  obtain ⟨t, ht⟩ := (R.fix_none_zero_iff (x * R.K)).mp
    ⟨by rw [act_mul, h1, act_zero_K], by rw [act_mul, h2, act_none_K]⟩
  refine ⟨t, ?_⟩
  calc x = x * R.K * R.K := by rw [mul_assoc, R.K_mul_K, mul_one]
    _ = _ := by rw [ht]

theorem swap_inverts
    {ω₁ ω₂ : Option (k × k × k)} (h : ω₁ ≠ ω₂) {x : G}
    (hx₁ : R.act ω₁ x = ω₂) (hx₂ : R.act ω₂ x = ω₁) {y : G}
    (hy₁ : R.act ω₁ y = ω₁) (hy₂ : R.act ω₂ y = ω₂) : x⁻¹ * y * x = y⁻¹ := by
  obtain ⟨g, h1, h2⟩ := R.exists_two h
  obtain ⟨t, ht⟩ := (R.fixes_two_iff_of h1 h2 y).mp ⟨hy₁, hy₂⟩
  have e1 : R.act none g⁻¹ = ω₁ := R.act_none_inv_of_act_eq_none h1
  have e2 : R.act (some (0, 0, 0)) g⁻¹ = ω₂ := by rw [← h2, act_act_inv]
  obtain ⟨t', ht'⟩ := R.eq_torus_mul_K_of_swap (x := g⁻¹ * x * g)
    (by rw [act_mul, act_mul, e1, hx₁, h2]) (by rw [act_mul, act_mul, e2, hx₂, h1])
  have hc : R.ι (ThompsonN.torus σ t') * R.ι (ThompsonN.torus σ t) =
      R.ι (ThompsonN.torus σ t) * R.ι (ThompsonN.torus σ t') := by
    have := congrArg R.ι (congrArg (ThompsonN.torus σ) (mul_comm t' t))
    simpa only [map_mul] using this
  have key : (g⁻¹ * x * g)⁻¹ * (g⁻¹ * y * g) * (g⁻¹ * x * g) = (g⁻¹ * y * g)⁻¹ := by
    rw [ht, ht']
    calc (R.ι (ThompsonN.torus σ t') * R.K)⁻¹ * R.ι (ThompsonN.torus σ t) *
          (R.ι (ThompsonN.torus σ t') * R.K)
        = R.K⁻¹ * (R.ι (ThompsonN.torus σ t'))⁻¹ *
          (R.ι (ThompsonN.torus σ t) * R.ι (ThompsonN.torus σ t')) * R.K := by group
      _ = R.K⁻¹ * (R.ι (ThompsonN.torus σ t'))⁻¹ *
          (R.ι (ThompsonN.torus σ t') * R.ι (ThompsonN.torus σ t)) * R.K := by rw [hc]
      _ = R.K * R.ι (ThompsonN.torus σ t) * R.K := by rw [R.K_inv_eq]; group
      _ = R.ι (ThompsonN.torus σ t⁻¹) * R.K * R.K := by rw [R.K_mul_torus]
      _ = (R.ι (ThompsonN.torus σ t))⁻¹ := by
          rw [mul_assoc, R.K_mul_K, mul_one, map_inv, map_inv]
  calc x⁻¹ * y * x = g * ((g⁻¹ * x * g)⁻¹ * (g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * y * g)⁻¹ * g⁻¹ := by rw [key]
    _ = y⁻¹ := by group

theorem sq_eq_one_of_fix_comm_J
    {ω : Option (k × k × k)} (hω : R.act ω R.Jg ≠ ω) {y : G}
    (hy : R.act ω y = ω) (hyJ : y * R.Jg = R.Jg * y) : y * y = 1 := by
  have hJJ : R.Jg * R.Jg = 1 := by
    rw [Jg, ← map_mul]
    have : ThompsonN.J σ * ThompsonN.J σ = 1 := by
      rw [ThompsonN.J, ← map_mul]; simp
    rw [this, map_one]
  have hJ' : R.act (R.act ω R.Jg) R.Jg = ω := by rw [← act_mul, hJJ, act_one]
  have hy' : R.act (R.act ω R.Jg) y = R.act ω R.Jg := by
    rw [← act_mul, ← hyJ, act_mul, hy]
  have := R.swap_inverts (Ne.symm hω) (x := R.Jg) rfl hJ' hy hy'
  have hJinv : R.Jg⁻¹ = R.Jg := inv_eq_of_mul_eq_one_right hJJ
  rw [hJinv, mul_assoc, hyJ, ← mul_assoc, hJJ, one_mul] at this
  calc y * y = y * y⁻¹ := by rw [← this]
    _ = 1 := mul_inv_cancel y

end RType

end CFSG.Walter.Ree.T2
