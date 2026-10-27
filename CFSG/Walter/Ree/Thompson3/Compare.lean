module

public import CFSG.Walter.Ree.Thompson3.FixK

public section

namespace CFSG.Walter.Ree.T2.RType

variable {k : Type} [Field k] [CharP k 3] [Finite k] {σ : k ≃+* k} {d : k}
variable {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]
variable (R₁ : RType G₁ k σ d) (R₂ : RType G₂ k σ d)

theorem act_ι_eq
    (ω : Option (k × k × k)) (n : ThompsonN k σ) :
    R₁.act ω (R₁.ι n) = R₂.act ω (R₂.ι n) := by
  rcases ω with _ | v
  · rw [act_none_ι, act_none_ι]
  · rw [act_ι, act_ι]

theorem act_Jg_eq
    (ω : Option (k × k × k)) : R₁.act ω R₁.Jg = R₂.act ω R₂.Jg :=
  R₁.act_ι_eq R₂ ω _

theorem fixSet_J_eq :
    R₁.fixSet R₁.Jg = R₂.fixSet R₂.Jg := by
  rw [fixSet_J, fixSet_J]

theorem act_none_K_eq :
    R₁.act none R₁.K = R₂.act none R₂.K := by
  rw [act_none_K, act_none_K]

@[expose] def agree :
    Set (Option (k × k × k)) := {ω | R₁.act ω R₁.K = R₂.act ω R₂.K}

theorem none_mem_agree :
    none ∈ agree R₁ R₂ := R₁.act_none_K_eq R₂

theorem zero_mem_agree :
    some (0, 0, 0) ∈ agree R₁ R₂ := by
  simp only [agree, Set.mem_ofPred_eq, act_zero_K]

theorem agree_K
    {ω : Option (k × k × k)} (h : ω ∈ agree R₁ R₂) :
    R₁.act ω R₁.K ∈ agree R₁ R₂ := by
  simp only [agree, Set.mem_ofPred_eq] at h ⊢
  rw [R₁.act_K_K]
  conv_rhs => rw [h]
  rw [R₂.act_K_K]

theorem agree_torus
    {ω : Option (k × k × k)} (h : ω ∈ agree R₁ R₂) (t : kˣ) :
    R₁.act ω (R₁.ι (ThompsonN.torus σ t)) ∈ agree R₁ R₂ := by
  simp only [agree, Set.mem_ofPred_eq] at h ⊢
  rw [← act_mul, R₁.torus_mul_K, act_mul, h, act_ι_eq R₁ R₂ ω, ← act_mul, R₂.torus_mul_K,
    act_mul, act_ι_eq R₁ R₂]

theorem agree_rel {n n₁ n₂ : ThompsonN k σ}
    (h₁ : R₁.K * R₁.ι n * R₁.K = R₁.ι n₁ * R₁.K * R₁.ι n₂)
    (h₂ : R₂.K * R₂.ι n * R₂.K = R₂.ι n₁ * R₂.K * R₂.ι n₂) {ω : Option (k × k × k)}
    (hω : ω ∈ agree R₁ R₂) (hω₁ : R₁.act ω (R₁.ι n₁) ∈ agree R₁ R₂) :
    R₁.act (R₁.act ω R₁.K) (R₁.ι n) ∈ agree R₁ R₂ := by
  simp only [agree, Set.mem_ofPred_eq] at hω hω₁ ⊢
  have e1 : R₁.act (R₁.act (R₁.act ω R₁.K) (R₁.ι n)) R₁.K =
      R₁.act (R₁.act (R₁.act ω (R₁.ι n₁)) R₁.K) (R₁.ι n₂) := by
    rw [← act_mul, ← act_mul, ← mul_assoc, h₁, act_mul, act_mul]
  have e2 : R₂.act (R₂.act (R₂.act ω R₂.K) (R₂.ι n)) R₂.K =
      R₂.act (R₂.act (R₂.act ω (R₂.ι n₁)) R₂.K) (R₂.ι n₂) := by
    rw [← act_mul, ← act_mul, ← mul_assoc, h₂, act_mul, act_mul]
  rw [e1, hω₁, act_ι_eq R₁ R₂ ω n₁, act_ι_eq R₁ R₂ _ n₂, ← e2, hω, act_ι_eq R₁ R₂ _ n]

variable {S : k → k × k × k} (hS₁ : IsS R₁ S) (hS₂ : IsS R₂ S)

theorem act_0x1_K
    {G : Type} [Group G] [Finite G] {R : RType G k σ d} (hS : IsS R S) (x : k) :
    R.act (some (0, x, 1)) R.K = some (S x) := by
  obtain ⟨ν, hν⟩ := hS x
  exact R.act_K_of_eq hν

include hS₁ hS₂ in
theorem mem_agree_0x1
    (x : k) : some (0, x, 1) ∈ agree R₁ R₂ := by
  show R₁.act (some (0, x, 1)) R₁.K = R₂.act (some (0, x, 1)) R₂.K
  rw [act_0x1_K hS₁, act_0x1_K hS₂]

theorem act_0x1_torus (x : k) (t : kˣ) :
    R₁.act (some (0, x, 1)) (R₁.ι (ThompsonN.torus σ t)) =
      some (0, x * (t * σ t), (t : k) ^ 2 * σ t) := by
  rw [act_ι]
  simp [coords, ThompsonN.mul_def, thompsonMul, pp]

include hS₁ hS₂ in
theorem mem_agree_0xy
    (x y : k) (hy : y ≠ 0) : some (0, x, y) ∈ agree R₁ R₂ := by
  obtain ⟨t, ht⟩ := R₁.sigmaTwo_surjective (Units.mk0 y hy)
  have ht' : σ t * (t : k) ^ 2 = y := by simpa using ht
  have htt : (t : k) * σ t ≠ 0 := mul_ne_zero t.ne_zero (by simp)
  have h := R₁.agree_torus R₂ (R₁.mem_agree_0x1 R₂ hS₁ hS₂ (x / ((t : k) * σ t))) t
  rw [act_0x1_torus, div_mul_cancel₀ x htt, mul_comm _ (σ (t : k)), ht'] at h
  exact h

variable {a : ℕ} (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (h69₁ : Eq69 R₁)
  (h69₂ : Eq69 R₂)

include ha haσ h69₁ h69₂ in
theorem agree_pp0
    {ω : Option (k × k × k)} (hω : ω ∈ agree R₁ R₂) (z : k)
    (hω' : ∀ hz : z ≠ 0, R₁.act ω (R₁.ι (pp σ 0 (-z⁻¹) 0 *
      ThompsonN.torus σ (Units.mk0 z hz ^ a))) ∈ agree R₁ R₂) :
    R₁.act (R₁.act ω R₁.K) (R₁.ι (pp σ 0 z 0)) ∈ agree R₁ R₂ := by
  by_cases hz : z = 0
  · rw [hz, show pp σ 0 0 0 = 1 from rfl, map_one, act_one]
    exact R₁.agree_K R₂ hω
  · exact R₁.agree_rel R₂ (R₁.K_pp0_K ha haσ h69₁ z hz) (R₂.K_pp0_K ha haσ h69₂ z hz) hω
      (hω' hz)

include ha haσ h69₁ h69₂ in
theorem fixSet_J_subset_agree :
    R₁.fixSet R₁.Jg ⊆ agree R₁ R₂ := by
  rw [fixSet_J]
  rintro ω (rfl | ⟨z, rfl⟩)
  · exact R₁.none_mem_agree R₂
  · have h := R₁.agree_pp0 R₂ ha haσ h69₁ h69₂ (R₁.none_mem_agree R₂) z (fun _ => by
      rw [act_none_ι]; exact R₁.none_mem_agree R₂)
    rw [act_none_K, act_ι, ppv_zero, one_mul] at h
    exact h

theorem act_001_b
    {b : ThompsonN k σ} (hb : b ∈ bSet σ) :
    R₁.act (some (0, 0, 1)) (R₁.ι b) = some (0, b.β, (b.κ : k) ^ 2 * σ b.κ) := by
  obtain ⟨h1, h2⟩ := hb
  rw [act_ι]
  simp [coords, ThompsonN.mul_def, thompsonMul, pp, h1, h2]

include hS₁ hS₂ in
theorem mem_agree_001_b
    {b : ThompsonN k σ} (hb : b ∈ bSet σ) :
    R₁.act (some (0, 0, 1)) (R₁.ι b) ∈ agree R₁ R₂ := by
  rw [act_001_b R₁ hb]
  exact R₁.mem_agree_0xy R₂ hS₁ hS₂ _ _ (mul_ne_zero (pow_ne_zero 2 b.κ.ne_zero) (by simp))

include hS₁ hS₂ ha haσ h69₁ h69₂ in
theorem mem_agree_001_bKp
    {b : ThompsonN k σ} (hb : b ∈ bSet σ) (z : k) :
    R₁.act (some (0, 0, 1)) (R₁.ι b * R₁.K * R₁.ι (pp σ 0 z 0)) ∈ agree R₁ R₂ := by
  rw [act_mul, act_mul]
  refine R₁.agree_pp0 R₂ ha haσ h69₁ h69₂ (R₁.mem_agree_001_b R₂ hS₁ hS₂ hb) z (fun hz => ?_)
  rw [← act_mul, ← map_mul]
  exact R₁.mem_agree_001_b R₂ hS₁ hS₂
    (bSet_mul hb (bSet_mul (pp0_mem_bSet σ _) (torus_mem_bSet σ _)))

include hS₁ hS₂ ha haσ h69₁ h69₂ in
theorem delta_subset_agree :
    R₁.delta ha haσ h69₁ ⊆ agree R₁ R₂ := by
  rintro _ ⟨h, hh, rfl⟩
  rcases hh with ⟨b, hb, rfl⟩ | ⟨b, hb, z, rfl⟩
  · exact R₁.mem_agree_001_b R₂ hS₁ hS₂ hb
  · exact R₁.mem_agree_001_bKp R₂ hS₁ hS₂ ha haσ h69₁ h69₂ hb z

include hS₁ hS₂ ha haσ h69₁ h69₂ in
theorem delta_eq_delta :
    R₁.delta ha haσ h69₁ = R₂.delta ha haσ h69₂ := by
  have key : ∀ (b : ThompsonN k σ), b ∈ bSet σ → ∀ z : k,
      R₁.act (some (0, 0, 1)) (R₁.ι b * R₁.K * R₁.ι (pp σ 0 z 0)) =
        R₂.act (some (0, 0, 1)) (R₂.ι b * R₂.K * R₂.ι (pp σ 0 z 0)) := by
    intro b hb z
    have h := R₁.mem_agree_001_b R₂ hS₁ hS₂ hb
    simp only [agree, Set.mem_ofPred_eq] at h
    rw [act_mul, act_mul, act_mul, act_mul, h, act_ι_eq R₁ R₂ _ b, act_ι_eq R₁ R₂ _ (pp σ 0 z 0)]
  ext ω
  constructor
  · rintro ⟨h, hh, rfl⟩
    rcases hh with ⟨b, hb, rfl⟩ | ⟨b, hb, z, rfl⟩
    · exact ⟨R₂.ι b, Or.inl ⟨b, hb, rfl⟩, (act_ι_eq R₁ R₂ _ b).symm⟩
    · exact ⟨_, Or.inr ⟨b, hb, z, rfl⟩, (key b hb z).symm⟩
  · rintro ⟨h, hh, rfl⟩
    rcases hh with ⟨b, hb, rfl⟩ | ⟨b, hb, z, rfl⟩
    · exact ⟨R₁.ι b, Or.inl ⟨b, hb, rfl⟩, act_ι_eq R₁ R₂ _ b⟩
    · exact ⟨_, Or.inr ⟨b, hb, z, rfl⟩, key b hb z⟩

include hS₁ hS₂ ha haσ h69₁ h69₂ in
theorem fixSet_K_eq :
    R₁.fixSet R₁.K = R₂.fixSet R₂.K := by
  have hsub : ∀ ω ∈ R₁.fixSet R₁.K ∪ R₂.fixSet R₂.K, ω ∈ agree R₁ R₂ := by
    rintro ω (h | h)
    · exact R₁.delta_subset_agree R₂ hS₁ hS₂ ha haσ h69₁ h69₂
        (R₁.fixSet_K_subset_delta ha haσ h69₁ h)
    · apply R₁.delta_subset_agree R₂ hS₁ hS₂ ha haσ h69₁ h69₂
      rw [R₁.delta_eq_delta R₂ hS₁ hS₂ ha haσ h69₁ h69₂]
      exact R₂.fixSet_K_subset_delta ha haσ h69₂ h
  ext ω
  have hω := hsub ω
  simp only [agree, Set.mem_ofPred_eq, mem_fixSet, Set.mem_union] at hω ⊢
  constructor
  · intro h; rw [← hω (Or.inl h)]; exact h
  · intro h; rw [hω (Or.inr h)]; exact h

@[expose] def qJK (σ : k ≃+* k) (d : k) (S : k → k × k × k) (x : k) : ThompsonN k σ :=
  (ThompsonN.J σ)⁻¹ * ppv σ (S (-x)) * ThompsonN.J σ * pp σ 1 1 d

omit [Finite k] in
theorem qJK_mem_P (S : k → k × k × k) (x : k) : qJK σ d S x ∈ ThompsonN.P σ := by
  simp only [qJK, ThompsonN.mem_P, ThompsonN.mul_κ, ThompsonN.inv_def, ThompsonN.J]
  simp [pp]

omit [Finite k] in
theorem J_conj_YT : (ThompsonN.J σ)⁻¹ * pp σ 1 1 d * ThompsonN.J σ = (tY σ d)⁻¹ * tT σ := by
  rw [show pp σ 1 1 d = ⟨1, 1, 1, d⟩ from rfl, ThompsonN.J_conj, tY, tT,
    show pp σ 1 0 d = ⟨1, 1, 0, d⟩ from rfl, show pp σ 0 1 0 = ⟨1, 0, 1, 0⟩ from rfl,
    ThompsonN.inv_P, ThompsonN.mul_P]
  simp

omit [Finite k] in
theorem pp_neg_mul_Y3 (x : k) : pp σ 0 (-x) 1 * tY σ d ^ 3 = pp σ 0 (-x) (-1) := by
  rw [tY_cube]
  simp only [pp]
  rw [ThompsonN.mul_P]
  have h3 := three_eq_zero' (k := k)
  ext
  · rfl
  · simp
  · simp
  · simp only; linear_combination h3

omit [Finite k] in
theorem J_conj_0x1 (x : k) :
    (ThompsonN.J σ)⁻¹ * pp σ 0 (-x) 1 * ThompsonN.J σ = pp σ 0 (-x) (-1) := by
  rw [show pp σ 0 (-x) 1 = ⟨1, 0, -x, 1⟩ from rfl, ThompsonN.J_conj]; simp [pp]

theorem JK_fixes_qJK
    {G : Type} [Group G] [Finite G] {R : RType G k σ d} (hS : IsS R S)
    (x : k) : R.act (some (coords (qJK σ d S x))) (R.Jg * R.K) = some (coords (qJK σ d S x)) := by
  obtain ⟨ν, hν⟩ := hS (-x)
  set s' := ppv σ (S (-x))
  have hJinv : R.Jg⁻¹ = R.Jg := inv_eq_of_mul_eq_one_right R.Jg_mul_Jg
  have hιJ : R.ι (ThompsonN.J σ)⁻¹ = R.Jg := by rw [map_inv]; exact hJinv
  have hs' : R.K * R.ι s' * R.K = R.ι ν⁻¹ * R.K * R.ι (pp σ 0 (-x) 1) := by
    rw [map_inv]
    calc R.K * R.ι s' * R.K = (R.ι ν)⁻¹ * (R.ι ν * R.K * R.ι s') * R.K := by group
      _ = (R.ι ν)⁻¹ * (R.K * R.ι (pp σ 0 (-x) 1) * R.K) * R.K := by rw [← hν]
      _ = _ := by simp only [mul_assoc, R.K_mul_K, mul_one]
  have hJK := R.Jg_mul_K
  have hneg : R.K * R.ι (pp σ 0 (-x) (-1)) * R.K =
      R.ι ((ThompsonN.J σ)⁻¹ * ν * ThompsonN.J σ) * R.K *
        R.ι ((ThompsonN.J σ)⁻¹ * s' * ThompsonN.J σ) := by
    rw [← J_conj_0x1, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, hιJ]
    change R.K * (R.Jg * R.ι (pp σ 0 (-x) 1) * R.Jg) * R.K = R.Jg * R.ι ν * R.Jg * R.K *
      (R.Jg * R.ι s' * R.Jg)
    calc R.K * (R.Jg * R.ι (pp σ 0 (-x) 1) * R.Jg) * R.K
        = R.K * R.Jg * R.ι (pp σ 0 (-x) 1) * (R.Jg * R.K) := by group
      _ = R.K * R.Jg * R.ι (pp σ 0 (-x) 1) * (R.K * R.Jg) := by rw [hJK]
      _ = R.Jg * R.K * R.ι (pp σ 0 (-x) 1) * (R.K * R.Jg) := by nth_rw 1 [← hJK]
      _ = R.Jg * (R.K * R.ι (pp σ 0 (-x) 1) * R.K) * R.Jg := by group
      _ = R.Jg * (R.ι ν * R.K * R.ι s') * R.Jg := by rw [hν]
      _ = R.Jg * R.ι ν * R.Jg * (R.Jg * R.K) * R.ι s' * R.Jg := by
          rw [show R.Jg * R.ι ν * R.Jg * (R.Jg * R.K) = R.Jg * R.ι ν * (R.Jg * R.Jg) * R.K by
            group, R.Jg_mul_Jg]; group
      _ = _ := by rw [hJK]; group
  have hc := R.rel_c
  have hq : R.ι (qJK σ d S x) = R.Jg * R.ι s' * R.Jg * R.ι (pp σ 1 1 d) := by
    simp only [qJK, map_mul, hιJ]; rfl
  have hYT : R.ι (pp σ 1 1 d) = R.ι (tY σ d) * R.ι (tT σ) := by rw [← map_mul, tY_mul_tT]
  have hJYTJ : R.Jg * R.ι (pp σ 1 1 d) * R.Jg = (R.ι (tY σ d))⁻¹ * R.ι (tT σ) := by
    have := congrArg R.ι (J_conj_YT (σ := σ) (d := d))
    rw [map_mul, map_mul, hιJ, map_mul, map_inv] at this
    exact this
  have hx3 : R.ι (pp σ 0 (-x) 1) * R.ι (tY σ d) ^ 3 = R.ι (pp σ 0 (-x) (-1)) := by
    rw [← map_pow, ← map_mul, pp_neg_mul_Y3]
  have e : R.K * R.ι (qJK σ d S x) * (R.Jg * R.K) =
      R.ι (ThompsonN.J σ * ν⁻¹ * ((ThompsonN.J σ)⁻¹ * ν * ThompsonN.J σ)) * R.K *
        R.ι (qJK σ d S x) := by
    calc R.K * R.ι (qJK σ d S x) * (R.Jg * R.K)
        = R.K * R.Jg * R.ι s' * (R.Jg * R.ι (pp σ 1 1 d) * R.Jg) * R.K := by rw [hq]; group
      _ = R.Jg * R.K * R.ι s' * ((R.ι (tY σ d))⁻¹ * R.ι (tT σ)) * R.K := by
          rw [hJYTJ, ← hJK]
      _ = R.Jg * (R.K * R.ι s' * R.K) * (R.K * (R.ι (tY σ d))⁻¹ * R.ι (tT σ) * R.K) := by
          rw [show R.Jg * (R.K * R.ι s' * R.K) * (R.K * (R.ι (tY σ d))⁻¹ * R.ι (tT σ) * R.K) =
            R.Jg * R.K * R.ι s' * (R.K * R.K) * (R.ι (tY σ d))⁻¹ * R.ι (tT σ) * R.K by group,
            R.K_mul_K]; group
      _ = R.Jg * R.ι ν⁻¹ * (R.K * (R.ι (pp σ 0 (-x) 1) * R.ι (tY σ d) ^ 3) * R.K) *
            (R.ι (tY σ d) * R.ι (tT σ)) := by rw [hs', hc]; group
      _ = R.Jg * R.ι ν⁻¹ * (R.K * R.ι (pp σ 0 (-x) (-1)) * R.K) * R.ι (pp σ 1 1 d) := by
          rw [hx3, hYT]
      _ = R.Jg * R.ι ν⁻¹ * R.ι ((ThompsonN.J σ)⁻¹ * ν * ThompsonN.J σ) * R.K *
            (R.ι ((ThompsonN.J σ)⁻¹ * s' * ThompsonN.J σ) * R.ι (pp σ 1 1 d)) := by
          rw [hneg]; group
      _ = _ := by
          simp only [qJK, map_mul, hιJ]
          rfl
  rw [act, rep, ppv_coords (qJK_mem_P S x), e]
  have := R.pt_pres (ThompsonN.J σ * ν⁻¹ * ((ThompsonN.J σ)⁻¹ * ν * ThompsonN.J σ))
    (coords (qJK σ d S x))
  rwa [ppv_coords (qJK_mem_P S x)] at this

end CFSG.Walter.Ree.T2.RType
