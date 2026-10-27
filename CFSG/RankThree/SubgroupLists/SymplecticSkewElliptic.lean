module

public import CFSG.RankThree.SubgroupLists.SymplecticRegulus
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonTwoTransvectionsClassification
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module Polynomial

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def jhat (x x' : GL V₄ K) : Matrix V₄ V₄ K :=
  ((x : Matrix V₄ V₄ K) - 1) * ((x' : Matrix V₄ V₄ K) - 1) +
    ((x' : Matrix V₄ V₄ K) - 1) * ((x : Matrix V₄ V₄ K) - 1)

theorem sub_one_mul_jhat {x x' : GL V₄ K} (hx : IsSqZero x) :
    ((x : Matrix V₄ V₄ K) - 1) * jhat x x' = jhat x x' * ((x : Matrix V₄ V₄ K) - 1) := by
  have h : ((x : Matrix V₄ V₄ K) - 1) * ((x : Matrix V₄ V₄ K) - 1) = 0 := hx
  simp only [jhat, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, h, Matrix.zero_mul]
  simp only [Matrix.mul_assoc, h, Matrix.mul_zero, zero_add, add_zero]

theorem sub_one_mul_jhat' {x x' : GL V₄ K} (hx' : IsSqZero x') :
    ((x' : Matrix V₄ V₄ K) - 1) * jhat x x' = jhat x x' * ((x' : Matrix V₄ V₄ K) - 1) := by
  have h : ((x' : Matrix V₄ V₄ K) - 1) * ((x' : Matrix V₄ V₄ K) - 1) = 0 := hx'
  simp only [jhat, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, h, Matrix.zero_mul]
  simp only [Matrix.mul_assoc, h, Matrix.mul_zero, zero_add, add_zero]

theorem coe_mul_jhat_left {x x' : GL V₄ K} (hx : IsSqZero x) :
    (x : Matrix V₄ V₄ K) * jhat x x' = jhat x x' * (x : Matrix V₄ V₄ K) := by
  have := sub_one_mul_jhat (x' := x') hx
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one] at this
  exact sub_left_injective this

theorem coe_mul_jhat_right {x x' : GL V₄ K} (hx' : IsSqZero x') :
    (x' : Matrix V₄ V₄ K) * jhat x x' = jhat x x' * (x' : Matrix V₄ V₄ K) := by
  have := sub_one_mul_jhat' (x := x) hx'
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one] at this
  exact sub_left_injective this

theorem jhat_mulVec_of_mem {x x' : GL V₄ K} {a : V₄ → K} (ha : a ∈ unipAxis x) :
    jhat x x' *ᵥ a = ((x : Matrix V₄ V₄ K) - 1) *ᵥ (((x' : Matrix V₄ V₄ K) - 1) *ᵥ a) := by
  rw [jhat, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    sub_one_mulVec_eq_zero ha, Matrix.mulVec_zero, add_zero]

theorem finrank_span_pair_of_not_mem {a b : V₄ → K} (ha : a ≠ 0) (hb : b ∉ K ∙ a) :
    finrank K (Submodule.span K {a, b}) = 2 := by
  rw [show ({a, b} : Set (V₄ → K)) = insert a {b} from rfl, Submodule.span_insert]
  have hb0 : b ≠ 0 := fun h => hb (h ▸ Submodule.zero_mem _)
  have hdisj : (K ∙ a) ⊓ (K ∙ b) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hva, hvb⟩ := Submodule.mem_inf.mp hv
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hva
    obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp hvb
    rw [Submodule.mem_bot]
    by_cases hm0 : m = 0
    · rw [hm0, zero_smul] at hm; exact hm.symm
    · exfalso
      apply hb
      rw [Submodule.mem_span_singleton]
      exact ⟨m⁻¹ * l, by rw [mul_smul, ← hm, inv_smul_smul₀ hm0]⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ a) (K ∙ b)
  rw [hdisj, finrank_bot, add_zero, finrank_span_singleton ha, finrank_span_singleton hb0] at h
  exact h

theorem sup_eq_top_of_inf_eq_bot {A B : Submodule K (V₄ → K)} (hA : finrank K A = 2)
    (hB : finrank K B = 2) (hAB : A ⊓ B = ⊥) : A ⊔ B = ⊤ := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hAB, finrank_bot, add_zero, hA, hB] at h
  apply Submodule.eq_top_of_finrank_eq
  rw [h, Module.finrank_fintype_fun_eq_card]
  simp

theorem exists_quadratic_jhat {x x' : GL V₄ K} (hx : IsSqZero x) (hx' : IsSqZero x')
    (hx2 : finrank K (unipAxis x) = 2) (hx'2 : finrank K (unipAxis x') = 2)
    (hdisj : unipAxis x ⊓ unipAxis x' = ⊥)
    (hnoeig : ∀ b ∈ unipAxis x, b ≠ 0 → ∀ μ : K,
      ((x : Matrix V₄ V₄ K) - 1) *ᵥ (((x' : Matrix V₄ V₄ K) - 1) *ᵥ b) ≠ μ • b) :
    ∃ α β : K, jhat x x' * jhat x x' = β • jhat x x' + α • 1 ∧
      (∀ μ : K, μ * μ ≠ β * μ + α) ∧ α ≠ 0 := by
  classical
  set N := (x : Matrix V₄ V₄ K) - 1 with hN
  set N' := (x' : Matrix V₄ V₄ K) - 1 with hN'
  set J := jhat x x' with hJ
  set P := N * N' with hP
  have hnoeig' : ∀ b ∈ unipAxis x, b ≠ 0 → ∀ μ : K, P *ᵥ b ≠ μ • b := by
    intro b hb hb0 μ
    rw [hP, ← Matrix.mulVec_mulVec]
    exact hnoeig b hb hb0 μ
  have hNL : ∀ v, N *ᵥ v ∈ unipAxis x := sub_one_mulVec_mem_unipAxis hx
  have hN'L' : ∀ v, N' *ᵥ v ∈ unipAxis x' := sub_one_mulVec_mem_unipAxis hx'
  have hPL : ∀ v, P *ᵥ v ∈ unipAxis x := fun v => by rw [hP, ← Matrix.mulVec_mulVec]; exact hNL _
  have hmemL : ∀ v, v ∈ unipAxis x → v ∈ unipAxis x' → v = 0 := by
    intro v hv hv'
    have : v ∈ unipAxis x ⊓ unipAxis x' := ⟨hv, hv'⟩
    rw [hdisj] at this
    exact (Submodule.mem_bot _).mp this
  obtain ⟨a, haL, ha0⟩ : ∃ a ∈ unipAxis x, a ≠ 0 := by
    by_contra h
    push Not at h
    have : unipAxis x = ⊥ := (Submodule.eq_bot_iff _).mpr h
    rw [this, finrank_bot] at hx2
    exact absurd hx2 (by norm_num)
  have hPa : P *ᵥ a ∉ K ∙ a := by
    intro h
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp h
    exact hnoeig' a haL ha0 μ hμ.symm
  have hspan : Submodule.span K {a, P *ᵥ a} = unipAxis x := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      intro v hv
      rcases hv with rfl | rfl
      · exact haL
      · exact hPL a
    · rw [finrank_span_pair_of_not_mem ha0 hPa, hx2]
  obtain ⟨α, β, hαβ⟩ : ∃ α β : K, P *ᵥ (P *ᵥ a) = α • a + β • (P *ᵥ a) := by
    have h := hPL (P *ᵥ a)
    rw [← hspan, Submodule.mem_span_pair] at h
    obtain ⟨α, β, h⟩ := h
    exact ⟨α, β, h.symm⟩
  have hJL : ∀ v ∈ unipAxis x, J *ᵥ v = P *ᵥ v := by
    intro v hv
    rw [hJ, jhat_mulVec_of_mem hv, hP, Matrix.mulVec_mulVec]
  set Q : Matrix V₄ V₄ K := J * J - (β • J + α • 1) with hQ
  have hQv : ∀ v, Q *ᵥ v = J *ᵥ (J *ᵥ v) - (β • (J *ᵥ v) + α • v) := by
    intro v
    rw [hQ, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_mulVec]
  set W : Submodule K (V₄ → K) := LinearMap.ker (Matrix.toLin' Q) with hW
  have hmemW : ∀ v, v ∈ W ↔ Q *ᵥ v = 0 := by
    intro v; rw [hW, LinearMap.mem_ker, Matrix.toLin'_apply]
  have hLW : unipAxis x ≤ W := by
    rw [← hspan, Submodule.span_le]
    intro v hv
    rcases hv with rfl | rfl
    · show v ∈ W
      rw [hmemW, hQv, hJL _ haL, hJL _ (hPL _), hαβ]
      abel
    · show P *ᵥ a ∈ W
      rw [hmemW, hQv, hJL _ (hPL _), hJL _ (hPL _), hαβ, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, hαβ]
      simp only [smul_add, smul_smul]
      rw [mul_comm β α]
      abel
  have hN'surj : ∀ w ∈ unipAxis x', ∃ v ∈ unipAxis x, N' *ᵥ v = w := by
    let f : unipAxis x →ₗ[K] unipAxis x' :=
      { toFun := fun v => ⟨N' *ᵥ v, hN'L' v⟩
        map_add' := by intro u v; ext; simp [Matrix.mulVec_add]
        map_smul' := by intro c v; ext; simp [Matrix.mulVec_smul] }
    have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have h1 : N' *ᵥ (v : V₄ → K) = 0 := congrArg Subtype.val hv
      have h2 : (v : V₄ → K) ∈ unipAxis x' := mem_unipAxis_of_sub_one_mulVec_eq_zero h1
      exact Subtype.ext (hmemL _ v.2 h2)
    have hsurj : Function.Surjective f := by
      rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
      · exact hinj
      · rw [hx2, hx'2]
    intro w hw
    obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
    exact ⟨v, v.2, congrArg Subtype.val hv⟩
  have hcommJ : Commute N' J := sub_one_mul_jhat' (x := x) hx'
  have hcommQ : Commute N' Q := by
    rw [hQ]
    exact (hcommJ.mul_right hcommJ).sub_right
      ((hcommJ.smul_right β).add_right ((Commute.one_right N').smul_right α))
  have hL'W : unipAxis x' ≤ W := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hN'surj w hw
    have hvW := hLW hv
    rw [hmemW] at hvW ⊢
    rw [Matrix.mulVec_mulVec, ← hcommQ.eq, ← Matrix.mulVec_mulVec, hvW, Matrix.mulVec_zero]
  have hWtop : W = ⊤ := by
    rw [eq_top_iff, ← sup_eq_top_of_inf_eq_bot hx2 hx'2 hdisj]
    exact sup_le hLW hL'W
  have hQ0 : Q = 0 := by
    ext i j
    have h := (hmemW (Pi.single j 1)).mp (hWtop ▸ Submodule.mem_top)
    have := congrFun h i
    rw [mulVec_single_one_apply] at this
    simpa using this
  refine ⟨α, β, sub_eq_zero.mp hQ0, ?_, ?_⟩
  · intro μ hμ
    set b := P *ᵥ a - (β - μ) • a with hb
    have hbL : b ∈ unipAxis x := (unipAxis x).sub_mem (hPL a) ((unipAxis x).smul_mem _ haL)
    by_cases hb0 : b = 0
    · apply hnoeig' a haL ha0 (β - μ)
      rw [hb, sub_eq_zero] at hb0
      exact hb0
    · apply hnoeig' b hbL hb0 μ
      rw [hb, Matrix.mulVec_sub, Matrix.mulVec_smul, hαβ, smul_sub, smul_smul]
      have hα : α = -(μ * (β - μ)) := by linear_combination -hμ
      rw [hα]
      simp only [neg_smul, sub_smul, mul_comm μ]
      abel
  · intro hα0
    have hPa0 : P *ᵥ a ≠ 0 := by
      intro h0
      apply hnoeig' a haL ha0 0
      rw [zero_smul]; exact h0
    apply hnoeig' (P *ᵥ a) (hPL a) hPa0 β
    rw [hαβ, hα0, zero_smul, zero_add]

theorem aeval_mulVec_mem_of_mulVec_mem {J : Matrix V₄ V₄ K} {W : Submodule K (V₄ → K)}
    (hJ : ∀ v ∈ W, J *ᵥ v ∈ W) (q : K[X]) : ∀ v ∈ W, (aeval J q) *ᵥ v ∈ W := by
  induction q using Polynomial.induction_on with
  | C c => intro v hv; simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, W.smul_mem _ hv]
  | add q₁ q₂ h₁ h₂ =>
    intro v hv; rw [map_add, Matrix.add_mulVec]; exact W.add_mem (h₁ v hv) (h₂ v hv)
  | monomial n c ih =>
    intro v hv
    rw [show (C c * X ^ (n + 1) : K[X]) = (C c * X ^ n) * X by ring, map_mul, aeval_X,
      ← Matrix.mulVec_mulVec]
    exact ih _ (hJ v hv)

theorem commute_aeval {J X' : Matrix V₄ V₄ K} (h : Commute X' J) (q : K[X]) :
    Commute X' (aeval J q) := by
  induction q using Polynomial.induction_on with
  | C c => rw [aeval_C, Algebra.algebraMap_eq_smul_one]; exact (Commute.one_right X').smul_right c
  | add q₁ q₂ h₁ h₂ => rw [map_add]; exact h₁.add_right h₂
  | monomial n c ih =>
    rw [show (C c * X ^ (n + 1) : K[X]) = (C c * X ^ n) * X by ring, map_mul, aeval_X]
    exact ih.mul_right h

theorem exists_sl_mulVec_eq_of_ne_zero {F : Type} [Field F] {u : Fin 2 → F} (hu : u ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = u := by
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := by
      intro h1; apply hu; ext i; fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![u 0, -(u 1)⁻¹; u 1, 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h1]
    · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![u 0, 0; u 1, (u 0)⁻¹], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h0]
    · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl_mulVec_eq {F : Type} [Field F] {u v : Fin 2 → F} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) *ᵥ u = v := by
  obtain ⟨a, ha⟩ := exists_sl_mulVec_eq_of_ne_zero hu
  obtain ⟨b, hb⟩ := exists_sl_mulVec_eq_of_ne_zero hv
  refine ⟨b * a⁻¹, ?_⟩
  have h1 : ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ u =
      ![1, 0] := by
    rw [← ha, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hb]

theorem eq_zero_of_smul_add_smul {F : Type} [Field F] {w u : F × F} (hw : w ≠ 0)
    (hu : u ∉ F ∙ w) {a b : F} (h : a • w + b • u = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · rw [hb, zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.mp h).resolve_right hw, hb⟩
  · exfalso
    apply hu
    rw [Submodule.mem_span_singleton]
    refine ⟨-(b⁻¹ * a), ?_⟩
    have : b • u = -(a • w) := eq_neg_of_add_eq_zero_right h
    calc -(b⁻¹ * a) • w = b⁻¹ • (-(a • w)) := by rw [neg_smul, mul_smul, smul_neg]
      _ = u := by rw [← this, inv_smul_smul₀ hb]

theorem exists_eq_smul_of_mem_span {F : Type} [Field F] (B : (F × F) →+ (F × F))
    (hB : ∀ w, B w ∈ F ∙ w) : ∃ c : F, ∀ w, B w = c • w := by
  classical
  choose c hc using fun w => Submodule.mem_span_singleton.mp (hB w)
  have hpair : ∀ w u : F × F, w ≠ 0 → u ∉ F ∙ w → c w = c u := by
    intro w u hw hu
    have h := map_add B w u
    rw [← hc (w + u), ← hc w, ← hc u, smul_add] at h
    have h' : (c (w + u) - c w) • w + (c (w + u) - c u) • u = 0 := by
      rw [sub_smul, sub_smul]
      rw [← sub_eq_zero] at h
      rw [← h]
      abel
    obtain ⟨h1, h2⟩ := eq_zero_of_smul_add_smul hw hu h'
    rw [sub_eq_zero] at h1 h2
    rw [← h1, h2]
  set e₁ : F × F := (1, 0)
  set e₂ : F × F := (0, 1)
  have he₁ : e₁ ≠ 0 := by simp [e₁]
  have he₂ : e₂ ≠ 0 := by simp [e₂]
  have h12 : e₂ ∉ F ∙ e₁ := by
    intro h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
    have := congrArg Prod.snd ht
    simp [e₁, e₂] at this
  refine ⟨c e₁, fun w => ?_⟩
  by_cases hw : w = 0
  · rw [hw, map_zero, smul_zero]
  rw [← hc w]
  congr 1
  by_cases hw1 : e₁ ∈ F ∙ w
  ·
    have hw2 : e₂ ∉ F ∙ w := by
      intro h2
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hw1
      obtain ⟨t', ht'⟩ := Submodule.mem_span_singleton.mp h2
      apply h12
      rw [Submodule.mem_span_singleton]
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ht
        exact he₁ ht.symm
      refine ⟨t' * t⁻¹, ?_⟩
      rw [mul_smul, ← ht', ← ht, inv_smul_smul₀ ht0]
    rw [hpair w e₂ hw hw2, ← hpair e₁ e₂ he₁ h12]
  · exact (hpair e₁ w he₁ (by
      intro h
      apply hw1
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ht
        exact hw ht.symm
      rw [Submodule.mem_span_singleton]
      exact ⟨t⁻¹, by rw [← ht, inv_smul_smul₀ ht0]⟩)).symm

@[expose] noncomputable def ellPoly (α β : K) : K[X] := X ^ 2 - C β * X - C α

theorem ellPoly_natDegree (α β : K) : (ellPoly α β).natDegree = 2 := by
  rw [ellPoly]; compute_degree!

theorem ellPoly_monic (α β : K) : (ellPoly α β).Monic := by
  rw [ellPoly]; monicity!

theorem aeval_ellPoly (α β : K) {A : Type} [Ring A] [Algebra K A] (y : A) :
    aeval y (ellPoly α β) = y * y - (algebraMap K A β * y + algebraMap K A α) := by
  rw [ellPoly, map_sub, map_sub, map_mul, aeval_C, aeval_C, aeval_X, map_pow, aeval_X, pow_two]
  abel

theorem eval_ellPoly (α β μ : K) : (ellPoly α β).eval μ = μ * μ - (β * μ + α) := by
  rw [ellPoly, eval_sub, eval_sub, eval_mul, eval_C, eval_C, eval_pow, eval_X]
  ring

theorem ellPoly_irreducible {α β : K} (hroot : ∀ μ : K, μ * μ ≠ β * μ + α) :
    Irreducible (ellPoly α β) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [ellPoly_natDegree]; decide
  · intro μ hμ
    apply hroot μ
    rw [IsRoot, eval_ellPoly, sub_eq_zero] at hμ
    exact hμ

theorem aeval_ellPoly_eq_zero {J : Matrix V₄ V₄ K} {α β : K}
    (hJ : J * J = β • J + α • 1) : aeval J (ellPoly α β) = 0 := by
  rw [aeval_ellPoly, hJ, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mul, Matrix.one_mul, sub_self]

@[expose] noncomputable def ellPhi (J : Matrix V₄ V₄ K) (α β : K) (hJ : J * J = β • J + α • 1) :
    AdjoinRoot (ellPoly α β) →ₐ[K] Matrix V₄ V₄ K :=
  Ideal.Quotient.liftₐ (Ideal.span {ellPoly α β}) (aeval J) (by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, aeval_ellPoly_eq_zero hJ, mul_zero])

theorem ellPhi_mk {J : Matrix V₄ V₄ K} {α β : K} (hJ : J * J = β • J + α • 1) (q : K[X]) :
    ellPhi J α β hJ (AdjoinRoot.mk _ q) = aeval J q := rfl

theorem ellPhi_root {J : Matrix V₄ V₄ K} {α β : K} (hJ : J * J = β • J + α • 1) :
    ellPhi J α β hJ (AdjoinRoot.root _) = J := by
  rw [← AdjoinRoot.mk_X, ellPhi_mk, aeval_X]

theorem ellPhi_mulVec_mem {J : Matrix V₄ V₄ K} {α β : K} (hJ : J * J = β • J + α • 1)
    {W : Submodule K (V₄ → K)} (hW : ∀ v ∈ W, J *ᵥ v ∈ W) (k : AdjoinRoot (ellPoly α β)) :
    ∀ v ∈ W, ellPhi J α β hJ k *ᵥ v ∈ W := by
  induction k using AdjoinRoot.induction_on with
  | ih q => rw [ellPhi_mk]; exact aeval_mulVec_mem_of_mulVec_mem hW q

theorem commute_ellPhi {J : Matrix V₄ V₄ K} {α β : K} (hJ : J * J = β • J + α • 1)
    {X' : Matrix V₄ V₄ K} (h : Commute X' J) (k : AdjoinRoot (ellPoly α β)) :
    Commute X' (ellPhi J α β hJ k) := by
  induction k using AdjoinRoot.induction_on with
  | ih q => rw [ellPhi_mk]; exact commute_aeval h q

@[expose] noncomputable def ellCoord {E : Type} [CommRing E] [Algebra K E]
    (φ : E →ₐ[K] Matrix V₄ V₄ K) (a b : V₄ → K) : (E × E) →ₗ[K] (V₄ → K) where
  toFun w := φ w.1 *ᵥ a + φ w.2 *ᵥ b
  map_add' w w' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Matrix.add_mulVec]
    abel
  map_smul' c w := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Matrix.smul_mulVec, smul_add,
      RingHom.id_apply]

theorem ellCoord_apply {E : Type} [CommRing E] [Algebra K E] (φ : E →ₐ[K] Matrix V₄ V₄ K)
    (a b : V₄ → K) (w : E × E) : ellCoord φ a b w = φ w.1 *ᵥ a + φ w.2 *ᵥ b := rfl

theorem ellCoord_smul {E : Type} [CommRing E] [Algebra K E] (φ : E →ₐ[K] Matrix V₄ V₄ K)
    (a b : V₄ → K) (k : E) (w : E × E) : ellCoord φ a b (k • w) = φ k *ᵥ ellCoord φ a b w := by
  rw [ellCoord_apply, ellCoord_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul,
    map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add]

section Coord

variable {x x' : GL V₄ K} {α β : K} (hJsq : jhat x x' * jhat x x' = β • jhat x x' + α • 1)

theorem jhat_mulVec_mem_left (hx : IsSqZero x) {v : V₄ → K} (hv : v ∈ unipAxis x) :
    jhat x x' *ᵥ v ∈ unipAxis x := by
  rw [jhat_mulVec_of_mem hv]
  exact sub_one_mulVec_mem_unipAxis hx _

theorem jhat_mulVec_mem_right (hx' : IsSqZero x') {v : V₄ → K} (hv : v ∈ unipAxis x') :
    jhat x x' *ᵥ v ∈ unipAxis x' := by
  rw [jhat, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    sub_one_mulVec_eq_zero hv, Matrix.mulVec_zero, zero_add]
  exact sub_one_mulVec_mem_unipAxis hx' _

theorem closure_commute_jhat (hx : IsSqZero x) (hx' : IsSqZero x') :
    ∀ h ∈ Subgroup.closure ({x, x'} : Set (GL V₄ K)),
      Commute (h : Matrix V₄ V₄ K) (jhat x x') := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact coe_mul_jhat_left hx
    · exact coe_mul_jhat_right hx'
  | one => rw [Units.val_one]; exact Commute.one_left _
  | mul y z _ _ hy hz => rw [Units.val_mul]; exact hy.mul_left hz
  | inv y _ hy => exact hy.units_inv_left

include hJsq in
theorem ellCoord_bijective [Fact (Irreducible (ellPoly α β))] (hx : IsSqZero x)
    (hx' : IsSqZero x') (hdisj : unipAxis x ⊓ unipAxis x' = ⊥) {a₀ : V₄ → K}
    (ha₀L : a₀ ∈ unipAxis x) (ha₀ : a₀ ≠ 0) :
    Function.Bijective (ellCoord (ellPhi (jhat x x') α β hJsq) a₀
      (((x' : Matrix V₄ V₄ K) - 1) *ᵥ a₀)) := by
  classical
  set φ := ellPhi (jhat x x') α β hJsq
  set b₀ := ((x' : Matrix V₄ V₄ K) - 1) *ᵥ a₀ with hb₀
  have hmemL : ∀ v, v ∈ unipAxis x → v ∈ unipAxis x' → v = 0 := by
    intro v hv hv'
    have : v ∈ unipAxis x ⊓ unipAxis x' := ⟨hv, hv'⟩
    rw [hdisj] at this
    exact (Submodule.mem_bot _).mp this
  have hb₀L' : b₀ ∈ unipAxis x' := sub_one_mulVec_mem_unipAxis hx' _
  have hb₀0 : b₀ ≠ 0 := by
    intro h
    exact ha₀ (hmemL a₀ ha₀L (mem_unipAxis_of_sub_one_mulVec_eq_zero h))
  have hφinj : Function.Injective φ := (φ : AdjoinRoot (ellPoly α β) →+* Matrix V₄ V₄ K).injective
  have hφunit : ∀ k : AdjoinRoot (ellPoly α β), k ≠ 0 → ∀ v, φ k *ᵥ v = 0 → v = 0 := by
    intro k hk v hv
    have h1 : φ k⁻¹ * φ k = 1 := by rw [← map_mul, inv_mul_cancel₀ hk, map_one]
    rw [← Matrix.one_mulVec v, ← h1, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hker : ∀ w, ellCoord φ a₀ b₀ w = 0 → w = 0 := by
    intro w hw
    rw [ellCoord_apply] at hw
    have h1 : φ w.1 *ᵥ a₀ ∈ unipAxis x :=
      ellPhi_mulVec_mem hJsq (fun v hv => jhat_mulVec_mem_left hx hv) w.1 a₀ ha₀L
    have h2 : φ w.2 *ᵥ b₀ ∈ unipAxis x' :=
      ellPhi_mulVec_mem hJsq (fun v hv => jhat_mulVec_mem_right hx' hv) w.2 b₀ hb₀L'
    have h1' : φ w.1 *ᵥ a₀ ∈ unipAxis x' := by
      have h0 : φ w.1 *ᵥ a₀ + φ w.2 *ᵥ b₀ ∈ unipAxis x' := by rw [hw]; exact Submodule.zero_mem _
      exact (Submodule.add_mem_iff_left _ h2).mp h0
    have h4 : φ w.1 *ᵥ a₀ = 0 := hmemL _ h1 h1'
    have h5 : φ w.2 *ᵥ b₀ = 0 := by rw [h4, zero_add] at hw; exact hw
    ext
    · by_contra hk; exact ha₀ (hφunit _ hk _ h4)
    · by_contra hk; exact hb₀0 (hφunit _ hk _ h5)
  have hinj : Function.Injective (ellCoord φ a₀ b₀) :=
    (injective_iff_map_eq_zero (ellCoord φ a₀ b₀)).mpr hker
  have hf0 : ellPoly α β ≠ 0 := (Fact.out : Irreducible (ellPoly α β)).ne_zero
  have : Module.Finite K (AdjoinRoot (ellPoly α β)) := (AdjoinRoot.powerBasis hf0).finite
  have hfinK : finrank K (AdjoinRoot (ellPoly α β)) = 2 := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, ellPoly_natDegree]
  have hdim : finrank K (AdjoinRoot (ellPoly α β) × AdjoinRoot (ellPoly α β)) =
      finrank K (V₄ → K) := by
    rw [Module.finrank_prod, hfinK, Module.finrank_fintype_fun_eq_card]
    simp
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

theorem mulVec_comm_of_commute {X Y : Matrix V₄ V₄ K} (h : Commute X Y) (v : V₄ → K) :
    X *ᵥ (Y *ᵥ v) = Y *ᵥ (X *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, h.eq, ← Matrix.mulVec_mulVec]

include hJsq in
theorem mulVec_ellCoord_left (hx : IsSqZero x) {a₀ : V₄ → K} (ha₀L : a₀ ∈ unipAxis x)
    (k₁ k₂ : AdjoinRoot (ellPoly α β)) :
    (x : Matrix V₄ V₄ K) *ᵥ ellCoord (ellPhi (jhat x x') α β hJsq) a₀
        (((x' : Matrix V₄ V₄ K) - 1) *ᵥ a₀) (k₁, k₂) =
      ellCoord (ellPhi (jhat x x') α β hJsq) a₀ (((x' : Matrix V₄ V₄ K) - 1) *ᵥ a₀)
        (k₁ + AdjoinRoot.root _ * k₂, k₂) := by
  set φ := ellPhi (jhat x x') α β hJsq
  set N := (x : Matrix V₄ V₄ K) - 1 with hN
  set N' := (x' : Matrix V₄ V₄ K) - 1 with hN'
  have hNJ : Commute N (jhat x x') := sub_one_mul_jhat hx
  have hxv : ∀ v, (x : Matrix V₄ V₄ K) *ᵥ v = v + N *ᵥ v := by
    intro v; rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have hNa₀ : N *ᵥ a₀ = 0 := sub_one_mulVec_eq_zero ha₀L
  have hNb₀ : N *ᵥ (N' *ᵥ a₀) = φ (AdjoinRoot.root _) *ᵥ a₀ := by
    rw [ellPhi_root, jhat_mulVec_of_mem ha₀L]
  rw [ellCoord_apply, ellCoord_apply, hxv, Matrix.mulVec_add,
    mulVec_comm_of_commute (commute_ellPhi hJsq hNJ k₁), hNa₀, Matrix.mulVec_zero, zero_add,
    mulVec_comm_of_commute (commute_ellPhi hJsq hNJ k₂), hNb₀,
    Matrix.mulVec_mulVec a₀ (φ k₂) (φ _), ← map_mul, map_add, Matrix.add_mulVec, mul_comm k₂]
  abel

include hJsq in
theorem mulVec_ellCoord_right (hx' : IsSqZero x') (a₀ : V₄ → K)
    (k₁ k₂ : AdjoinRoot (ellPoly α β)) :
    (x' : Matrix V₄ V₄ K) *ᵥ ellCoord (ellPhi (jhat x x') α β hJsq) a₀
        (((x' : Matrix V₄ V₄ K) - 1) *ᵥ a₀) (k₁, k₂) =
      ellCoord (ellPhi (jhat x x') α β hJsq) a₀ (((x' : Matrix V₄ V₄ K) - 1) *ᵥ a₀)
        (k₁, k₂ + k₁) := by
  set φ := ellPhi (jhat x x') α β hJsq
  set N' := (x' : Matrix V₄ V₄ K) - 1 with hN'
  have hN'J : Commute N' (jhat x x') := sub_one_mul_jhat' hx'
  have hx'v : ∀ v, (x' : Matrix V₄ V₄ K) *ᵥ v = v + N' *ᵥ v := by
    intro v; rw [hN', Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have hN'N' : N' *ᵥ (N' *ᵥ a₀) = 0 := by
    rw [Matrix.mulVec_mulVec, hN', hx', Matrix.zero_mulVec]
  rw [ellCoord_apply, ellCoord_apply, hx'v, Matrix.mulVec_add,
    mulVec_comm_of_commute (commute_ellPhi hJsq hN'J k₁),
    mulVec_comm_of_commute (commute_ellPhi hJsq hN'J k₂), hN'N', Matrix.mulVec_zero, add_zero,
    map_add, Matrix.add_mulVec]
  abel

end Coord

theorem false_of_elliptic_core (h2 : (2 : K) ≠ 0) {G : Subgroup (GL V₄ K)}
    [Group.IsPerfect G] (hcomm : commutant G = ⊥)
    (hdich : ∀ y ∈ G, ∀ z ∈ G, IsSqZero y → IsSqZero z → finrank K (unipAxis y) = 2 →
      finrank K (unipAxis z) = 2 → unipAxis y = unipAxis z ∨ unipAxis y ⊓ unipAxis z = ⊥)
    {x x' : GL V₄ K} (hxG : x ∈ G) (hx'G : x' ∈ G) (hx : IsSqZero x) (hx' : IsSqZero x')
    (hx2 : finrank K (unipAxis x) = 2) (hdisj : unipAxis x ⊓ unipAxis x' = ⊥) {α β : K}
    (hJsq : jhat x x' * jhat x x' = β • jhat x x' + α • 1) (hroot : ∀ μ : K, μ * μ ≠ β * μ + α)
    [Fact (Irreducible (ellPoly α β))] {a₀ : V₄ → K} (ha₀L : a₀ ∈ unipAxis x) (ha₀ : a₀ ≠ 0)
    (htrans : ∀ w : AdjoinRoot (ellPoly α β) × AdjoinRoot (ellPoly α β), w ≠ 0 →
      ∃ h ∈ Subgroup.closure ({x, x'} : Set (GL V₄ K)),
        (h : Matrix V₄ V₄ K) *ᵥ ellCoord (ellPhi (jhat x x') α β hJsq) a₀
            (((x' : Matrix V₄ V₄ K) - 1) *ᵥ a₀) (1, 0) =
          ellCoord (ellPhi (jhat x x') α β hJsq) a₀ (((x' : Matrix V₄ V₄ K) - 1) *ᵥ a₀) w) :
    False := by
  classical
  set J := jhat x x' with hJ
  set φ := ellPhi J α β hJsq with hφ
  set b₀ := ((x' : Matrix V₄ V₄ K) - 1) *ᵥ a₀ with hb₀
  set E := AdjoinRoot (ellPoly α β)
  have hbij := ellCoord_bijective hJsq hx hx' hdisj ha₀L ha₀
  set Φe : (E × E) ≃ₗ[K] (V₄ → K) := LinearEquiv.ofBijective (ellCoord φ a₀ b₀) hbij with hΦedef
  have hΦe : ∀ w, Φe w = ellCoord φ a₀ b₀ w := fun w => rfl
  have hΦesmul : ∀ (k : E) (w : E × E), Φe (k • w) = φ k *ᵥ Φe w := by
    intro k w; rw [hΦe, hΦe, ellCoord_smul]
  have hHJ := closure_commute_jhat hx hx'
  have hφinj : Function.Injective φ := (φ : E →+* Matrix V₄ V₄ K).injective
  let ψ : (E × E) → (E →ₗ[K] (V₄ → K)) := fun w =>
    { toFun := fun k => Φe (k • w)
      map_add' := by intro k k'; rw [add_smul, map_add]
      map_smul' := by intro c k; rw [RingHom.id_apply, smul_assoc, map_smul] }
  let kline : (E × E) → Submodule K (V₄ → K) := fun w => LinearMap.range (ψ w)
  have hmemk : ∀ w v, v ∈ kline w ↔ ∃ k : E, Φe (k • w) = v := fun w v => LinearMap.mem_range
  have hf0 : ellPoly α β ≠ 0 := (Fact.out : Irreducible (ellPoly α β)).ne_zero
  have : Module.Finite K E := (AdjoinRoot.powerBasis hf0).finite
  have hfinK : finrank K E = 2 := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, ellPoly_natDegree]
  have hfink : ∀ w : E × E, w ≠ 0 → finrank K (kline w) = 2 := by
    intro w hw
    rw [LinearMap.finrank_range_of_inj, hfinK]
    intro k k' hkk
    have h1 : k • w = k' • w := Φe.injective hkk
    rw [← sub_eq_zero, ← sub_smul] at h1
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hw)
  have hkline_tr : ∀ h ∈ Subgroup.closure ({x, x'} : Set (GL V₄ K)), ∀ w w' : E × E,
      (h : Matrix V₄ V₄ K) *ᵥ Φe w = Φe w' → translate h (kline w) = kline w' := by
    intro h hh w w' hww'
    ext v
    rw [mem_translate, hmemk]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨k, rfl⟩ := (hmemk w u).mp hu
      exact ⟨k, by rw [hΦesmul, hΦesmul, mulVec_comm_of_commute
        (commute_ellPhi hJsq (hHJ h hh) k), hww']⟩
    · rintro ⟨k, rfl⟩
      exact ⟨Φe (k • w), (hmemk w _).mpr ⟨k, rfl⟩, by
        rw [hΦesmul, hΦesmul, mulVec_comm_of_commute (commute_ellPhi hJsq (hHJ h hh) k), hww']⟩
  have h10 : ((1 : E), (0 : E)) ≠ 0 := by simp
  have hkline10 : kline (1, 0) = unipAxis x := by
    have hle : kline (1, 0) ≤ unipAxis x := by
      intro v hv
      obtain ⟨k, rfl⟩ := (hmemk _ v).mp hv
      rw [hΦe, ellCoord_apply]
      simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, map_zero, Matrix.zero_mulVec,
        add_zero]
      exact ellPhi_mulVec_mem hJsq (fun v hv => jhat_mulVec_mem_left hx hv) k a₀ ha₀L
    exact Submodule.eq_of_le_of_finrank_eq hle ((hfink _ h10).trans hx2.symm)
  have hkaxis : ∀ w : E × E, w ≠ 0 → ∃ z ∈ G, IsSqZero z ∧
      finrank K (unipAxis z) = 2 ∧ unipAxis z = kline w := by
    intro w hw
    obtain ⟨h, hh, hhw⟩ := htrans w hw
    have hhG : h ∈ G := (Subgroup.closure_le G).mpr (by
      intro y hy; rcases hy with rfl | rfl
      · exact hxG
      · exact hx'G) hh
    refine ⟨h * x * h⁻¹, G.mul_mem (G.mul_mem hhG hxG) (G.inv_mem hhG), isSqZero_conj hx _,
      by rw [finrank_unipAxis_conj]; exact hx2, ?_⟩
    rw [unipAxis_conj, ← hkline10]
    exact hkline_tr h hh _ _ hhw
  have haxisK : ∀ z ∈ G, IsSqZero z → finrank K (unipAxis z) = 2 →
      ∀ k : E, ∀ v ∈ unipAxis z, φ k *ᵥ v ∈ unipAxis z := by
    intro z hzG hz hz2 k v hv
    by_cases hv0 : v = 0
    · rw [hv0, Matrix.mulVec_zero]; exact Submodule.zero_mem _
    set w := Φe.symm v with hw
    have hw0 : w ≠ 0 := by
      intro h0; apply hv0; rw [← Φe.apply_symm_apply v, ← hw, h0, map_zero]
    obtain ⟨z', hz'G, hz', hz'2, hz'ax⟩ := hkaxis w hw0
    have hvz' : v ∈ unipAxis z' := by
      rw [hz'ax, hmemk]
      exact ⟨1, by rw [one_smul, hw, Φe.apply_symm_apply]⟩
    rcases hdich _ hzG _ hz'G hz hz' hz2 hz'2 with heq | hdisj'
    · rw [heq, hz'ax, hmemk]
      exact ⟨k, by rw [hΦesmul, hw, Φe.apply_symm_apply]⟩
    · exfalso
      have : v ∈ unipAxis z ⊓ unipAxis z' := ⟨hv, hvz'⟩
      rw [hdisj'] at this
      exact hv0 ((Submodule.mem_bot _).mp this)
  have hconjK : ∀ g ∈ G, ∃ k : E,
      (g : Matrix V₄ V₄ K) * J * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = φ k := by
    intro g hg
    set A := (g : Matrix V₄ V₄ K) * J * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) with hA
    let B : (E × E) →+ (E × E) :=
      { toFun := fun w => Φe.symm (A *ᵥ Φe w)
        map_zero' := by rw [map_zero, Matrix.mulVec_zero, map_zero]
        map_add' := by intro w w'; rw [map_add, Matrix.mulVec_add, map_add] }
    have hB : ∀ w, B w ∈ E ∙ w := by
      intro w
      by_cases hw0 : w = 0
      · rw [hw0, map_zero]; exact Submodule.zero_mem _
      obtain ⟨z, hzG, hz, hz2, hzax⟩ := hkaxis w hw0
      have hg' : g⁻¹ ∈ G := G.inv_mem hg
      have hw'G : g⁻¹ * z * g⁻¹⁻¹ ∈ G := G.mul_mem (G.mul_mem hg' hzG) (G.inv_mem hg')
      have hw'2 : finrank K (unipAxis (g⁻¹ * z * g⁻¹⁻¹)) = 2 := by
        rw [finrank_unipAxis_conj]; exact hz2
      have h1 : ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ Φe w ∈ unipAxis (g⁻¹ * z * g⁻¹⁻¹) := by
        rw [unipAxis_conj]
        exact mulVec_mem_translate (hzax ▸ (hmemk w _).mpr ⟨1, by rw [one_smul]⟩)
      have h2' := haxisK _ hw'G (isSqZero_conj hz _) hw'2 (AdjoinRoot.root _) _ h1
      rw [hφ, ellPhi_root] at h2'
      have h3 : A *ᵥ Φe w ∈ unipAxis z := by
        have hzt : unipAxis z = translate g (unipAxis (g⁻¹ * z * g⁻¹⁻¹)) := by
          rw [unipAxis_conj, ← translate_mul, mul_inv_cancel, translate_one]
        rw [hA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzt]
        exact mulVec_mem_translate h2'
      rw [hzax, hmemk] at h3
      obtain ⟨k, hk⟩ := h3
      rw [Submodule.mem_span_singleton]
      refine ⟨k, ?_⟩
      show k • w = Φe.symm (A *ᵥ Φe w)
      rw [← hk, LinearEquiv.symm_apply_apply]
    obtain ⟨c, hc⟩ := exists_eq_smul_of_mem_span B hB
    refine ⟨c, ?_⟩
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    obtain ⟨w, rfl⟩ := Φe.surjective v
    have := hc w
    change Φe.symm (A *ᵥ Φe w) = c • w at this
    rw [← hΦesmul, ← this, LinearEquiv.apply_symm_apply]
  have hrr : AdjoinRoot.root (ellPoly α β) * AdjoinRoot.root (ellPoly α β) =
      algebraMap K E β * AdjoinRoot.root (ellPoly α β) + algebraMap K E α := by
    have h1 : aeval (AdjoinRoot.root (ellPoly α β)) (ellPoly α β) = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    rw [aeval_ellPoly] at h1
    exact sub_eq_zero.mp h1
  set J₀ : Matrix V₄ V₄ K := (2 : K) • J - β • 1 with hJ₀
  have hconj₀ : ∀ g ∈ G, ∃ c : K,
      (g : Matrix V₄ V₄ K) * J₀ * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = c • J₀ := by
    intro g hg
    obtain ⟨k, hk⟩ := hconjK g hg
    have hgg : ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * g = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 : (g : Matrix V₄ V₄ K) * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    set A := (g : Matrix V₄ V₄ K) * J * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) with hA
    have hAA : A * A = β • A + α • 1 := by
      have e : A * A = (g : Matrix V₄ V₄ K) * (J * J) * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
        rw [hA]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) (g : Matrix V₄ V₄ K), hgg,
          Matrix.one_mul]
      rw [e, hJsq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, e2]
    have hkk : k * k = algebraMap K E β * k + algebraMap K E α := by
      apply hφinj
      rw [map_add, map_mul, map_mul, ← hk, AlgHom.commutes, AlgHom.commutes,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
        Matrix.one_mul, hAA]
    have hfac : (k - AdjoinRoot.root _) * (k + AdjoinRoot.root _ - algebraMap K E β) = 0 := by
      linear_combination hkk - hrr
    have hJA : ∀ c : K, (g : Matrix V₄ V₄ K) * (c • (1 : Matrix V₄ V₄ K)) *
        ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = c • 1 := by
      intro c
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, e2]
    rcases mul_eq_zero.mp hfac with h | h
    · refine ⟨1, ?_⟩
      have hAJ : A = J := by rw [hk, sub_eq_zero.mp h, hφ, ellPhi_root]
      rw [one_smul, hJ₀, Matrix.mul_sub, Matrix.sub_mul, hJA, Matrix.mul_smul, Matrix.smul_mul,
        ← hA, hAJ]
    · refine ⟨-1, ?_⟩
      have hk' : k = algebraMap K E β - AdjoinRoot.root _ := by linear_combination h
      have hAJ : A + J = β • 1 := by
        rw [hk, hk', map_sub, hφ, ellPhi_root, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
          sub_add_cancel]
      have hA' : A = β • 1 - J := eq_sub_of_add_eq hAJ
      rw [hJ₀, Matrix.mul_sub, Matrix.sub_mul, hJA, Matrix.mul_smul, Matrix.smul_mul, ← hA, hA',
        neg_one_smul, neg_sub, smul_sub, two_smul, two_smul]
      abel
  have hJscalar : ∀ c : K, J ≠ c • 1 := by
    intro c hc
    apply hroot c
    have := hJsq
    rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, smul_smul,
      ← add_smul] at this
    have h1 := congrFun (congrFun this (Sum.inl 0)) (Sum.inl 0)
    simpa [Matrix.one_apply] using h1
  have hJ₀0 : J₀ ≠ 0 := by
    intro h0
    apply hJscalar (β / 2)
    have : (2 : K) • J = β • 1 := sub_eq_zero.mp h0
    calc J = (2 : K)⁻¹ • ((2 : K) • J) := by rw [inv_smul_smul₀ h2]
      _ = (β / 2) • 1 := by rw [this, smul_smul, div_eq_inv_mul]
  have hmem : J₀ ∈ commutant G := mem_commutant.mpr (commute_of_forall_conj_eq_smul hJ₀0 hconj₀)
  rw [hcomm, Algebra.mem_bot] at hmem
  obtain ⟨c, hc⟩ := hmem
  apply hJscalar ((c + β) / 2)
  have h1 : (2 : K) • J - β • 1 = c • 1 := by
    rw [← hJ₀, ← hc, Algebra.algebraMap_eq_smul_one]
  have h3 : (2 : K) • J = (c + β) • 1 := by
    rw [add_smul, ← h1]; abel
  calc J = (2 : K)⁻¹ • ((2 : K) • J) := by rw [inv_smul_smul₀ h2]
    _ = ((c + β) / 2) • 1 := by rw [h3, smul_smul, div_eq_inv_mul]

theorem false_of_elliptic_pair {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p)) [Group.IsPerfect G]
    (hcomm : commutant G = ⊥)
    (hnotr : ∀ (a : V₄ → ZMod p) (c : ZMod p), a ≠ 0 → c ≠ 0 → spTrans a c ∉ G)
    {x x' : GL V₄ (ZMod p)} (hxG : x ∈ G) (hx'G : x' ∈ G) (hx : IsSqZero x) (hx' : IsSqZero x')
    (hx2 : finrank (ZMod p) (unipAxis x) = 2) (hx'2 : finrank (ZMod p) (unipAxis x') = 2)
    (hdisj : unipAxis x ⊓ unipAxis x' = ⊥)
    (hnoeig : ∀ b ∈ unipAxis x, b ≠ 0 → ∀ μ : ZMod p,
      ((x : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ (((x' : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ b) ≠ μ • b) :
    False := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨α, β, hJsq, hroot, hα0⟩ := exists_quadratic_jhat hx hx' hx2 hx'2 hdisj hnoeig
  have : Fact (Irreducible (ellPoly α β)) := ⟨ellPoly_irreducible hroot⟩
  obtain ⟨a₀, ha₀L, ha₀⟩ : ∃ a ∈ unipAxis x, a ≠ 0 := by
    by_contra h
    push Not at h
    have : unipAxis x = ⊥ := (Submodule.eq_bot_iff _).mpr h
    rw [this, finrank_bot] at hx2
    exact absurd hx2 (by norm_num)
  refine false_of_elliptic_core h2 hcomm
    (fun y hy z hz hy' hz' hy2 hz2 => unipAxis_eq_or_disjoint hp5 hGS hnotr hy hz hy' hz' hy2 hz2)
    hxG hx'G hx hx' hx2 hdisj hJsq hroot ha₀L ha₀ ?_
  set E := AdjoinRoot (ellPoly α β)
  set φ := ellPhi (jhat x x') α β hJsq
  set b₀ := ((x' : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ a₀
  have hbij := ellCoord_bijective hJsq hx hx' hdisj ha₀L ha₀
  set Φe : (E × E) ≃ₗ[ZMod p] (V₄ → ZMod p) := LinearEquiv.ofBijective (ellCoord φ a₀ b₀) hbij
  have hΦe : ∀ w, Φe w = ellCoord φ a₀ b₀ w := fun w => rfl
  set H : Subgroup (GL V₄ (ZMod p)) := Subgroup.closure {x, x'} with hHdef
  have hHJ := closure_commute_jhat hx hx'
  let rhoF : H →* LinearMap.GeneralLinearGroup (ZMod p) (E × E) :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv Φe.symm).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp H.subtype)
  have hrhoF : ∀ (h : H) (w : E × E), (rhoF h : (E × E) →ₗ[ZMod p] (E × E)) w =
      Φe.symm (((h : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) *ᵥ Φe w) := by
    intro h w
    simp [rhoF]
  have hrhoFinj : Function.Injective rhoF := by
    intro h₁ h₂ h12
    apply Subtype.ext
    apply gl_ext_mulVec
    intro v
    have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod p) (E × E) =>
      (g : (E × E) →ₗ[ZMod p] (E × E)) (Φe.symm v)) h12
    simp only [hrhoF, LinearEquiv.apply_symm_apply] at this
    exact Φe.symm.injective this
  have hlinear : ∀ (h : H) (k : E) (w : E × E),
      (rhoF h : (E × E) →ₗ[ZMod p] (E × E)) (k • w) =
        k • (rhoF h : (E × E) →ₗ[ZMod p] (E × E)) w := by
    intro h k w
    rw [hrhoF, hrhoF]
    apply Φe.injective
    rw [LinearEquiv.apply_symm_apply, hΦe, ellCoord_smul, ← hΦe, hΦe (k • _), ellCoord_smul,
      ← hΦe, LinearEquiv.apply_symm_apply,
      mulVec_comm_of_commute (commute_ellPhi hJsq (hHJ h h.2) k)]
  have hxH : x ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hx'H : x' ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hxmodel : ∀ a c : E, (rhoF ⟨x, hxH⟩ : (E × E) →ₗ[ZMod p] (E × E)) (a, c) =
      (a + AdjoinRoot.root _ * c, c) := by
    intro a c
    rw [hrhoF]
    apply Φe.injective
    rw [LinearEquiv.apply_symm_apply, hΦe, hΦe]
    exact mulVec_ellCoord_left hJsq hx ha₀L a c
  have hx'model : ∀ a c : E, (rhoF ⟨x', hx'H⟩ : (E × E) →ₗ[ZMod p] (E × E)) (a, c) =
      (a, c + a) := by
    intro a c
    rw [hrhoF]
    apply Φe.injective
    rw [LinearEquiv.apply_symm_apply, hΦe, hΦe]
    exact mulVec_ellCoord_right hJsq hx' a₀ a c
  have hf0 : ellPoly α β ≠ 0 := (Fact.out : Irreducible (ellPoly α β)).ne_zero
  have : Module.Finite (ZMod p) E := (AdjoinRoot.powerBasis hf0).finite
  have hfinK : finrank (ZMod p) E = 2 := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, ellPoly_natDegree]
  have : Finite E := Module.finite_of_finite (ZMod p)
  have hdegr :
      finrank (ZMod p) E = (minpoly (ZMod p) (AdjoinRoot.root (ellPoly α β))).natDegree := by
    rw [hfinK, AdjoinRoot.minpoly_root hf0, (ellPoly_monic α β).leadingCoeff, inv_one, map_one,
      mul_one, ellPoly_natDegree]
  have hr0 : AdjoinRoot.root (ellPoly α β) ≠ 0 := by
    intro h0
    have h1 : aeval (AdjoinRoot.root (ellPoly α β)) (ellPoly α β) = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    rw [aeval_ellPoly, h0, mul_zero, mul_zero, zero_add, zero_sub, neg_eq_zero] at h1
    exact hα0 ((algebraMap (ZMod p) E).injective (by rw [h1, map_zero]))
  have hxy : Subgroup.closure ({⟨x, hxH⟩, ⟨x', hx'H⟩} : Set H) = ⊤ := by
    have h := Subgroup.closure_closure_coe_preimage (k := ({x, x'} : Set (GL V₄ (ZMod p))))
    convert h using 2
    ext y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl) <;> simp
    · rintro (h | h)
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
  obtain ⟨coordFin, rhoSL, -, -, -, haction, hsurj | hexc⟩ :=
    CFSG.Glauberman.Dickson.two_transvections_classification_aligned (hpodd := hp2) rhoF hrhoFinj
      E hlinear (LinearEquiv.refl E (E × E)) (AdjoinRoot.root _)
      ⟨x, hxH⟩ ⟨x', hx'H⟩ hdegr hr0 hxy (by simpa using hxmodel) (by simpa using hx'model)
  swap
  · exfalso
    have hcard := hexc.1
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, hfinK] at hcard
    have : p ^ 2 = 3 ^ 2 := by rw [hcard]; norm_num
    have := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) this
    omega
  intro w hw
  have hu : coordFin (1, 0) ≠ 0 := by
    intro h0
    have := coordFin.injective (h0.trans (map_zero coordFin).symm)
    simp at this
  have hv : coordFin w ≠ 0 := by
    intro h0
    exact hw (coordFin.injective (h0.trans (map_zero coordFin).symm))
  obtain ⟨g, hg⟩ := exists_sl_mulVec_eq hu hv
  obtain ⟨h, rfl⟩ := hsurj g
  have hrh : (rhoF h : (E × E) →ₗ[ZMod p] (E × E)) (1, 0) = w := by
    apply coordFin.injective
    rw [haction, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
    exact hg
  refine ⟨h, h.2, ?_⟩
  rw [hrhoF] at hrh
  rw [← hΦe, ← hΦe, ← hrh, LinearEquiv.apply_symm_apply]

end CFSG.RankThree.SubgroupLists
