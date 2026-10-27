module

public import CFSG.Quasithin.Background.RonanD321ModelSchur

public section

namespace CFSG.Quasithin.RonanD321.SL2Model

open Matrix CFSG.Open Multiplicative
open scoped Pointwise

variable {G : Type*} [Group G] {Q : Type*} [CommGroup Q] [MulDistribMulAction G Q]
  {K : Type} [Field K]

@[expose] def IsCoord (π : ↥(StatedSL 2 K) →* G)
    (Ψ : Multiplicative (Matrix (Fin 2) (Fin 2) K) →* Q) : Prop :=
  Function.Injective Ψ ∧ ∀ γ X, Ψ (ofAdd (slm γ * X)) = π γ • Ψ (ofAdd X)

@[expose] def IsAct (Ψ : Multiplicative (Matrix (Fin 2) (Fin 2) K) →* Q) (g : G) (σ : K ≃+* K)
    (A B : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ X, g • Ψ (ofAdd X) = Ψ (ofAdd (A * X.map σ * B))

@[expose] def IsSemi (Ψ : Multiplicative (Matrix (Fin 2) (Fin 2) K) →* Q) (g : G)
    (σ : K ≃+* K) : Prop :=
  ∃ F : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K,
    (∀ X, g • Ψ (ofAdd X) = Ψ (ofAdd (F X))) ∧ ∀ (c : K) X, F (c • X) = σ c • F X

variable {π : ↥(StatedSL 2 K) →* G} {Ψ : Multiplicative (Matrix (Fin 2) (Fin 2) K) →* Q}

theorem IsCoord.injective_π (hΨ : IsCoord π Ψ) : Function.Injective π := by
  intro γ δ h
  apply slm_injective
  have h1 := hΨ.2 γ 1
  rw [h, ← hΨ.2 δ 1] at h1
  simpa using congrArg toAdd (hΨ.1 h1)

theorem IsAct.isSemi {g : G} {σ : K ≃+* K} {A B : Matrix (Fin 2) (Fin 2) K}
    (h : IsAct Ψ g σ A B) : IsSemi Ψ g σ := by
  refine ⟨fun X => A * X.map σ * B, h, fun c X => ?_⟩
  have e : (c • X).map σ = σ c • X.map σ := by
    ext i j
    simp
  simp only [e, Matrix.mul_smul, Matrix.smul_mul]

theorem IsSemi.unique (hΨ : Function.Injective Ψ) {g : G} {σ τ : K ≃+* K} (h1 : IsSemi Ψ g σ)
    (h2 : IsSemi Ψ g τ) : σ = τ := by
  obtain ⟨F, hF, hFs⟩ := h1
  obtain ⟨F', hF', hF's⟩ := h2
  have hFF : ∀ X, F X = F' X := fun X => congrArg toAdd (hΨ ((hF X).symm.trans (hF' X)))
  have hF1 : F 1 ≠ 0 := by
    intro h0
    have h := hF 1
    rw [h0, ofAdd_zero, map_one Ψ] at h
    have h' : Ψ (ofAdd (1 : Matrix (Fin 2) (Fin 2) K)) = 1 := by
      rw [← inv_smul_smul g (Ψ (ofAdd 1)), h, smul_one]
    have h'' := congrArg toAdd (hΨ (h'.trans (map_one Ψ).symm))
    have h3 := congrFun (congrFun h'' 0) 0
    simp at h3
  ext c
  have e1 := hFs c 1
  rw [hFF, hFF, hF's] at e1
  rw [← hFF] at e1
  exact smul_left_injective K hF1 e1.symm

theorem IsSemi.mul {g h : G} {σ τ : K ≃+* K} (h1 : IsSemi Ψ g σ) (h2 : IsSemi Ψ h τ) :
    IsSemi Ψ (g * h) (σ * τ) := by
  obtain ⟨F, hF, hFs⟩ := h1
  obtain ⟨F', hF', hF's⟩ := h2
  refine ⟨F ∘ F', fun X => ?_, fun c X => ?_⟩
  · rw [mul_smul, hF', hF]
    rfl
  · simp only [Function.comp_apply]
    rw [hF's, hFs]
    rfl

theorem isSemi_one : IsSemi Ψ (1 : G) 1 := ⟨id, fun X => one_smul _ _, fun _ _ => rfl⟩

theorem exists_conj_eq_of_inv {g : G} (h : ∀ γ, ∃ δ, g⁻¹ * π γ * g⁻¹⁻¹ = π δ)
    (δ : ↥(StatedSL 2 K)) : ∃ γ, g * π γ * g⁻¹ = π δ := by
  obtain ⟨γ, hγ⟩ := h δ
  refine ⟨γ, ?_⟩
  rw [← hγ, inv_inv]
  group

theorem exists_form [Finite K] (hK : ringChar K = 2) (hΨ : IsCoord π Ψ) {g : G}
    (hg1 : ∀ γ, ∃ δ, g * π γ * g⁻¹ = π δ) (hg2 : ∀ δ, ∃ γ, g * π γ * g⁻¹ = π δ)
    (hgU : ∀ X, ∃ Y, g • Ψ (ofAdd X) = Ψ (ofAdd Y)) :
    ∃ (σ : K ≃+* K) (A : ↥(StatedSL 2 K)) (B : Matrix (Fin 2) (Fin 2) K), IsUnit B ∧
      IsAct Ψ g σ (slm A) B ∧ ∀ γ, g * π γ * g⁻¹ = π A * π (slMap σ γ) * (π A)⁻¹ := by
  choose F hF using hgU
  choose α hα using hg1
  have hadd : ∀ X Y, F (X + Y) = F X + F Y := by
    intro X Y
    refine congrArg toAdd (hΨ.1 ?_)
    calc Ψ (ofAdd (F (X + Y))) = g • Ψ (ofAdd (X + Y)) := (hF _).symm
      _ = g • Ψ (ofAdd X) * g • Ψ (ofAdd Y) := by rw [ofAdd_add, map_mul, smul_mul']
      _ = Ψ (ofAdd (F X + F Y)) := by rw [hF, hF, ofAdd_add, map_mul]
  let Φ : Matrix (Fin 2) (Fin 2) K →+ Matrix (Fin 2) (Fin 2) K := AddMonoidHom.mk' F hadd
  have hΦ : ∀ X, Φ X = F X := fun X => rfl
  have hΦi : Function.Injective Φ := by
    intro X Y h
    rw [hΦ, hΦ] at h
    have h1 : g • Ψ (ofAdd X) = g • Ψ (ofAdd Y) := by rw [hF, hF, h]
    exact congrArg toAdd (hΨ.1 (MulAction.injective g h1))
  have hαs : Function.Surjective α := by
    intro δ
    obtain ⟨γ, hγ⟩ := hg2 δ
    exact ⟨γ, hΨ.injective_π ((hα γ).symm.trans hγ)⟩
  have htw : ∀ γ X, Φ (slm γ * X) = slm (α γ) * Φ X := by
    intro γ X
    rw [hΦ, hΦ]
    have h : Ψ (ofAdd (F (slm γ * X))) = Ψ (ofAdd (slm (α γ) * F X)) := by
      rw [← hF, hΨ.2, hΨ.2, ← hF, ← hα, smul_smul, smul_smul, inv_mul_cancel_right]
    exact congrArg toAdd (hΨ.1 h)
  obtain ⟨σ, A, B, hA, hB, hform, hconj⟩ := exists_semilinear_form Φ hΦi hαs htw
  obtain ⟨μ, hμ, hdet⟩ := exists_det_one hK hA
  refine ⟨σ, slOf _ hdet, μ • B, ?_, fun X => ?_, fun γ => ?_⟩
  · rw [isUnit_iff_isUnit_det] at hB
    rw [isUnit_iff_isUnit_det, det_smul]
    exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ hμ)).mul hB
  · rw [hF, slm_slOf, ← hΦ, hform]
    congr 2
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  · rw [hα]
    congr 1
    rw [eq_mul_inv_iff_mul_eq, ← map_mul, ← map_mul]
    congr 1
    apply slm_injective
    simp only [slm, Subgroup.coe_mul, Units.val_mul]
    rw [← slm, ← slm, ← slm, slm_slOf, slm_slMap, Matrix.mul_smul, hconj, Matrix.smul_mul]

theorem exists_semiHom [Finite K] (hK : ringChar K = 2) (hΨ : IsCoord π Ψ) (N : Subgroup G)
    (hN1 : ∀ g ∈ N, ∀ γ, ∃ δ, g * π γ * g⁻¹ = π δ)
    (hNU : ∀ g ∈ N, ∀ X, ∃ Y, g • Ψ (ofAdd X) = Ψ (ofAdd Y)) :
    ∃ s : ↥N →* (K ≃+* K), ∀ g : ↥N, IsSemi Ψ (g : G) (s g) := by
  have hex : ∀ g : ↥N, ∃ σ, IsSemi Ψ (g : G) σ := by
    intro g
    obtain ⟨σ, A, B, -, hact, -⟩ := exists_form hK hΨ (hN1 g g.2)
      (exists_conj_eq_of_inv (hN1 _ (N.inv_mem g.2))) (hNU g g.2)
    exact ⟨σ, hact.isSemi⟩
  choose s hs using hex
  refine ⟨{ toFun := s, map_one' := ?_, map_mul' := ?_ }, hs⟩
  · exact (hs 1).unique hΨ.1 isSemi_one
  · intro g h
    exact (hs (g * h)).unique hΨ.1 ((hs g).mul (hs h))

theorem smul_eq_of_conj_one
    (hC : ∀ c : G, (∀ γ, c * π γ = π γ * c) → ∀ X, c • Ψ X = Ψ X) {g : G}
    {A : ↥(StatedSL 2 K)} (hconj : ∀ γ, g * π γ * g⁻¹ = π A * π (slMap 1 γ) * (π A)⁻¹) :
    ∀ X, g • Ψ X = π A • Ψ X := by
  intro X
  have h := hC ((π A)⁻¹ * g) (fun γ => by
    have h1 := hconj γ
    rw [slMap_one] at h1
    calc (π A)⁻¹ * g * π γ = (π A)⁻¹ * (g * π γ * g⁻¹) * g := by group
      _ = π γ * ((π A)⁻¹ * g) := by rw [h1]; group) X
  rw [mul_smul, inv_smul_eq_iff] at h
  exact h

@[expose] def lineHom (r : Fin 2 → K) : (Fin 2 → K) →+ Matrix (Fin 2) (Fin 2) K :=
  AddMonoidHom.mk' (fun v => vecMulVec v r) fun v w => add_vecMulVec v w r

variable (Ψ) in
@[expose] def lineSub (r : Fin 2 → K) : Subgroup Q :=
  (Ψ.comp (AddMonoidHom.toMultiplicative (lineHom r))).range

theorem mem_lineSub {r : Fin 2 → K} {q : Q} :
    q ∈ lineSub Ψ r ↔ ∃ v, Ψ (ofAdd (vecMulVec v r)) = q := Iff.rfl

theorem lineSub_le_range (r : Fin 2 → K) : lineSub Ψ r ≤ Ψ.range := by
  rintro _ ⟨v, rfl⟩
  exact ⟨_, rfl⟩

theorem smul_mem_lineSub (hΨ : IsCoord π Ψ) {r : Fin 2 → K} (γ : ↥(StatedSL 2 K)) {q : Q}
    (hq : q ∈ lineSub Ψ r) : π γ • q ∈ lineSub Ψ r := by
  obtain ⟨v, rfl⟩ := mem_lineSub.1 hq
  exact mem_lineSub.2 ⟨slm γ *ᵥ v, by rw [← mul_vecMulVec, hΨ.2]⟩

theorem lineSub_ne_bot (hΨ : IsCoord π Ψ) {r : Fin 2 → K} (hr : r ≠ 0) : lineSub Ψ r ≠ ⊥ := by
  intro h
  have h1 : Ψ (ofAdd (vecMulVec (Pi.single 0 1) r)) = 1 := by
    have : Ψ (ofAdd (vecMulVec (Pi.single 0 1) r)) ∈ lineSub Ψ r := mem_lineSub.2 ⟨_, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  have h2 := congrArg toAdd (hΨ.1 (h1.trans (map_one Ψ).symm))
  apply hr
  ext j
  have h3 := congrFun (congrFun h2 0) j
  simpa [vecMulVec] using h3

theorem eq_bot_or_eq_lineSub (hΨ : IsCoord π Ψ) {r : Fin 2 → K} {J : Subgroup Q}
    (hJ : ∀ γ, ∀ q ∈ J, π γ • q ∈ J) (hle : J ≤ lineSub Ψ r) : J = ⊥ ∨ J = lineSub Ψ r := by
  rcases J.bot_or_exists_ne_one with hbot | ⟨q, hqJ, hq1⟩
  · exact Or.inl hbot
  right
  obtain ⟨v, hv⟩ := mem_lineSub.1 (hle hqJ)
  let S : AddSubgroup (Fin 2 → K) :=
    { carrier := {w | Ψ (ofAdd (vecMulVec w r)) ∈ J}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, add_vecMulVec, ofAdd_add, map_mul] at ha hb ⊢
        exact J.mul_mem ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, zero_vecMulVec, ofAdd_zero, map_one]
        exact J.one_mem
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, neg_vecMulVec, ofAdd_neg, map_inv] at ha ⊢
        exact J.inv_mem ha }
  have hS : S = ⊤ := by
    refine eq_top_of_slMulVec_mem le_rfl (S := S) (fun γ w hw => ?_) (v := v) ?_ ?_
    · show Ψ (ofAdd (vecMulVec (slm γ *ᵥ w) r)) ∈ J
      rw [← mul_vecMulVec, hΨ.2]
      exact hJ γ _ hw
    · show Ψ (ofAdd (vecMulVec v r)) ∈ J
      rw [hv]
      exact hqJ
    · rintro rfl
      apply hq1
      rw [← hv, zero_vecMulVec, ofAdd_zero, map_one]
  refine le_antisymm hle fun q' hq' => ?_
  obtain ⟨w, rfl⟩ := mem_lineSub.1 hq'
  have hw : w ∈ S := hS ▸ AddSubgroup.mem_top w
  exact hw

theorem smul_lineSub {g : G} {σ : K ≃+* K} {A B : Matrix (Fin 2) (Fin 2) K}
    (hact : IsAct Ψ g σ A B) (hA : IsUnit A) (r : Fin 2 → K) :
    g • lineSub Ψ r = lineSub Ψ (Bᵀ *ᵥ (σ ∘ r)) := by
  have hX : ∀ v, A * (vecMulVec v r).map σ * B = vecMulVec (A *ᵥ (σ ∘ v)) (Bᵀ *ᵥ (σ ∘ r)) :=
    fun v => by rw [map_vecMulVec, mul_vecMulVec_mul]
  ext q
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨q', hq', rfl⟩
    obtain ⟨v, rfl⟩ := mem_lineSub.1 hq'
    exact mem_lineSub.2 ⟨A *ᵥ (σ ∘ v), by rw [hact, hX]⟩
  · intro hq
    obtain ⟨w, rfl⟩ := mem_lineSub.1 hq
    obtain ⟨u, hu⟩ := (mulVec_surjective_iff_isUnit.2 hA) w
    refine ⟨Ψ (ofAdd (vecMulVec (σ.symm ∘ u) r)), mem_lineSub.2 ⟨_, rfl⟩, ?_⟩
    rw [hact, hX]
    have hu' : A *ᵥ (σ ∘ (σ.symm ∘ u)) = w := by
      rw [← hu]
      congr 1
      ext i
      simp
    rw [hu']

theorem lineSub_smul {c : K} (hc : c ≠ 0) (r : Fin 2 → K) :
    lineSub Ψ (c • r) = lineSub Ψ r := by
  ext q
  constructor
  · intro hq
    obtain ⟨v, rfl⟩ := mem_lineSub.1 hq
    exact mem_lineSub.2 ⟨c • v, by rw [vecMulVec_smul, smul_vecMulVec]⟩
  · intro hq
    obtain ⟨v, rfl⟩ := mem_lineSub.1 hq
    exact mem_lineSub.2 ⟨c⁻¹ • v, by
      rw [vecMulVec_smul, smul_vecMulVec, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩

theorem exists_eq_smul_of_lineSub_le (hΨ : IsCoord π Ψ) {r s : Fin 2 → K}
    (h : lineSub Ψ s ≤ lineSub Ψ r) : ∃ c : K, s = c • r := by
  obtain ⟨v, hv⟩ := mem_lineSub.1 (h (mem_lineSub.2 ⟨Pi.single 0 1, rfl⟩))
  exact ⟨v 0, eq_smul_of_vecMulVec_eq (congrArg toAdd (hΨ.1 hv))⟩

theorem comp_mulVec (σ : K ≃+* K) (P : Matrix (Fin 2) (Fin 2) K) (w : Fin 2 → K) :
    σ ∘ (P *ᵥ w) = P.map σ *ᵥ (σ ∘ w) := by
  ext i
  exact RingHom.map_mulVec σ.toRingHom P w i

theorem exists_fixed_lineSub [Finite K] (hK : ringChar K = 2) (hΨ : IsCoord π Ψ)
    (N : Subgroup G) (hN1 : ∀ g ∈ N, ∀ γ, ∃ δ, g * π γ * g⁻¹ = π δ)
    (hNU : ∀ g ∈ N, ∀ X, ∃ Y, g • Ψ (ofAdd X) = Ψ (ofAdd Y))
    (hC : ∀ c : G, (∀ γ, c * π γ = π γ * c) → ∀ X, c • Ψ X = Ψ X) :
    ∃ r : Fin 2 → K, r ≠ 0 ∧ ∀ g ∈ N, g • lineSub Ψ r = lineSub Ψ r := by
  obtain ⟨s, hs⟩ := exists_semiHom hK hΨ N hN1 hNU
  have hform : ∀ g : ↥N, ∃ (A : ↥(StatedSL 2 K)) (B : Matrix (Fin 2) (Fin 2) K), IsUnit B ∧
      IsAct Ψ (g : G) (s g) (slm A) B ∧
      ∀ γ, (g : G) * π γ * (g : G)⁻¹ = π A * π (slMap (s g) γ) * (π A)⁻¹ := by
    intro g
    obtain ⟨σ, A, B, hB, hact, hconj⟩ := exists_form hK hΨ (hN1 g g.2)
      (exists_conj_eq_of_inv (hN1 _ (N.inv_mem g.2))) (hNU g g.2)
    have e : s g = σ := (hs g).unique hΨ.1 hact.isSemi
    exact ⟨A, B, hB, e ▸ hact, e ▸ hconj⟩
  have hslu : ∀ A : ↥(StatedSL 2 K), IsUnit (slm A) := fun A => (A : GL (Fin 2) K).isUnit
  have hN0 : ∀ g : ↥N, s g = 1 → ∀ r, (g : G) • lineSub Ψ r = lineSub Ψ r := by
    intro g hg r
    obtain ⟨A, B, -, -, hconj⟩ := hform g
    rw [hg] at hconj
    have h1 := smul_eq_of_conj_one hC hconj
    have hact : IsAct Ψ (g : G) 1 (slm A) 1 := fun X => by
      have e : X.map ⇑(1 : K ≃+* K) = X := by
        ext i j
        rfl
      rw [h1, ← hΨ.2, Matrix.mul_one, e]
    rw [smul_lineSub hact (hslu A), transpose_one, one_mulVec]
    rfl
  haveI := isCyclic_ringEquiv (K := K)
  obtain ⟨⟨_, g₀, rfl⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥s.range)
  obtain ⟨A₀, B₀, hB₀, hact₀, -⟩ := hform g₀
  have hCu : IsUnit B₀ᵀ := (Matrix.isUnit_transpose B₀).2 hB₀
  have hiter : ∀ (k : ℕ) (r : Fin 2 → K), ((g₀ ^ k : ↥N) : G) • lineSub Ψ r =
      lineSub Ψ (HardMathSupport.Foote.ModuleExclusions.Ai (s g₀) B₀ᵀ k *ᵥ
        ((s g₀ ^ k : K ≃+* K) ∘ r)) := by
    intro k
    induction k with
    | zero =>
      intro r
      rw [pow_zero, OneMemClass.coe_one, one_smul]
      show _ = lineSub Ψ ((1 : Matrix (Fin 2) (Fin 2) K) *ᵥ _)
      rw [one_mulVec]
      rfl
    | succ k ih =>
      intro r
      rw [pow_succ', Subgroup.coe_mul, mul_smul, ih, smul_lineSub hact₀ (hslu A₀), comp_mulVec,
        mulVec_mulVec]
      congr 2
      ext i
      exact (HardMathSupport.Foote.ModuleExclusions.pow_succ_apply (s g₀) k (r i)).symm
  have hm1 : s (g₀ ^ orderOf (s g₀)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
  have hP : ∀ r : Fin 2 → K, ∃ c : K,
      HardMathSupport.Foote.ModuleExclusions.Ai (s g₀) B₀ᵀ (orderOf (s g₀)) *ᵥ r = c • r := by
    intro r
    have h1 := hiter (orderOf (s g₀)) r
    rw [hN0 _ hm1, pow_orderOf_eq_one] at h1
    exact exists_eq_smul_of_lineSub_le hΨ h1.symm.le
  obtain ⟨c, hc⟩ := exists_smul_one_of_forall hP
  obtain ⟨b, hb, l, hl⟩ := exists_fixed_vec (s g₀) hCu hc
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_smul, ← mulVec_zero B₀ᵀ] at hl
    have h1 := Matrix.mulVec_injective_iff_isUnit.2 hCu hl
    apply hb
    ext i
    have h2 := congrFun h1 i
    simpa using h2
  have hfix₀ : ((g₀ : ↥N) : G) • lineSub Ψ b = lineSub Ψ b := by
    rw [smul_lineSub hact₀ (hslu A₀), hl, lineSub_smul hl0]
  refine ⟨b, hb, fun g hg => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨s ⟨g, hg⟩, ⟨g, hg⟩, rfl⟩)
  have hk' : s (g₀ ^ k) = s ⟨g, hg⟩ := by
    have h1 := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at h1
    rw [map_zpow]
    exact h1
  have hh : s ((g₀ ^ k)⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hk', inv_mul_cancel]
  have hstab : ((g₀ : ↥N) : G) ^ k ∈ MulAction.stabilizer G (lineSub Ψ b) :=
    Subgroup.zpow_mem _ (MulAction.mem_stabilizer_iff.2 hfix₀) k
  have e : g = ((g₀ ^ k : ↥N) : G) * (((g₀ ^ k)⁻¹ * ⟨g, hg⟩ : ↥N) : G) := by
    rw [← Subgroup.coe_mul, mul_inv_cancel_left]
  rw [e, mul_smul, hN0 _ hh b, Subgroup.coe_zpow]
  exact MulAction.mem_stabilizer_iff.1 hstab

end CFSG.Quasithin.RonanD321.SL2Model
