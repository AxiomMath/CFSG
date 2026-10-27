module

public import CFSG.Quasithin.Background.SmithB45SL3Fix
public import CFSG.Quasithin.Background.SmithB42SL3Field
public import CFSG.Quasithin.Background.SmithB42SL3Aut

public section

namespace CFSG.Quasithin

namespace B45SL3

open CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.H CFSG.Quasithin.H.SL3Pair Matrix
open CFSG.Quasithin.B42SL3 (innerPart mem_innerPart exists_lift_of_inner elem_mul_self
  commute_of_rep isTransvection_of_involution)
open CFSG.QuasithinUnique.K1 (stdAut descendAut_stdAut eq_of_proj_eq_of_mul_self_eq_one)
open scoped MatrixGroups Matrix

section Lift

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {U : Type} [AddCommGroup U]
  [Module (ZMod 2) U] (ρ : Representation (ZMod 2) SL(3, F) U)
  (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
  (A : Subgroup (U ≃ₗ[ZMod 2] U)) (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)
  [CFSG.IsElementaryAbelian 2 A]

omit [Fintype F] in
include hker in
theorem eq_of_rep_eq {t t' : SL(3, F)} (ht : t * t = 1) (ht' : t' * t' = 1) (h : ρ t = ρ t') :
    t = t' := by
  refine eq_of_proj_eq_of_mul_self_eq_one (by norm_num) ht ht' ?_
  rw [proj_eq_proj_iff]
  apply hker
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [hinv, map_mul, h, ← map_mul, ht', map_one]

@[expose] noncomputable def liftSub : Subgroup SL(3, F) where
  carrier := {t | t * t = 1 ∧ ∃ b ∈ innerPart ρ hker A hA,
    ∀ u, ((b : ↥A) : U ≃ₗ[ZMod 2] U) u = ρ t u}
  one_mem' := ⟨mul_one 1, 1, Subgroup.one_mem _, fun u => by simp⟩
  mul_mem' := by
    rintro t t' ⟨ht, b, hb, hbt⟩ ⟨ht', b', hb', hbt'⟩
    have hcommρ : ρ t * ρ t' = ρ t' * ρ t := by
      have hc := CFSG.QuasithinUnique.Setup.Layer.Actor.comm_of_isElementaryAbelian_two
        inferInstance _ (b : ↥A).2 _ (b' : ↥A).2
      refine LinearMap.ext fun u => ?_
      have h1 := LinearEquiv.congr_fun hc u
      simp only [LinearEquiv.mul_apply] at h1
      rw [Module.End.mul_apply, Module.End.mul_apply, ← hbt, ← hbt', ← hbt, ← hbt']
      exact h1
    have hcomm : t * t' = t' * t := by
      by_cases ht1 : t' = 1
      · rw [ht1, mul_one, one_mul]
      exact commute_of_rep ρ hker (isTransvection_of_involution ht1 ht') hcommρ
    refine ⟨?_, b * b', Subgroup.mul_mem _ hb hb', fun u => ?_⟩
    · calc t * t' * (t * t') = t * (t' * t) * t' := by group
        _ = t * (t * t') * t' := by rw [hcomm]
        _ = (t * t) * (t' * t') := by group
        _ = 1 := by rw [ht, ht', one_mul]
    · show ((b : ↥A) : U ≃ₗ[ZMod 2] U) (((b' : ↥A) : U ≃ₗ[ZMod 2] U) u) = ρ (t * t') u
      rw [hbt', hbt, map_mul]
      rfl
  inv_mem' := by
    rintro t ⟨ht, b, hb, hbt⟩
    have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    exact ⟨by rw [hinv]; exact ht, b, hb, fun u => by rw [hinv]; exact hbt u⟩

omit [Fintype F] in
theorem liftSub_sq {t : SL(3, F)} (ht : t ∈ liftSub ρ hker A hA) : t * t = 1 := ht.1

omit [Fintype F] in
theorem liftSub_comm {t t' : SL(3, F)} (ht : t ∈ liftSub ρ hker A hA)
    (ht' : t' ∈ liftSub ρ hker A hA) : t * t' = t' * t := by
  have h1 := (liftSub ρ hker A hA).mul_mem ht ht'
  have h2 := liftSub_sq ρ hker A hA h1
  have h3 := liftSub_sq ρ hker A hA ht
  have h4 := liftSub_sq ρ hker A hA ht'
  calc t * t' = t * (t * t' * (t * t')) * t' := by rw [h2, mul_one]
    _ = (t * t) * t' * t * (t' * t') := by group
    _ = t' * t := by rw [h3, h4, one_mul, mul_one]

variable {f : ℕ}

theorem card_innerPart_le_liftSub (hf : 1 ≤ f) (hNat : Nat.card F = 2 ^ f)
    (hirr : ρ.IsIrreducible) :
    Nat.card ↥(innerPart ρ hker A hA) ≤ Nat.card ↥(liftSub ρ hker A hA) := by
  classical
  have hlift : ∀ x : ↥(innerPart ρ hker A hA), ∃ t : SL(3, F), t * t = 1 ∧
      ∀ u, ((x : ↥A) : U ≃ₗ[ZMod 2] U) u = ρ t u :=
    fun x => exists_lift_of_inner ρ hker A hA hf hNat hirr x x.2
  choose t ht2 htρ using hlift
  refine Nat.card_le_card_of_injective (fun x => ⟨t x, ht2 x, x, x.2, htρ x⟩) ?_
  intro x y hxy
  have h : t x = t y := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Subtype.ext
  refine LinearEquiv.ext fun u => ?_
  rw [htρ x, htρ y, h]

theorem exists_std_of_outer (a : ↥A) (ha : a ∉ innerPart ρ hker A hA) :
    ∃ (M : GL (Fin 3) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      normalizerHom ρ hker A hA a =
        LinearFlag.conjAut 3 F M * LinearFlag.fieldAut 3 F σ * LinearFlag.dualAut 3 F ^ ε ∧
      (ε = 0 → σ ≠ 1) := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨M, σ, ε, hε, hαeq⟩ := hgen (normalizerHom ρ hker A hA a)
  refine ⟨M, σ, ε, hε, hαeq, fun h0 hσ => ha ?_⟩
  subst h0 hσ
  rw [pow_zero, mul_one, map_one, mul_one] at hαeq
  rw [mem_innerPart, hαeq]
  refine mem_inner_of_sq_conjAut ?_
  rw [← hαeq, ← map_mul, elem_mul_self A a, map_one]

omit [Fintype F] in
theorem stdAut_fix (a : ↥A) {M : GL (Fin 3) F} {σ : F ≃+* F} {ε : ℕ}
    (hΦ : normalizerHom ρ hker A hA a =
      LinearFlag.conjAut 3 F M * LinearFlag.fieldAut 3 F σ * LinearFlag.dualAut 3 F ^ ε)
    {t : SL(3, F)} (ht : t ∈ liftSub ρ hker A hA) : stdAut M σ ε t = t := by
  obtain ⟨ht2, b, hb, hbt⟩ := ht
  have hint := intertwines_psi ρ (normalizerHom ρ hker A hA a) (stdAut M σ ε)
    (by rw [descendAut_stdAut, hΦ]) (a : U ≃ₗ[ZMod 2] U) (exists_induced ρ hker A hA a)
  have hab : ∀ u, (a : U ≃ₗ[ZMod 2] U) (((b : ↥A) : U ≃ₗ[ZMod 2] U) u) =
      ((b : ↥A) : U ≃ₗ[ZMod 2] U) ((a : U ≃ₗ[ZMod 2] U) u) := by
    intro u
    have hc := CFSG.QuasithinUnique.Setup.Layer.Actor.comm_of_isElementaryAbelian_two
      inferInstance _ a.2 _ (b : ↥A).2
    have := LinearEquiv.congr_fun hc u
    simpa only [LinearEquiv.mul_apply] using this
  have hρ : ρ (stdAut M σ ε t) = ρ t := by
    refine LinearMap.ext fun u => ?_
    obtain ⟨v, rfl⟩ := (a : U ≃ₗ[ZMod 2] U).surjective u
    have h1 := hint t v
    rw [← hbt, hab, hbt] at h1
    exact h1.symm
  have hψ2 : stdAut M σ ε t * stdAut M σ ε t = 1 := by rw [← map_mul, ht2, map_one]
  exact eq_of_rep_eq ρ hker hψ2 ht2 hρ

@[expose] noncomputable def liftGL : Subgroup (GL (Fin 3) F) :=
  (liftSub ρ hker A hA).map Matrix.SpecialLinearGroup.toGL

omit [Fintype F] in
theorem card_liftGL : Nat.card ↥(liftGL ρ hker A hA) = Nat.card ↥(liftSub ρ hker A hA) :=
  Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective

omit [Fintype F] in
theorem liftGL_sq : ∀ B ∈ liftGL ρ hker A hA, B * B = 1 := by
  rintro _ ⟨t, ht, rfl⟩
  rw [← map_mul, liftSub_sq ρ hker A hA ht, map_one]

omit [Fintype F] in
theorem liftGL_comm : ∀ B ∈ liftGL ρ hker A hA, ∀ C ∈ liftGL ρ hker A hA, B * C = C * B := by
  rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
  rw [← map_mul, ← map_mul, liftSub_comm ρ hker A hA ht ht']

theorem card_innerPart_le_of_outer (hf : 1 ≤ f) (hNat : Nat.card F = 2 ^ f)
    (hirr : ρ.IsIrreducible) (a : ↥A) (ha : a ∉ innerPart ρ hker A hA) :
    Nat.card ↥(innerPart ρ hker A hA) ≤ Nat.card F := by
  classical
  refine (card_innerPart_le_liftSub ρ hker A hA hf hNat hirr).trans ?_
  rw [← card_liftGL ρ hker A hA]
  obtain ⟨M, σ, ε, hε, hΦ, hσ⟩ := exists_std_of_outer ρ hker A hA a ha
  have hfix := fun {t : SL(3, F)} (ht : t ∈ liftSub ρ hker A hA) => stdAut_fix ρ hker A hA a hΦ ht
  interval_cases ε
  ·
    have hσ1 : σ ≠ RingEquiv.refl F := hσ rfl
    let s : MulAut (StdMod (Fin 3) F) := matAut M * fieldMap σ
    have hs : IsSemilinear s σ := by
      intro c v
      show (M : Matrix (Fin 3) (Fin 3) F) *ᵥ (fun i => σ ((c • v) i)) =
        σ c • ((M : Matrix (Fin 3) (Fin 3) F) *ᵥ fun i => σ (v i))
      rw [← Matrix.mulVec_smul]
      congr 1
      funext i
      simp
    refine B42SL3.card_le_of_comm_semilinear (liftGL ρ hker A hA) (liftGL_sq ρ hker A hA)
      (liftGL_comm ρ hker A hA) hs hσ1 ?_
    rintro _ ⟨t, ht, rfl⟩ v
    have h1 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) (hfix ht)
    simp only [stdAut, pow_zero, mul_one, MulAut.mul_apply] at h1
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix] at h1
    change (M : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F).map σ *
      ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = t at h1
    show (M : Matrix (Fin 3) (Fin 3) F) *ᵥ (fun i => σ (((t : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)) =
      (t : Matrix (Fin 3) (Fin 3) F) *ᵥ ((M : Matrix (Fin 3) (Fin 3) F) *ᵥ fun i => σ (v i))
    have h2 : (fun i => σ (((t : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)) =
        (t : Matrix (Fin 3) (Fin 3) F).map σ *ᵥ fun i => σ (v i) := by
      funext i
      exact RingHom.map_mulVec (σ : F →+* F) _ v i
    have h4 : (M : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F).map σ =
        (t : Matrix (Fin 3) (Fin 3) F) * (M : Matrix (Fin 3) (Fin 3) F) := by
      calc (M : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F).map σ =
          (M : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F).map σ *
            ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (M : Matrix (Fin 3) (Fin 3) F) := by
            rw [Matrix.mul_assoc _ ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F),
              ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        _ = (t : Matrix (Fin 3) (Fin 3) F) * (M : Matrix (Fin 3) (Fin 3) F) := by rw [h1]
    rw [h2, Matrix.mulVec_mulVec, h4, ← Matrix.mulVec_mulVec]
  ·
    let z : MulAut (StdMod (Fin 3) F) := fieldMap σ.symm * matAut M⁻¹
    have hz : IsSemilinear z σ.symm := by
      intro c v
      show (fun i => σ.symm ((((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (c • v)) i)) =
        σ.symm c • (fun i => σ.symm ((((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i))
      rw [Matrix.mulVec_smul]
      funext i
      simp
    refine card_le_of_comm_transpose (liftGL ρ hker A hA) (liftGL_sq ρ hker A hA)
      (liftGL_comm ρ hker A hA) hz ?_
    rintro _ ⟨t, ht, rfl⟩ v
    have ht2 := liftSub_sq ρ hker A hA ht
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have h1 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) (hfix ht)
    simp only [stdAut, pow_one, MulAut.mul_apply] at h1
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix] at h1
    change (M : Matrix (Fin 3) (Fin 3) F) *
      ((((t⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ).map σ *
      ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = t at h1
    rw [htinv] at h1
    have h3 : ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F) =
        ((t : Matrix (Fin 3) (Fin 3) F)ᵀ).map σ *
          ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      conv_lhs => rw [← h1]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul]
    show (fun i => σ.symm ((((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((t : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) i)) =
      (Matrix.SpecialLinearGroup.toGL t : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ
        (fun i => σ.symm ((((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i))
    rw [Matrix.mulVec_mulVec, h3, ← Matrix.mulVec_mulVec]
    funext i
    have := RingHom.map_mulVec (σ.symm : F →+* F) (((t : Matrix (Fin 3) (Fin 3) F)ᵀ).map σ)
      (((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i
    simp only [RingEquiv.coe_toRingHom] at this
    rw [this]
    congr 1
    ext r s
    simp

end Lift

section RootPair

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem vecMulVec_ne_zero {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0) : vecMulVec v w ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  intro h0
  have := congrFun (congrFun h0 i) j
  simp only [vecMulVec_apply, Matrix.zero_apply] at this
  exact mul_ne_zero hi hj this

omit [CharP F 2] in
theorem exists_dual_pair {w₁ w₂ : Fin 3 → F} (hind : LinearIndependent F ![w₁, w₂]) :
    ∃ x y : Fin 3 → F, w₁ ⬝ᵥ x = 1 ∧ w₂ ⬝ᵥ x = 0 ∧ w₁ ⬝ᵥ y = 0 ∧ w₂ ⬝ᵥ y = 1 := by
  classical
  set c := crossProduct w₁ w₂ with hc
  have hc0 : c ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hind
  have h1 : w₁ ⬝ᵥ c = 0 := dot_self_cross w₁ w₂
  have h2 : w₂ ⬝ᵥ c = 0 := dot_cross_self w₁ w₂
  obtain ⟨ψ₀, h0⟩ := exists_dotProduct_eq_one hc0
  let P : Matrix (Fin 3) (Fin 3) F := Matrix.of ![ψ₀, w₁, w₂]
  have hP : IsUnit P := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    have := linearIndependent_three h0 h1 h2 hind
    convert this using 1
    funext r
    fin_cases r <;> rfl
  obtain ⟨Q, hPQ⟩ : ∃ Q : Matrix (Fin 3) (Fin 3) F, P * Q = 1 :=
    ⟨P⁻¹, Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)⟩
  have hent : ∀ r s : Fin 3, ![ψ₀, w₁, w₂] r ⬝ᵥ (Q *ᵥ Pi.single s 1) = if r = s then 1 else 0 := by
    intro r s
    have := congrFun (congrFun hPQ r) s
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this, Matrix.mulVec_single_one]
    simp [dotProduct, P, Matrix.col_apply]
  refine ⟨Q *ᵥ Pi.single 1 1, Q *ᵥ Pi.single 2 1, ?_, ?_, ?_, ?_⟩
  · exact (hent 1 1).trans (by simp)
  · exact (hent 2 1).trans (by simp)
  · exact (hent 1 2).trans (by simp)
  · exact (hent 2 2).trans (by simp)

theorem isRootPair_of_comm {t₁ t₂ : SL(3, F)}
    (h1 : CFSG.QuasithinUnique.Setup.X7a.IsTransvection t₁)
    (h2 : CFSG.QuasithinUnique.Setup.X7a.IsTransvection t₂)
    (hc : t₁ * t₂ = t₂ * t₁)
    (hne : ∀ μ : F, (t₂ : Matrix (Fin 3) (Fin 3) F) - 1 ≠
      μ • ((t₁ : Matrix (Fin 3) (Fin 3) F) - 1)) :
    IsRootPair t₁ t₂ := by
  classical
  have hq12 := B42SL3.sub_one_mul_sub_one_eq_zero h1 h2 hc
  have hq21 := B42SL3.sub_one_mul_sub_one_eq_zero h2 h1 hc.symm
  have hsq1 := isTransvection_sq h1
  have hsq2 := isTransvection_sq h2
  obtain ⟨v₁, w₁, hv₁, hw₁, hwv₁, ht₁⟩ := h1
  obtain ⟨v₂, w₂, hv₂, hw₂, hwv₂, ht₂⟩ := h2
  rw [ht₁, ht₂, add_sub_cancel_left, add_sub_cancel_left, vecMulVec_mul_vecMulVec] at hq12
  rw [ht₁, ht₂, add_sub_cancel_left, add_sub_cancel_left, vecMulVec_mul_vecMulVec] at hq21
  have hwv12 : w₁ ⬝ᵥ v₂ = 0 := by
    by_contra h
    rw [vecMulVec_smul, smul_eq_zero] at hq12
    rcases hq12 with h' | h'
    · exact h h'
    · exact vecMulVec_ne_zero hv₁ hw₂ h'
  have hwv21 : w₂ ⬝ᵥ v₁ = 0 := by
    by_contra h
    rw [vecMulVec_smul, smul_eq_zero] at hq21
    rcases hq21 with h' | h'
    · exact h h'
    · exact vecMulVec_ne_zero hv₂ hw₁ h'
  by_cases hdep : ∃ lam : F, lam • v₁ = v₂
  ·
    obtain ⟨lam, rfl⟩ := hdep
    have hlam : lam ≠ 0 := by
      rintro rfl
      exact hv₂ (zero_smul F v₁)
    refine Or.inl ⟨v₁, w₁, lam • w₂, hv₁, hwv₁, ?_, ?_, ht₁, ?_⟩
    · rw [smul_dotProduct, hwv21, smul_zero]
    · rw [LinearIndependent.pair_iff' hw₁]
      intro a ha
      apply hne a
      rw [ht₂, ht₁, add_sub_cancel_left, add_sub_cancel_left, smul_vecMulVec, ← vecMulVec_smul,
        ← ha, vecMulVec_smul]
    · rw [ht₂, smul_vecMulVec, vecMulVec_smul]
  ·
    push Not at hdep
    have hind₁₂ : LinearIndependent F ![v₁, v₂] := by
      rw [LinearIndependent.pair_iff' hv₁]
      exact hdep
    have hprod1 : t₁ * t₂ ≠ 1 := by
      intro h
      apply hne 1
      have h3 : t₂ = t₁ := by
        calc t₂ = t₁ * t₁ * t₂ := by rw [hsq1, one_mul]
          _ = t₁ * (t₁ * t₂) := by group
          _ = t₁ := by rw [h, mul_one]
      rw [h3, one_smul]
    have hprod2 : t₁ * t₂ * (t₁ * t₂) = 1 := by
      calc t₁ * t₂ * (t₁ * t₂) = t₁ * (t₂ * t₁) * t₂ := by group
        _ = t₁ * (t₁ * t₂) * t₂ := by rw [hc]
        _ = (t₁ * t₁) * (t₂ * t₂) := by group
        _ = 1 := by rw [hsq1, hsq2, one_mul]
    obtain ⟨v, w, -, -, -, hvw⟩ := isTransvection_of_involution hprod1 hprod2
    have hsum : vecMulVec v₁ w₁ + vecMulVec v₂ w₂ = vecMulVec v w := by
      have e : ((t₁ * t₂ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
          1 + vecMulVec v₁ w₁ + vecMulVec v₂ w₂ := by
        rw [Matrix.SpecialLinearGroup.coe_mul, ht₁, ht₂]
        have : vecMulVec v₁ w₁ * vecMulVec v₂ w₂ = 0 := by
          rw [vecMulVec_mul_vecMulVec, hwv12, zero_smul, vecMulVec_zero]
        calc (1 + vecMulVec v₁ w₁) * (1 + vecMulVec v₂ w₂) =
            1 + vecMulVec v₁ w₁ + vecMulVec v₂ w₂ + vecMulVec v₁ w₁ * vecMulVec v₂ w₂ := by
              noncomm_ring
          _ = _ := by rw [this, add_zero]
      have := hvw.symm.trans e
      rw [add_assoc] at this
      exact (add_left_cancel this).symm
    have hdepw : ¬ LinearIndependent F ![w₁, w₂] := by
      intro hindw
      obtain ⟨x, y, hx1, hx2, hy1, hy2⟩ := exists_dual_pair hindw
      have hX := congrArg (fun M => M *ᵥ x) hsum
      have hY := congrArg (fun M => M *ᵥ y) hsum
      simp only [Matrix.add_mulVec, B42SL3.vecMulVec_mulVec_eq, hx1, hx2, hy1, hy2, one_smul,
        zero_smul, add_zero, zero_add] at hX hY
      have hwx : w ⬝ᵥ x ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hX
        exact hv₁ hX
      apply hdep ((w ⬝ᵥ y) / (w ⬝ᵥ x))
      rw [hX, hY, smul_smul, div_mul_cancel₀ _ hwx]
    rw [LinearIndependent.pair_iff' hw₁] at hdepw
    push Not at hdepw
    obtain ⟨μ, rfl⟩ := hdepw
    have hμ : μ ≠ 0 := by
      rintro rfl
      exact hw₂ (zero_smul F w₁)
    refine Or.inr ⟨w₁, v₁, μ • v₂, hw₁, ?_, ?_, ?_, ?_, ?_⟩
    · rw [dotProduct_comm] at hwv₁
      rw [dotProduct_comm]
      exact hwv₁
    · rw [dotProduct_smul, hwv12, smul_zero]
    · rw [LinearIndependent.pair_iff' hv₁]
      intro a ha
      apply hdep (a / μ)
      rw [div_eq_inv_mul, mul_smul, ha, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    · rw [ht₁]
    · rw [ht₂, vecMulVec_smul, smul_vecMulVec]

end RootPair

section RootPairLift

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {U : Type} [AddCommGroup U]
  [Module (ZMod 2) U] (ρ : Representation (ZMod 2) SL(3, F) U)
  (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
  (A : Subgroup (U ≃ₗ[ZMod 2] U)) (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)
  [CFSG.IsElementaryAbelian 2 A]

theorem exists_rootPair_of_lt {t₁ : SL(3, F)} (ht₁ : t₁ ∈ liftSub ρ hker A hA) (ht₁1 : t₁ ≠ 1)
    (hlt : Nat.card {t : ↥(liftSub ρ hker A hA) // ∃ μ : F, ((t : SL(3, F)) :
      Matrix (Fin 3) (Fin 3) F) - 1 = μ • ((t₁ : Matrix (Fin 3) (Fin 3) F) - 1)} <
      Nat.card ↥(liftSub ρ hker A hA)) :
    ∃ t₂ ∈ liftSub ρ hker A hA, IsRootPair t₁ t₂ := by
  classical
  obtain ⟨t₂, ht₂⟩ : ∃ t₂ : ↥(liftSub ρ hker A hA), ¬ ∃ μ : F, ((t₂ : SL(3, F)) :
      Matrix (Fin 3) (Fin 3) F) - 1 = μ • ((t₁ : Matrix (Fin 3) (Fin 3) F) - 1) := by
    by_contra h
    push Not at h
    have : Nat.card ↥(liftSub ρ hker A hA) ≤ Nat.card {t : ↥(liftSub ρ hker A hA) //
        ∃ μ : F, ((t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - 1 =
          μ • ((t₁ : Matrix (Fin 3) (Fin 3) F) - 1)} :=
      Nat.card_le_card_of_injective (fun t => ⟨t, h t⟩) (fun x y hxy => congrArg Subtype.val hxy)
    omega
  push Not at ht₂
  have ht₂1 : (t₂ : SL(3, F)) ≠ 1 := by
    intro h
    apply ht₂ 0
    rw [h, Matrix.SpecialLinearGroup.coe_one, sub_self, zero_smul]
  refine ⟨t₂, t₂.2, isRootPair_of_comm (isTransvection_of_involution ht₁1 (liftSub_sq ρ hker A hA
    ht₁)) (isTransvection_of_involution ht₂1 (liftSub_sq ρ hker A hA t₂.2))
    (liftSub_comm ρ hker A hA ht₁ t₂.2) ht₂⟩

omit [Fintype F] [CharP F 2] [CFSG.IsElementaryAbelian 2 A] in
theorem card_rootGroup_le [Fintype F] {t₁ : SL(3, F)} (ht₁1 : t₁ ≠ 1) (S : Subgroup SL(3, F)) :
    Nat.card {t : S // ∃ μ : F, ((t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - 1 =
      μ • ((t₁ : Matrix (Fin 3) (Fin 3) F) - 1)} ≤ Nat.card F := by
  classical
  have hX : (t₁ : Matrix (Fin 3) (Fin 3) F) - 1 ≠ 0 := by
    intro h
    exact ht₁1 (Subtype.ext (sub_eq_zero.mp h))
  choose μ hμ using fun t : {t : S // ∃ μ : F, ((t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - 1 =
    μ • ((t₁ : Matrix (Fin 3) (Fin 3) F) - 1)} => t.2
  refine Nat.card_le_card_of_injective μ fun x y hxy => ?_
  have h1 : ((x : S) : SL(3, F)) = ((y : S) : SL(3, F)) := by
    apply Subtype.ext
    have := (hμ x).trans ((congrArg (· • ((t₁ : Matrix (Fin 3) (Fin 3) F) - 1)) hxy).trans
      (hμ y).symm)
    exact sub_left_injective this
  exact Subtype.ext (Subtype.ext h1)

variable {f : ℕ}

theorem exists_rootPair_of_card (hf : 1 ≤ f) (hNat : Nat.card F = 2 ^ f)
    (hirr : ρ.IsIrreducible) (hcard : Nat.card F < Nat.card ↥(innerPart ρ hker A hA)) :
    ∃ t₁ ∈ liftSub ρ hker A hA, ∃ t₂ ∈ liftSub ρ hker A hA, IsRootPair t₁ t₂ := by
  classical
  have hle := card_innerPart_le_liftSub ρ hker A hA hf hNat hirr
  have h1 : 1 < Nat.card ↥(liftSub ρ hker A hA) := by
    have : 1 ≤ Nat.card F := Nat.card_pos
    omega
  have : Nontrivial ↥(liftSub ρ hker A hA) := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨⟨t₁, ht₁⟩, ht₁1⟩ := exists_ne (1 : ↥(liftSub ρ hker A hA))
  have ht₁1' : t₁ ≠ 1 := fun h => ht₁1 (Subtype.ext h)
  refine ⟨t₁, ht₁, exists_rootPair_of_lt ρ hker A hA ht₁ ht₁1' ?_⟩
  have := card_rootGroup_le ht₁1' (liftSub ρ hker A hA)
  omega

end RootPairLift

section Field

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {U : Type} [AddCommGroup U]
  [Module (ZMod 2) U] (ρ : Representation (ZMod 2) SL(3, F) U)
  (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
  (A : Subgroup (U ≃ₗ[ZMod 2] U)) (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)
  [CFSG.IsElementaryAbelian 2 A]

@[expose] def IsFieldType (a : ↥A) : Prop :=
  ∃ (M : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 ∧
    normalizerHom ρ hker A hA a = LinearFlag.conjAut 3 F M * LinearFlag.fieldAut 3 F σ

theorem exists_field_of_card (hirr : ρ.IsIrreducible)
    (hcard : 2 * Nat.card ↥(innerPart ρ hker A hA) < Nat.card ↥A) :
    ∃ a : ↥A, IsFieldType ρ hker A hA a := by
  classical
  by_contra hno
  push Not at hno
  set Φ := normalizerHom ρ hker A hA with hΦ
  set E := semilinearAutGroup 3 F with hE
  obtain ⟨-, -, -, -, -, -, -, hRE, -, -⟩ := standard_outer_quotients (K := F) (n := 3)
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) le_rfl).1
  have hEi : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hRE' : E.index ≤ 2 := by
    rw [hR] at hRE
    have h1 : E.relIndex ⊤ ≤ 2 := hRE
    rwa [Subgroup.relIndex_top_right] at h1
  have hrel : E.relIndex Φ.range ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right le_top (by rw [Subgroup.relIndex_top_right]; exact hEi)).trans
      ((Subgroup.relIndex_top_right E).le.trans hRE')
  have hle : E ⊓ Φ.range ≤ (innerPart ρ hker A hA).map Φ := by
    rintro x ⟨hxE, a, rfl⟩
    refine ⟨a, ?_, rfl⟩
    obtain ⟨M, σ, hMσ⟩ := mem_semilinearAutGroup_iff.mp hxE
    by_cases hσ : σ = 1
    · rw [SetLike.mem_coe, mem_innerPart, hMσ, hσ, map_one, mul_one]
      refine mem_inner_of_sq_conjAut ?_
      have := elem_mul_self A a
      have h2 : Φ a * Φ a = 1 := by rw [← map_mul, this, map_one]
      rwa [hMσ, hσ, map_one, mul_one] at h2
    · exact absurd ⟨M, σ, hσ, hMσ⟩ (hno a)
  have hcardΦ : Nat.card Φ.range = Nat.card ↥A :=
    (Nat.card_congr (Equiv.ofInjective Φ (B42SL3.normalizerHom_injective ρ hker A hA hirr))).symm
  have hcardI : Nat.card ((innerPart ρ hker A hA).map Φ) = Nat.card ↥(innerPart ρ hker A hA) :=
    Subgroup.card_map_of_injective (B42SL3.normalizerHom_injective ρ hker A hA hirr)
  have hmul := Subgroup.relIndex_mul_card (H := E) (K := Φ.range)
  have hle' := Subgroup.card_le_of_le hle
  rw [hcardI] at hle'
  have : Nat.card ↥A ≤ 2 * Nat.card ↥(innerPart ρ hker A hA) := by
    rw [← hcardΦ, ← hmul]
    exact Nat.mul_le_mul hrel hle'
  omega

variable {f : ℕ}

theorem exists_rootPair_of_field (hf : 1 ≤ f) (hNat : Nat.card F = 2 ^ f)
    (hirr : ρ.IsIrreducible) {a : ↥A} (ha : IsFieldType ρ hker A hA a)
    (hcard : Nat.card F ≤ Nat.card ↥(innerPart ρ hker A hA)) :
    ∃ t₁ ∈ liftSub ρ hker A hA, ∃ t₂ ∈ liftSub ρ hker A hA, IsRootPair t₁ t₂ := by
  classical
  obtain ⟨M, σ, hσ, hΦ⟩ := ha
  have hΦ' : normalizerHom ρ hker A hA a =
      LinearFlag.conjAut 3 F M * LinearFlag.fieldAut 3 F σ * LinearFlag.dualAut 3 F ^ 0 := by
    rw [pow_zero, mul_one]
    exact hΦ
  have hfix := fun {t : SL(3, F)} (ht : t ∈ liftSub ρ hker A hA) => stdAut_fix ρ hker A hA a hΦ' ht
  have hle := card_innerPart_le_liftSub ρ hker A hA hf hNat hirr
  have hq2 : 2 ≤ Nat.card F := by
    rw [hNat]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h1 : 1 < Nat.card ↥(liftSub ρ hker A hA) := by omega
  have : Nontrivial ↥(liftSub ρ hker A hA) := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨⟨t₁, ht₁⟩, ht₁1⟩ := exists_ne (1 : ↥(liftSub ρ hker A hA))
  have ht₁1' : t₁ ≠ 1 := fun h => ht₁1 (Subtype.ext h)
  refine ⟨t₁, ht₁, exists_rootPair_of_lt ρ hker A hA ht₁ ht₁1' ?_⟩
  have hmat : ∀ {t : SL(3, F)}, t ∈ liftSub ρ hker A hA →
      (M : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F).map σ *
        ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = t := by
    intro t ht
    have h1 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) (hfix ht)
    simp only [stdAut, pow_zero, mul_one, MulAut.mul_apply] at h1
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix] at h1
    exact h1
  set X : Matrix (Fin 3) (Fin 3) F := (t₁ : Matrix (Fin 3) (Fin 3) F) - 1 with hXdef
  have hX0 : X ≠ 0 := fun h => ht₁1' (Subtype.ext (sub_eq_zero.mp h))
  have hXσ : (M : Matrix (Fin 3) (Fin 3) F) * X.map σ *
      ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = X := by
    have hmap : X.map σ = (t₁ : Matrix (Fin 3) (Fin 3) F).map σ - 1 := by
      rw [hXdef, Matrix.map_sub _ (map_sub σ), Matrix.map_one σ (map_zero σ) (map_one σ)]
    rw [hmap, Matrix.mul_sub, Matrix.sub_mul, hmat ht₁, Matrix.mul_one, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  have hfixμ : ∀ (t : ↥(liftSub ρ hker A hA)) (μ : F), ((t : SL(3, F)) :
      Matrix (Fin 3) (Fin 3) F) - 1 = μ • X → σ μ = μ := by
    intro t μ hμ
    have h2 := hmat t.2
    have ht : ((t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 + μ • X := by
      rw [← hμ, add_sub_cancel]
    rw [ht, Matrix.map_add _ (map_add σ), Matrix.map_one σ (map_zero σ) (map_one σ),
      Matrix.map_smul' _ _ _ (map_mul σ),
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.mul_smul, Matrix.smul_mul, hXσ] at h2
    have h3 : (σ μ - μ) • X = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr (add_left_cancel h2)
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hX0)
  have hσne : ∃ x : F, σ x ≠ x := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  obtain ⟨x₀, hx₀⟩ := hσne
  choose μ hμ using fun t : {t : ↥(liftSub ρ hker A hA) // ∃ μ : F, ((t : SL(3, F)) :
    Matrix (Fin 3) (Fin 3) F) - 1 = μ • ((t₁ : Matrix (Fin 3) (Fin 3) F) - 1)} => t.2
  have hinj : Function.Injective fun t => (⟨μ t, hfixμ t.1 (μ t) (hμ t)⟩ : {y : F // σ y = y}) := by
    intro t t' h
    have h1 : μ t = μ t' := congrArg Subtype.val h
    have h2 : ((t : ↥(liftSub ρ hker A hA)) : SL(3, F)) = ((t' : ↥(liftSub ρ hker A hA)) :
        SL(3, F)) := by
      apply Subtype.ext
      have := (hμ t).trans ((congrArg (· • X) h1).trans (hμ t').symm)
      exact sub_left_injective this
    exact Subtype.ext (Subtype.ext h2)
  have hlt1 := Nat.card_le_card_of_injective _ hinj
  have hlt2 : Nat.card {y : F // σ y = y} < Nat.card F := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_lt hx₀
  exact lt_of_le_of_lt hlt1 (lt_of_lt_of_le hlt2 (hcard.trans hle))

end Field

end B45SL3

end CFSG.Quasithin
