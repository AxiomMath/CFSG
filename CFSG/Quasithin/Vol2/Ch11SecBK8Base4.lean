module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

abbrev FixW (x : MulAut (W6 K)) : Type := {v : I6 → K // toAddMap x v = v}

theorem card_fix_sq_le [Finite K] {ι : Type} [Finite ι] {g : MulAut (StdMod ι K)}
    {σ : K ≃+* K} (hg : IsSemilinear g σ) (hσ : σ ≠ RingEquiv.refl K) :
    Nat.card {v : ι → K // toAddMap g v = v} ^ 2 ≤ Nat.card (ι → K) := by
  obtain ⟨θ, hθ⟩ : ∃ θ : K, σ θ ≠ θ := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  have hd : θ - σ θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  let φ : {v : ι → K // toAddMap g v = v} × {v : ι → K // toAddMap g v = v} → (ι → K) :=
    fun p => p.1.1 + θ • p.2.1
  have hφ : Function.Injective φ := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    simp only [φ] at h
    have h1 : toAddMap g (a + θ • b) = toAddMap g (a' + θ • b') := by rw [h]
    rw [toAddMap_add, toAddMap_add, hg, hg, ha, hb, ha', hb'] at h1
    have h2 : (θ - σ θ) • (b - b') = 0 := by
      have e : (θ - σ θ) • (b - b') =
          (a + θ • b - (a' + θ • b')) - (a + σ θ • b - (a' + σ θ • b')) := by
        rw [smul_sub, sub_smul, sub_smul]
        abel
      rw [e, h, h1, sub_self, sub_self, sub_zero]
    have hbb : b = b' := sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_left hd)
    subst hbb
    have haa : a = a' := add_right_cancel h
    subst haa
    rfl
  have := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, ← pow_two] at this

omit [Field K] in
theorem card_W6 [Finite K] : Nat.card (I6 → K) = Nat.card K ^ 6 := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := I6)]
  rfl

theorem inv_mulVec_eq {A : GL (Fin 3) K} {y z : Fin 3 → K}
    (h : z = (A : Matrix (Fin 3) (Fin 3) K) *ᵥ y) :
    ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ z = y := by
  rw [h, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]

theorem isSemilinear_of_tens {x : MulAut (W6 K)} {σ : K ≃+* K} {Φ : MulAut (StdMod (Fin 3) K)}
    {M : Matrix (Fin 2) (Fin 2) K} (hΦ : IsSemilinear Φ σ)
    (hx : ∀ v : I6 → K, toAddMap x v =
      Sum.elim (toAddMap Φ (M 0 0 • (v ∘ Sum.inl) + M 0 1 • (v ∘ Sum.inr)))
        (toAddMap Φ (M 1 0 • (v ∘ Sum.inl) + M 1 1 • (v ∘ Sum.inr)))) :
    IsSemilinear x σ := by
  intro c v
  rw [hx, hx]
  have e : ∀ a b : K, a • ((c • v) ∘ Sum.inl) + b • ((c • v) ∘ Sum.inr) =
      c • (a • (v ∘ Sum.inl) + b • (v ∘ Sum.inr)) := by
    intro a b
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    ring
  rw [e, e, hΦ, hΦ]
  funext i
  rcases i with i | i <;> rfl

theorem scalar_mulVec {β : K} (hβ : β ≠ 0) (w : Fin 3 → K) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 β hβ) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ w = β • w := by
  funext j
  simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem exists_dg_of_scalar {x : MulAut (W6 K)} {A₀ : GL (Fin 3) K} {β : K}
    (hx : ∀ v : I6 → K, toAddMap x v =
      Sum.elim ((A₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ (β • (v ∘ Sum.inl)))
        ((A₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ (β • (v ∘ Sum.inr)))) :
    ∃ A : GL (Fin 3) K, x = matAut (dgHom A) := by
  have hβ : β ≠ 0 := by
    rintro rfl
    have h1 : toAddMap x (Sum.elim (Pi.single 0 1) 0) = 0 := by
      rw [hx]
      funext i
      rcases i with i | i <;> simp
    rw [toAddMap_eq_zero_iff] at h1
    have h2 := congrFun h1 (Sum.inl 0)
    simp at h2
  refine ⟨A₀ * Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 β hβ),
    toAddMap_injective fun v => ?_⟩
  rw [hx, toAddMap_matAut]
  funext i
  rcases i with i | i
  · have h1 := congrFun (dgHom_mulVec_inl
      (A₀ * Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 β hβ)) v) i
    simp only [Function.comp_apply] at h1
    rw [h1, Units.val_mul, ← Matrix.mulVec_mulVec, scalar_mulVec]
    rfl
  · have h1 := congrFun (dgHom_mulVec_inr
      (A₀ * Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 β hβ)) v) i
    simp only [Function.comp_apply] at h1
    rw [h1, Units.val_mul, ← Matrix.mulVec_mulVec, scalar_mulVec]
    rfl

theorem card_fix_tens_le [Finite K] {x : MulAut (W6 K)} {A₀ : GL (Fin 3) K}
    {M : Matrix (Fin 2) (Fin 2) K}
    (hx : ∀ v : I6 → K, toAddMap x v =
      Sum.elim ((A₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ (M 0 0 • (v ∘ Sum.inl) + M 0 1 • (v ∘ Sum.inr)))
        ((A₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ (M 1 0 • (v ∘ Sum.inl) + M 1 1 • (v ∘ Sum.inr))))
    (hM : ¬ (M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1)) :
    Nat.card (FixW x) ≤ Nat.card K ^ 3 := by
  have hq : Nat.card (Fin 3 → K) = Nat.card K ^ 3 := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
  rw [← hq]
  have hc : ∀ v : FixW x,
      ((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (v.1 ∘ Sum.inl) =
        M 0 0 • (v.1 ∘ Sum.inl) + M 0 1 • (v.1 ∘ Sum.inr) ∧
      ((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (v.1 ∘ Sum.inr) =
        M 1 0 • (v.1 ∘ Sum.inl) + M 1 1 • (v.1 ∘ Sum.inr) := by
    intro v
    have h := v.2
    rw [hx] at h
    constructor
    · refine inv_mulVec_eq ?_
      funext j
      exact (congrFun h (Sum.inl j)).symm
    · refine inv_mulVec_eq ?_
      funext j
      exact (congrFun h (Sum.inr j)).symm
  have hext : ∀ v w : FixW x, v.1 ∘ Sum.inl = w.1 ∘ Sum.inl → v.1 ∘ Sum.inr = w.1 ∘ Sum.inr →
      v = w := by
    intro v w h1 h2
    apply Subtype.ext
    funext i
    rcases i with i | i
    · exact congrFun h1 i
    · exact congrFun h2 i
  by_cases h10 : M 1 0 = 0
  · by_cases h01 : M 0 1 = 0
    · have h00 : M 0 0 ≠ M 1 1 := fun h => hM ⟨h01, h10, h⟩
      refine Nat.card_le_card_of_injective (fun v : FixW x => v.1 ∘ Sum.inl + v.1 ∘ Sum.inr)
        fun v w hvw => ?_
      have hv := hc v
      have hw := hc w
      rw [h01, h10, zero_smul, add_zero, zero_smul, zero_add] at hv hw
      set z := v.1 ∘ Sum.inl - w.1 ∘ Sum.inl with hz
      have hz2 : z = w.1 ∘ Sum.inr - v.1 ∘ Sum.inr := by
        rw [hz]
        have := hvw
        simp only at this
        rw [sub_eq_sub_iff_add_eq_add, this, add_comm]
      have e1 : ((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ z = M 0 0 • z := by
        rw [hz, Matrix.mulVec_sub, hv.1, hw.1, smul_sub]
      have e2 : ((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ z = M 1 1 • z := by
        rw [hz2, Matrix.mulVec_sub, hv.2, hw.2, smul_sub]
      have e3 : (M 0 0 - M 1 1) • z = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
      have hz0 : z = 0 := (smul_eq_zero.mp e3).resolve_left (sub_ne_zero.mpr h00)
      have h1 : v.1 ∘ Sum.inl = w.1 ∘ Sum.inl := sub_eq_zero.mp (hz ▸ hz0)
      have h2 : v.1 ∘ Sum.inr = w.1 ∘ Sum.inr := (sub_eq_zero.mp (hz2 ▸ hz0)).symm
      exact hext v w h1 h2
    · refine Nat.card_le_card_of_injective (fun v : FixW x => v.1 ∘ Sum.inl) fun v w hvw => ?_
      have hv := (hc v).1
      have hw := (hc w).1
      simp only at hvw
      rw [hvw] at hv
      have e : M 0 1 • (v.1 ∘ Sum.inr) = M 0 1 • (w.1 ∘ Sum.inr) := by
        have := hv.symm.trans hw
        exact add_left_cancel this
      exact hext v w hvw (smul_right_injective _ h01 e)
  · refine Nat.card_le_card_of_injective (fun v : FixW x => v.1 ∘ Sum.inr) fun v w hvw => ?_
    have hv := (hc v).2
    have hw := (hc w).2
    simp only at hvw
    rw [hvw] at hv
    have e : M 1 0 • (v.1 ∘ Sum.inl) = M 1 0 • (w.1 ∘ Sum.inl) := by
      have := hv.symm.trans hw
      exact add_right_cancel this
    exact hext v w (smul_right_injective _ h10 e) hvw

theorem exists_dg_of_lt_card_fix [Finite K] {x : MulAut (W6 K)} (hx : x ∈ normD K)
    (hC : Nat.card K ^ 3 < Nat.card (FixW x)) : ∃ A : GL (Fin 3) K, x = matAut (dgHom A) := by
  obtain ⟨σ, Φ, M, hΦ, hxf⟩ := exists_semilinear_tens hx
  by_cases hσ : σ = RingEquiv.refl K
  swap
  · exfalso
    have h1 := card_fix_sq_le (isSemilinear_of_tens hΦ hxf) hσ
    rw [card_W6] at h1
    have h2 : (Nat.card K ^ 3) ^ 2 < Nat.card (FixW x) ^ 2 := Nat.pow_lt_pow_left hC (by norm_num)
    rw [← pow_mul] at h2
    exact absurd h1 (not_le.mpr h2)
  subst hσ
  obtain ⟨A₀, rfl⟩ := exists_matAut_of_mem_linSub (show Φ ∈ linSub from hΦ)
  have hxf' : ∀ v : I6 → K, toAddMap x v =
      Sum.elim ((A₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ (M 0 0 • (v ∘ Sum.inl) + M 0 1 • (v ∘ Sum.inr)))
        ((A₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (M 1 0 • (v ∘ Sum.inl) + M 1 1 • (v ∘ Sum.inr))) := fun v => hxf v
  by_cases hM : M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1
  · obtain ⟨h01, h10, h00⟩ := hM
    refine exists_dg_of_scalar (A₀ := A₀) (β := M 0 0) fun v => ?_
    rw [hxf', h01, h10, ← h00, zero_smul, zero_smul, add_zero, zero_add]
  · exact absurd (card_fix_tens_le hxf' hM) (not_le.mpr hC)

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
