module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.MatRows
public import CFSG.Quasithin.Background.F918Z2SwapData
public import CFSG.Quasithin.Background.F918Z2Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

private theorem mat_eq_one_of_mul_mul_eq_self {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (P R : Matrix (Fin 4) (Fin 4) F)
    (h : ∀ M : Matrix (Fin 4) (Fin 4) F, P * M * R = M) : P = 1 ∧ R = 1 := by
  classical
  have hPP' : P * R = 1 := by simpa using h 1
  have hcomm : ∀ X : Matrix (Fin 4) (Fin 4) F, P * X = X * P := by
    intro X
    have h1 : P * X * (P * R) = X * P := by
      calc P * X * (P * R) = P * (X * P) * R := by noncomm_ring
        _ = X * P := h (X * P)
    rwa [hPP', Matrix.mul_one] at h1
  obtain ⟨c, hc⟩ : P ∈ Set.range (Matrix.scalar (Fin 4)) :=
    Matrix.mem_range_scalar_iff_commute_single'.mpr fun i j => (hcomm _).symm
  have hc0 : c ≠ 0 := by
    intro hc0
    have h1 : (Matrix.scalar (Fin 4) c * R) 0 0 = 1 := by
      rw [hc, hPP']
      exact Matrix.one_apply_eq 0
    simp only [Matrix.scalar_apply, Matrix.diagonal_mul, hc0, zero_mul] at h1
    exact zero_ne_one h1
  have hc1 : c = 1 := (CFSG.Quasithin.G64.eq_zero_or_eq_one_of_card_two hF c).resolve_left hc0
  have hP : P = 1 := by
    rw [← hc, hc1, Matrix.scalar_apply, Matrix.diagonal_one]
  have hR : R = 1 := by
    have h1 := h 1
    rw [hP] at h1
    simpa using h1
  exact ⟨hP, hR⟩

private theorem map_eq_self_of_card_eq_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (ϑ : F ≃+* F) (M : Matrix (Fin 4) (Fin 4) F) : M.map ⇑ϑ = M := by
  have hϑ : ∀ x : F, ϑ x = x := fun x =>
    (CFSG.Quasithin.G64.eq_zero_or_eq_one_of_card_two hF x).elim
      (fun h => by rw [h, map_zero]) (fun h => by rw [h, map_one])
  ext i j
  simpa using hϑ (M i j)

section SwapNormal

variable {W : Type} [CommGroup W] [Finite W] {L₁ L₂ : Subgroup (MulAut W)} {F : Type} [Field F]
  [Finite F] {β : W ≃* Multiplicative (Matrix (Fin 4) (Fin 4) F)}
  {ρ : ↥L₁ →* Matrix.GeneralLinearGroup (Fin 4) F} {σ : ↥L₂ →* Matrix.GeneralLinearGroup (Fin 4) F}

theorem exists_transpose_model (hF : Nat.card F = 2) (hM : IsMatModel L₁ L₂ β ρ σ)
    {t : MulAut W} (ht : t * t = 1) (ht₁ : L₂ = L₁.map (MulAut.conj t).toMonoidHom) :
    ∃ (β' : W ≃* Multiplicative (Matrix (Fin 4) (Fin 4) F))
      (ρ' : ↥L₁ →* Matrix.GeneralLinearGroup (Fin 4) F),
      IsMatModel L₁ L₂ β' ρ' σ ∧ matColSub β' 0 = matColSub β 0 ∧
        ∀ v, Multiplicative.toAdd (β' (t v)) = (Multiplicative.toAdd (β' v))ᵀ := by
  classical
  obtain ⟨ϑ, Q, R, hQ, _, hform⟩ :=
    CFSG.Quasithin.SwapModel.swap_form_of_sqModel hM (by norm_num : 0 < 4) ht₁
  have hform' : ∀ v, Multiplicative.toAdd (β (t v)) =
      Q * (Multiplicative.toAdd (β v))ᵀ * R := by
    intro v
    rw [hform v, map_eq_self_of_card_eq_two hF ϑ]
  have ht_apply : ∀ v : W, t (t v) = v := by
    intro v
    have h1 := congrArg (fun u : MulAut W => u v) ht
    simpa using h1
  have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQdet
  have hQ'Q : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQdet
  have hrel : ∀ M : Matrix (Fin 4) (Fin 4) F, Q * Rᵀ * M * Qᵀ * R = M := by
    intro M
    obtain ⟨v, rfl⟩ : ∃ v, Multiplicative.toAdd (β v) = M :=
      ⟨β.symm (Multiplicative.ofAdd M), by simp⟩
    have h1 := hform' (t v)
    rw [ht_apply v] at h1
    have h2 := hform' v
    rw [h2, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h1
    calc Q * Rᵀ * Multiplicative.toAdd (β v) * Qᵀ * R
        = Q * (Rᵀ * (Multiplicative.toAdd (β v) * Qᵀ)) * R := by noncomm_ring
      _ = Multiplicative.toAdd (β v) := h1.symm
  have hrel' : ∀ M : Matrix (Fin 4) (Fin 4) F, (Q * Rᵀ) * M * (Qᵀ * R) = M := by
    intro M
    simpa only [Matrix.mul_assoc] using hrel M
  obtain ⟨hQR, -⟩ := mat_eq_one_of_mul_mul_eq_self hF (Q * Rᵀ) (Qᵀ * R) hrel'
  have hRQt : R * Qᵀ = 1 := by
    have h1 := congrArg Matrix.transpose hQR
    simpa [Matrix.transpose_mul] using h1
  have hRinv : R = (Q⁻¹)ᵀ := by
    refine Matrix.left_inv_eq_left_inv hRQt ?_
    rw [← Matrix.transpose_mul, hQQ, Matrix.transpose_one]
  let q : Matrix.GeneralLinearGroup (Fin 4) F := ⟨Q⁻¹, Q, hQ'Q, hQQ⟩
  have hq : ((q : Matrix.GeneralLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Q⁻¹ := rfl
  have hqinv : (((q⁻¹ : Matrix.GeneralLinearGroup (Fin 4) F)) :
      Matrix (Fin 4) (Fin 4) F) = Q := rfl
  let ρ' : ↥L₁ →* Matrix.GeneralLinearGroup (Fin 4) F := (MulAut.conj q).toMonoidHom.comp ρ
  have hρ' : ∀ g : ↥L₁, ((ρ' g : Matrix.GeneralLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = Q⁻¹ * (ρ g : Matrix (Fin 4) (Fin 4) F) * Q := by
    intro g
    show ((q * ρ g * q⁻¹ : Matrix.GeneralLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = _
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hq, hqinv]
  let Lm : Matrix (Fin 4) (Fin 4) F ≃+ Matrix (Fin 4) (Fin 4) F :=
    { toFun := fun M => Q⁻¹ * M
      invFun := fun M => Q * M
      left_inv := fun M => by
        show Q * (Q⁻¹ * M) = M
        rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
      right_inv := fun M => by
        show Q⁻¹ * (Q * M) = M
        rw [← Matrix.mul_assoc, hQ'Q, Matrix.one_mul]
      map_add' := fun M N => by rw [Matrix.mul_add] }
  let β' : W ≃* Multiplicative (Matrix (Fin 4) (Fin 4) F) :=
    β.trans (AddEquiv.toMultiplicative Lm)
  have hβ' : ∀ v : W, Multiplicative.toAdd (β' v) = Q⁻¹ * Multiplicative.toAdd (β v) := by
    intro v
    simp [β', Lm, AddEquiv.toMultiplicative_apply_apply]
  have hmul : ∀ g : ↥L₁, (ρ g : Matrix (Fin 4) (Fin 4) F) * Q =
      Q * (ρ' g : Matrix (Fin 4) (Fin 4) F) := by
    intro g
    calc (ρ g : Matrix (Fin 4) (Fin 4) F) * Q
        = 1 * ((ρ g : Matrix (Fin 4) (Fin 4) F) * Q) := (Matrix.one_mul _).symm
      _ = (Q * Q⁻¹) * ((ρ g : Matrix (Fin 4) (Fin 4) F) * Q) := by rw [hQQ]
      _ = Q * (Q⁻¹ * (ρ g : Matrix (Fin 4) (Fin 4) F) * Q) := by noncomm_ring
      _ = Q * (ρ' g : Matrix (Fin 4) (Fin 4) F) := by rw [hρ' g]
  have hmul2 : ∀ g : ↥L₁, Q⁻¹ * (ρ g : Matrix (Fin 4) (Fin 4) F) =
      (ρ' g : Matrix (Fin 4) (Fin 4) F) * Q⁻¹ := by
    intro g
    calc Q⁻¹ * (ρ g : Matrix (Fin 4) (Fin 4) F)
        = Q⁻¹ * (ρ g : Matrix (Fin 4) (Fin 4) F) * 1 := (Matrix.mul_one _).symm
      _ = Q⁻¹ * (ρ g : Matrix (Fin 4) (Fin 4) F) * (Q * Q⁻¹) := by rw [hQQ]
      _ = (Q⁻¹ * (ρ g : Matrix (Fin 4) (Fin 4) F) * Q) * Q⁻¹ := by noncomm_ring
      _ = (ρ' g : Matrix (Fin 4) (Fin 4) F) * Q⁻¹ := by rw [hρ' g]
  have hkey : ∀ (g : ↥L₁) (M : Matrix (Fin 4) (Fin 4) F),
      Q⁻¹ * ((ρ g : Matrix (Fin 4) (Fin 4) F) * M) =
        (Q⁻¹ * (ρ g : Matrix (Fin 4) (Fin 4) F) * Q) * (Q⁻¹ * M) := by
    intro g M
    calc Q⁻¹ * ((ρ g : Matrix (Fin 4) (Fin 4) F) * M)
        = Q⁻¹ * (ρ g : Matrix (Fin 4) (Fin 4) F) * M := by rw [Matrix.mul_assoc]
      _ = Q⁻¹ * (ρ g : Matrix (Fin 4) (Fin 4) F) * (Q * Q⁻¹) * M := by
            rw [hQQ, Matrix.mul_one]
      _ = (Q⁻¹ * (ρ g : Matrix (Fin 4) (Fin 4) F) * Q) * (Q⁻¹ * M) := by noncomm_ring
  have hmodel : IsMatModel L₁ L₂ β' ρ' σ := by
    refine ⟨?_, ?_, ?_, ?_, hM.U_irr⟩
    · intro g v
      apply Multiplicative.toAdd.injective
      have h1 : Multiplicative.toAdd (β ((g : MulAut W) v)) =
          (ρ g : Matrix (Fin 4) (Fin 4) F) * Multiplicative.toAdd (β v) := by
        simpa using congrArg Multiplicative.toAdd (hM.hρ g v)
      rw [hβ', h1]
      rw [hβ' v]
      rw [hρ' g]
      exact hkey g (Multiplicative.toAdd (β v))
    · intro x v
      apply Multiplicative.toAdd.injective
      have h1 : Multiplicative.toAdd (β ((x : MulAut W) v)) = Multiplicative.toAdd (β v) *
          (((σ x : Matrix.GeneralLinearGroup (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
        simpa using congrArg Multiplicative.toAdd (hM.hσ x v)
      rw [hβ', h1]
      rw [hβ' v]
      rw [toAdd_ofAdd, Matrix.mul_assoc]
    · intro U hU
      let Lv : (Fin 4 → F) ≃+ (Fin 4 → F) :=
        { toFun := fun w => Q.mulVec w
          invFun := fun w => Q⁻¹.mulVec w
          left_inv := fun w => by
            show Q⁻¹.mulVec (Q.mulVec w) = w
            rw [Matrix.mulVec_mulVec, hQ'Q, Matrix.one_mulVec]
          right_inv := fun w => by
            show Q.mulVec (Q⁻¹.mulVec w) = w
            rw [Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
          map_add' := fun a b => by rw [Matrix.mulVec_add] }
      have hmapinv : ∀ (g : ↥L₁) (w : Fin 4 → F),
          (ρ g : Matrix (Fin 4) (Fin 4) F).mulVec (Lv w) =
            Lv ((ρ' g : Matrix (Fin 4) (Fin 4) F).mulVec w) := by
        intro g w
        show (ρ g : Matrix (Fin 4) (Fin 4) F).mulVec (Q.mulVec w) =
          Q.mulVec ((ρ' g : Matrix (Fin 4) (Fin 4) F).mulVec w)
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul g]
      have hU' : ∀ (g : ↥L₁) (w : Fin 4 → F), w ∈ U.map Lv.toAddMonoidHom →
          (ρ g : Matrix (Fin 4) (Fin 4) F).mulVec w ∈ U.map Lv.toAddMonoidHom := by
        intro g w hw
        obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp hw
        exact AddSubgroup.mem_map.mpr
          ⟨((ρ' g : Matrix.GeneralLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec u,
            hU g u hu, (hmapinv g u).symm⟩
      rcases hM.I_irr (U.map Lv.toAddMonoidHom) hU' with hbot | htop
      · left
        refine le_bot_iff.mp ?_
        intro w hw
        have hmem : Lv w ∈ U.map Lv.toAddMonoidHom := ⟨w, hw, rfl⟩
        rw [hbot] at hmem
        have h0 : Lv w = 0 := by simpa using hmem
        have h1 : w = Lv.symm 0 := by rw [← h0, Lv.symm_apply_apply]
        simpa using h1
      · right
        refine eq_top_iff.mpr ?_
        intro w _
        have hmem : Lv w ∈ U.map Lv.toAddMonoidHom := by
          rw [htop]
          exact AddSubgroup.mem_top _
        obtain ⟨u, hu, huw⟩ := AddSubgroup.mem_map.mp hmem
        rwa [← Lv.injective huw]
    · intro φ hφ
      let ψ : (Fin 4 → F) →+ (Fin 4 → F) :=
        { toFun := fun w => Q.mulVec (φ (Q⁻¹.mulVec w))
          map_zero' := by simp
          map_add' := by
            intro a b
            simp [map_add, Matrix.mulVec_add] }
      have hψ : ∀ (g : ↥L₁) (w : Fin 4 → F),
          ψ ((ρ g : Matrix (Fin 4) (Fin 4) F).mulVec w) =
            (ρ g : Matrix (Fin 4) (Fin 4) F).mulVec (ψ w) := by
        intro g w
        show Q.mulVec (φ (Q⁻¹.mulVec ((ρ g : Matrix (Fin 4) (Fin 4) F).mulVec w))) =
          (ρ g : Matrix (Fin 4) (Fin 4) F).mulVec (Q.mulVec (φ (Q⁻¹.mulVec w)))
        have h1 : Q⁻¹.mulVec ((ρ g : Matrix (Fin 4) (Fin 4) F).mulVec w) =
            ((ρ' g : Matrix.GeneralLinearGroup (Fin 4) F) :
              Matrix (Fin 4) (Fin 4) F).mulVec (Q⁻¹.mulVec w) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul2 g]
        rw [h1, hφ g (Q⁻¹.mulVec w), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul g]
      obtain ⟨c, hc⟩ := hM.comm_F ψ hψ
      refine ⟨c, fun w => ?_⟩
      have h2 : Q⁻¹.mulVec (Q.mulVec (φ (Q⁻¹.mulVec (Q.mulVec w)))) =
          Q⁻¹.mulVec (c • Q.mulVec w) := by
        simpa [ψ] using congrArg (fun x => Q⁻¹.mulVec x) (hc (Q.mulVec w))
      have hL : Q⁻¹.mulVec (Q.mulVec (φ (Q⁻¹.mulVec (Q.mulVec w)))) = φ w := by
        rw [Matrix.mulVec_mulVec, hQ'Q, Matrix.one_mulVec, Matrix.mulVec_mulVec,
          hQ'Q, Matrix.one_mulVec]
      have hR : Q⁻¹.mulVec (c • Q.mulVec w) = c • w := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hQ'Q, Matrix.one_mulVec]
      rw [hL, hR] at h2
      exact h2
  have hcol : matColSub β' 0 = matColSub β 0 := by
    ext v
    constructor
    · intro hv a k hk
      have hv' : ∀ l : Fin 4, (Q⁻¹ * Multiplicative.toAdd (β v)) l k = 0 := by
        intro l
        rw [← hβ' v]
        exact hv l k hk
      have hMv : Multiplicative.toAdd (β v) = Q * (Q⁻¹ * Multiplicative.toAdd (β v)) := by
        rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
      rw [hMv, Matrix.mul_apply]
      exact Finset.sum_eq_zero fun l _ => by rw [hv' l, mul_zero]
    · intro hv a k hk
      rw [hβ' v, Matrix.mul_apply]
      exact Finset.sum_eq_zero fun l _ => by rw [hv l k hk, mul_zero]
  refine ⟨β', ρ', hmodel, hcol, ?_⟩
  intro v
  have hstep : ∀ M : Matrix (Fin 4) (Fin 4) F,
      Q⁻¹ * (Q * M * (Q⁻¹)ᵀ) = M * (Q⁻¹)ᵀ := by
    intro M
    calc Q⁻¹ * (Q * M * (Q⁻¹)ᵀ) = (Q⁻¹ * Q) * (M * (Q⁻¹)ᵀ) := by noncomm_ring
      _ = M * (Q⁻¹)ᵀ := by rw [hQ'Q, Matrix.one_mul]
  rw [hβ' (t v), hform' v, hβ' v, Matrix.transpose_mul, hRinv]
  exact hstep _

theorem exists_congr_form (hF : Nat.card F = 2) (hM : IsMatModel L₁ L₂ β ρ σ) {t : MulAut W}
    (htr : ∀ v, Multiplicative.toAdd (β (t v)) = (Multiplicative.toAdd (β v))ᵀ)
    {a : MulAut W} (ha : L₁.map (MulAut.conj a).toMonoidHom = L₁) (hat : a * t = t * a) :
    ∃ B : Matrix (Fin 4) (Fin 4) F, IsUnit B ∧
      ∀ v, Multiplicative.toAdd (β (a v)) = B * Multiplicative.toAdd (β v) * Bᵀ := by
  classical
  obtain ⟨ϑ, B₁, B₂, hB₁, hB₂, hform⟩ :=
    CFSG.Quasithin.normalizer_form_of_sqModel_left hM (by norm_num : 0 < 4) ha
  have hform' : ∀ v, Multiplicative.toAdd (β (a v)) =
      B₁ * Multiplicative.toAdd (β v) * B₂ := by
    intro v
    rw [hform v, map_eq_self_of_card_eq_two hF ϑ]
  have hrelT : ∀ M : Matrix (Fin 4) (Fin 4) F, B₁ * Mᵀ * B₂ = B₂ᵀ * Mᵀ * B₁ᵀ := by
    intro M
    obtain ⟨v, hv⟩ : ∃ v, Multiplicative.toAdd (β v) = M :=
      ⟨β.symm (Multiplicative.ofAdd M), by simp⟩
    have h1 : Multiplicative.toAdd (β (a (t v))) = B₁ * Mᵀ * B₂ := by
      rw [hform' (t v), htr v, hv]
    have h2 : a (t v) = t (a v) := by
      have h2 := congrArg (fun u : MulAut W => u v) hat
      simpa using h2
    have h3 : Multiplicative.toAdd (β (a (t v))) = B₂ᵀ * Mᵀ * B₁ᵀ := by
      rw [h2, htr (a v), hform' v, hv, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.mul_assoc]
    rw [h1] at h3
    exact h3
  have hrel : ∀ N : Matrix (Fin 4) (Fin 4) F, B₁ * N * B₂ = B₂ᵀ * N * B₁ᵀ := by
    intro N
    have h1 := hrelT Nᵀ
    simpa using h1
  have hB₁det : IsUnit B₁.det := (Matrix.isUnit_iff_isUnit_det B₁).mp hB₁
  have hB₂det : IsUnit B₂.det := (Matrix.isUnit_iff_isUnit_det B₂).mp hB₂
  have hB₁'inv : B₁⁻¹ * B₁ = 1 := Matrix.nonsing_inv_mul B₁ hB₁det
  have hB₂mul : B₂ * B₂⁻¹ = 1 := Matrix.mul_nonsing_inv B₂ hB₂det
  have hB₂'inv : B₂⁻¹ * B₂ = 1 := Matrix.nonsing_inv_mul B₂ hB₂det
  have h2inv : (B₂⁻¹)ᵀ * B₂ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hB₂mul, Matrix.transpose_one]
  have h1inv : B₁ᵀ * (B₁⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hB₁'inv, Matrix.transpose_one]
  have hrelP : ∀ N : Matrix (Fin 4) (Fin 4) F, ((B₂⁻¹)ᵀ * B₁) * N * (B₂ * (B₁⁻¹)ᵀ) = N := by
    intro N
    calc ((B₂⁻¹)ᵀ * B₁) * N * (B₂ * (B₁⁻¹)ᵀ)
        = (B₂⁻¹)ᵀ * (B₁ * N * B₂) * (B₁⁻¹)ᵀ := by noncomm_ring
      _ = (B₂⁻¹)ᵀ * (B₂ᵀ * N * B₁ᵀ) * (B₁⁻¹)ᵀ := by rw [hrel N]
      _ = N := by
          calc (B₂⁻¹)ᵀ * (B₂ᵀ * N * B₁ᵀ) * (B₁⁻¹)ᵀ
              = ((B₂⁻¹)ᵀ * B₂ᵀ) * N * (B₁ᵀ * (B₁⁻¹)ᵀ) := by noncomm_ring
            _ = 1 * N * 1 := by rw [h2inv, h1inv]
            _ = N := by noncomm_ring
  obtain ⟨hP1, -⟩ := mat_eq_one_of_mul_mul_eq_self hF ((B₂⁻¹)ᵀ * B₁) (B₂ * (B₁⁻¹)ᵀ) hrelP
  have hB₂eq : B₂ = B₁ᵀ := by
    have h3 : B₂ᵀ * (B₂⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hB₂'inv, Matrix.transpose_one]
    have h4 : B₁ = B₂ᵀ := by
      calc B₁ = 1 * B₁ := (Matrix.one_mul B₁).symm
        _ = (B₂ᵀ * (B₂⁻¹)ᵀ) * B₁ := by rw [h3]
        _ = B₂ᵀ * ((B₂⁻¹)ᵀ * B₁) := by rw [Matrix.mul_assoc]
        _ = B₂ᵀ * 1 := by rw [hP1]
        _ = B₂ᵀ := Matrix.mul_one _
    rw [h4, Matrix.transpose_transpose]
  exact ⟨B₁, hB₁, fun v => by rw [hform' v, hB₂eq]⟩

end SwapNormal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
