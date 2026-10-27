module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTau

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec19

section Plain

variable {F : Type} [Field F] [Finite F] (σ : F ≃+* F)

theorem sl2_lang (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (y : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ)) (hy : y ^ 3 = 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
      Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype y =
        g * (Matrix.SpecialLinearGroup.map σ.toRingHom g)⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  set Y := Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype y with hY
  set A : Matrix (Fin 2) (Fin 2) F := (Y : Matrix (Fin 2) (Fin 2) F) with hA
  have hAσ : A.map σ = A := by
    ext i j
    exact RingHom.mem_eqLocusField.mp (y.1 i j).2
  have hAi : ∀ k : ℕ, CFSG.GH74.GLS.IVK.H90.Ai σ A k = A ^ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      show A * (CFSG.GH74.GLS.IVK.H90.Ai σ A k).map σ = A ^ (k + 1)
      rw [ih]
      have hk : (A ^ k).map σ = A ^ k := by
        have h := map_pow σ.toRingHom.mapMatrix A k
        simpa [RingHom.mapMatrix_apply, hAσ] using h
      rw [hk, pow_succ']
  have hA3 : CFSG.GH74.GLS.IVK.H90.Ai σ A 3 = 1 := by
    rw [hAi, hA, hY, ← Matrix.SpecialLinearGroup.coe_pow, ← map_pow, hy, map_one]
    rfl
  obtain ⟨B, hBdet, hAB⟩ := CFSG.GH74.GLS.IVK.H90.speiser σ A 3 hord (by norm_num) hA3
  have hAdet : A.det = 1 := Y.2
  have hmapdet : ∀ M : Matrix (Fin 2) (Fin 2) F, (M.map σ).det = σ M.det := fun M => by
    have := RingHom.map_det σ.toRingHom M
    simpa [RingHom.mapMatrix_apply] using this.symm
  have hδσ : σ B.det = B.det := by
    have h := congrArg Matrix.det hAB
    rw [Matrix.det_mul, hAdet, one_mul, hmapdet] at h
    exact h
  set δ := B.det with hδ
  set D : Matrix (Fin 2) (Fin 2) F := !![δ⁻¹, 0; 0, 1] with hDdef
  have hD : D.det = δ⁻¹ := by simp [hDdef, Matrix.det_fin_two_of]
  have hB'det : (B * D).det = 1 := by
    rw [Matrix.det_mul, hD]
    exact mul_inv_cancel₀ hBdet
  have hDσ : D.map σ = D := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hDdef, map_inv₀, hδσ]
  refine ⟨⟨B * D, hB'det⟩, ?_⟩
  have key : Y * Matrix.SpecialLinearGroup.map σ.toRingHom (⟨B * D, hB'det⟩ :
      Matrix.SpecialLinearGroup (Fin 2) F) = ⟨B * D, hB'det⟩ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show A * (σ.toRingHom.mapMatrix (B * D)) = B * D
    rw [map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
    show A * (B.map σ * D.map σ) = B * D
    rw [hDσ, ← mul_assoc, hAB]
  exact eq_mul_inv_of_mul_eq key

end Plain

section Model


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem exists_lang_A0 (P : D4Par n X σ) {a : C0 σ} (ha : a ∈ A0sub σ) (ha3 : a ^ 3 = 1) :
    ∃ h ∈ Asub σ, a = h * (tauAut σ h)⁻¹ := by
  obtain ⟨y, rfl⟩ := (mem_A0sub_iff P).mp ha
  have hinjm : Function.Injective
      (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype :
        Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ) →* Matrix.SpecialLinearGroup (Fin 2) X) := by
    intro u v huv
    apply Subtype.ext
    ext i j
    exact congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) X =>
      (M : Matrix (Fin 2) (Fin 2) X) i j) huv
  have hy3 : y ^ 3 = 1 := by
    apply hinjm
    apply iotaA_injective P
    rw [map_pow, map_pow, map_one, map_one]
    exact ha3
  have hσ1 : σ ≠ 1 := by
    obtain ⟨c, hc⟩ := P.exists_not_fixed
    intro h
    exact hc (by rw [h]; rfl)
  obtain ⟨g, hg⟩ := sl2_lang σ P.sigma_pow_three hσ1 y hy3
  refine ⟨iotaA P g, ?_, ?_⟩
  · rw [← iotaA_range P]
    exact ⟨g, rfl⟩
  · rw [hg, map_mul, map_inv, tau_iotaA P g]

end Model

end CFSG.RankThree.PartTwo.Sec19
