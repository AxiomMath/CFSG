module

public import CFSG.Quasithin.MS93.ML3Basic
public import CFSG.Quasithin.Vol2.KGNatSemiLin

public section

namespace CFSG.Quasithin.MS93.S36

open CFSG.Quasithin CFSG.Quasithin.Vol2 Matrix

variable {F : Type} [Field F]

theorem matrix_ext_of_mulVec {A B : Matrix (Fin 3) (Fin 3) F} (h : ∀ x, A *ᵥ x = B *ᵥ x) :
    A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rwa [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mulVec_single_one,
    Matrix.col_apply] at this

theorem mulVec_of_cols (c₀ c₁ c₂ x : Fin 3 → F) :
    (Matrix.of fun i j => (![c₀, c₁, c₂] : Fin 3 → Fin 3 → F) j i) *ᵥ x =
      x 0 • c₀ + x 1 • c₁ + x 2 • c₂ := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]

variable [Finite F] [CharP F 2]

theorem exists_conj_mem_rootGroup {γ : SL3 F} (hγ1 : γ ≠ 1) (hγ2 : γ * γ = 1)
    (hfix : Nat.card F ^ 2 ≤ Nat.card ↥(KGNat.fixAdd
      (Matrix.mulVecLin ((γ : SL3 F) : Matrix (Fin 3) (Fin 3) F)).toAddMonoidHom)) :
    ∃ g : SL3 F, g * γ * g⁻¹ ∈ rootGroup 0 2 := by
  set A : Matrix (Fin 3) (Fin 3) F := (γ : Matrix (Fin 3) (Fin 3) F) with hA
  have hA2 : A * A = 1 := by
    have := congrArg (fun g : SL3 F => (g : Matrix (Fin 3) (Fin 3) F)) hγ2
    simpa [hA] using this
  have hmemfix : ∀ x, x ∈ KGNat.fixAdd (Matrix.mulVecLin A).toAddMonoidHom ↔ A *ᵥ x = x :=
    fun x => KGNat.mem_fixAdd
  have hN : ∀ x, A *ᵥ (A *ᵥ x - x) = A *ᵥ x - x := by
    intro x
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec]
    funext i
    simp only [Pi.sub_apply]
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm]
  obtain ⟨w, hw⟩ : ∃ w, A *ᵥ w ≠ w := by
    by_contra hall
    push Not at hall
    apply hγ1
    refine Subtype.ext ?_
    rw [← hA]
    exact matrix_ext_of_mulVec fun x => by
      rw [hall, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  set v := A *ᵥ w - w with hv
  have hv0 : v ≠ 0 := sub_ne_zero.mpr hw
  have hAv : A *ᵥ v = v := hN w
  obtain ⟨p, hp, hpv⟩ : ∃ p, A *ᵥ p = p ∧ ∀ c : F, p ≠ c • v := by
    by_contra hall
    push Not at hall
    have hle : Nat.card ↥(KGNat.fixAdd (Matrix.mulVecLin A).toAddMonoidHom) ≤ Nat.card F := by
      have hex : ∀ x : ↥(KGNat.fixAdd (Matrix.mulVecLin A).toAddMonoidHom), ∃ c : F,
          (x : Fin 3 → F) = c • v := fun x => hall _ ((hmemfix _).mp x.2)
      choose c hc using hex
      refine Nat.card_le_card_of_injective c fun x y hxy => Subtype.ext ?_
      rw [hc x, hc y, hxy]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have := hfix.trans hle
    nlinarith
  set P : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => (![v, p, w] : Fin 3 → Fin 3 → F) j i
    with hP
  have hPx : ∀ x, P *ᵥ x = x 0 • v + x 1 • p + x 2 • w := fun x => mulVec_of_cols v p w x
  have hd : P.det ≠ 0 := by
    intro h0
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hPx] at hy
    have h2 : y 2 = 0 := by
      have := congrArg (fun z => A *ᵥ z - z) hy
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hAv, hp, Matrix.mulVec_zero,
        sub_zero] at this
      have h3 : y 2 • v = 0 := by
        rw [hv, smul_sub]
        linear_combination (norm := module) this
      exact (smul_eq_zero.mp h3).resolve_right hv0
    rw [h2, zero_smul, add_zero] at hy
    have h1 : y 1 = 0 := by
      by_contra hne
      apply hpv (-(y 1)⁻¹ * y 0)
      have : y 1 • p = -(y 0 • v) := eq_neg_of_add_eq_zero_right hy
      calc p = (y 1)⁻¹ • (y 1 • p) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
        _ = (-(y 1)⁻¹ * y 0) • v := by rw [this, smul_neg, smul_smul]; module
    rw [h1, zero_smul, add_zero] at hy
    have h0' : y 0 = 0 := (smul_eq_zero.mp hy).resolve_right hv0
    apply hy0
    funext i
    fin_cases i
    · exact h0'
    · exact h1
    · exact h2
  obtain ⟨P', hdet, hP'x⟩ : ∃ P' : Matrix (Fin 3) (Fin 3) F, P'.det = 1 ∧
      ∀ x, P' *ᵥ x = x 0 • v + (P.det⁻¹ * x 1) • p + x 2 • w := by
    refine ⟨P * Matrix.diagonal ![1, P.det⁻¹, 1], ?_, fun x => ?_⟩
    · rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three]
      simp [hd]
    · rw [← Matrix.mulVec_mulVec, hPx]
      simp [Matrix.mulVec_diagonal]
  have hAP : A * P' = P' * (1 + single 0 2 1) := by
    refine matrix_ext_of_mulVec fun x => ?_
    rw [← Matrix.mulVec_mulVec x A P', ← Matrix.mulVec_mulVec x P' _, hP'x, Matrix.add_mulVec,
      Matrix.one_mulVec, hP'x]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hAv, hp]
    have hAw : A *ᵥ w = w + v := by rw [hv]; abel
    rw [hAw]
    have hs : single (0 : Fin 3) (2 : Fin 3) (1 : F) *ᵥ x = Pi.single 0 (x 2) := by
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
    rw [hs]
    simp only [Pi.add_apply, Pi.single_eq_same]
    rw [Pi.single_eq_of_ne (show (1 : Fin 3) ≠ 0 by decide),
      Pi.single_eq_of_ne (show (2 : Fin 3) ≠ 0 by decide)]
    module
  set s : SL3 F := ⟨P', hdet⟩ with hs
  have hγs : γ * s = s * rootElt 0 2 1 := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_rootElt (by decide)]
    exact hAP
  refine ⟨s⁻¹, 1, ?_⟩
  rw [inv_inv, mul_assoc, hγs, ← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.Quasithin.MS93.S36
