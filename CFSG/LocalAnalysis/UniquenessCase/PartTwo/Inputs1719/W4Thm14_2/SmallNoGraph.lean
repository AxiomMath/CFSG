module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.SmallFourLabels
public import CFSG.Quasithin.Background.L34OutFacts
public import CFSG.Quasithin.Background.P4SL34Core
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorGraph

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open scoped MatrixGroups Matrix

section Transport

private theorem natCard_fix_congr {G W W' ι : Type*}
    (B : W ≃ W') (β : G → G) (actW : G → W → W) (actW' : G → W' → W')
    (hB : ∀ g w, B (actW g w) = actW' (β g) (B w)) (P : ι → G) :
    Nat.card {w : W // ∀ i, actW (P i) w = w} =
    Nat.card {w' : W' // ∀ i, actW' (β (P i)) w' = w'} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv B ?_
  intro w
  constructor
  · intro h i
    rw [← hB, h i]
  · intro h i
    apply B.injective
    rw [hB, h i]

end Transport

section Rep
variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

private def qRoot (a b : F) : SL(3, F) :=
  ⟨!![1, a, b; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

private theorem coe_qRoot (a b : F) :
    (qRoot a b : Matrix (Fin 3) (Fin 3) F) = !![1, a, b; 0, 1, 0; 0, 0, 1] := rfl

private noncomputable def natCardFix (P : F → F → SL(3, F)) : ℕ :=
  Nat.card {v : Fin 3 → F // ∀ a b, (P a b : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}

private noncomputable def FD (P : F → F → SL(3, F)) : ℕ :=
  Nat.card {v : Fin 3 → F // ∀ a b, ((P a b : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v = v}

private noncomputable def natCardHermFix (hK : Nat.card F = (2 ^ 1) ^ 2)
    (P : F → F → SL(3, F)) : ℕ :=
  Nat.card {M : H.L3Nine.HMod 1 F // ∀ a b, H.L3Nine.rho hK (P a b) M = M}

private noncomputable def natCardHermFixDual (hK : Nat.card F = (2 ^ 1) ^ 2)
    (P : F → F → SL(3, F)) : ℕ :=
  Nat.card {M : H.L3Nine.HMod 1 F // ∀ a b,
    H.L3Nine.tw 1 ((P a b : Matrix (Fin 3) (Fin 3) F))ᵀ (H.L3Nine.mat M) = H.L3Nine.mat M}

private noncomputable def transposeFinThreeGL (A : GL (Fin 3) F) : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.inverseTranspose A⁻¹

private theorem coe_transposeFinThreeGL (A : GL (Fin 3) F) :
    ((transposeFinThreeGL A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F)ᵀ := by
  rw [transposeFinThreeGL, Matrix.GeneralLinearGroup.coe_inverseTranspose]
  simp

private theorem tw_transpose_iff (g : SL(3, F)) (X : Matrix (Fin 3) (Fin 3) F) :
    H.L3Nine.tw 1 ((g : Matrix (Fin 3) (Fin 3) F))ᵀ X = X ↔
      H.L3Nine.tw 1 (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ X = X := by
  constructor
  · intro h
    have h1 : H.L3Nine.tw 1 (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ
        (H.L3Nine.tw 1 ((g : Matrix (Fin 3) (Fin 3) F))ᵀ X) =
        H.L3Nine.tw 1 (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ X := by rw [h]
    have hmul : (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ *
        ((g : Matrix (Fin 3) (Fin 3) F))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
    rw [H.L3Nine.tw_tw, hmul, H.L3Nine.tw_one] at h1
    exact h1.symm
  · intro h
    have h1 : H.L3Nine.tw 1 ((g : Matrix (Fin 3) (Fin 3) F))ᵀ
        (H.L3Nine.tw 1 (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ X) =
        H.L3Nine.tw 1 ((g : Matrix (Fin 3) (Fin 3) F))ᵀ X := by rw [h]
    have hmul : ((g : Matrix (Fin 3) (Fin 3) F))ᵀ *
        (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
    rw [H.L3Nine.tw_tw, hmul, H.L3Nine.tw_one] at h1
    exact h1.symm

private theorem HD_eq_prod (hK : Nat.card F = (2 ^ 1) ^ 2) (P : F → F → SL(3, F)) :
    natCardHermFixDual hK P = Nat.card {M : H.L3Nine.HMod 1 F // ∀ p : F × F,
      H.L3Nine.tw 1 ((P p.1 p.2 : Matrix (Fin 3) (Fin 3) F))ᵀ (H.L3Nine.mat M) =
        H.L3Nine.mat M} := by
  rw [natCardHermFixDual]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun M =>
    ⟨fun h p => h p.1 p.2, fun h a b => h (a, b)⟩)

private theorem tw_inv_iff (g : SL(3, F)) (X : Matrix (Fin 3) (Fin 3) F) :
    H.L3Nine.tw 1 (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) X = X ↔
      H.L3Nine.tw 1 ((g : Matrix (Fin 3) (Fin 3) F)) X = X := by
  constructor
  · intro h
    have h1 : H.L3Nine.tw 1 ((g : Matrix (Fin 3) (Fin 3) F))
        (H.L3Nine.tw 1 (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) X) =
        H.L3Nine.tw 1 ((g : Matrix (Fin 3) (Fin 3) F)) X := by rw [h]
    have hmul : ((g : Matrix (Fin 3) (Fin 3) F)) *
        (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    rw [H.L3Nine.tw_tw, hmul, H.L3Nine.tw_one] at h1
    exact h1.symm
  · intro h
    have h1 : H.L3Nine.tw 1 (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))
        (H.L3Nine.tw 1 ((g : Matrix (Fin 3) (Fin 3) F)) X) =
        H.L3Nine.tw 1 (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) X := by rw [h]
    have hmul : (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) *
        ((g : Matrix (Fin 3) (Fin 3) F)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    rw [H.L3Nine.tw_tw, hmul, H.L3Nine.tw_one] at h1
    exact h1.symm

private theorem FN_eq_prod (P : F → F → SL(3, F)) :
    natCardFix P = Nat.card {v : Fin 3 → F // ∀ p : F × F,
      (P p.1 p.2 : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v} := by
  rw [natCardFix]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun v =>
    ⟨fun h p => h p.1 p.2, fun h a b => h (a, b)⟩)

private theorem HN_eq_prod (hK : Nat.card F = (2 ^ 1) ^ 2)
    (P : F → F → SL(3, F)) :
    natCardHermFix hK P = Nat.card {M : H.L3Nine.HMod 1 F // ∀ p : F × F,
      H.L3Nine.rho hK (P p.1 p.2) M = M} := by
  rw [natCardHermFix]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun M =>
    ⟨fun h p => h p.1 p.2, fun h a b => h (a, b)⟩)

private theorem fixN_transport_natural {ρ : Representation (ZMod 2) SL(3, F) U}
    {b : U ≃ₗ[ZMod 2] U} (ψ : SL(3, F) →* SL(3, F)) (E : U ≃+ (Fin 3 → F))
    (hE : ∀ g u, E (ρ g u) =
      ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E u)
    (ν : MulAut SL(3, F)) (hb : ∀ x : SL(3, F), X7a.Intertwines ρ b x (ν x))
    (P : F → F → SL(3, F)) :
    natCardFix (fun a b => ψ (P a b)) = natCardFix (fun a b => ψ (ν (P a b))) := by
  have h1 := natCard_fix_congr E.toEquiv (fun g => ψ g) (fun g u => ρ g u)
    (fun g v => ((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
    (fun g u => hE g u) (fun p : F × F => P p.1 p.2)
  have h2 := natCard_fix_congr b.toEquiv (fun x => ν x) (fun g u => ρ g u)
    (fun g u => ρ g u) (fun g u => hb g u) (fun p : F × F => P p.1 p.2)
  have h3 := natCard_fix_congr E.toEquiv (fun g => ψ g) (fun g u => ρ g u)
    (fun g v => ((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
    (fun g u => hE g u) (fun p : F × F => ν (P p.1 p.2))
  calc natCardFix (fun a b => ψ (P a b))
      = Nat.card {v : Fin 3 → F // ∀ p : F × F,
          (((ψ (P p.1 p.2) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) *ᵥ v = v} :=
        FN_eq_prod _
    _ = Nat.card {u : U // ∀ p : F × F, ρ (P p.1 p.2) u = u} := h1.symm
    _ = Nat.card {u : U // ∀ p : F × F, ρ (ν (P p.1 p.2)) u = u} := h2
    _ = Nat.card {v : Fin 3 → F // ∀ p : F × F,
          (((ψ (ν (P p.1 p.2)) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) *ᵥ v = v} := h3
    _ = natCardFix (fun a b => ψ (ν (P a b))) :=
        (FN_eq_prod (fun a b => ψ (ν (P a b)))).symm

private theorem herm_transport {ρ : Representation (ZMod 2) SL(3, F) U}
    {b : U ≃ₗ[ZMod 2] U} (hK : Nat.card F = (2 ^ 1) ^ 2)
    (ψ : SL(3, F) →* SL(3, F)) (E : Multiplicative U ≃* H.L3Nine.HMod 1 F)
    (hE : ∀ g u, E (Multiplicative.ofAdd (ρ g u)) =
      H.L3Nine.rho hK (ψ g) (E (Multiplicative.ofAdd u)))
    (ν : MulAut SL(3, F)) (hb : ∀ x : SL(3, F), X7a.Intertwines ρ b x (ν x))
    (P : F → F → SL(3, F)) :
    natCardHermFix hK (fun a b => ψ (P a b)) = natCardHermFix hK (fun a b => ψ (ν (P a b))) := by
  let B : U ≃ H.L3Nine.HMod 1 F :=
    { toFun := fun u => E.toEquiv (Multiplicative.ofAdd u)
      invFun := fun M => Multiplicative.toAdd (E.toEquiv.symm M)
      left_inv := fun u => by simp
      right_inv := fun M => by simp }
  have hB : ∀ g u, B (ρ g u) = H.L3Nine.rho hK (ψ g) (B u) := fun g u => hE g u
  have h1 := natCard_fix_congr B (fun g => ψ g) (fun g u => ρ g u)
    (fun g M => H.L3Nine.rho hK g M) hB (fun p : F × F => P p.1 p.2)
  have h2 := natCard_fix_congr b.toEquiv (fun x => ν x) (fun g u => ρ g u)
    (fun g u => ρ g u) (fun g u => hb g u) (fun p : F × F => P p.1 p.2)
  have h3 := natCard_fix_congr B (fun g => ψ g) (fun g u => ρ g u)
    (fun g M => H.L3Nine.rho hK g M) hB (fun p : F × F => ν (P p.1 p.2))
  calc natCardHermFix hK (fun a b => ψ (P a b))
      = Nat.card {M : H.L3Nine.HMod 1 F // ∀ p : F × F,
          H.L3Nine.rho hK (ψ (P p.1 p.2)) M = M} := HN_eq_prod hK _
    _ = Nat.card {u : U // ∀ p : F × F, ρ (P p.1 p.2) u = u} := h1.symm
    _ = Nat.card {u : U // ∀ p : F × F, ρ (ν (P p.1 p.2)) u = u} := h2
    _ = Nat.card {M : H.L3Nine.HMod 1 F // ∀ p : F × F,
          H.L3Nine.rho hK (ψ (ν (P p.1 p.2))) M = M} := h3
    _ = natCardHermFix hK (fun a b => ψ (ν (P a b))) :=
        (HN_eq_prod hK (fun a b => ψ (ν (P a b)))).symm

private def FirstForm (β : SL(3, F) → SL(3, F)) : Prop :=
  ∃ A : GL (Fin 3) F, ∃ σ : F ≃+* F, ∀ g : SL(3, F),
    (β g : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F).map σ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

private def SecondForm (β : SL(3, F) → SL(3, F)) : Prop :=
  ∃ A : GL (Fin 3) F, ∃ σ : F ≃+* F, ∀ g : SL(3, F),
    (β g : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) *
        ((((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ).map σ *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

private theorem mulAut_of_involutive (ψ : SL(3, F) →* SL(3, F)) (hψ : ∀ g, ψ (ψ g) = g) :
    ∃ Ψ : MulAut (SL(3, F)), ∀ g, Ψ g = ψ g := by
  refine ⟨MonoidHom.toMulEquiv ψ ψ ?_ ?_, fun g => rfl⟩
  · ext g
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [hψ g]
  · ext g
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [hψ g]

private theorem matrix_form_of_aut (ψ : SL(3, F) →* SL(3, F)) (hψ : ∀ g, ψ (ψ g) = g) :
    FirstForm ψ ∨ SecondForm ψ := by
  obtain ⟨Ψ, hΨ⟩ := mulAut_of_involutive ψ hψ
  obtain ⟨A, σ, ε, hε, hA⟩ := CFSG.Quasithin.G11.P4SL34.aut_cases Ψ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with h0 | h1
  · subst ε
    left
    refine ⟨A, σ, fun g => ?_⟩
    have hg : Ψ g = (ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A *
        ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ) g := by
      rw [hA, pow_zero, mul_one]
    rw [← hΨ g, hg]
    have hF : ((ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ g :
        SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F).map σ := by
      ext i j
      exact ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv_entry (Fin 3) σ g i j
    rw [MulAut.mul_apply,
      ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hF]
  · subst ε
    right
    have hG : L34Out.IsGraphType Ψ := ⟨A, σ, by rw [hA, pow_one]⟩
    obtain ⟨A', σ', hA'⟩ := L34Out.IsGraphType.exists_matrix hG
    refine ⟨A', σ', fun g => ?_⟩
    rw [← hΨ g]
    exact hA' g

private def phiFirst (A : GL (Fin 3) F) (σ : F ≃+* F) :
    (Fin 3 → F) ≃ (Fin 3 → F) where
  toFun v := fun i => σ.symm ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)
  invFun w := fun i => (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ fun j => σ (w j)) i
  left_inv v := by
    ext i
    dsimp only
    have hfun : (fun j => σ (σ.symm ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) j))) =
        (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
      funext j
      exact σ.apply_symm_apply ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) j)
    rw [hfun, Matrix.mulVec_mulVec, CFSG.Quasithin.G11.P4SL34.coe_mul_coe_inv A, Matrix.one_mulVec]
  right_inv w := by
    ext i
    dsimp only
    rw [Matrix.mulVec_mulVec, CFSG.Quasithin.G11.P4SL34.coe_inv_mul_coe A, Matrix.one_mulVec]
    exact σ.symm_apply_apply (w i)

private theorem fixN_comp_first (β : SL(3, F) → SL(3, F)) (hβ : FirstForm β)
    (P : F → F → SL(3, F)) :
    natCardFix (fun a b => β (P a b)) = natCardFix P := by
  obtain ⟨A, σ, hA⟩ := hβ
  let φ := phiFirst A σ
  apply Nat.card_congr
  refine Equiv.subtypeEquiv φ ?_
  intro v
  constructor
  · intro hv a b
    have h1 : (β (P a b) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := hv a b
    rw [hA (P a b)] at h1
    let B : Matrix (Fin 3) (Fin 3) F :=
      Matrix.map ((P a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) ⇑σ
    have h2 : B *ᵥ (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
      have h_matrix : B * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * B *
              ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
          CFSG.Quasithin.G11.P4SL34.coe_inv_mul_coe A, Matrix.one_mul]
      calc
        B *ᵥ (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
            = (B * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ v := by
          rw [Matrix.mulVec_mulVec]
        _ = (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
              (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * B *
                ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) *ᵥ v := by
          rw [h_matrix]
        _ = ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
              ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * B *
                ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ v) := by
          rw [Matrix.mulVec_mulVec]
        _ = ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
              dsimp only [B]
              rw [h1]
    change (P a b : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (fun i => σ.symm ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)) =
      fun i => σ.symm ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)
    funext i
    have h4 := RingHom.map_mulVec σ.symm.toRingHom B
      (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i
    have hmap : (Matrix.map ((P a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) ⇑σ).map
        ⇑σ.symm.toRingHom = ((P a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
      rw [Matrix.map_map]
      have hcomp : (⇑σ.symm.toRingHom : F → F) ∘ ⇑σ = id := by
        funext x
        exact σ.symm_apply_apply x
      rw [hcomp, Matrix.map_id]
    rw [h2, hmap] at h4
    exact h4.symm
  · intro hv a b
    have h1 : (P a b : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (fun i => σ.symm ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)) =
        (fun i => σ.symm ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)) := hv a b
    let B : Matrix (Fin 3) (Fin 3) F :=
      Matrix.map ((P a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) ⇑σ
    have h2 : B *ᵥ (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
      funext i
      have h4 := RingHom.map_mulVec σ.toRingHom ((P a b : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F)
        (fun i => σ.symm ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)) i
      have hcomp : (fun j => σ ((fun i =>
          σ.symm ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)) j)) =
          (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
        funext j
        exact σ.apply_symm_apply ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) j)
      dsimp only [B]
      conv_lhs => rw [← hcomp]
      change ((((P a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).map ⇑σ.toRingHom) *ᵥ
          ((⇑σ.toRingHom) ∘ fun i =>
            σ.symm ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i))) i =
          (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i
      rw [← h4, h1]
      exact σ.apply_symm_apply ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)
    rw [hA (P a b)]
    change (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * B *
      ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ v = v
    calc
      (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * B *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ v
          = ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
              (B *ᵥ (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) := by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by rw [h2]
      _ = v := by
            rw [Matrix.mulVec_mulVec, CFSG.Quasithin.G11.P4SL34.coe_mul_coe_inv A,
              Matrix.one_mulVec]

private def phiFirstTD (A : GL (Fin 3) F) (σ : F ≃+* F) :
    (Fin 3 → F) ≃ (Fin 3 → F) where
  toFun v := fun i => σ.symm (((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v) i)
  invFun w := fun i =>
    (((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ fun j => σ (w j)) i)
  left_inv v := by
    ext i
    dsimp only
    have hfun : (fun j => σ (σ.symm
        (((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v) j))) =
        ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v) := by
      funext j
      exact σ.apply_symm_apply (((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v) j)
    rw [hfun, Matrix.mulVec_mulVec]
    rw [← Matrix.transpose_mul, CFSG.Quasithin.G11.P4SL34.coe_mul_coe_inv A,
      Matrix.transpose_one, Matrix.one_mulVec]
  right_inv w := by
    ext i
    dsimp only
    rw [Matrix.mulVec_mulVec]
    rw [← Matrix.transpose_mul, CFSG.Quasithin.G11.P4SL34.coe_inv_mul_coe A,
      Matrix.transpose_one, Matrix.one_mulVec]
    exact σ.symm_apply_apply (w i)

private theorem fixD_comp_first (β : SL(3, F) → SL(3, F)) (hβ : FirstForm β)
    (P : F → F → SL(3, F)) :
    FD (fun a b => β (P a b)) = FD P := by
  obtain ⟨A, σ, hA⟩ := hβ
  let φ := phiFirstTD A σ
  apply Nat.card_congr
  refine Equiv.subtypeEquiv φ ?_
  intro v
  constructor
  · intro hv a b
    have h1 : (((β (P a b) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ v = v := hv a b
    rw [hA (P a b)] at h1
    let B : Matrix (Fin 3) (Fin 3) F :=
      Matrix.map ((P a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) ⇑σ
    have h2 : Bᵀ *ᵥ ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v) =
        ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v) := by
      have h_matrix : Bᵀ * ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) =
          ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *
            (((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) * Bᵀ *
              ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ)) := by
        conv_rhs =>
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
            CFSG.Quasithin.G11.P4SL34.coe_inv_mul_coe A, Matrix.transpose_one, Matrix.one_mul]
      calc
        Bᵀ *ᵥ ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v)
            = (Bᵀ * ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ)) *ᵥ v := by
          rw [Matrix.mulVec_mulVec]
        _ = (((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *
              (((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) * Bᵀ *
                ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ))) *ᵥ v := by
          rw [h_matrix]
        _ = ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ
              ((((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) * Bᵀ *
                ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ)) *ᵥ v) := by
          rw [Matrix.mulVec_mulVec]
        _ = ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ v := by
              rw [Matrix.transpose_mul, Matrix.transpose_mul] at h1
              rw [← Matrix.mul_assoc] at h1
              rw [h1]
    change (P a b : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ
      (fun i => σ.symm ((((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ v) i)) =
      fun i => σ.symm ((((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ v) i)
    funext i
    have h4 := RingHom.map_mulVec σ.symm.toRingHom Bᵀ
      ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v) i
    have hmap : Bᵀ.map σ.symm.toRingHom = ((P a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ := by
      dsimp only [B]
      rw [Matrix.transpose_map, Matrix.map_map]
      have hcomp : (σ.symm.toRingHom : F → F) ∘ ⇑σ = id := by
        funext x
        exact σ.symm_apply_apply x
      rw [hcomp, Matrix.map_id]
    rw [h2, hmap] at h4
    exact h4.symm
  · intro hv a b
    have h1 : ((P a b : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ
        (fun i => σ.symm ((((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ v) i)) =
        (fun i => σ.symm ((((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ v) i)) := hv a b
    let B : Matrix (Fin 3) (Fin 3) F :=
      Matrix.map ((P a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) ⇑σ
    have h2 : Bᵀ *ᵥ ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v) =
        ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v) := by
      funext i
      have h4 := RingHom.map_mulVec σ.toRingHom (((P a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ)
        (fun i => σ.symm ((((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ v) i)) i
      have hcomp : (fun j => σ ((fun i =>
          σ.symm ((((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ v) i)) j)) =
          ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v) := by
        funext j
        exact σ.apply_symm_apply ((((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ v) j)
      dsimp only [B]
      rw [← hcomp]
      rw [← Matrix.transpose_map]
      change (((((P a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ).map ⇑σ.toRingHom) *ᵥ
          ((⇑σ.toRingHom) ∘ (fun i =>
            σ.symm ((((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ v) i)))) i =
          ((⇑σ.toRingHom) ∘ (fun i =>
            σ.symm ((((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ v) i))) i
      rw [← h4, h1]
      rfl
    rw [hA (P a b)]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc]
    calc
      ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ * Bᵀ *
          (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ v
          = ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ
              (Bᵀ *ᵥ ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v)) := by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ) *ᵥ
            ((((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v) := by rw [h2]
      _ = v := by
            rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
              CFSG.Quasithin.G11.P4SL34.coe_mul_coe_inv A, Matrix.transpose_one, Matrix.one_mulVec]

private noncomputable def slGraphAutDelta (g : SL(3, F)) : SL(3, F) :=
  CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F g

private theorem coe_delta (g : SL(3, F)) :
    (slGraphAutDelta g : Matrix (Fin 3) (Fin 3) F) =
      ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ :=
  CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix 3 F g

private theorem FN_delta_comp (P : F → F → SL(3, F)) :
    natCardFix (fun a b => slGraphAutDelta (P a b)) = FD P := by
  apply Nat.card_congr
  refine Equiv.refl _ |>.subtypeEquiv ?_
  intro v
  constructor
  · intro h a b
    have h1 : (((P a b)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        (P a b : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h4 : (P a b : Matrix (Fin 3) (Fin 3) F)ᵀ *
        (((P a b)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
    calc
      (P a b : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v
          = (P a b : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ
            ((((P a b)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v) := by
            congr 1
            exact (h a b).symm
      _ = v := by
            rw [Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]
  · intro h a b
    have h2 : (P a b : Matrix (Fin 3) (Fin 3) F) *
        (((P a b)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h3 : (((P a b)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ *
        (P a b : Matrix (Fin 3) (Fin 3) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
    calc
      (((P a b)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v
          = (((P a b)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ
            ((P a b : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v) := by
            congr 1
            exact (h a b).symm
      _ = v := by
            rw [Matrix.mulVec_mulVec, h3, Matrix.one_mulVec]

private theorem FD_delta_comp (P : F → F → SL(3, F)) :
    FD (fun a b => slGraphAutDelta (P a b)) = natCardFix P := by
  apply Nat.card_congr
  refine Equiv.refl _ |>.subtypeEquiv ?_
  intro v
  constructor
  · intro h a b
    have h2 : (P a b : Matrix (Fin 3) (Fin 3) F) *
        (((P a b)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    calc
      (P a b : Matrix (Fin 3) (Fin 3) F) *ᵥ v
          = (P a b : Matrix (Fin 3) (Fin 3) F) *ᵥ
            ((((P a b)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
            congr 1
            exact (h a b).symm
      _ = v := by
            rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  · intro h a b
    have h1 : (((P a b)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        (P a b : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    calc
      (((P a b)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v
          = (((P a b)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            ((P a b : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
            congr 1
            exact (h a b).symm
      _ = v := by
            rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

private theorem HN_delta_comp (hK : Nat.card F = (2 ^ 1) ^ 2)
    (P : F → F → SL(3, F)) :
    natCardHermFix hK (fun a b => slGraphAutDelta (P a b)) = natCardHermFixDual hK P := by
  have hiff : ∀ (g : SL(3, F)) (M : H.L3Nine.HMod 1 F),
      H.L3Nine.rho hK (slGraphAutDelta g) M = M ↔
        H.L3Nine.tw 1 ((g : Matrix (Fin 3) (Fin 3) F))ᵀ (H.L3Nine.mat M) =
          H.L3Nine.mat M := by
    intro g M
    rw [← H.L3Nine.mat_injective.eq_iff, H.L3Nine.mat_rho, coe_delta]
    exact (tw_transpose_iff g (H.L3Nine.mat M)).symm
  rw [HN_eq_prod hK (fun a b => slGraphAutDelta (P a b)), HD_eq_prod hK P]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun M =>
    ⟨fun h p => (hiff (P p.1 p.2) M).mp (h p),
      fun h p => (hiff (P p.1 p.2) M).mpr (h p)⟩)

private theorem HD_delta_comp (hK : Nat.card F = (2 ^ 1) ^ 2)
    (P : F → F → SL(3, F)) :
    natCardHermFixDual hK (fun a b => slGraphAutDelta (P a b)) = natCardHermFix hK P := by
  have hiff : ∀ (g : SL(3, F)) (M : H.L3Nine.HMod 1 F),
      H.L3Nine.tw 1 ((slGraphAutDelta g : Matrix (Fin 3) (Fin 3) F))ᵀ (H.L3Nine.mat M) =
        H.L3Nine.mat M ↔ H.L3Nine.rho hK g M = M := by
    intro g M
    rw [coe_delta, Matrix.transpose_transpose, ← H.L3Nine.mat_injective.eq_iff,
      H.L3Nine.mat_rho]
    exact tw_inv_iff g (H.L3Nine.mat M)
  rw [HD_eq_prod hK (fun a b => slGraphAutDelta (P a b)), HN_eq_prod hK P]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun M =>
    ⟨fun h p => (hiff (P p.1 p.2) M).mp (h p),
      fun h p => (hiff (P p.1 p.2) M).mpr (h p)⟩)

private theorem fixN_comp_second (β : SL(3, F) → SL(3, F)) (hβ : SecondForm β)
    (P : F → F → SL(3, F)) :
    natCardFix (fun a b => β (P a b)) = FD P := by
  obtain ⟨A, σ, hA⟩ := hβ
  let β₁ : SL(3, F) → SL(3, F) := fun g =>
    (ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A *
      ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ) g
  have hβ₁_matrix : ∀ g : SL(3, F), (β₁ g : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F).map σ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro g
    dsimp only [β₁]
    have hF : ((ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ g :
        SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F).map σ := by
      ext i j
      exact ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv_entry (Fin 3) σ g i j
    rw [MulAut.mul_apply,
      ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hF]
  have hβ₁ : FirstForm β₁ := ⟨A, σ, hβ₁_matrix⟩
  have h_eq : ∀ g : SL(3, F), β g = β₁ (slGraphAutDelta g) := by
    intro g
    apply Subtype.ext
    rw [hA g, hβ₁_matrix (slGraphAutDelta g), coe_delta]
  calc
    natCardFix (fun a b => β (P a b))
        = natCardFix (fun a b => β₁ (slGraphAutDelta (P a b))) := by
            congr 1
            funext a b
            exact h_eq (P a b)
    _ = natCardFix (fun a b => slGraphAutDelta (P a b)) := by
            exact fixN_comp_first β₁ hβ₁ (fun a b => slGraphAutDelta (P a b))
    _ = FD P := FN_delta_comp P

private theorem fixD_comp_second (β : SL(3, F) → SL(3, F)) (hβ : SecondForm β)
    (P : F → F → SL(3, F)) :
    FD (fun a b => β (P a b)) = natCardFix P := by
  obtain ⟨A, σ, hA⟩ := hβ
  let β₁ : SL(3, F) → SL(3, F) := fun g =>
    (ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A *
      ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ) g
  have hβ₁_matrix : ∀ g : SL(3, F), (β₁ g : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F).map σ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro g
    dsimp only [β₁]
    have hF : ((ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ g :
        SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F).map σ := by
      ext i j
      exact ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv_entry (Fin 3) σ g i j
    rw [MulAut.mul_apply,
      ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hF]
  have hβ₁ : FirstForm β₁ := ⟨A, σ, hβ₁_matrix⟩
  have h_eq : ∀ g : SL(3, F), β g = β₁ (slGraphAutDelta g) := by
    intro g
    apply Subtype.ext
    rw [hA g, hβ₁_matrix (slGraphAutDelta g), coe_delta]
  calc
    FD (fun a b => β (P a b))
        = FD (fun a b => β₁ (slGraphAutDelta (P a b))) := by
            congr 1
            funext a b
            exact h_eq (P a b)
    _ = FD (fun a b => slGraphAutDelta (P a b)) := by
            exact fixD_comp_first β₁ hβ₁ (fun a b => slGraphAutDelta (P a b))
    _ = natCardFix P := FD_delta_comp P

private theorem herm_fixN_comp_first (hK : Nat.card F = (2 ^ 1) ^ 2)
    (β : SL(3, F) → SL(3, F)) (hβ : FirstForm β) (P : F → F → SL(3, F)) :
    natCardHermFix hK (fun a b => β (P a b)) = natCardHermFix hK P := by
  obtain ⟨A, σ, hA⟩ := hβ
  let B : MulAut (H.L3Nine.HMod 1 F) := H.L3Nine.rhoT hK A * H.L3Nine.fldAut σ
  have hBinv : ∀ x, B⁻¹ (B x) = x := fun x => by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hinvB : ∀ x, B (B⁻¹ x) = x := fun x => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hconj : ∀ g : SL(3, F),
      H.L3Nine.rho hK (β g) = B * H.L3Nine.rho hK g * B⁻¹ := by
    intro g
    have htoGL : Matrix.SpecialLinearGroup.toGL (β g) =
        A * H.L3Nine.mapGL σ (Matrix.SpecialLinearGroup.toGL g) * A⁻¹ := by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Units.val_mul, Units.val_mul,
        H.L3Nine.coe_mapGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA g]
    rw [show H.L3Nine.rho hK (β g) =
      H.L3Nine.rhoT hK (Matrix.SpecialLinearGroup.toGL (β g)) from rfl, htoGL,
      map_mul, map_mul, map_inv,
      ← H.L3Nine.fldAut_conj_rhoT hK σ (Matrix.SpecialLinearGroup.toGL g)]
    simp only [show H.L3Nine.rho hK g =
      H.L3Nine.rhoT hK (Matrix.SpecialLinearGroup.toGL g) from rfl]
    dsimp only [B]
    group
  rw [HN_eq_prod hK (fun a b => β (P a b)), HN_eq_prod hK P]
  refine Nat.card_congr (Equiv.subtypeEquiv
    (B⁻¹ : H.L3Nine.HMod 1 F ≃ H.L3Nine.HMod 1 F) ?_)
  intro M
  constructor
  · intro h p
    have h1 := congrArg (fun X => B⁻¹ X) (h p)
    rw [hconj (P p.1 p.2)] at h1
    simp only [MulAut.mul_apply] at h1
    rw [hBinv] at h1
    exact h1
  · intro h p
    have h1 : H.L3Nine.rho hK (P p.1 p.2) (B⁻¹ M) = B⁻¹ M := h p
    rw [hconj (P p.1 p.2)]
    simp only [MulAut.mul_apply]
    rw [h1, hinvB]

private theorem herm_fixD_comp_first (hK : Nat.card F = (2 ^ 1) ^ 2)
    (β : SL(3, F) → SL(3, F)) (hβ : FirstForm β) (P : F → F → SL(3, F)) :
    natCardHermFixDual hK (fun a b => β (P a b)) = natCardHermFixDual hK P := by
  obtain ⟨A, σ, hA⟩ := hβ
  let S : GL (Fin 3) F := Matrix.GeneralLinearGroup.inverseTranspose A
  let B : MulAut (H.L3Nine.HMod 1 F) := H.L3Nine.rhoT hK S * H.L3Nine.fldAut σ
  have hBinv : ∀ x, B⁻¹ (B x) = x := fun x => by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hinvB : ∀ x, B (B⁻¹ x) = x := fun x => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have htoGL : ∀ g : SL(3, F), Matrix.SpecialLinearGroup.toGL (β g) =
      A * H.L3Nine.mapGL σ (Matrix.SpecialLinearGroup.toGL g) * A⁻¹ := by
    intro g
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Units.val_mul, Units.val_mul,
      H.L3Nine.coe_mapGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA g]
  have hTV : ∀ g : SL(3, F), transposeFinThreeGL (Matrix.SpecialLinearGroup.toGL (β g)) =
      S * H.L3Nine.mapGL σ (transposeFinThreeGL (Matrix.SpecialLinearGroup.toGL g)) * S⁻¹ := by
    intro g
    apply Units.ext
    dsimp only [S]
    simp only [coe_transposeFinThreeGL, htoGL g, Units.val_mul, Units.val_inv_eq_inv_val,
      Matrix.GeneralLinearGroup.coe_inverseTranspose, H.L3Nine.coe_mapGL,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      CFSG.ComponentClassification.OddSelector.coe_inverseTranspose_inv,
      Matrix.transpose_mul, Matrix.transpose_map, Matrix.mul_assoc]
  have hconj : ∀ g : SL(3, F),
      H.L3Nine.rhoT hK (transposeFinThreeGL (Matrix.SpecialLinearGroup.toGL (β g))) =
        B * H.L3Nine.rhoT hK (transposeFinThreeGL (Matrix.SpecialLinearGroup.toGL g)) * B⁻¹ := by
    intro g
    rw [hTV g, map_mul, map_mul, map_inv,
      ← H.L3Nine.fldAut_conj_rhoT hK σ (transposeFinThreeGL (Matrix.SpecialLinearGroup.toGL g))]
    dsimp only [B]
    group
  have hiffβ : ∀ (g : SL(3, F)) (M : H.L3Nine.HMod 1 F),
      H.L3Nine.tw 1 (((β g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ
        (H.L3Nine.mat M) = H.L3Nine.mat M ↔
        H.L3Nine.rhoT hK (transposeFinThreeGL (Matrix.SpecialLinearGroup.toGL (β g))) M = M := by
    intro g M
    rw [← H.L3Nine.mat_injective.eq_iff, H.L3Nine.mat_rhoT, coe_transposeFinThreeGL,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  have hiff : ∀ (g : SL(3, F)) (M : H.L3Nine.HMod 1 F),
      H.L3Nine.tw 1 ((g : Matrix (Fin 3) (Fin 3) F))ᵀ (H.L3Nine.mat M) =
        H.L3Nine.mat M ↔
        H.L3Nine.rhoT hK (transposeFinThreeGL (Matrix.SpecialLinearGroup.toGL g)) M = M := by
    intro g M
    rw [← H.L3Nine.mat_injective.eq_iff, H.L3Nine.mat_rhoT, coe_transposeFinThreeGL,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rw [HD_eq_prod hK (fun a b => β (P a b)), HD_eq_prod hK P]
  refine Nat.card_congr (Equiv.subtypeEquiv
    (B⁻¹ : H.L3Nine.HMod 1 F ≃ H.L3Nine.HMod 1 F) ?_)
  intro M
  constructor
  · intro h p
    have h1 : H.L3Nine.rhoT hK (transposeFinThreeGL
        (Matrix.SpecialLinearGroup.toGL (β (P p.1 p.2)))) M = M :=
      (hiffβ (P p.1 p.2) M).mp (h p)
    have h2 := congrArg (fun X => B⁻¹ X) h1
    rw [hconj (P p.1 p.2)] at h2
    simp only [MulAut.mul_apply] at h2
    rw [hBinv] at h2
    exact (hiff (P p.1 p.2) (B⁻¹ M)).mpr h2
  · intro h p
    rw [hiffβ (P p.1 p.2) M]
    have h1 : H.L3Nine.rhoT hK (transposeFinThreeGL
        (Matrix.SpecialLinearGroup.toGL (P p.1 p.2))) (B⁻¹ M) = B⁻¹ M :=
      (hiff (P p.1 p.2) (B⁻¹ M)).mp (h p)
    have h2 := congrArg (fun X => B X) h1
    rw [hconj (P p.1 p.2)]
    simp only [MulAut.mul_apply]
    rw [h2, hinvB]

private theorem herm_fixN_comp_second (hK : Nat.card F = (2 ^ 1) ^ 2)
    (β : SL(3, F) → SL(3, F)) (hβ : SecondForm β) (P : F → F → SL(3, F)) :
    natCardHermFix hK (fun a b => β (P a b)) = natCardHermFixDual hK P := by
  obtain ⟨A, σ, hA⟩ := hβ
  let β₁ : SL(3, F) → SL(3, F) := fun g =>
    (ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A *
      ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ) g
  have hβ₁_matrix : ∀ g : SL(3, F), (β₁ g : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F).map σ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro g
    dsimp only [β₁]
    have hF : ((ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ g :
        SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F).map σ := by
      ext i j
      exact ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv_entry (Fin 3) σ g i j
    rw [MulAut.mul_apply,
      ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hF]
  have hβ₁ : FirstForm β₁ := ⟨A, σ, hβ₁_matrix⟩
  have h_eq : ∀ g : SL(3, F), β g = β₁ (slGraphAutDelta g) := by
    intro g
    apply Subtype.ext
    rw [hA g, hβ₁_matrix (slGraphAutDelta g), coe_delta]
  calc
    natCardHermFix hK (fun a b => β (P a b))
        = natCardHermFix hK (fun a b => β₁ (slGraphAutDelta (P a b))) := by
            congr 1
            funext a b
            exact h_eq (P a b)
    _ = natCardHermFix hK (fun a b => slGraphAutDelta (P a b)) := by
            exact herm_fixN_comp_first hK β₁ hβ₁ (fun a b => slGraphAutDelta (P a b))
    _ = natCardHermFixDual hK P := HN_delta_comp hK P

private theorem herm_fixD_comp_second (hK : Nat.card F = (2 ^ 1) ^ 2)
    (β : SL(3, F) → SL(3, F)) (hβ : SecondForm β) (P : F → F → SL(3, F)) :
    natCardHermFixDual hK (fun a b => β (P a b)) = natCardHermFix hK P := by
  obtain ⟨A, σ, hA⟩ := hβ
  let β₁ : SL(3, F) → SL(3, F) := fun g =>
    (ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A *
      ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ) g
  have hβ₁_matrix : ∀ g : SL(3, F), (β₁ g : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F).map σ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro g
    dsimp only [β₁]
    have hF : ((ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ g :
        SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F).map σ := by
      ext i j
      exact ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv_entry (Fin 3) σ g i j
    rw [MulAut.mul_apply,
      ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hF]
  have hβ₁ : FirstForm β₁ := ⟨A, σ, hβ₁_matrix⟩
  have h_eq : ∀ g : SL(3, F), β g = β₁ (slGraphAutDelta g) := by
    intro g
    apply Subtype.ext
    rw [hA g, hβ₁_matrix (slGraphAutDelta g), coe_delta]
  calc
    natCardHermFixDual hK (fun a b => β (P a b))
        = natCardHermFixDual hK (fun a b => β₁ (slGraphAutDelta (P a b))) := by
            congr 1
            funext a b
            exact h_eq (P a b)
    _ = natCardHermFixDual hK (fun a b => slGraphAutDelta (P a b)) := by
            exact herm_fixD_comp_first hK β₁ hβ₁ (fun a b => slGraphAutDelta (P a b))
    _ = natCardHermFix hK P := HD_delta_comp hK P

private theorem fixN_lt_fixD : natCardFix (F := F) qRoot < FD (F := F) qRoot := by
  have hFN : natCardFix (F := F) qRoot ≤ Nat.card F := by
    refine Nat.card_le_card_of_injective (fun v => v.1 0) ?_
    intro v w h
    have hv1 : v.1 1 = 0 := by
      have h1 := congrFun (v.2 1 0) 0
      rw [coe_qRoot] at h1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1
      linear_combination h1
    have hv2 : v.1 2 = 0 := by
      have h1 := congrFun (v.2 0 1) 0
      rw [coe_qRoot] at h1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1
      linear_combination h1
    have hw1 : w.1 1 = 0 := by
      have h1 := congrFun (w.2 1 0) 0
      rw [coe_qRoot] at h1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1
      linear_combination h1
    have hw2 : w.1 2 = 0 := by
      have h1 := congrFun (w.2 0 1) 0
      rw [coe_qRoot] at h1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1
      linear_combination h1
    ext i
    fin_cases i <;> simp [hv1, hv2, hw1, hw2, h]
  have hFD : Nat.card (F × F) ≤ FD (F := F) qRoot := by
    refine Nat.card_le_card_of_injective (fun p : F × F =>
      (⟨![0, p.1, p.2], ?_⟩ : {v : Fin 3 → F // ∀ a b,
        ((qRoot (F := F) a b : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v = v})) ?_
    · intro a b
      ext i
      fin_cases i <;>
        simp [coe_qRoot, Matrix.transpose, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · intro p q h
      have h1 := congrFun (congrArg Subtype.val h) 1
      have h2 := congrFun (congrArg Subtype.val h) 2
      simp at h1 h2
      exact Prod.ext h1 h2
  have h3 : 1 < Nat.card F := Finite.one_lt_card
  have h4 : Nat.card F < Nat.card F * Nat.card F := by nlinarith
  rw [Nat.card_prod] at hFD
  exact lt_of_le_of_lt hFN (lt_of_lt_of_le h4 hFD)

private theorem card_fixN_qRoot_le (hK : Nat.card F = (2 ^ 1) ^ 2) :
    natCardHermFix hK qRoot ≤ Nat.card F := by
  refine Nat.card_le_card_of_injective
    (fun M : {M : H.L3Nine.HMod 1 F // ∀ a b,
      H.L3Nine.rho hK (qRoot a b) M = M} => H.L3Nine.mat M.1 0 0) ?_
  intro M N hMN
  have hM1 : ∀ a : F,
      H.L3Nine.rhoT hK (H.Tri.trGL (0 : Fin 3) 1 (by decide) a) M.1 = M.1 := by
    intro a
    have h := M.2 a 0
    have hq : Matrix.SpecialLinearGroup.toGL (qRoot a 0) =
        H.Tri.trGL (0 : Fin 3) 1 (by decide) a := by
      rw [show qRoot a 0 = X7a.up3 0 0 a from Subtype.ext rfl]
      exact CFSG.Quasithin.B45SL3.toGL_up3_01 a
    rwa [show H.L3Nine.rho hK (qRoot a 0) M.1 =
      H.L3Nine.rhoT hK (Matrix.SpecialLinearGroup.toGL (qRoot a 0)) M.1 from rfl, hq] at h
  have hM2 : ∀ a : F,
      H.L3Nine.rhoT hK (H.Tri.trGL (0 : Fin 3) 2 (by decide) a) M.1 = M.1 := by
    intro a
    have h := M.2 0 a
    have hq : Matrix.SpecialLinearGroup.toGL (qRoot 0 a) =
        H.Tri.trGL (0 : Fin 3) 2 (by decide) a := by
      rw [show qRoot 0 a = X7a.up3 0 a 0 from Subtype.ext rfl]
      exact CFSG.Quasithin.B45SL3.toGL_up3_02 a
    rwa [show H.L3Nine.rho hK (qRoot 0 a) M.1 =
      H.L3Nine.rhoT hK (Matrix.SpecialLinearGroup.toGL (qRoot 0 a)) M.1 from rfl, hq] at h
  have hN1 : ∀ a : F,
      H.L3Nine.rhoT hK (H.Tri.trGL (0 : Fin 3) 1 (by decide) a) N.1 = N.1 := by
    intro a
    have h := N.2 a 0
    have hq : Matrix.SpecialLinearGroup.toGL (qRoot a 0) =
        H.Tri.trGL (0 : Fin 3) 1 (by decide) a := by
      rw [show qRoot a 0 = X7a.up3 0 0 a from Subtype.ext rfl]
      exact CFSG.Quasithin.B45SL3.toGL_up3_01 a
    rwa [show H.L3Nine.rho hK (qRoot a 0) N.1 =
      H.L3Nine.rhoT hK (Matrix.SpecialLinearGroup.toGL (qRoot a 0)) N.1 from rfl, hq] at h
  have hN2 : ∀ a : F,
      H.L3Nine.rhoT hK (H.Tri.trGL (0 : Fin 3) 2 (by decide) a) N.1 = N.1 := by
    intro a
    have h := N.2 0 a
    have hq : Matrix.SpecialLinearGroup.toGL (qRoot 0 a) =
        H.Tri.trGL (0 : Fin 3) 2 (by decide) a := by
      rw [show qRoot 0 a = X7a.up3 0 a 0 from Subtype.ext rfl]
      exact CFSG.Quasithin.B45SL3.toGL_up3_02 a
    rwa [show H.L3Nine.rho hK (qRoot 0 a) N.1 =
      H.L3Nine.rhoT hK (Matrix.SpecialLinearGroup.toGL (qRoot 0 a)) N.1 from rfl, hq] at h
  have hzM := H.L3Nine.eq_zero_of_fix (n := 1) le_rfl hK hM1 hM2
  have hzN := H.L3Nine.eq_zero_of_fix (n := 1) le_rfl hK hN1 hN2
  apply Subtype.ext
  apply H.L3Nine.mat_injective
  ext i j
  by_cases h00 : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h00
    exact hMN
  · rw [hzM i j h00, hzN i j h00]

private noncomputable def hermFixedMat (a : F) (c : ZMod 2) : Matrix (Fin 3) (Fin 3) F :=
  !![0, 0, 0; 0, ZMod.castHom (dvd_refl 2) F c, a; 0, H.SU3.bar 1 a, 0]

private theorem hermFixedMat_herm (hK : Nat.card F = (2 ^ 1) ^ 2) (a : F) (c : ZMod 2) :
    (H.SU3.conjM 1 (hermFixedMat a c))ᵀ = hermFixedMat a c := by
  have hc : H.SU3.bar 1 (ZMod.castHom (dvd_refl 2) F c) =
      ZMod.castHom (dvd_refl 2) F c := by
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl <;>
      simp [H.SU3.bar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermFixedMat, H.SU3.conjM, H.SU3.bar_bar hK]
  simpa using hc

private noncomputable def hermFixed (hK : Nat.card F = (2 ^ 1) ^ 2) (a : F)
    (c : ZMod 2) : H.L3Nine.HMod 1 F :=
  H.L3Nine.mkH (hermFixedMat a c) (hermFixedMat_herm hK a c)

private theorem hermFixed_fix (hK : Nat.card F = (2 ^ 1) ^ 2) (a : F) (c : ZMod 2) :
    ∀ a' b', H.L3Nine.tw 1 (((qRoot a' b' : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ
      (H.L3Nine.mat (hermFixed hK a c)) = H.L3Nine.mat (hermFixed hK a c) := by
  intro a' b'
  rw [show H.L3Nine.mat (hermFixed hK a c) = hermFixedMat a c from
    H.L3Nine.mat_mkH _ _]
  rw [H.L3Nine.tw]
  have hleft : (((qRoot a' b' : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ * hermFixedMat a c =
      hermFixedMat a c := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_qRoot, hermFixedMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  have hright : hermFixedMat a c *
      (H.SU3.conjM 1 (((qRoot a' b' : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ)ᵀ =
        hermFixedMat a c := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_qRoot, hermFixedMat, H.SU3.conjM, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.transpose_apply]
  rw [hleft, hright]

private theorem card_le_HD_qRoot (hK : Nat.card F = (2 ^ 1) ^ 2) :
    Nat.card (F × ZMod 2) ≤ natCardHermFixDual hK qRoot := by
  refine Nat.card_le_card_of_injective (fun p : F × ZMod 2 =>
    (⟨hermFixed hK p.1 p.2, hermFixed_fix hK p.1 p.2⟩ :
      {M : H.L3Nine.HMod 1 F // ∀ a b,
        H.L3Nine.tw 1 (((qRoot a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ
          (H.L3Nine.mat M) =
          H.L3Nine.mat M})) ?_
  intro p q hpq
  have hval : hermFixed hK p.1 p.2 = hermFixed hK q.1 q.2 := congrArg Subtype.val hpq
  have hmat : H.L3Nine.mat (hermFixed hK p.1 p.2) =
      H.L3Nine.mat (hermFixed hK q.1 q.2) := by
    rw [hval]
  have h12 := congrFun (congrFun hmat 1) 2
  have h11 := congrFun (congrFun hmat 1) 1
  simp only [hermFixed, H.L3Nine.mat_mkH, hermFixedMat] at h12 h11
  exact Prod.ext h12 (ZMod.castHom_injective (R := F) h11)

private theorem herm_fixN_lt_fixD (hK : Nat.card F = (2 ^ 1) ^ 2) :
    natCardHermFix (F := F) hK qRoot < natCardHermFixDual (F := F) hK qRoot := by
  have hHN := card_fixN_qRoot_le hK
  have hHD := card_le_HD_qRoot hK
  have hcard : Nat.card F = 4 := by
    rw [hK]
    norm_num
  have h2 : Nat.card (F × ZMod 2) = Nat.card F * 2 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card]
  rw [h2, hcard] at hHD
  omega

theorem not_isGraphType_of_intertwines (ρ : Representation (ZMod 2) SL(3, F) U)
    (hcase : IsTwistedNatural ρ ∨ IsTwistedHerm ρ) (b : U ≃ₗ[ZMod 2] U)
    (ν : MulAut SL(3, F)) (hb : ∀ x : SL(3, F), X7a.Intertwines ρ b x (ν x)) :
    ¬ L34Out.IsGraphType ν := by
  rintro hG
  rcases hcase with ⟨ψ, hψ, E, hE⟩ | ⟨hK, ψ, hψ, E, hE⟩
  · have hsec : SecondForm ν := L34Out.IsGraphType.exists_matrix hG
    have htr : natCardFix (F := F) qRoot = natCardFix (fun a b => ψ (ν (ψ (qRoot a b)))) := by
      have h : natCardFix (fun a b => ψ (ψ (qRoot a b))) =
          natCardFix (fun a b => ψ (ν (ψ (qRoot a b)))) :=
        fixN_transport_natural ψ E hE ν hb (fun a b => ψ (qRoot a b))
      have hq : (fun a b => ψ (ψ (qRoot a b))) = (qRoot : F → F → SL(3, F)) := by
        funext a b
        exact hψ (qRoot a b)
      rwa [hq] at h
    have hchain : natCardFix (fun a b => ψ (ν (ψ (qRoot a b)))) = FD (F := F) qRoot := by
      rcases matrix_form_of_aut ψ hψ with h1 | h2
      · calc natCardFix (fun a b => ψ (ν (ψ (qRoot a b))))
            = natCardFix (fun a b => ν (ψ (qRoot a b))) :=
              fixN_comp_first ψ h1 (fun a b => ν (ψ (qRoot a b)))
          _ = FD (fun a b => ψ (qRoot a b)) :=
              fixN_comp_second ν hsec (fun a b => ψ (qRoot a b))
          _ = FD (F := F) qRoot := fixD_comp_first ψ h1 qRoot
      · calc natCardFix (fun a b => ψ (ν (ψ (qRoot a b))))
            = FD (fun a b => ν (ψ (qRoot a b))) :=
              fixN_comp_second ψ h2 (fun a b => ν (ψ (qRoot a b)))
          _ = natCardFix (fun a b => ψ (qRoot a b)) :=
              fixD_comp_second ν hsec (fun a b => ψ (qRoot a b))
          _ = FD (F := F) qRoot := fixN_comp_second ψ h2 qRoot
    exact (ne_of_lt fixN_lt_fixD) (htr.trans hchain)
  · have hsec : SecondForm ν := L34Out.IsGraphType.exists_matrix hG
    have htr : natCardHermFix hK (F := F) qRoot =
        natCardHermFix hK (fun a b => ψ (ν (ψ (qRoot a b)))) := by
      have h : natCardHermFix hK (fun a b => ψ (ψ (qRoot a b))) =
          natCardHermFix hK (fun a b => ψ (ν (ψ (qRoot a b)))) :=
        herm_transport hK ψ E hE ν hb (fun a b => ψ (qRoot a b))
      have hq : (fun a b => ψ (ψ (qRoot a b))) = (qRoot : F → F → SL(3, F)) := by
        funext a b
        exact hψ (qRoot a b)
      rwa [hq] at h
    have hchain : natCardHermFix hK (fun a b => ψ (ν (ψ (qRoot a b)))) =
        natCardHermFixDual hK (F := F) qRoot := by
      rcases matrix_form_of_aut ψ hψ with h1 | h2
      · calc natCardHermFix hK (fun a b => ψ (ν (ψ (qRoot a b))))
            = natCardHermFix hK (fun a b => ν (ψ (qRoot a b))) :=
              herm_fixN_comp_first hK ψ h1 (fun a b => ν (ψ (qRoot a b)))
          _ = natCardHermFixDual hK (fun a b => ψ (qRoot a b)) :=
              herm_fixN_comp_second hK ν hsec (fun a b => ψ (qRoot a b))
          _ = natCardHermFixDual hK (F := F) qRoot := herm_fixD_comp_first hK ψ h1 qRoot
      · calc natCardHermFix hK (fun a b => ψ (ν (ψ (qRoot a b))))
            = natCardHermFixDual hK (fun a b => ν (ψ (qRoot a b))) :=
              herm_fixN_comp_second hK ψ h2 (fun a b => ν (ψ (qRoot a b)))
          _ = natCardHermFix hK (fun a b => ψ (qRoot a b)) :=
              herm_fixD_comp_second hK ν hsec (fun a b => ψ (qRoot a b))
          _ = natCardHermFixDual hK (F := F) qRoot := herm_fixN_comp_second hK ψ h2 qRoot
    exact (ne_of_lt (herm_fixN_lt_fixD hK)) (htr.trans hchain)
end Rep

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2
