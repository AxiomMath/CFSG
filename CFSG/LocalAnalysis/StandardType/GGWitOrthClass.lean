module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassCrAux
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassDim3Aux3
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassL51Aux
import CFSG.LocalAnalysis.StandardType.GGWitOrthNormal
import CFSG.LocalAnalysis.StandardType.GGWitOrthTransport
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR33Aux
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR53Aux3
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR53Aux4
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR35Aux2
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR34Aux2
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR34Aux4

public section

namespace CFSG.StandardType.ZS

open Subgroup

open scoped BigOperators

private theorem owR53_weyl_half (w : Fin 3 → ZMod 5) (h0 : w 0 ≠ 0) (h1 : w 1 ≠ 0)
    (h2 : w 2 ≠ 0) (c : ZMod 5) (hc : c ≠ 0) (hsq : ¬ IsSquare (-(w 0 * w 1 * w 2) * c)) :
    LinWeyl 5 (closure (ClassRefl 5 (QuadraticMap.weightedSumSquares (ZMod 5) w) c)) :=
  owR53_weyl_half_core w c ⟨h0, h1, h2, hc, hsq⟩

private theorem owR53_coord {n : ℕ} (hn : n = 3) (w : Fin n → ZMod 5) (hw : ∀ i, w i ≠ 0)
    (c : ZMod 5) (hc : c ≠ 0) :
    LinWeyl 5 (closure (ClassRefl 5 (QuadraticMap.weightedSumSquares (ZMod 5) w) c)) ∨
      WitNEG3 5 (closure (ClassRefl 5 (QuadraticMap.weightedSumSquares (ZMod 5) w) c)) := by
  subst hn
  by_cases hsq : IsSquare (-(w 0 * w 1 * w 2) * c)
  · exact Or.inr (owR53_neg_half w (hw 0) (hw 1) (hw 2) c hc hsq)
  · exact Or.inl (owR53_weyl_half w (hw 0) (hw 1) (hw 2) c hc hsq)

theorem wit_orthClass_cr {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c))
    (hp5 : 5 ≤ p) (hd : 4 ≤ Module.finrank (ZMod p) U) :
    ∀ r ∈ A, IsRefl p r → WitCR p A r :=
  owCc_wit_orthClass_cr hp hp2 Q hQ c hc hA hp5 hd

theorem wit_orthClass_dim3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c))
    (hp7 : 7 ≤ p) (hd : Module.finrank (ZMod p) U = 3) :
    WitNEG3 p A ∨ ∀ r ∈ A, IsRefl p r → WitCR p A r :=
  owD3_wit_orthClass_dim3 hp hp2 Q hQ c hc hA hp7 hd

theorem wit_orthClass_l51 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c))
    (hp3 : p = 3) (hd : 6 ≤ Module.finrank (ZMod p) U) :
    ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  exact owC5_wit_orthClass_l51 hp hp2 Q hQ c hc hA hp3 hd

theorem wit_orthClass_three_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c)) (hai : AbsIrred p A)
    (hp3 : p = 3) (hd : Module.finrank (ZMod p) U = 3) : LinWeyl p A := by
  obtain ⟨e, w, hw, hQe⟩ := wit_orth_normal hp hp2 Q hQ
  letI : Module (ZMod p) (Fin (Module.finrank (ZMod p) U) → ZMod p) :=
    Pi.Function.module (Fin (Module.finrank (ZMod p) U)) (ZMod p) (ZMod p)
  let Q' := owR33_Qw p (Module.finrank (ZMod p) U) w
  have he : ∀ v, Q' (e v) = Q v := by
    intro v
    rw [owR33_Qw_apply, hQe v]
  let A' := closure (ClassRefl p Q' c)
  have hA' : A' = closure (ClassRefl p Q' c) := rfl
  obtain ⟨φ, hφ⟩ := @wit_classRefl_transport p hp hp2 U
    (Fin (Module.finrank (ZMod p) U) → ZMod p) _ _ _ _ Q Q' e he c A A' hA hA'
  have hai' : AbsIrred p A' := @wit_absIrred_transport p hp U
    (Fin (Module.finrank (ZMod p) U) → ZMod p) _ _ _ _ e A A' φ hφ hai
  have hlin' : LinWeyl p A' := owR33_coord_linWeyl hp hp3 hd hw c hc hai'
  exact wit_linWeyl_transport e φ hφ hlin'

theorem wit_orthClass_five_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c)) (hai : AbsIrred p A)
    (hp5 : p = 5) (hd : Module.finrank (ZMod p) U = 3) : LinWeyl p A ∨ WitNEG3 p A := by
  subst p
  obtain ⟨e, w, hw, he⟩ := wit_orth_normal hp hp2 Q hQ
  have he' : ∀ v : U, QuadraticMap.weightedSumSquares (ZMod 5) w (e v) = Q v := by
    intro v
    simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two] using (he v).symm
  obtain ⟨φ, hφ⟩ := wit_classRefl_transport hp hp2 Q (QuadraticMap.weightedSumSquares (ZMod 5) w) e he' c hA rfl
  rcases owR53_coord hd w hw c hc with hl | hn
  · exact Or.inl (wit_linWeyl_transport e φ hφ hl)
  · exact Or.inr (wit_neg3_transport e φ hφ hn)

private def owR34_diag {d : ℕ} (w : Fin d → ZMod 3) : QuadraticForm (ZMod 3) (Fin d → ZMod 3) :=
  @QuadraticMap.weightedSumSquares (ZMod 3) (ZMod 3) _ (Fin d) _ _ _ _ w

private def owR34_A {d : ℕ} (w : Fin d → ZMod 3) (c : ZMod 3) :
    Subgroup ((Fin d → ZMod 3) ≃ₗ[ZMod 3] (Fin d → ZMod 3)) :=
  @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin d → ZMod 3) _ _
      (Pi.Function.module (Fin d) (ZMod 3) (ZMod 3)))
    (@ClassRefl 3 (Fin d → ZMod 3) (Pi.addCommGroup) (Pi.Function.module (Fin d) (ZMod 3) (ZMod 3))
      (owR34_diag w) c)

private theorem owR34_coord_diag {d : ℕ} (hd : d = 4) (w : Fin d → ZMod 3) (hw : ∀ i, w i ≠ 0)
    (c : ZMod 3) (hc : c ≠ 0) :
    @LinWeyl 3 (Fin d → ZMod 3) (Pi.addCommGroup) (Pi.Function.module (Fin d) (ZMod 3) (ZMod 3))
      (owR34_A w c) := by
  subst hd
  change @LinWeyl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))
    (@Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
      (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)))
      (@ClassRefl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (owR34_QQ w) c))
  rw [← owR34_classRefl_smul w c hc]
  exact owR34_linWeyl_vec (c⁻¹ • w) (fun i => owR34_zmod3_eq_one_or_two ((c⁻¹ • w) i) (by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero hc) (hw i)))

theorem wit_orthClass_three_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c)) (hai : AbsIrred p A)
    (hp3 : p = 3) (hd : Module.finrank (ZMod p) U = 4) : LinWeyl p A := by
  subst hp3
  obtain ⟨e, w, hw, he⟩ := wit_orth_normal (p := 3) (by decide) (by decide) Q hQ
  let Q' := owR34_diag w
  have he' : ∀ v, Q' (e v) = Q v := by
    intro v
    rw [he v]
    simp only [Q', owR34_diag, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two]
  let A' := owR34_A w c
  have hA'' : A' = @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin (Module.finrank (ZMod 3) U) → ZMod 3) _ _
      (Pi.Function.module (Fin (Module.finrank (ZMod 3) U)) (ZMod 3) (ZMod 3)))
      (@ClassRefl 3 (Fin (Module.finrank (ZMod 3) U) → ZMod 3) (Pi.addCommGroup) (Pi.Function.module (Fin (Module.finrank (ZMod 3) U)) (ZMod 3) (ZMod 3)) Q' c) := rfl
  obtain ⟨φ, hφ⟩ := @wit_classRefl_transport 3 (by decide) (by decide) U (Fin (Module.finrank (ZMod 3) U) → ZMod 3)
    _ _ (Pi.addCommGroup) (Pi.Function.module (Fin (Module.finrank (ZMod 3) U)) (ZMod 3) (ZMod 3))
    Q Q' e he' c A A' hA hA''
  have hlin' : @LinWeyl 3 (Fin (Module.finrank (ZMod 3) U) → ZMod 3) (Pi.addCommGroup)
      (Pi.Function.module (Fin (Module.finrank (ZMod 3) U)) (ZMod 3) (ZMod 3)) A' :=
    owR34_coord_diag hd w hw c hc
  exact @wit_linWeyl_transport 3 U (Fin (Module.finrank (ZMod 3) U) → ZMod 3) _ _
    (Pi.addCommGroup) (Pi.Function.module (Fin (Module.finrank (ZMod 3) U)) (ZMod 3) (ZMod 3)) e A A' φ hφ hlin'

theorem wit_orthClass_three_five {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c)) (hai : AbsIrred p A)
    (hp3 : p = 3) (hd : Module.finrank (ZMod p) U = 5) :
    LinWeyl p A ∨ ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  subst hp3
  obtain ⟨e, w, hw, he⟩ := wit_orth_normal (p := 3) hp hp2 Q hQ
  generalize hdU : Module.finrank (ZMod 3) U = d at e w he
  have hd5 : d = 5 := by rw [← hdU]; exact hd
  subst hd5
  rw [hA]
  exact owR35_coord (p := 3) hp hp2 Q hQ e w he hw c hc rfl

end CFSG.StandardType.ZS

end
