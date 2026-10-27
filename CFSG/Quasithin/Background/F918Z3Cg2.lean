module

public import CFSG.Quasithin.Background.F918Z3Cg1
public import CFSG.Quasithin.Background.F918Z3Cg2H2
public import CFSG.Quasithin.Background.F918Z3Cg2H4b

public section

namespace CFSG.Quasithin

open scoped Matrix

theorem orth_exclusion_core {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)}
    {s : MulAut V} (hZ : Z37 D X G T' s) {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    (hd : 3 ≤ d) (β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F))
    (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F)
    (σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F) (hM : IsMatModel D X β ρ σ)
    {I : Subgroup V} (hI0 : I ≠ ⊥) (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) {a : ℕ}
    (hO : OrthMinusData D I a) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar G)
    (hAD : ∀ b ∈ A, D.map (MulAut.conj b).toMonoidHom = D) : False := by
  obtain ⟨hd4, hFa⟩ := Z3Cg2.params_of_orth hd hM hI0 hIinv hImin hO
  have ha : 1 ≤ a := hO.one_le
  refine orth_exclusion_abstract hZ ha hO.psl (Z3Cg2.isPSL_X hZ.swapDX hO.psl)
    (Z3Cg2.card_V_orth β hd4 hFa) ?_ ?_ ?_ ?_ hA hAD
  · intro j hj hj1 hjj
    exact Z3Cg2.card_fixV_sq_of_mem_sup hZ hM hI0 hIinv hImin hO hj hj1 hjj
  · intro j₁ hj₁ hj₁1 hj₁j₁ j₂ hj₂ hj₂1 _
    exact Z3Cg2.fixV_ne_of_model hM hj₁ hj₂ hj₁1 hj₁j₁ hj₂1
  · intro b hb1 hbb hbD hbX
    exact Z3Cg2.three_le_rkIdx_of_model hZ hM hd4 ha hFa hb1 hbb hbD hbX
  · intro b hbb hbD hbX hoD hoX
    exact Z3Cg2.five_le_rkIdx_of_model hZ hM hd4 ha hFa hbb hbD hbX hoD hoX

set_option linter.unusedVariables false in
theorem orth_exclusion {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)}
    {s : MulAut V} (hZ : Z37 D X G T' s) {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    (hd : 3 ≤ d) (β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F))
    (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F)
    (σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F) (hM : IsMatModel D X β ρ σ)
    (ϑ₀ : F ≃+* F) (Q R : Matrix (Fin d) (Fin d) F) (hQ : IsUnit Q) (hR : IsUnit R)
    (hform : ∀ v : V, Multiplicative.toAdd (β (s v)) =
      Q * ((Multiplicative.toAdd (β v)).map ϑ₀)ᵀ * R)
    {I : Subgroup V} (hI0 : I ≠ ⊥) (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) {a : ℕ}
    (hO : OrthMinusData D I a) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar G)
    (hAD : ∀ b ∈ A, D.map (MulAut.conj b).toMonoidHom = D) : False :=
  orth_exclusion_core hZ hd β ρ σ hM hI0 hIinv hImin hO hA hAD

end CFSG.Quasithin
