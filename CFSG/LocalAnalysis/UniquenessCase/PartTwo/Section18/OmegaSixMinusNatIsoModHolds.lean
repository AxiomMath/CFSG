module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaMinusNatTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusSUFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourteenK
public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open CFSG.Quasithin
open scoped Matrix

theorem exists_natAct_intertwine_omegaSixMinus {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (α : MulAut (StatedOmega (StatedQuadMinus 3 K b c))) :
    ∃ A : Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) ≃*
        Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K),
      ∀ (γ : StatedOmega (StatedQuadMinus 3 K b c))
        (x : Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K)),
        A (natAct (StatedOmega (StatedQuadMinus 3 K b c)) γ x) =
          natAct (StatedOmega (StatedQuadMinus 3 K b c)) (α γ) (A x) := by
  classical
  obtain ⟨E, _, _, D, Φ, ψ, ρ, -, -, hψρ, hΦ⟩ := exists_statedOmegaMinus_equiv_sixSU hK hirr
  obtain ⟨α', hα'⟩ : ∃ α' : MulAut D.sixSU, ∀ g, Φ (α' g) = α (Φ g) :=
    ⟨MulAut.congr Φ.symm α, fun g => by simp [MulAut.congr_apply]⟩
  obtain ⟨B, hB⟩ := D.exists_sixSpace_intertwine α'
  have hψs : ∀ (g : D.sixSU) (Y : D.sixSpace), ψ.symm (D.sixRho g Y) = ρ g (ψ.symm Y) := by
    intro g Y
    rw [LinearEquiv.symm_apply_eq, hψρ, LinearEquiv.apply_symm_apply]
  let A : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) ≃+ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
    ψ.toAddEquiv.trans (B.trans ψ.symm.toAddEquiv)
  have hA : ∀ (g : D.sixSU) v, A (ρ g v) = ρ (α' g) (A v) := by
    intro g v
    change ψ.symm (B (ψ (ρ g v))) = ρ (α' g) (ψ.symm (B (ψ v)))
    rw [hψρ, hB, hψs]
  refine ⟨A.toMultiplicative, fun γ x => ?_⟩
  obtain ⟨g, rfl⟩ := Φ.surjective γ
  rw [← hα' g]
  apply Multiplicative.toAdd.injective
  change A ((((Φ g : StatedOmega (StatedQuadMinus 3 K b c)) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ
      Multiplicative.toAdd x) =
    (((Φ (α' g) : StatedOmega (StatedQuadMinus 3 K b c)) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ
      A (Multiplicative.toAdd x)
  rw [hΦ, hΦ, hA]

theorem k_Omega6Minus_natIsoMod_holds : K_Omega6Minus_natIsoMod := by
  intro W _ H U₁ U₂ n h₁ h₂
  obtain ⟨-, K₁, _, _, b₁, c₁, hK₁, hirr₁, π₁, hπ₁⟩ := h₁
  obtain ⟨-, K₂, _, _, b₂, c₂, hK₂, hirr₂, π₂, hπ₂⟩ := h₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K₁ := Fintype.ofFinite K₁
  have : CharP K₁ 2 := charP_of_card_eq_prime_pow (by rw [Fintype.card_eq_nat_card]; exact hK₁)
  have hinj₁ := hπ₁.injective_of_faithful_on (FFModel.nat_faithful _)
  have hinj₂ := hπ₂.injective_of_faithful_on (FFModel.nat_faithful _)
  let e₁ := MulEquiv.ofBijective π₁ ⟨hinj₁, hπ₁.1⟩
  let e₂ := MulEquiv.ofBijective π₂ ⟨hinj₂, hπ₂.1⟩
  let φ := e₁.trans e₂.symm
  obtain ⟨χ, B, hB⟩ := exists_statedOmegaMinus_natTransport (hK₁.trans hK₂.symm) 3 hirr₁ hirr₂
  obtain ⟨A₁, hA₁⟩ := exists_natAct_intertwine_omegaSixMinus hK₁ hirr₁ (φ.trans χ.symm)
  refine isoMod_of_realizesVia_nat_intertwine hπ₁ hπ₂ φ.toMonoidHom φ.surjective ?_
    (A₁.trans B) fun γ x => ?_
  · exact MonoidHom.ext fun γ => e₂.apply_symm_apply (e₁ γ)
  · rw [MulEquiv.trans_apply, hA₁, hB]
    exact congrArg (fun g => natAct _ g (B (A₁ x))) (χ.apply_symm_apply (φ γ))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
