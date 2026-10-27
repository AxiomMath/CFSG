module

public import CFSG.LocalAnalysis.StandardType.GGTBRowDSignedFrame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven
public import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBRowCoordFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative NbrOrth

theorem ggTorusEvenSignedPermEltSCOf_of_orthFrameSC {p ℓ : ℕ} (hp : p.Prime) {R : Type}
    [Group R] (hF : GGTorusOrthFrameSC p R ℓ)
    (hE : GGTorusEvenSignedPermEltSC p R fun k => k = ℓ) :
    GGTorusEvenSignedPermEltSCOf p R (fun k => k = ℓ) fun _ ε => ∏ i, ε i = 1 := by
  intro E hEa h3 hsc
  obtain ⟨k, τ, hinj, hrange, hperm, hcase⟩ := hF E hEa h3 hsc
  obtain ⟨k', τ', hinj', hrange', hk', -⟩ := hE E hEa h3 hsc
  rcases hcase with ⟨hk, hd, hN⟩ | ⟨hk1, -, -⟩
  · exact ⟨k, τ, hinj, hrange, hk, hd, hperm, hN⟩
  · exfalso
    have hcard : Nat.card E = p ^ k := by
      rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
        Nat.card_fun, Nat.card_fin]
      congr 1
      exact Nat.card_zmod p
    have hcard' : Nat.card E = p ^ k' := by
      rw [← hrange', ← Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv,
        Nat.card_fun, Nat.card_fin]
      congr 1
      exact Nat.card_zmod p
    have hpow : p ^ k = p ^ k' := by rw [← hcard, hcard']
    have hkk' : k = k' := Nat.pow_right_injective hp.two_le hpow
    omega

theorem ggTorusDFrameW_of_evenSignedPermEltSCOf {p r ℓ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hℓ : 4 ≤ ℓ) {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R)
    (h : GGTorusEvenSignedPermEltSCOf p R (fun k => k = ℓ) fun _ ε => ∏ i, ε i = 1) :
    GGTorusWeylFrameW p r R I (ggCoxeterMatrixD ℓ) ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → Nat.card ↥A = p ^ ℓ := by
  refine ⟨fun L' _ _ ψ A hA => ?_, fun L' _ _ ψ A hA => ?_⟩
  · obtain ⟨hψ, hker, hperf, hAe, hAI, _hr, h3, hsc⟩ := hA
    obtain ⟨k, Θ, -, hk, hW, hd, hP, -, hN⟩ :=
      OrthExcEven.exists_evenSignedPermModelSCOf hp hp2 hI hZ hcp h hψ hker hperf hAe hAI h3 hsc
    subst hk
    exact ggWeylFrame_of_dSignedModel hp hp2 hℓ Θ hW hd hP hN
  · obtain ⟨hψ, hker, hperf, hAe, hAI, _hr, h3, hsc⟩ := hA
    obtain ⟨k, Θ, -, hk, -, -, -, -, -⟩ :=
      OrthExcEven.exists_evenSignedPermModelSCOf hp hp2 hI hZ hcp h hψ hker hperf hAe hAI h3 hsc
    subst hk
    have hcV : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [Nat.card_fun, Nat.card_fin]
      congr 1
      exact Nat.card_zmod p
    have hcard : Nat.card (Fin k → Multiplicative (ZMod p)) = Nat.card ↥A :=
      Nat.card_congr Θ.toEquiv
    rw [← hcard, hcV]

end CFSG.StandardType

end
