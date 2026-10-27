module

public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTorusSignedFrameW (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      ∃ k : ℕ, 3 ≤ k ∧ Nat.card ↥A = p ^ k ∧ GGWeylFrame p A (CoxeterMatrix.B k)

theorem ggTorusSignedFrameW_of_signedElt {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type}
    [Group R] {I : Set (MulAut R)} (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (h : GGTorusSignedElt p r R) : GGTorusSignedFrameW p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, -⟩ := hA
  obtain ⟨k, Θ, hk, hW, hsgn, hperm, hsp⟩ :=
    exists_signedModel hp hp2 hI hZ h hψ hker hperf hAe hAI hr h3
  refine ⟨k, hk, ?_, ggWeylFrame_of_signedModel hp hp2 hk Θ hW hsgn hperm hsp⟩
  have hcV : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
    rw [Nat.card_fun, Nat.card_fin]
    congr 1
    exact Nat.card_zmod p
  have hcard : Nat.card (Fin k → Multiplicative (ZMod p)) = Nat.card ↥A :=
    Nat.card_congr Θ.toEquiv
  rw [← hcard, hcV]

end CFSG.StandardType

end
