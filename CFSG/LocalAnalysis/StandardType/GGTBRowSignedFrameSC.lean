module

public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameW
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTorusSignedFrameW_of_signedEltSC {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type}
    [Group R] {I : Set (MulAut R)} (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R) (h : GGTorusSignedEltSC p R) :
    GGTorusSignedFrameW p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, _hr, h3, hsc⟩ := hA
  obtain ⟨k, Θ, hk, hW, hsgn, hperm, hsp⟩ :=
    exists_signedModelSC hp hp2 hI hZ hcp h hψ hker hperf hAe hAI h3 hsc
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
