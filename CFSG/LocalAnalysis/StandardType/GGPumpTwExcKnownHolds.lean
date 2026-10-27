module

public import CFSG.LocalAnalysis.StandardType.GGPumpTwExcFactsE6
public import CFSG.LocalAnalysis.StandardType.GGPumpTwExcFactsTwE6
public import CFSG.LocalAnalysis.StandardType.GGKGAF4AutCard
public import CFSG.LocalAnalysis.StandardType.GGR4PumpTwKnownDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional

theorem ggPumpTwExc_transport {p : ℕ} {R : Type} [Group R] (hZ : Subgroup.center R = ⊥)
    {I : Set (MulAut R)} (hI : GGOutdiagPrime p R I) (hAO : KGA.GGF4AutOrderAt p R)
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A : Subgroup (MulAut L')) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (h4 : p ^ 4 ≤ Nat.card A) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152 := by
  refine KGA.ggF4_transport (I := {φ ∈ I | φ ^ p = 1}) hZ ?_ hAO ψ hψ hker hperf A hA ?_ h4
  · rintro φ ⟨hφ, hφp⟩
    obtain ⟨r, hr⟩ := hI φ hφ hφp
    exact ⟨r, hr.symm⟩
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    refine ⟨φ, ⟨hφ, ?_⟩, hφa⟩
    have hpow : ∀ n : ℕ, ∀ l : L', (φ ^ n) (ψ l) = ψ ((a ^ n) l) := by
      intro n
      induction n with
      | zero => intro l; simp
      | succ n ih =>
          intro l
          rw [pow_succ, MulAut.mul_apply, hφa l, ih (a l), pow_succ, MulAut.mul_apply]
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [hpow p l, hA.2 a ha]
    rfl

theorem ggPumpTwExcKnown_holds
    : GGPumpTwExcKnown := by
  intro f hf lab hlab
  rcases hlab with ⟨rfl, h3⟩ | ⟨rfl, h3⟩
  · exact (ggPumpTwExc_facts_E6 h3).mono fun R _ I _ ⟨hZ, hcp, hout, hAO⟩ =>
      ⟨hcp, hout, fun L' _ _ ψ hψ hker hperf A hA hAI h4 _ =>
        ggPumpTwExc_transport hZ hout hAO ψ hψ hker hperf A hA hAI h4⟩
  · exact (ggPumpTwExc_facts_twE6 hf h3).mono fun R _ I _ ⟨hZ, hcp, hout, hAO⟩ =>
      ⟨hcp, hout, fun L' _ _ ψ hψ hker hperf A hA hAI h4 _ =>
        ggPumpTwExc_transport hZ hout hAO ψ hψ hker hperf A hA hAI h4⟩

end CFSG.StandardType

end
