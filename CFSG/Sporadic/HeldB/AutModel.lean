module

public import CFSG.Sporadic.HeldB.AutModelCore
public import CFSG.Sporadic.Schreier.PairHePairs

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.ComponentClassification.OuterAutomorphisms

theorem ctbh_full_automorphism_permutation_model :
    Function.Bijective heConjR ∧
    (heP.subgroupOf heAutGroup).map heConjR = (MulAut.conj : heP →* MulAut heP).range ∧
    Nat.card heAutGroup = 8060774400 ∧ IsCyclic (Outer heP) ∧ Nat.card (Outer heP) = 2 ∧
    ∀ θ : Blueprint.NativeSporadic.He ≃* heP,
      ∃ Φ : heAutGroup ≃* MulAut Blueprint.NativeSporadic.He,
        ∀ x h, Φ x h = θ.symm (heConjR x (θ h)) := by
  obtain ⟨hbij, -, hcyc, hcard⟩ := heConjR_facts CFSG.Sporadic.Schreier.AT_He_Schreier.1
  refine ⟨hbij, heConjR_map_heP, card_heAutGroup, hcyc, hcard, fun θ => ?_⟩
  exact ⟨(MulEquiv.ofBijective heConjR hbij).trans (@MulAut.congr _ _ _ Units.instGroup θ.symm),
    fun _ _ => rfl⟩

end CFSG.Sporadic.HeldB
