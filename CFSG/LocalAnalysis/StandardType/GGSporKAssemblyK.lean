module

public import CFSG.LocalAnalysis.StandardType.GGSporKAssemblyS

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

@[expose] def GGSporKInputsAK (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  (CFSG.Open.IsKGroup K → BMNoLiePComp p K) ∧ BMPPrimeCore p K ∧ BMCentreZ p K ∧ BMOrd p K

theorem ggSporK_pair_of_inputsAK_of_simple (s : TauCeti.SporadicName) (p : ℕ)
    [Finite (TauCeti.CFSGIndex.sporadic s).Group]
    (hInn : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group →
      ∀ φ : MulAut (TauCeti.CFSGIndex.sporadic s).Group, ∃ g, φ = MulAut.conj g)
    (hIn : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group →
      GGSporKInputsAK p (TauCeti.CFSGIndex.sporadic s).Group) :
    GGKGroupFusionAtFlatKPair s p := by
  intro W _ _ hW q H E i hi hyp hL hK he
  have hKs : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group := by
    obtain ⟨rfl, rfl⟩ := hi
    obtain ⟨e⟩ := he
    haveI : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hyp.2.1.1
    exact e.symm.isSimpleGroup
  have hKk : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group := by
    obtain ⟨rfl, rfl⟩ := hi
    obtain ⟨e⟩ := he
    exact ggSporK_isKGroup_of_fstar hW e
  exact ggSporK_pair_of_inputsA s p (hInn hKs) ((hIn hKs).1 hKk) (hIn hKs).2.1 (hIn hKs).2.2.1
    (hIn hKs).2.2.2 W hW q H E i hi hyp hL hK he

end CFSG.StandardType.SporadicShape
