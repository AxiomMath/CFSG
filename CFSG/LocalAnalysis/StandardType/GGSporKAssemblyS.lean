module

public import CFSG.LocalAnalysis.StandardType.GGSporKAssembly

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem ggSporK_pair_of_elevenComp_of_simple (s : TauCeti.SporadicName)
    [Finite (TauCeti.CFSGIndex.sporadic s).Group]
    (hInn : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group →
      ∀ φ : MulAut (TauCeti.CFSGIndex.sporadic s).Group, ∃ g, φ = MulAut.conj g)
    (h11 : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group →
      BMElevenComp (TauCeti.CFSGIndex.sporadic s).Group) :
    GGKGroupFusionAtFlatKPair s 11 := by
  intro W _ _ hW q H E i hi hyp hL hK he
  have hKs : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group := by
    obtain ⟨rfl, rfl⟩ := hi
    obtain ⟨e⟩ := he
    haveI : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hyp.2.1.1
    exact e.symm.isSimpleGroup
  exact ggSporK_pair_of_elevenComp s (hInn hKs) (h11 hKs) W hW q H E i hi hyp hL hK he

theorem ggSporK_pair_of_inputsB_of_simple (s : TauCeti.SporadicName)
    [Finite (TauCeti.CFSGIndex.sporadic s).Group]
    (hInn : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group →
      ∀ φ : MulAut (TauCeti.CFSGIndex.sporadic s).Group, ∃ g, φ = MulAut.conj g)
    (ha : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group →
      BSevenComp (TauCeti.CFSGIndex.sporadic s).Group)
    (hb : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group →
      BSevenCentAbelian (TauCeti.CFSGIndex.sporadic s).Group)
    (hc : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group →
      BSevenSpread (TauCeti.CFSGIndex.sporadic s).Group)
    (hOrd : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group →
      BSevenOrd (TauCeti.CFSGIndex.sporadic s).Group)
    (hLie : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group →
      LieSevenOddCentre7sq (TauCeti.CFSGIndex.sporadic s).Group)
    (h49 : (Nat.card (TauCeti.CFSGIndex.sporadic s).Group).factorization 7 = 2) :
    GGKGroupFusionAtFlatKPair s 7 := by
  intro W _ _ hW q H E i hi hyp hL hK he
  have hKs : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group := by
    obtain ⟨rfl, rfl⟩ := hi
    obtain ⟨e⟩ := he
    haveI : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hyp.2.1.1
    exact e.symm.isSimpleGroup
  exact ggSporK_pair_of_inputsB s (hInn hKs) (ha hKs) (hb hKs) (hc hKs) (hOrd hKs) (hLie hKs) h49
    W hW q H E i hi hyp hL hK he

theorem ggSporK_pair_of_not_sq_dvd_card_of_simple (s : TauCeti.SporadicName) (p : ℕ)
    [Finite (TauCeti.CFSGIndex.sporadic s).Group]
    (hInn : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group →
      ∀ φ : MulAut (TauCeti.CFSGIndex.sporadic s).Group, ∃ g, φ = MulAut.conj g)
    (hp : ¬ p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group) :
    GGKGroupFusionAtFlatKPair s p := by
  intro W _ _ hW q H E i hi hyp hL hK he
  have hKs : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group := by
    obtain ⟨rfl, rfl⟩ := hi
    obtain ⟨e⟩ := he
    haveI : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hyp.2.1.1
    exact e.symm.isSimpleGroup
  exact ggSporK_pair_of_not_sq_dvd_card s p (hInn hKs) hp W hW q H E i hi hyp hL hK he

end CFSG.StandardType.SporadicShape
