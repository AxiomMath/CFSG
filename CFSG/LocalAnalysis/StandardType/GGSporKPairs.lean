module

public import CFSG.LocalAnalysis.StandardType.GGSporKShape
public import CFSG.LocalAnalysis.StandardType.GGSporKFittingEq
public import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA
public import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportB
public import CFSG.LocalAnalysis.StandardType.GGSporKFalseA
public import CFSG.LocalAnalysis.StandardType.GGSporKFalseB
public import CFSG.LocalAnalysis.StandardType.GGSporKFalseEleven

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem ggSporK_pair_of_inputsA (s : TauCeti.SporadicName) (p : ℕ)
    [Finite (TauCeti.CFSGIndex.sporadic s).Group]
    (hInn : ∀ φ : MulAut (TauCeti.CFSGIndex.sporadic s).Group, ∃ g, φ = MulAut.conj g)
    (hCen : BMNoLiePComp p (TauCeti.CFSGIndex.sporadic s).Group)
    (hG1 : BMPPrimeCore p (TauCeti.CFSGIndex.sporadic s).Group)
    (hZ : BMCentreZ p (TauCeti.CFSGIndex.sporadic s).Group)
    (hOrd : BMOrd p (TauCeti.CFSGIndex.sporadic s).Group) :
    GGKGroupFusionAtFlatKPair s p := by
  intro W _ _ hW q H E i hi hyp hL hK he
  obtain ⟨rfl, rfl⟩ := hi
  obtain ⟨f⟩ := ggSporK_nonempty_mulEquiv hyp.2.1.1 hyp.2.1.2.1 hInn he
  exact (ggSporK_false_of_inputsA_W q (bmNoLiePComp_of_mulEquiv q f.symm hCen)
    (bmPPrimeCore_of_mulEquiv q f.symm hG1) (bmCentreZ_of_mulEquiv q f.symm hZ)
    (bmOrd_of_mulEquiv q f.symm hOrd) H E hyp hL).elim

theorem ggSporK_pair_of_elevenComp (s : TauCeti.SporadicName)
    [Finite (TauCeti.CFSGIndex.sporadic s).Group]
    (hInn : ∀ φ : MulAut (TauCeti.CFSGIndex.sporadic s).Group, ∃ g, φ = MulAut.conj g)
    (h11 : BMElevenComp (TauCeti.CFSGIndex.sporadic s).Group) :
    GGKGroupFusionAtFlatKPair s 11 := by
  intro W _ _ hW q H E i hi hyp hL hK he
  obtain ⟨rfl, rfl⟩ := hi
  obtain ⟨f⟩ := ggSporK_nonempty_mulEquiv hyp.2.1.1 hyp.2.1.2.1 hInn he
  exact (ggSporK_false_of_elevenComp_W (bmElevenComp_of_mulEquiv f.symm h11) hyp).elim

theorem ggSporK_pair_of_inputsB (s : TauCeti.SporadicName)
    [Finite (TauCeti.CFSGIndex.sporadic s).Group]
    (hInn : ∀ φ : MulAut (TauCeti.CFSGIndex.sporadic s).Group, ∃ g, φ = MulAut.conj g)
    (ha : BSevenComp (TauCeti.CFSGIndex.sporadic s).Group)
    (hb : BSevenCentAbelian (TauCeti.CFSGIndex.sporadic s).Group)
    (hc : BSevenSpread (TauCeti.CFSGIndex.sporadic s).Group)
    (hOrd : BSevenOrd (TauCeti.CFSGIndex.sporadic s).Group)
    (hLie : LieSevenOddCentre7sq (TauCeti.CFSGIndex.sporadic s).Group)
    (h49 : (Nat.card (TauCeti.CFSGIndex.sporadic s).Group).factorization 7 = 2) :
    GGKGroupFusionAtFlatKPair s 7 := by
  intro W _ _ hW q H E i hi hyp hL hK he
  obtain ⟨rfl, rfl⟩ := hi
  obtain ⟨f⟩ := ggSporK_nonempty_mulEquiv hyp.2.1.1 hyp.2.1.2.1 hInn he
  have hcard : Nat.card W = Nat.card (TauCeti.CFSGIndex.sporadic s).Group :=
    Nat.card_congr f.toEquiv
  exact (ggSporK_false_of_inputsB_W (bSevenComp_of_mulEquiv f.symm ha)
    (bSevenCentAbelian_of_mulEquiv f.symm hb) (bSevenSpread_of_mulEquiv f.symm hc)
    (bSevenOrd_of_mulEquiv f.symm hOrd) (lieSevenOddCentre7sq_of_mulEquiv f.symm hLie)
    (hcard ▸ h49) H E hyp hL).elim

end CFSG.StandardType.SporadicShape
