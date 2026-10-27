module

public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary

public section

namespace CFSG.Quasithin.J4L4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a in
theorem alt8_of_isPSL {X : Type} [Group X] (h : IsPSL 4 2 1 X) :
    Nonempty (X ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK2, ZMod.card]
  let ε : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard'
  have hunits : ∀ c : Kˣ, c = 1 := fun c => by
    have h1 : Units.map ε.toMonoidHom c = 1 := Subsingleton.elim _ _
    exact (Units.map_injective ε.injective) (by simpa using h1)
  exact ⟨(e.trans ((statedSLEquivProjectiveSL 4 K).trans
    ((slEquivProjectiveSL_two hunits 4).symm.trans (slMulEquivOfRingEquiv ε 4)))).trans
    ((CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).trans
      CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm)⟩

end CFSG.Quasithin.J4L4
