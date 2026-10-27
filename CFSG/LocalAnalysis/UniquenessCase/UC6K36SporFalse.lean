module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporM22
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporJ2
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Bridge.J2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup CFSG.Blueprint


theorem Spor.planeGenOrExc_catalog {s : TauCeti.SporadicName} (hs : s = .M12 ∨ s = .M22 ∨ s = .J2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : PlaneGenOrExc (TauCeti.CFSGIndex.sporadic s).Group p := by
  rcases hs with rfl | rfl | rfl
  · obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
    exact Spor.planeGenOrExc_of_mulEquiv e (Spor.planeGenOrExc_M12 hp hp2)
  · obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    exact Spor.planeGenOrExc_of_mulEquiv e (Spor.planeGenOrExc_M22 hp hp2)
  · obtain ⟨e⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
    exact Spor.planeGenOrExc_of_mulEquiv e (Spor.planeGenOrExc_J2 hp hp2)

namespace Hyp36

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem false_of_spor (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) {s : TauCeti.SporadicName} (hs : s = .M12 ∨ s = .M22 ∨ s = .J2)
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group) : False :=
  h.false_of_planeGen hL hne φ (Spor.planeGenOrExc_catalog hs h.prime h.odd)

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
