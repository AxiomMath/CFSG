module

public import CFSG.Quasithin.Background.ASVolIRu.BridgeOne
public import CFSG.Quasithin.Background.ASVolIRu.BridgeTwo
public import CFSG.Quasithin.Recognition.RuTypeNorm2
public import CFSG.Quasithin.Recognition.RuTypeJ22c
public import CFSG.Quasithin.Recognition.RuTypeJ22d

public section

namespace CFSG.ASVolI.ChIJK.RuType

open CFSG.Quasithin.RuType

variable {G : Type} [Group G] [Finite G] {L V T : Subgroup G}

theorem isTypeRu (hSt : StUniqueStatement) (h : RuType G L V T) : IsTypeRu G :=
  h.isTypeRu_of_two hSt (h.ruTwo fun _ hl hc => h.centralizer_V_le_S hl hc)

theorem exists_ruData (hSt : StUniqueStatement) (h : RuType G L V T) :
    ∃ R : RuData G, R.L = L ∧ R.T = h.sylowT := by
  have h1 := h.ruOne hSt
  have h2 := h.ruTwo fun _ hl hc => h.centralizer_V_le_S hl hc
  obtain ⟨θ, hθs, hθk, ⟨ψV, hψV⟩, ⟨χ, hχk, hχt, hχs, hχe⟩⟩ := h1.modules
  obtain ⟨σ5, hσs, hσk⟩ := h2.symmetric
  obtain ⟨φ, ψU, hφs, hφk, hψs, hψk, hψe⟩ := h2.natural
  exact ⟨⟨L, h.sylowT, h1, h2, θ, hθs, hθk, ψV, hψV, χ, hχk, hχt, hχs, hχe, σ5, hσs, hσk, φ, hφs,
    hφk, ψU, hψs, hψk, hψe⟩, rfl, rfl⟩

theorem exists_ruDataM (hSt : StUniqueStatement) (h : RuType G L V T) :
    ∃ M : RuDataM G, M.L = L ∧ M.T = h.sylowT := by
  obtain ⟨R, hL, hT⟩ := h.exists_ruData hSt
  exact ⟨R.normalize.normalizeS, hL, hT⟩

end CFSG.ASVolI.ChIJK.RuType
