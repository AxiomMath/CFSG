module

public import CFSG.Adapters.TauCetiExceptional.ReeBridge

public section

namespace CFSG.Open

open TauCeti in
theorem models_lieModel_twistedG2_of_blueprint
    {G : Type} [Group G] {p f : ℕ} (h : Blueprint.LieModel G .twistedG2 0 p f) :
    Models.LieModel G .twistedG2 0 p f := by
  rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ | ⟨-, hsz, -⟩
  · exact absurd hcl (by decide)
  · exact absurd hce (by decide)
  · refine ⟨hadm, .inr ⟨rfl, ?_⟩⟩
    obtain ⟨-, -, -, rfl, -, h3⟩ := hadm
    have ha : 1 ≤ a := by omega
    have hv : (LieTypeIndex.reeG2 a).Valid := by
      refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
      · simpa [LieTypeIndex.inStandardRange_iff] using ha
      · simp [LieTypeIndex.isDuplicateRepresentative_iff]
    obtain ⟨b⟩ := TauCetiBridge.reeG2Bridge a hv K (by rw [hK, hfa])
    exact ⟨⟨LieTypeIndex.reeG2 a, hv⟩, ⟨rfl, hfa⟩, ⟨e.trans b⟩⟩
  · exact absurd hsz (by decide)

end CFSG.Open
