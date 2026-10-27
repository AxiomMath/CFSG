module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45TorusHRaw_of_vac {p : ℕ} {lab : LargeEvenLabel} {R : Type} [Group R]
    {I F : Set (MulAut R)} (h : GGL45NtVac p R I F) : GGL45TorusHRaw p lab R I F := by
  intro K _ _ θ hK _ ψ E hyp
  obtain ⟨hψ, ⟨f, hf, u, hu, hord, hind⟩, hE, hcard, hD4, hEI, hψE, hsat, hrk, hpi⟩ := hyp
  exfalso
  rcases h with hno | hno
  · exact hno f hf hord
  · refine hno ⟨E.map (ggInducedAut θ), ?_, ?_, ?_⟩
    · rw [IsElemAbelian]
      constructor
      · haveI : IsMulCommutative E := hE.1
        exact Subgroup.map_isMulCommutative (H := E) (ggInducedAut θ)
      · intro x hx
        obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
        rw [← map_pow, hE.2 e he, map_one]
    · rw [Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hK θ)]
      exact hcard
    · intro a ha
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp ha
      exact (ggL45_inducesIn_iff θ I e).1 (hEI e he)

end CFSG.StandardType
