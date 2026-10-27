module

public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin

namespace StabLat

theorem mem_stabSub_of_eq_orbSup {W : Type} [CommGroup W] {T : Subgroup (MulAut W)}
    {U : Subgroup W} (h : U = orbSup T U) {t : MulAut W} (ht : t ∈ T) :
    t ∈ CFSG.Quasithin.stabSub U := by
  have hmap : ∀ s ∈ T, ∀ u ∈ U, s u ∈ U := by
    intro s hs u hu
    rw [h]
    exact (le_iSup₂ (f := fun s (_ : s ∈ T) => U.map s.toMonoidHom) s hs) ⟨u, hu, rfl⟩
  intro u
  refine ⟨fun hu => ?_, hmap t ht u⟩
  have := hmap t⁻¹ (T.inv_mem ht) _ hu
  simpa using this

end StabLat

end CFSG.Quasithin
