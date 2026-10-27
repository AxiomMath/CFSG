module

public import CFSG.Timmesfeld.Bridge.Asc72Local

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

theorem centSet_image {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (D : Set X) (z : X) :
    centSet (e '' D) (e z) = e '' centSet D z := by
  ext y
  constructor
  · rintro ⟨hy, hc⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨hx, Commute.of_map e.injective hc⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    exact ⟨Set.mem_image_of_mem e hx, Commute.map hc e⟩

end CFSG.Timmesfeld.Bridge.Asc72
