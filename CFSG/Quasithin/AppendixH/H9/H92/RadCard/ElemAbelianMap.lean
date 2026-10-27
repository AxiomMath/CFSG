module

public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin

theorem isElemAbelian2_map_of_comm_sq {V : Type*} [CommGroup V] {G : Type*} [Group G]
    (f : G →* MulAut V) (A : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hs : ∀ a ∈ A, a * a = 1) : IsElemAbelian2 (A.map f) := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [pow_two, ← map_mul, hs a ha, map_one]

end CFSG.ASVolI.ChH
