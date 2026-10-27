module

public import CFSG.Quasithin.Background.H16TwoM22PfA
public import CFSG.Quasithin.Background.H16TwoM22PfB

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin.H.Mathieu

theorem card_orbit_mog22_le (x : Finset (Fin 24)) :
    Nat.card (MulAction.orbit ↥mog22 x) ≤ Nat.card (MulAction.orbit ↥mog22plus x) := by
  let f : MulAction.orbit ↥mog22 x → MulAction.orbit ↥mog22plus x := fun y =>
    ⟨y.1, by
      obtain ⟨⟨g, hg⟩, h⟩ := y.2
      exact ⟨⟨g, mog22_le_mog22plus hg⟩, h⟩⟩
  have hf : Function.Injective f := by
    intro y z h
    apply Subtype.ext
    exact congrArg (fun w : MulAction.orbit ↥mog22plus x => (w : Finset (Fin 24))) h
  exact Nat.card_le_card_of_injective f hf

theorem card_stab_plus_mul_le
    {m₀ : ℕ} {L : List (ℕ × ℕ × ℕ)} (hL : bfsOK m₀ L = true) (hnd : (L.map Prod.fst).Nodup)
    (hlt : ∀ e ∈ L, e.1 < 2 ^ 24) :
    Nat.card (MulAction.stabilizer ↥mog22plus (maskSet m₀)) * L.length ≤ 887040 := by
  have h := (MulAction.stabilizer ↥mog22plus (maskSet m₀)).card_mul_index
  rw [MulAction.index_stabilizer, card_mog22plus] at h
  rw [← h]
  exact Nat.mul_le_mul_left _ ((le_card_orbit_of_bfs hL hnd hlt).trans (card_orbit_mog22_le _))

end CFSG.Quasithin.RonanH143
