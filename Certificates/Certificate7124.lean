
module

public import CFSG.Quasithin.Background.E2TwoProofSporJ1Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import CFSG.Sporadic.J1.Setup
public import Certificates.Data.CFSGNative.J1.Certificate
import Certificates.Kernel.J1Dc.Final

public section

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.E2P.SporB CFSG.Quasithin.E2P.SporB.J1Lat
  CFSG.Sporadic.J1 CFSG.KD.J1Dc

namespace Certificates

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.E2P.SporB.J1Lat CFSG.Sporadic.J1 in
theorem certificate7124 : 
    Nat.card (Subgroup.closure {x | x ∈ j1Words.map (wordElt (a : CFSG.Sporadic.J1.J) (b : CFSG.Sporadic.J1.J))}) = 8 ∧
    ∃ Y : ℕ → Subgroup CFSG.Sporadic.J1.J,
      (∀ j < 17, Subgroup.closure {x | x ∈ j1Words.map (wordElt (a : CFSG.Sporadic.J1.J) (b : CFSG.Sporadic.J1.J))} ≤ Y j ∧
        Nat.card (Y j) = [1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21].getD j 0 * 8) ∧
      ∀ Z : Subgroup CFSG.Sporadic.J1.J, Subgroup.closure {x | x ∈ j1Words.map (wordElt (a : CFSG.Sporadic.J1.J) (b : CFSG.Sporadic.J1.J))} ≤ Z →
        Z = ⊤ ∨ ∃ j < 17, Z = Y j := by
  refine ⟨j1K_card_S, j1CtxK.Y, fun j hj => ⟨?_, ?_⟩, fun Z hZ => ?_⟩
  · have h := j1CtxK.S_le_Y j
    rw [j1K_S] at h
    exact h
  · rw [j1K_card hj]
    rfl
  · obtain ⟨j, hj, rfl⟩ := j1CtxK.complete Z (by rw [j1K_S]; exact hZ)
    rw [j1K_J] at hj ⊢
    by_cases hj17 : j < 17
    · right
      refine ⟨j, hj17, ?_⟩
      unfold memberOrTop
      rw [if_pos hj17]
    · left
      unfold memberOrTop
      rw [if_neg hj17]

end Certificates
