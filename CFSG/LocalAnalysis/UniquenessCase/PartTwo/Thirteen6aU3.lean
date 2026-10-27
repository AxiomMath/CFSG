module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s136a_false_of_inP11_of_isU3 {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (h1 : S17.R17_1At D V₀ V hV) (h333 : S17.R17_33_3At D V₀ V) {L : Subgroup G}
    (hL : L ∈ calC D.M) {n : ℕ} (hU : IsU3 (Bar2 L) n) {X : Subgroup G}
    (hX : F11.InP11 D X) : False := by
  have hV₀ : V₀ = ⊥ := (h1.2 ⟨X, hX⟩).1
  have h := h333 L n hL (uc22p22d_isSU3_of_isU3 hL.2.2 hU)
  have h0 : mSub (⊥ : Subgroup G) = 0 := CFSG.Quasithin.rk_bot
  rw [hV₀, h0] at h
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a
