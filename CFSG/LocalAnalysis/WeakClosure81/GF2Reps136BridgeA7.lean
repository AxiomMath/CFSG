module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Sec
import CFSG.Quasithin.Background.HA7Rec

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem bridge_row_a7 (hw2 : ∀ w : W, w ^ 2 = 1) {U Z : Subgroup W}
    {L : Subgroup (MulAut W)} (hZU : Z ≤ U) (hL : StabPair L U Z) (hf : FaithOn L U Z)
    (hirr : IsIrrOn L U Z)
    (h : IsAlt ↥(secSub U Z L) 7 ∧ Nat.card (Sect U Z) = 2 ^ 4) : A7Four L U Z := by
  obtain ⟨hAlt, hcard⟩ := h
  have hU : ∀ h ∈ secSub U Z L, ∀ u ∈ (⊤ : Subgroup (Sect U Z)), h u ∈ ⊤ :=
    fun _ _ _ _ => Subgroup.mem_top _
  have hsq : ∀ u ∈ (⊤ : Subgroup (Sect U Z)), u * u = 1 := fun u _ => by
    rw [← pow_two]
    exact sect_exp_two hw2 U Z u
  have hcardU : Nat.card (⊤ : Subgroup (Sect U Z)) = 2 ^ 4 := by
    rw [Subgroup.card_top, hcard]
  have hfaithH : ∀ h ∈ secSub U Z L, (∀ u ∈ (⊤ : Subgroup (Sect U Z)), h u = u) → h = 1 :=
    fun h _ hfix => by
      ext u
      exact hfix u (Subgroup.mem_top u)
  have hfour : A7Four (secSub U Z L) ⊤ ⊥ :=
    CFSG.Quasithin.H.A7.a7Four_of_faithful hAlt hU hsq hcardU hfaithH
  obtain ⟨α, hreal⟩ := hfour
  exact ⟨α, (realizes_secSub_iff (FFModel.a7Four α) hL hZU hf).mp hreal⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
