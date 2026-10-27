module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2OmegaPts
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmNonsing

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
open MulAction

theorem Om_sing_ncard : {v : Fin 6 → ZMod 2 | qMinus v = 0 ∧ v ≠ 0}.ncard = 27 := by
  have e : {v : Fin 6 → ZMod 2 | qMinus v = 0 ∧ v ≠ 0} =
      ↑(Finset.univ.filter fun v : Fin 6 → ZMod 2 => qMinus v = 0 ∧ v ≠ 0) := by
    ext v
    simp
  rw [e, Set.ncard_coe_finset]
  decide

theorem orbit_sing {p : Fin 6 → ZMod 2} (hp : qMinus p = 0) (hp0 : p ≠ 0) :
    orbit OmG p = {v | qMinus v = 0 ∧ v ≠ 0} := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨?_, ?_⟩
    · change qMinus ((g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) p) = 0
      rw [qMinus_apply_of_mem g.2, hp]
    · intro h0
      apply hp0
      have : (g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) p = 0 := h0
      exact (g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)).map_eq_zero_iff.1 this
  · rintro ⟨hv, hv0⟩
    obtain ⟨g, hg, hgv⟩ := exists_mem_timmesfeldOmega_apply_eq hp0 hv0 (by rw [hp, hv])
    exact ⟨⟨g, hg⟩, hgv⟩

theorem card_stabilizer_sing {s : Fin 6 → ZMod 2} (hs : qMinus s = 0) (hs0 : s ≠ 0) :
    Nat.card (stabilizer OmG s) = 960 := by
  have h1 := index_stabilizer OmG s
  rw [orbit_sing hs hs0, Om_sing_ncard] at h1
  have h2 := Subgroup.card_mul_index (stabilizer OmG s)
  rw [h1, card_timmesfeldOmega] at h2
  omega

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
