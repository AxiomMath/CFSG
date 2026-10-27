module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Idx

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431
open scoped Pointwise

theorem L0S_eq : L0S = ((({0, 15, 16, 20, 24} : Finset (Fin 45))) : Set (Fin 45)) := by
  have h : ∀ p : Fin 45, (p.val ∈ L0) ↔ p ∈ ({0, 15, 16, 20, 24} : Finset (Fin 45)) := by decide
  ext p
  exact h p

theorem L0S_ncard : L0S.ncard = 5 := by
  rw [L0S_eq, Set.ncard_coe_finset]
  decide

theorem zero_mem_L0S : (0 : Fin 45) ∈ L0S := by
  rw [L0S_eq]
  simp

theorem stabilizer_P2 : MulAction.stabilizer ↥P2 (0 : Fin 45) = B0.subgroupOf P2 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, B0, Subgroup.mem_inf]
  constructor
  · intro h
    exact ⟨(mem_P1_iff _).2 h, g.2⟩
  · intro h
    exact (mem_P1_iff _).1 h.1

theorem orbit_P2 : MulAction.orbit ↥P2 (0 : Fin 45) = L0S := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    have h := (mem_P2_iff (g : Y)).1 g.2
    have hz : ((g : Y) : P45) 0 ∈ ((g : Y) : P45) '' L0S := ⟨0, zero_mem_L0S, rfl⟩
    rw [h] at hz
    exact hz
  · intro hp
    have hp' : p.val ∈ L0 := hp
    have hmem : p.val ∈ p2W.map Prod.fst := by rw [p_spec.2.2.2.2.2]; exact hp'
    obtain ⟨pw, hpw, hpwe⟩ := List.mem_map.1 hmem
    obtain ⟨-, hap, hss⟩ := p_spec.2.2.2.2.1 pw hpw
    refine ⟨⟨⟨wordP pw.2, wordP_mem _⟩, ?_⟩, ?_⟩
    · rw [mem_P2_iff]
      show (wordP pw.2) '' L0S = L0S
      rw [L0S, image_lineSet (repL_wordP _) L0_lt, lineSet_eq_of_sameSet hss]
    · apply Fin.ext
      show ((wordP pw.2) 0 : ℕ) = p.val
      rw [applyW_eq]
      exact hap.trans hpwe

theorem relIndex_B0_P2 : B0.relIndex P2 = 5 := by
  have h := MulAction.index_stabilizer ↥P2 (0 : Fin 45)
  rw [stabilizer_P2, orbit_P2, L0S_ncard] at h
  exact h

theorem card_P2 :
    Nat.card P2 = 960 := by
  have h1 := Subgroup.relIndex_mul_card (H := B0) (K := P2)
  rw [inf_eq_left.2 B0_le_P2, relIndex_B0_P2, card_B0] at h1
  omega

end CFSG.Quasithin.H13.F431.U42
