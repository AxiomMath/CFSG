module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Ident
public import CFSG.Quasithin.H13.NQCatBND4
public import CFSG.Quasithin.H13.NQCatBNRee
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Lie

public section

namespace CFSG.Quasithin.H13.D42

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_isTits
    (hT : IsTits Y) {U W : Subgroup Y} (hU : IsSylowTwoOf U ⊤) (hW : ¬ Group.IsSolvable ↥W)
    (hWU : W ⊔ U ≠ ⊤) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H', N', -, -, -, -, -, hlat, hHs, hNs⟩ :=
    Setup.X6.titsSylowOvergroupLattice Y hT U hU
  have hns : ¬ Group.IsSolvable ↥(W ⊔ U) := fun hs => hW
    (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (le_sup_left : W ≤ W ⊔ U)) (Subgroup.inclusion_injective _))
  rcases hlat (W ⊔ U) le_sup_right with h1 | h1 | h1 | h1
  · apply hns
    rw [h1]
    have := hU.2.1.isNilpotent
    infer_instance
  · exact hns (h1 ▸ hHs)
  · exact hns (h1 ▸ hNs)
  · exact hWU h1


theorem false_of_is2F4 [Group.IsPerfect Y] [Nontrivial Y] {k : ℕ} (h : Is2F4 k Y)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤)
    (hmax : ∃ U' P : Subgroup Y, IsSylowTwoOf U' ⊤ ∧ U' ≤ P ∧ P ⋖ ⊤ ∧ Group.IsSolvable ↥P) :
    False := by
  obtain ⟨⟨-, -, -, -, hodd, hk3⟩, -⟩ := id h
  exact false_of_solvOver hU
    (Setup.X6.even_rank_two_exceptional_proper_Sylow_overgroup_residual hU
      (Or.inr (Or.inr ⟨k, hk3, hodd, h⟩)))
    (NQCat.BN.solvOver_of_is2F4 h hU) hmax

theorem is3D4_of_solvable_max
    [Group.IsPerfect Y] [Nontrivial Y] (hR : IsRank2LieChar2 Y) {U W : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) (hW : ¬ Group.IsSolvable ↥W) (hWU : W ⊔ U ≠ ⊤) {k : ℕ}
    (hk : 2 ≤ k) (hWk : 2 ^ k * (4 ^ k - 1) ∣ Nat.card ↥W)
    (hmax : ∃ U' P : Subgroup Y, IsSylowTwoOf U' ⊤ ∧ U' ≤ P ∧ P ⋖ ⊤ ∧ Group.IsSolvable ↥P) :
    Is3D4 2 1 Y := by
  rcases hR with ⟨f, ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hodd, hf3, h⟩⟩ | hT
  · rcases Nat.lt_or_ge f 2 with h1 | h2
    · obtain rfl : f = 1 := by omega
      exact (not_dvd_of_card_168 (card_eq_168_of_isPSL3 h) hk hWk).elim
    · exact (false_of_solvOver hU
        (Setup.X7a.even_rank_two_classical_proper_Sylow_overgroup_residual hU (Or.inl ⟨f, h⟩))
        (solvOver_of_isPSL3 h2 h hU) hmax).elim
  · rcases Nat.lt_or_ge f 2 with h1 | h2
    · obtain rfl : f = 1 := by omega
      exact (not_dvd_of_card_168 (card_eq_168_of_isSL3 h) hk hWk).elim
    · exact (false_of_solvOver hU (residualOvergroups_of_isSL3 h hU)
        (solvOver_of_isSL3 h2 h hU) hmax).elim
  · exact (false_of_solvOver hU
      (Setup.X7a.even_rank_two_classical_proper_Sylow_overgroup_residual hU (Or.inr ⟨f, h⟩))
      (solvOver_of_isPSp4 hf h hU) hmax).elim
  · exact (false_of_solvOver hU
      (Setup.X6.even_rank_two_exceptional_proper_Sylow_overgroup_residual hU
        (Or.inl ⟨f, hf, h⟩))
      (NQCat.BN.solvOver_of_isG2 hf h hU) hmax).elim
  · rcases Nat.lt_or_ge f 2 with h1 | h2
    · obtain rfl : f = 1 := by omega
      exact h
    · exact (false_of_solvOver hU
        (Setup.X6.even_rank_two_exceptional_proper_Sylow_overgroup_residual hU
          (Or.inr (Or.inl ⟨f, hf, h⟩)))
        (NQCat.BN.solvOver_of_is3D4 h2 h hU) hmax).elim
  · exact (false_of_is2F4 h hU hmax).elim
  · exact (false_of_isTits hT hU hW hWU).elim

end CFSG.Quasithin.H13.D42
