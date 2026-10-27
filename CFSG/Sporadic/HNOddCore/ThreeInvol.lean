
module

public import CFSG.Sporadic.HNOddCore.ThreeInvolBase

public import CFSG.Sporadic.HNOddCore.InvRow2
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.RkCheckInputs
public meta import CFSG.Sporadic.HNSchreier.RankCheck
public meta import CFSG.Sporadic.HNOddCore.RankData
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem range_g4 :
    Set.range (fun s : Fin s4J.size => g4 s) = Set.range c4W ∪ {x4J} := by
  ext y
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, rfl⟩
    by_cases h : (s : ℕ) < 9
    · exact Or.inl ⟨⟨s, h⟩, (ite_eq_left h).symm⟩
    · exact Or.inr (ite_eq_right h)
  · rintro (⟨j, rfl⟩ | rfl)
    · exact ⟨⟨j, by rw [s4J_size]; omega⟩, ite_eq_left j.2⟩
    · exact ⟨⟨9, by rw [s4J_size]; omega⟩, ite_eq_right (by norm_num)⟩

theorem range_g6 :
    Set.range (fun s : Fin InvData.s6Perms.size => g6 s) =
    Set.range c6W ∪ {e6J 1, e6J 2} := by
  ext y
  simp only [Set.mem_range, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, rfl⟩
    have hs : (s : ℕ) < 12 := by rw [← row6_parts.2.2.2.2.1]; exact s.2
    by_cases h : (s : ℕ) < 10
    · exact Or.inl ⟨⟨s, h⟩, (ite_eq_left h).symm⟩
    · refine Or.inr ?_
      have e : g6 s = e6J (s - 9) := ite_eq_right h
      rw [e]
      rcases (show (s : ℕ) = 10 ∨ (s : ℕ) = 11 by omega) with h10 | h11
      · exact Or.inl (by rw [h10])
      · exact Or.inr (by rw [h11])
  · rintro (⟨j, rfl⟩ | rfl | rfl)
    · exact ⟨⟨j, by rw [row6_parts.2.2.2.2.1]; omega⟩, ite_eq_left j.2⟩
    · exact ⟨⟨10, by rw [row6_parts.2.2.2.2.1]; omega⟩, ite_eq_right (by norm_num)⟩
    · exact ⟨⟨11, by rw [row6_parts.2.2.2.2.1]; omega⟩, ite_eq_right (by norm_num)⟩

theorem ctuc_hn_three_involution_centralizers_exact :
    Nat.card {x : X // t1R • x = x} = 1156 ∧ CJ t1R ≤ HJ ∧
    Nonempty (CJ t1R ≃* Perm (Fin 10)) ∧ Nat.card (CJ t1R) = 3628800 ∧
    (∃ y₁ y₂ : X, {x : X | t1R • x = x} = MulAction.orbit (CJ t1R) x0 ∪
        MulAction.orbit (CJ t1R) y₁ ∪ MulAction.orbit (CJ t1R) y₂ ∧
      (MulAction.orbit (CJ t1R) x0).ncard = 1 ∧ (MulAction.orbit (CJ t1R) y₁).ncard = 210 ∧
      (MulAction.orbit (CJ t1R) y₂).ncard = 945) ∧
    Subgroup.centralizer {t1R} = (CJ t1R).map jR ⊔ Subgroup.zpowers t1R ∧
    (CJ t1R).map jR ⊓ Subgroup.zpowers t1R = ⊥ ∧
    (∀ r ∈ Subgroup.centralizer {t1R}, r * t1R = t1R * r) ∧
    Nat.card {x : X // jR t4J • x = x} = 800 ∧
    (∀ j, c4W j ∈ HJ) ∧ Subgroup.centralizer {t4J} = Subgroup.closure (Set.range c4W ∪ {x4J}) ∧
    (∀ x : X, jR t4J • x = x → ∃ g ∈ Subgroup.centralizer {t4J}, g • x0 = x) ∧
    Nat.card (Subgroup.centralizer {t4J}) = 3686400 ∧
    Subgroup.centralizer {jR t4J} = (Subgroup.centralizer {t4J}).map jR ⊔ Subgroup.zpowers cR ∧
    Nat.card (Subgroup.centralizer {jR t4J}) = 7372800 ∧
    Nat.card {x : X // jR t6J • x = x} = 8800 ∧
    (∀ j, c6W j ∈ HJ) ∧
    Subgroup.centralizer {t6J} = Subgroup.closure (Set.range c6W ∪ {e6J 1, e6J 2}) ∧
    Nat.card (Subgroup.centralizer {t6J}) = 177408000 ∧
    (∃ y : X, {x : X | jR t6J • x = x} = MulAction.orbit (Subgroup.centralizer {t6J}) x0 ∪
        MulAction.orbit (Subgroup.centralizer {t6J}) y ∧
      (MulAction.orbit (Subgroup.centralizer {t6J}) x0).ncard = 7700 ∧
      (MulAction.orbit (Subgroup.centralizer {t6J}) y).ncard = 1100) ∧
    Nat.card {x : X // jR t2J • x = x} = 8800 ∧
    (matJ t2J - 1).rank = 56 ∧ (matJ t6J - 1).rank = 56 ∧ (matJ t4J - 1).rank = 64 ∧
    {x : X | jR t2J • x = x ∧ ∀ g ∈ A8J, g • x = x} = {x0} := by
  rw [t1R_eq]
  obtain ⟨hcov, h0, h1, h2⟩ := orbits_CJc
  obtain ⟨hC, hinf, hcen⟩ := centralizer_cR_eq
  refine ⟨card_fix_t1, CJc_le_HJ, ⟨cjcEquiv⟩, card_CJc,
    ⟨b1 2 (by norm_num), b1 1 (by norm_num), ?_, h0, h2, h1⟩, hC, hinf, hcen, card_fix_t4,
    fun j => hWordJ_mem _, ?_, ?_, card_CJ_t4, CR_t4_eq, card_CR_t4, card_fix_t6,
    fun j => hWordJ_mem _, ?_, card_CJ_t6, ?_, card_fix_t2, rank_t2, rank_t6, rank_t4, fix_t2_A8⟩
  · rw [hcov, Set.union_right_comm]
  · rw [← CJ_t4_eq, ← range_g4]
  · intro x hx
    have hx' : x ∈ MulAction.orbit S4 x0 := by rw [orbit_S4]; exact hx
    obtain ⟨⟨g, hg⟩, rfl⟩ := hx'
    exact ⟨g, S4_le hg, rfl⟩
  · rw [← CJ_t6_eq, ← range_g6]
  · refine ⟨b6 1 (by norm_num), ?_, ?_, ?_⟩
    · rw [← CJ_t6_eq, ← b6_zero]
      exact fix_t6_eq
    · rw [← CJ_t6_eq]
      exact orbit6_ncard_x0
    · rw [← CJ_t6_eq, orbit6_ncard]
      rfl

end CFSG.Sporadic.HNOddCore
