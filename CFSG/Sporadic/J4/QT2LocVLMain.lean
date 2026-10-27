module

public import CFSG.Sporadic.J4.QT2LocVLCheck
public import CFSG.Sporadic.J4.QT2LocX0MainBase
public import CFSG.Sporadic.J4.QTRankProof

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A Matrix
open scoped Classical

structure XfV (V : Subgroup J) : Prop where
  hVH : V ≤ Hj
  hVcard : Nat.card V = 16
  hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  hV2 : ∀ a ∈ V, a * a = 1
  hVx : ∀ v ∈ V, fiveElt * v * fiveElt⁻¹ ∈ V
  hfpf : ∀ v ∈ V, fiveElt * v = v * fiveElt → v = 1

theorem XfV.exists_ne_one {V : Subgroup J} (hV : XfV V) : ∃ v ∈ V, v ≠ 1 := by
  by_contra hcon
  have hbot : V = ⊥ := (Subgroup.eq_bot_iff_forall V).2 fun v hv => by
    by_contra hne
    exact hcon ⟨v, hv, hne⟩
  have h16 := hV.hVcard
  rw [hbot] at h16
  simp at h16

theorem Acts_vlLift
    (hM : MatFacts) {y : List ℕ} (hy : y ∈ vlTables) :
    Acts (el5 (vlLiftWord y)) y ∧ el5 (vlLiftWord y) ∈ Hj := by
  have h := chkVlLifts_true
  unfold chkVlLifts at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨-, hall⟩ := h
  obtain ⟨hl, hw⟩ := hall y hy
  have hl' : ∀ ℓ ∈ vlLiftWord y, ℓ ∈ letters := by
    intro ℓ hℓ
    simpa [List.contains_iff_mem] using hl ℓ hℓ
  have hA := Acts_wordProd hM (vlLiftWord y) hl'
  rw [hw] at hA
  have e : el5 (vlLiftWord y) = wordProd xJ (vlLiftWord y) := wordProd_gen5_xJ _ hl'
  rw [e]
  exact ⟨hA, wordProd_mem_Hj hl'⟩

theorem vlGroups_cover {p : List Nat × Nat} (hp : p ∈ vlPairs) :
    vlDistinct (vlGroupOf (vlT p)) = true ∧
      ∃ G ∈ vlGroups, ∀ M ∈ vlGroupOf (vlT p), ∃ M' ∈ G, eqRows M M' = true := by
  have h := chkVlGroups_true
  unfold chkVlGroups at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨-, hall⟩ := h
  obtain ⟨hd, G, hG, hsub⟩ := hall p hp
  refine ⟨hd, G, hG, fun M hM => ?_⟩
  have := hsub M hM
  simpa using this

end CFSG.Sporadic.J4.QT2
