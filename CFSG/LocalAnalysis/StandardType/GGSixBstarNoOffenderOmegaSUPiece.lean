module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockFour
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaMono

public section

namespace CFSG.StandardType

namespace NoOffOm

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB

section PieceSet

open Classical

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

structure IsPieceSet (h : UnitaryFieldData 2 f K) (A : Subgroup ↥(unitarySU 2 f K n))
    (S : Finset ↥(unitarySU 2 f K n)) : Prop where
  mem : ∀ y ∈ S, y ∈ A
  ne_one : ∀ y ∈ S, y ≠ 1
  orth : ∀ y ∈ S, ∀ y' ∈ S, y ≠ y' → ∀ u ∈ rng y, ∀ v ∈ rng y', stdHermForm h n u v = 0
  cyc : ∀ y ∈ S, ∀ c ∈ A, ∃ k : ℕ, ∀ u ∈ rng y, lin c u = lin (y ^ k) u

noncomputable abbrev pieceSpan (S : Finset ↥(unitarySU 2 f K n)) : Submodule K (Fin n → K) :=
  ⨆ y ∈ S, rng y

theorem IsPieceSet.mono {S S' : Finset ↥(unitarySU 2 f K n)} (hS : IsPieceSet h A S)
    (hS' : S' ⊆ S) : IsPieceSet h A S' where
  mem y hy := hS.mem y (hS' hy)
  ne_one y hy := hS.ne_one y (hS' hy)
  orth y hy y' hy' := hS.orth y (hS' hy) y' (hS' hy')
  cyc y hy := hS.cyc y (hS' hy)

theorem rng_ne_bot {y : ↥(unitarySU 2 f K n)} (hy : y ≠ 1) : rng y ≠ ⊥ := by
  intro h0
  apply hy
  apply lin_injective
  rw [lin_one]
  have h1 : lin y - 1 = 0 := LinearMap.range_eq_bot.mp h0
  exact sub_eq_zero.mp h1

theorem orth_pieceSpan {S : Finset ↥(unitarySU 2 f K n)} {y : ↥(unitarySU 2 f K n)}
    (hS : IsPieceSet h A (insert y S)) (hyS : y ∉ S) :
    ∀ u ∈ rng y, ∀ v ∈ pieceSpan S, stdHermForm h n u v = 0 ∧ stdHermForm h n v u = 0 := by
  intro u hu v hv
  have hle : pieceSpan S ≤ LinearMap.ker (stdHermForm h n u) := by
    refine iSup₂_le fun y' hy' => ?_
    intro w hw
    exact hS.orth y (Finset.mem_insert_self y S) y' (Finset.mem_insert_of_mem hy')
      (fun e => hyS (e ▸ hy')) u hu w hw
  have h1 : stdHermForm h n u v = 0 := hle hv
  refine ⟨h1, ?_⟩
  rw [← (stdHermForm_isSymm h n).eq u v, h1, map_zero]

theorem IsPieceSet.nondegOn_card [FiniteDimensional K (Fin n → K)] (hA : MaxElemAb p A)
    {S : Finset ↥(unitarySU 2 f K n)} (hS : IsPieceSet h A S) :
    NondegOn (stdHermForm h n) (pieceSpan S) ∧ S.card ≤ finrank K (pieceSpan S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨?_, by simp⟩
    have : pieceSpan (∅ : Finset ↥(unitarySU 2 f K n)) = ⊥ := by simp
    rw [this]
    exact nondegOn_bot h
  | insert y S hyS ih =>
    obtain ⟨hX, hcard⟩ := ih (hS.mono (Finset.subset_insert y S))
    have hsp : pieceSpan (insert y S) = pieceSpan S ⊔ rng y := by
      rw [pieceSpan, Finset.iSup_insert, sup_comm]
    have hyA : y ∈ A := hS.mem y (Finset.mem_insert_self y S)
    have hU : NondegOn (stdHermForm h n) (rng y) := nondegOn_rng hA hyA
    have horth := orth_pieceSpan hS hyS
    have hX' : NondegOn (stdHermForm h n) (pieceSpan S ⊔ rng y) :=
      SUTB.nondegOn_sup hX hU horth
    rw [hsp]
    refine ⟨hX', ?_⟩
    have hinf : pieceSpan S ⊓ rng y = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun v hv => hX v hv.1 fun m hm => ?_
      exact (horth v hv.2 m hm).2
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq (pieceSpan S) (rng y)
    rw [hinf, finrank_bot, add_zero] at hfr
    have hpos : 0 < finrank K (rng y) := by
      rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      exact rng_ne_bot (hS.ne_one y (Finset.mem_insert_self y S))
    rw [Finset.card_insert_of_notMem hyS, hfr]
    omega

theorem IsPieceSet.exists_insert [FiniteDimensional K (Fin n → K)] (hA : MaxElemAb p A)
    {S : Finset ↥(unitarySU 2 f K n)} (hS : IsPieceSet h A S)
    (hne : ∃ c ∈ A, c ≠ 1 ∧ ∀ v ∈ pieceSpan S, lin c v = v) :
    ∃ y, y ∉ S ∧ IsPieceSet h A (insert y S) := by
  classical
  obtain ⟨y, hy⟩ := exists_isPiece (h := h) hA hne
  have hyS : y ∉ S := by
    intro hyS
    apply rng_ne_bot hy.ne_one
    refine (Submodule.eq_bot_iff _).mpr fun u hu => ?_
    have hle : rng y ≤ pieceSpan S := le_iSup₂ (f := fun y _ => rng y) y hyS
    exact eq_zero_of_mem_rng h hA hy.mem hu (hy.triv u (hle hu))
  have horth := rng_orth_of_triv (h := h) hy.triv
  have hle : ∀ y' ∈ S, rng y' ≤ pieceSpan S := fun y' hy' =>
    le_iSup₂ (f := fun y _ => rng y) y' hy'
  refine ⟨y, hyS, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro y' hy'
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · exact hy.mem
    · exact hS.mem y' hy'
  · intro y' hy'
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · exact hy.ne_one
    · exact hS.ne_one y' hy'
  · intro y₁ hy₁ y₂ hy₂ hne₁₂ u hu v hv
    rcases Finset.mem_insert.mp hy₁ with rfl | h₁ <;>
      rcases Finset.mem_insert.mp hy₂ with rfl | h₂
    · exact absurd rfl hne₁₂
    · exact (horth u hu v (hle y₂ h₂ hv)).1
    · exact (horth v hv u (hle y₁ h₁ hu)).2
    · exact hS.orth y₁ h₁ y₂ h₂ hne₁₂ u hu v hv
  · intro y' hy'
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · exact hy.cyc
    · exact hS.cyc y' hy'

theorem exists_terminal_pieceSet [FiniteDimensional K (Fin n → K)] (hA : MaxElemAb p A) :
    ∃ S, IsPieceSet h A S ∧ ∀ c ∈ A, (∀ v ∈ pieceSpan S, lin c v = v) → c = 1 := by
  classical
  set P : ℕ → Prop := fun k => ∃ S, IsPieceSet h A S ∧ S.card = k with hP
  have hP0 : P 0 := ⟨∅, ⟨by simp, by simp, by simp, by simp⟩, rfl⟩
  have hbound : ∀ k, P k → k ≤ n := by
    rintro k ⟨S, hS, rfl⟩
    have h1 := (hS.nondegOn_card hA).2
    have h2 := Submodule.finrank_le (pieceSpan S)
    rw [Module.finrank_fin_fun] at h2
    omega
  set m := Nat.findGreatest P n with hm
  obtain ⟨S, hS, hSm⟩ : P m := Nat.findGreatest_spec (Nat.zero_le n) hP0
  refine ⟨S, hS, fun c hc htriv => ?_⟩
  by_contra hc1
  obtain ⟨y, hyS, hyS'⟩ := hS.exists_insert hA ⟨c, hc, hc1, htriv⟩
  have hPm : P (m + 1) := ⟨_, hyS', by rw [Finset.card_insert_of_notMem hyS, hSm]⟩
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self m) (hbound _ hPm) hPm

end PieceSet

end NoOffOm

end CFSG.StandardType
