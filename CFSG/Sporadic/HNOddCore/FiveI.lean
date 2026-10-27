module

public import CFSG.Sporadic.HNOddCore.FiveH
public import CFSG.Sporadic.HNOddCore.SylA
public import Certificates.Certificate2085
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate16041
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv Equiv.Perm

theorem fiber_parts : a6Sm.size = 4 ∧
    (∀ k < 4, (a6Sm[k]!).size = 50 ∧ (a6Sm[k]!)[17]! = 17 ∧
      ∀ x ∈ FAData.fiber, (a6Sm[k]!)[x]! ∈ FAData.fiber) ∧
    FAData.fiber = ((List.range 50).filter fun i => orb42.contains i &&
      (FAData.gamma[i]!).contains 17) := by
  have h := five_small_parts.2.2.2.2.2.2.1
  unfold fiberOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun k hk => ?_, h3⟩
  have := allBelowN_spec h2 hk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem pairs_parts :
    FiveData.pairWords.size = 30 ∧ FiveData.fiberPairs.length = 30 ∧
    (∀ p < 30, (∀ l ∈ FiveData.pairWords[p]!, 0 < l ∧ l ≤ 4) ∧
      (evalPos a6Sm FiveData.pairWords[p]! 10, evalPos a6Sm FiveData.pairWords[p]! 13) =
        FiveData.fiberPairs[p]!) ∧
    FiveData.fiberPairs = (FAData.fiber.flatMap fun x =>
      (FAData.fiber.filter (· != x)).map fun y => (x, y)) := by
  have h := five_small_parts.2.2.2.2.2.2.2
  unfold pairsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun p hp => ?_, h4⟩
  have := allBelowN_spec h3 hp
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at this
  exact this

theorem a6Gen_mem_AH
    {k : ℕ} (hk : k < 4) : (⟨a6Gen k, hWordJ_mem _⟩ : HJ) ∈ AH := by
  obtain ⟨hlet, hfix⟩ := a6_parts.2 k hk
  show thetaJ ⟨a6Gen k, hWordJ_mem _⟩ ∈ alt5
  rw [mem_alt5]
  intro i hi
  have e : (thetaJ ⟨a6Gen k, hWordJ_mem _⟩ : Perm (Fin 12)) = natWord FAData.a6Words[k]! :=
    thetaJ_hWord _
  rw [e]
  apply Fin.ext
  rw [← (prep_natWord hlet) i]
  have h2 := hfix i (by omega)
  rw [natImgs, map_getElem! _ _ (by rw [a6_parts.1]; exact hk)] at h2
  exact h2

theorem a6Gen_mem_AJ
    {k : ℕ} (hk : k < 4) : a6Gen k ∈ AJ := ⟨_, a6Gen_mem_AH hk, rfl⟩

theorem a6_act
    {k : ℕ} (hk : k < 4) (x : Fin 50) :
    ∃ h : (a6Sm[k]!)[(x : ℕ)]! < 50, a6Gen k • omPt x = omPt ⟨(a6Sm[k]!)[(x : ℕ)]!, h⟩ := by
  obtain ⟨h, he⟩ := hactA6 k (by rw [fiber_parts.1]; exact hk) ⟨x, by rw [fFixed_size]; exact x.2⟩
  exact ⟨h.trans_eq fFixed_size, he⟩

theorem a6Gen_fix17
    {k : ℕ} (hk : k < 4) : a6Gen k • omPt 17 = omPt 17 := by
  obtain ⟨h, he⟩ := a6_act hk 17
  rw [he]
  congr 1
  exact Fin.ext (fiber_parts.2.1 k hk).2.1

abbrev KF : Subgroup JH := Subgroup.closure (Set.range fun k : Fin 4 => a6Gen k)

theorem KF_le_AJ :
    KF ≤ AJ := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact a6Gen_mem_AJ k.2

theorem KF_fix17
    {g : JH} (hg : g ∈ KF) : g • omPt 17 = omPt 17 := by
  have hle : KF ≤ MulAction.stabilizer JH (omPt 17) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact a6Gen_fix17 k.2
  exact hle hg

abbrev fiber17 :
    Set (Fin 50) := {v | omPt v ∈ orbit42 ∧ gammaAdj v 17}

theorem mem_fiber17_iff
    (v : Fin 50) : v ∈ fiber17 ↔ (v : ℕ) ∈ FAData.fiber := by
  rw [fiber_parts.2.2, List.mem_filter, Bool.and_eq_true]
  simp only [List.mem_range, v.2, true_and, List.contains_iff_mem]
  rw [Set.mem_ofPred_eq, mem_orbit42_iff]
  rfl

abbrev fiberPts :
    Set X := omPt '' fiber17

theorem a6Gen_fiber
    {k : ℕ} (hk : k < 4) : ∀ p ∈ fiberPts, a6Gen k • p ∈ fiberPts := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨h, he⟩ := a6_act hk v
  rw [he]
  refine ⟨_, ?_, rfl⟩
  rw [mem_fiber17_iff] at hv ⊢
  exact (fiber_parts.2.1 k hk).2.2 _ hv

theorem KF_fiber
    {g : JH} (hg : g ∈ KF) : ∀ p ∈ fiberPts, g • p ∈ fiberPts := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨k, rfl⟩ := hg
    exact a6Gen_fiber k.2
  | one => intro p hp; rwa [one_smul]
  | mul a b _ _ ha hb => intro p hp; rw [mul_smul]; exact ha _ (hb p hp)
  | inv a _ ha => exact smul_preimage_of_image ha

theorem word_act :
    ∀ w : List ℤ, (∀ l ∈ w, 0 < l ∧ l ≤ 4) → ∀ x : Fin 50,
    ∃ h : evalPos a6Sm w x < 50, wordVal a6Gen w • omPt x = omPt ⟨evalPos a6Sm w x, h⟩
  | [], _, x => ⟨x.2, by rw [wordVal_nil, one_smul]; rfl⟩
  | l :: w, hw, x => by
    obtain ⟨h1, he⟩ := word_act w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) x
    have hl := hw l (List.mem_cons_self ..)
    have hk : l.toNat - 1 < 4 := by omega
    have e1 : (if 0 < l then a6Gen (l.natAbs - 1) else (a6Gen (l.natAbs - 1))⁻¹) =
        a6Gen (l.toNat - 1) := by
      rw [ite_eq_left hl.1, show l.natAbs - 1 = l.toNat - 1 by omega]
    obtain ⟨h2, he2⟩ := a6_act hk ⟨evalPos a6Sm w x, h1⟩
    rw [wordVal_cons, e1, mul_smul, he, he2]
    exact ⟨h2, rfl⟩

theorem wordVal_mem_KF (w : List ℤ) (hw : ∀ l ∈ w, 0 < l ∧ l ≤ 4) : wordVal a6Gen w ∈ KF := by
  have hK : ∀ h < 4, a6Gen h ∈ KF := fun h hh => Subgroup.subset_closure ⟨⟨h, hh⟩, rfl⟩
  refine wordVal_mem hK w ?_
  simp only [plettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq]
  intro l hl
  have := hw l hl
  omega

theorem fiberPairs_mem
    {x y : ℕ} (hx : x ∈ FAData.fiber) (hy : y ∈ FAData.fiber) (hxy : x ≠ y) :
    (x, y) ∈ FiveData.fiberPairs := by
  rw [pairs_parts.2.2.2, List.mem_flatMap]
  refine ⟨x, hx, List.mem_map.2 ⟨y, List.mem_filter.2 ⟨hy, ?_⟩, rfl⟩⟩
  simpa using hxy.symm

theorem exists_pair_elt
    {x y : Fin 50} (hx : x ∈ fiber17) (hy : y ∈ fiber17) (hxy : x ≠ y) :
    ∃ g ∈ KF, g • omPt 10 = omPt x ∧ g • omPt 13 = omPt y := by
  rw [mem_fiber17_iff] at hx hy
  obtain ⟨p, hp, hpe⟩ := List.getElem_of_mem
    (fiberPairs_mem hx hy (fun h => hxy (Fin.ext h)))
  have hp30 : p < 30 := by rw [← pairs_parts.2.1]; exact hp
  obtain ⟨hw, hev⟩ := pairs_parts.2.2.1 p hp30
  rw [getElem!_pos FiveData.fiberPairs p hp, hpe, Prod.mk.injEq] at hev
  refine ⟨wordVal a6Gen FiveData.pairWords[p]!, wordVal_mem_KF _ hw, ?_, ?_⟩
  · obtain ⟨h1, he⟩ := word_act _ hw 10
    rw [he]
    exact congrArg omPt (Fin.ext hev.1)
  · obtain ⟨h1, he⟩ := word_act _ hw 13
    rw [he]
    exact congrArg omPt (Fin.ext hev.2)

theorem KF_two_transitive
    {x y x' y' : Fin 50} (hx : x ∈ fiber17) (hy : y ∈ fiber17)
    (hx' : x' ∈ fiber17) (hy' : y' ∈ fiber17) (hxy : x ≠ y) (hxy' : x' ≠ y') :
    ∃ g ∈ KF, g • omPt x = omPt x' ∧ g • omPt y = omPt y' := by
  obtain ⟨g, hg, hg1, hg2⟩ := exists_pair_elt hx hy hxy
  obtain ⟨g', hg', hg1', hg2'⟩ := exists_pair_elt hx' hy' hxy'
  refine ⟨g' * g⁻¹, KF.mul_mem hg' (KF.inv_mem hg), ?_, ?_⟩
  · rw [mul_smul, ← hg1, inv_smul_smul, hg1']
  · rw [mul_smul, ← hg2, inv_smul_smul, hg2']

end CFSG.Sporadic.HNOddCore
