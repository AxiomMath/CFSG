module

public import CFSG.Sporadic.HNOddCore.FiveG
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

theorem labels_parts : labPos.size = 7 ∧ labPos.toList.Nodup ∧
    (∀ i < 7, orb7.contains labPos[i]! = true) ∧ labLet = #[5, 6, 7, 8, 9, 10, 11] ∧
    ∀ k < 5, ∀ i < 7, labPos.contains (aSm[k]!)[labPos[i]!]! = true ∧
      labLet[labPos.idxOf (aSm[k]!)[labPos[i]!]!]! =
        ((natImgs natStrongArr FAData.aWords)[k]!)[labLet[i]!]! := by
  have h := five_small_parts.2.2.2.2.1
  unfold labelsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun i hi => allBelowN_spec h3 hi, h4, fun k hk i hi => ?_⟩
  have := allBelowN_spec (allBelowN_spec h5 hk) hi
  simpa only [Bool.and_eq_true, beq_iff_eq] using this

theorem orb7_pts : PtList 50 orb7 :=
  ptList_of_pointsOK (orbitCertOK_spec (by
    have h := aOrbit_parts.2.2.2.2.2.1
    exact h)).2.1

theorem orb7_lt {j : ℕ} (h : orb7.contains j = true) : j < 50 := by
  rw [Array.contains_iff_mem, Array.mem_iff_getElem] at h
  obtain ⟨k, hk, rfl⟩ := h
  rw [← getElem!_pos orb7 k hk]
  exact orb7_pts.lt k hk

theorem labPos_lt
    {i : ℕ} (hi : i < 7) : labPos[i]! < 50 := orb7_lt (labels_parts.2.2.1 i hi)

theorem orb7_nodup : orb7.toList.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro a b h
  have ha := a.2
  have hb := b.2
  simp only [Array.length_toList] at ha hb
  have e : orb7[(a : ℕ)]! = orb7[(b : ℕ)]! := by
    rw [getElem!_pos orb7 (a : ℕ) ha, getElem!_pos orb7 (b : ℕ) hb]
    simpa using h
  exact Fin.ext (orb7_pts.inj a ha b hb e)

theorem orb7_iff_labPos
    (j : ℕ) : orb7.contains j = true ↔ labPos.contains j = true := by
  have hsub : labPos.toList.toFinset ⊆ orb7.toList.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi7 : i < 7 := by simpa [labels_parts.1] using hi
    have := labels_parts.2.2.1 i hi7
    rw [Array.contains_iff_mem] at this
    simpa [getElem!_pos labPos i (by rw [labels_parts.1]; exact hi7)] using this
  have heq : labPos.toList.toFinset = orb7.toList.toFinset := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [List.toFinset_card_of_nodup orb7_nodup, List.toFinset_card_of_nodup labels_parts.2.1]
    simp [labels_parts.1, aOrbit_parts.2.2.2.2.2.2.1]
  rw [Array.contains_iff_mem, Array.contains_iff_mem, ← Array.mem_toList_iff,
    ← Array.mem_toList_iff, ← List.mem_toFinset, ← List.mem_toFinset, heq]

@[expose] def labP
    (i : Fin 7) : Fin 50 := ⟨labPos[(i : ℕ)]!, labPos_lt i.2⟩

theorem labP_injective : Function.Injective labP := by
  intro a b h
  have e : labPos[(a : ℕ)]! = labPos[(b : ℕ)]! := congrArg Fin.val h
  have ha : (a : ℕ) < labPos.toList.length := by simp [labels_parts.1]
  have hb : (b : ℕ) < labPos.toList.length := by simp [labels_parts.1]
  rw [getElem!_pos labPos (a : ℕ) (by rw [labels_parts.1]; exact a.2),
    getElem!_pos labPos (b : ℕ) (by rw [labels_parts.1]; exact b.2)] at e
  have := (List.Nodup.getElem_inj_iff labels_parts.2.1 (i := a) (j := b) (hi := ha)
    (hj := hb)).1 (by simpa using e)
  exact Fin.ext this

theorem mem_orbit7_iff'
    (j : Fin 50) : omPt j ∈ orbit7 ↔ ∃ i : Fin 7, labP i = j := by
  rw [mem_orbit7_iff, orb7_iff_labPos, Array.contains_iff_mem, Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, hie⟩
    refine ⟨⟨i, by rw [← labels_parts.1]; exact hi⟩, Fin.ext ?_⟩
    show labPos[i]! = (j : ℕ)
    rw [getElem!_pos labPos i hi]
    exact hie
  · rintro ⟨i, rfl⟩
    refine ⟨i, by rw [labels_parts.1]; exact i.2, ?_⟩
    exact (getElem!_pos labPos (i : ℕ) (by rw [labels_parts.1]; exact i.2)).symm

theorem arr_getElem_idxOf {xs : Array ℕ} {a : ℕ} (h : xs.contains a = true) :
    xs.idxOf a < xs.size ∧ xs[xs.idxOf a]! = a := by
  rw [Array.contains_iff_mem] at h
  have hlt := Array.idxOf_lt_length_of_mem h
  refine ⟨hlt, ?_⟩
  rw [getElem!_pos xs (xs.idxOf a) hlt]
  rcases xs with ⟨l⟩
  have hl : a ∈ l := by simpa using h
  simp [List.getElem_idxOf]

theorem labLet_get (i : Fin 7) : labLet[(i : ℕ)]! = 5 + i := by
  rw [labels_parts.2.2.2.1]
  fin_cases i <;> rfl

@[expose] def let5 (i : Fin 7) : Fin 12 := ⟨5 + i, by omega⟩

theorem gen_label
    {k : ℕ} (hk : k < 5) (i : Fin 7) : ∃ j : Fin 7,
    aGenJ k • omPt (labP i) = omPt (labP j) ∧
      (thetaJ ⟨aGenJ k, aGenJ_mem k⟩ : Perm (Fin 12)) (let5 i) = let5 j := by
  obtain ⟨hc, hl⟩ := labels_parts.2.2.2.2 k hk i i.2
  obtain ⟨hjlt, hje⟩ := arr_getElem_idxOf hc
  set j : Fin 7 := ⟨labPos.idxOf (aSm[k]!)[labPos[(i : ℕ)]!]!, by
    have := labels_parts.1; omega⟩ with hj
  refine ⟨j, ?_, ?_⟩
  · obtain ⟨h50, he⟩ := hactA k (by rw [aOrbit_parts.1]; exact hk)
      ⟨labPos[(i : ℕ)]!, by rw [fFixed_size]; exact labPos_lt i.2⟩
    refine he.trans (congrArg omList.pt (Fin.ext ?_))
    show (aSm[k]!)[labPos[(i : ℕ)]!]! = labPos[(j : ℕ)]!
    rw [hje]
  · apply Fin.ext
    have e1 := (prep_natWord (aWords_letters hk)) (let5 i)
    have e2 : (thetaJ ⟨aGenJ k, aGenJ_mem k⟩ : Perm (Fin 12)) = natWord FAData.aWords[k]! :=
      thetaJ_hWord _
    rw [e2, ← e1]
    show (pword 12 natStrongArr (pinvs 12 natStrongArr) FAData.aWords[k]!)[5 + (i : ℕ)]! =
      5 + (j : ℕ)
    rw [← labLet_get i, ← labLet_get j]
    rw [natImgs, map_getElem! _ _ (by rw [aWords_size]; exact hk)] at hl
    exact hl.symm

@[expose] def LabelEquiv
    (h : HJ) : Prop :=
  ∀ i j : Fin 7, (thetaJ h : Perm (Fin 12)) (let5 i) = let5 j →
    (h : JH) • omPt (labP i) = omPt (labP j)

theorem let5_injective : Function.Injective let5 := fun a b h =>
  Fin.ext (by have := congrArg Fin.val h; simp [let5] at this; omega)

theorem exists_let5_of_AH
    {h : HJ} (hh : h ∈ AH) (i : Fin 7) :
    ∃ j : Fin 7, (thetaJ h : Perm (Fin 12)) (let5 i) = let5 j := by
  have hfix := (mem_alt5 _).1 hh
  set y := (thetaJ h : Perm (Fin 12)) (let5 i) with hy
  have hy5 : 5 ≤ (y : ℕ) := by
    by_contra hlt
    push Not at hlt
    have hfy : (thetaJ h : Perm (Fin 12)) y = y := hfix y hlt
    have e : (thetaJ h : Perm (Fin 12)) y = (thetaJ h : Perm (Fin 12)) (let5 i) := by
      rw [hfy, hy]
    have := congrArg Fin.val ((thetaJ h : Perm (Fin 12)).injective e)
    simp [let5] at this
    omega
  exact ⟨⟨y - 5, by omega⟩, Fin.ext (by simp [let5]; omega)⟩

theorem labelEquiv_mul
    {a b : HJ} (hb : b ∈ AH) (ha' : LabelEquiv a) (hb' : LabelEquiv b) :
    LabelEquiv (a * b) := by
  intro i j hij
  obtain ⟨m, hm⟩ := exists_let5_of_AH hb i
  rw [map_mul, Subgroup.coe_mul, Perm.mul_apply, hm] at hij
  rw [Subgroup.coe_mul, mul_smul, hb' i m hm, ha' m j hij]

theorem labelEquiv_inv
    {a : HJ} (ha' : LabelEquiv a) : LabelEquiv a⁻¹ := by
  intro i j hij
  have e : (thetaJ a : Perm (Fin 12)) (let5 j) = let5 i := by
    rw [← hij, map_inv, Subgroup.coe_inv, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
  rw [Subgroup.coe_inv, inv_smul_eq_iff, ha' j i e]

theorem labelEquiv_one :
    LabelEquiv 1 := by
  intro i j hij
  rw [map_one, Subgroup.coe_one, Perm.one_apply] at hij
  rw [let5_injective hij, Subgroup.coe_one, one_smul]

theorem labelEquiv_AH
    (h : AH) : LabelEquiv h := by
  have key : ∀ x ∈ B5, x ∈ AH ∧ LabelEquiv x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨aGenJ_mem_AH k.2, fun i j hij => ?_⟩
      obtain ⟨j', hj1, hj2⟩ := gen_label k.2 i
      rw [hj2] at hij
      rw [← let5_injective hij]
      exact hj1
    | one => exact ⟨AH.one_mem, labelEquiv_one⟩
    | mul a b _ _ ha hb => exact ⟨AH.mul_mem ha.1 hb.1, labelEquiv_mul hb.1 ha.2 hb.2⟩
    | inv a _ ha => exact ⟨AH.inv_mem ha.1, labelEquiv_inv ha.2⟩
  exact (key h (by rw [B5_eq]; exact h.2)).2

end CFSG.Sporadic.HNOddCore
