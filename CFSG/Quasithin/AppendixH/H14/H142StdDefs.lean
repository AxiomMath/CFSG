module

public import CFSG.Quasithin.AppendixH.H14.H142Bfs

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open scoped Pointwise

@[expose] def stdB : Finset (Fin 24) := {8, 11, 14, 20}

@[expose] def stdB' : Finset (Fin 24) := {13, 17, 18, 23}

@[expose] def stdO : Finset (Fin 24) := stdB ∪ stdB'

@[expose] def stdS : Finset (Finset (Fin 24)) :=
  {{0, 1, 12, 21}, {2, 6, 9, 16}, {3, 4, 10, 19}, {5, 7, 15, 22}, stdB, stdB'}

@[expose] def stdQ : Finset (Finset (Fin 24)) := stdS.erase stdB

@[expose] def stdH : Finset (Fin 24) := stdO.erase 8

@[expose] def qMasks : List ℕ := [2101251, 66116, 525336, 4227232, 8790016]

@[expose] def stdMasks : List ℕ := [2101251, 66116, 525336, 4227232, 1067264, 8790016]

theorem stdB_eq : stdB = maskSetOf 1067264 := by
  decide

theorem stdO_eq : stdO = maskSetOf 9857280 := by
  decide

theorem stdQ_eq : stdQ = (qMasks.map maskSetOf).toFinset := by
  decide

theorem maskSetOf_or (m m' : ℕ) :
    maskSetOf (m ||| m') = maskSetOf m ∪ maskSetOf m' := by
  ext i
  rw [mem_maskSetOf, Finset.mem_union, mem_maskSetOf, mem_maskSetOf, Nat.testBit_or,
    Bool.or_eq_true]

theorem eY_maskSetOf (m : ℕ) : eY (maskSetOf m) = Multiplicative.ofAdd (bvec 24 m) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_ofAdd, toAdd_eY, mem_maskSetOf, bvec_apply]

theorem isOctad_maskSetOf (m : ℕ) (hc : (maskSetOf m).card = 8) (hs : syndM m = 0) :
    IsOctad (maskSetOf m) := by
  refine ⟨hc, ?_⟩
  rw [eY_maskSetOf]
  exact (mem_golayC_iff' (Multiplicative.ofAdd (bvec 24 m))).2 ((bvec_mem_C_iff m).2 hs)

theorem stdS_eq_stdMasks : stdS = (stdMasks.map maskSetOf).toFinset := by
  decide

theorem syndM_or_stdMasks : ∀ m ∈ stdMasks, ∀ m' ∈ stdMasks, m ≠ m' →
    syndM (m ||| m') = 0 ∧ (maskSetOf (m ||| m')).card = 8 := by
  decide +kernel

theorem stdMasks_card_four : ∀ m ∈ stdMasks, (maskSetOf m).card = 4 := by
  decide +kernel

theorem stdMasks_disjoint : ∀ m ∈ stdMasks, ∀ m' ∈ stdMasks, m ≠ m' →
    Disjoint (maskSetOf m) (maskSetOf m') := by
  decide +kernel

theorem isSextet_stdS : IsSextet stdS := by
  refine ⟨by decide, ?_, ?_, by decide, ?_⟩
  · intro B hB
    rw [stdS_eq_stdMasks, List.mem_toFinset, List.mem_map] at hB
    obtain ⟨m, hm, rfl⟩ := hB
    exact stdMasks_card_four m hm
  · intro B hB B' hB' hne
    rw [stdS_eq_stdMasks, List.mem_toFinset, List.mem_map] at hB hB'
    obtain ⟨m, hm, rfl⟩ := hB
    obtain ⟨m', hm', rfl⟩ := hB'
    exact stdMasks_disjoint m hm m' hm' (fun h => hne (by rw [h]))
  · intro B hB B' hB' hne
    rw [stdS_eq_stdMasks, List.mem_toFinset, List.mem_map] at hB hB'
    obtain ⟨m, hm, rfl⟩ := hB
    obtain ⟨m', hm', rfl⟩ := hB'
    have hmm' : m ≠ m' := fun h => hne (by rw [h])
    obtain ⟨hsynd, hcard⟩ := syndM_or_stdMasks m hm m' hm' hmm'
    rw [← maskSetOf_or]
    exact isOctad_maskSetOf _ hcard hsynd

theorem mem_stdB_iff (x : Fin 24) : x ∈ stdB ↔ ∀ T ∈ stdQ, x ∉ T := by
  have hmem : (∀ T ∈ stdQ, x ∉ T) ↔ x ∉ stdQ.biUnion id := by
    rw [Finset.mem_biUnion]
    exact ⟨fun h ⟨T, hT, hxT⟩ => h T hT hxT, fun h T hT hxT => h ⟨T, hT, hxT⟩⟩
  have hcomp : stdQ.biUnion id = Finset.univ \ stdB := by decide
  rw [hmem, hcomp, Finset.mem_sdiff]
  simp

theorem smul_stdQ_of_arr {g : S24} {a : Array ℕ} (hg : HasArr g a)
    (h : ∀ m ∈ qMasks, permM a m ∈ qMasks) : g • stdQ = stdQ := by
  apply Finset.eq_of_subset_of_card_le
  · intro T hT
    rw [Finset.mem_smul_finset] at hT
    obtain ⟨T₀, hT₀, rfl⟩ := hT
    rw [stdQ_eq, List.mem_toFinset, List.mem_map] at hT₀
    obtain ⟨m, hm, rfl⟩ := hT₀
    rw [smul_maskSetOf hg, stdQ_eq, List.mem_toFinset, List.mem_map]
    exact ⟨permM a m, h m hm, rfl⟩
  · rw [Finset.card_smul_finset]

theorem forall_notMem_smul_finset_iff {g : S24} {s : Finset (Finset (Fin 24))}
    (h : g • s = s) (x : Fin 24) : (∀ T ∈ s, x ∉ g • T) ↔ ∀ T ∈ s, x ∉ T := by
  constructor
  · intro hx T hT
    rw [← h, Finset.mem_smul_finset] at hT
    obtain ⟨T₀, hT₀, rfl⟩ := hT
    exact hx T₀ hT₀
  · intro hx T hT
    exact hx (g • T) (by rw [← h]; exact Finset.smul_mem_smul_finset hT)

theorem smul_stdB_of_stdQ {g : S24} (h : g • stdQ = stdQ) : g • stdB = stdB := by
  ext x
  rw [← Finset.inv_smul_mem_iff, mem_stdB_iff, mem_stdB_iff]
  simp only [Finset.inv_smul_mem_iff]
  exact forall_notMem_smul_finset_iff h x

theorem smul_stdH_of_arr {g : S24} {a : Array ℕ} (hg : HasArr g a) (h8 : a[8]! = 8)
    (ho : permM a 9857280 = 9857280) : g • stdH = stdH := by
  have hg8 : g 8 = 8 := by
    apply Fin.ext
    exact (hg 8).trans h8
  have hstdO : g • stdO = stdO := by
    rw [stdO_eq, smul_maskSetOf hg, ho]
  have herase : g • (stdO.erase 8) = (g • stdO).erase (g 8) := by
    ext y
    simp only [Finset.mem_smul_finset, Finset.mem_erase]
    constructor
    · rintro ⟨x, ⟨hx8, hxO⟩, rfl⟩
      exact ⟨fun h => hx8 (g.injective (by simpa [Equiv.Perm.smul_def] using h)),
        ⟨x, hxO, rfl⟩⟩
    · rintro ⟨hne, ⟨x, hxO, rfl⟩⟩
      exact ⟨x, ⟨fun hx8 => hne (by rw [hx8, Equiv.Perm.smul_def]), hxO⟩, rfl⟩
  simp only [stdH]
  rw [herase, hstdO, hg8]

theorem smul_stdO_of_stdH {g : S24} (h8 : g 8 = 8) (h : g • stdH = stdH) : g • stdO = stdO := by
  have hins : stdO = insert 8 stdH := by decide
  rw [hins, Finset.smul_finset_insert, h, Equiv.Perm.smul_def, h8]

end CFSG.Quasithin.AppendixH.H14
