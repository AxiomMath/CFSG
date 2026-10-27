
module

public import CFSG.Sporadic.Th.ChainBase

@[expose] public section

namespace CFSG.Sporadic.Th

open Native Pointwise

@[expose] def subSizes : Fin 11 → ℕ :=
  ![1, 11741184, 5031936, 105670656, 8805888, 8128512, 1304576, 45864, 2201472, 179712, 17199]

set_option maxRecDepth 100000 in
theorem subSizes_blocks : ∀ S : Finset (Fin 11), (0 : Fin 11) ∈ S →
    (∑ i ∈ S, subSizes i) ∣ 143127000 → S = {0} ∨ S = Finset.univ := by
  decide

theorem subSizes_eq_one {i : Fin 11} (h : subSizes i = 1) : i = 0 := by
  revert i h; decide

theorem suborbitSizes_getElem (i : Fin 11) : suborbitSizes[i.val]! = subSizes i := by
  revert i; decide

theorem gplT_ap {k : ℕ} (hk : k < nX) : (gplT[k]!).toNat = readU32 thSt.par k :=
  ap_tblOfBytes _ hk

section TreeId

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)] {g₁ g₂ : G} {pl : Table}

theorem TreeData.of_id (hn : 0 < n) (hpar : ∀ k < n, 0 < k → treePar (pl[k]!).toNat < k)
    (helt : ∀ k < n, idx n (treeElt pl (lettersG g₁ g₂) k) 0 = k) :
    TreeData n g₁ g₂ n 0 id id pl :=
  ⟨hn, rfl, fun _ hk => hk, fun _ _ => rfl, fun _ hk => ⟨idx_lt g₁ hk, rfl⟩,
    fun _ hk => ⟨idx_lt g₂ hk, rfl⟩, hpar, helt⟩

theorem TreeData.stab_le_two_three_id (hT : TreeData n g₁ g₂ n 0 id id pl) (hg₁ : g₁ ^ 2 = 1)
    (hg₂ : g₂ ^ 3 = 1) (K' : Subgroup G) {P₁ P₂ : ℕ → ℕ}
    (hP₁ : ∀ k < n, P₁ k = idx n g₁ k) (hP₂ : ∀ k < n, P₂ k = idx n g₂ k)
    (h₁ : ∀ k < n, reqTwo pl P₁ 1 k = true →
      (treeElt pl (lettersG g₁ g₂) (P₁ k))⁻¹ * g₁ * treeElt pl (lettersG g₁ g₂) k ∈ K')
    (h₂ : ∀ k < n, reqThree pl P₂ 2 k = true →
      (treeElt pl (lettersG g₁ g₂) (P₂ k))⁻¹ * g₂ * treeElt pl (lettersG g₁ g₂) k ∈ K') :
    ∀ g ∈ Subgroup.closure ({g₁, g₂} : Set G), idx n g 0 = 0 → g ∈ K' :=
  hT.stab_le_two_three hg₁ hg₂ K' hP₁ hP₂ h₁ h₂

end TreeId

section Global

variable {c : ℕ} (hC : CertFacts c)
include hC

theorem globalChecks_parts :
    (∀ i < nX, (reqTwo gplT (ap alphaT) 1 i = true →
        globalTest gplT (letters alphaT betaT) (letters alphaT betaInvT) chainT 1 i = true) ∧
      (reqThree gplT (ap betaT) 2 i = true →
        globalTest gplT (letters alphaT betaT) (letters alphaT betaInvT) chainT 2 i = true)) ∧
    ∀ i < nX, abPow19 alphaT betaT i = i := by
  have h := hC.tables.global
  simp only [globalChecks, Bool.and_eq_true] at h
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := parAll_eq_true h.1 i hi
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
    constructor
    · intro hreq
      rcases this.1 with h' | h'
      · exact absurd (hreq.symm.trans h') (by decide)
      · exact h'
    · intro hreq
      rcases this.2 with h' | h'
      · exact absurd (hreq.symm.trans h') (by decide)
      · exact h'
  · have := parAll_eq_true h.2 i hi
    simpa using this

theorem zero_lt_nX : 0 < nX := hC.orbit.pos

noncomputable abbrev root : Fin nX := ⟨0, hC.orbit.pos⟩

omit hC in
theorem getElem!_of_toList_eq {A : Array ℕ} {L : List ℕ} (h : A.toList = L) (i : ℕ) :
    A[i]! = L[i]! := by
  subst h
  simp [getElem!_def]

end Global

end CFSG.Sporadic.Th
