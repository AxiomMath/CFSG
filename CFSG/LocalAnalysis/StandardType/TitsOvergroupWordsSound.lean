module

public import CFSG.LocalAnalysis.StandardType.TitsOvergroupSound

public section

namespace CFSG.StandardType.TitsOvergroup

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2

theorem wordVal_append {G : Type*} [Group G] (S : List G) (u v : List ℤ) :
    wordVal S (u ++ v) = wordVal S u * wordVal S v := by
  induction u with
  | nil => simp [wordVal]
  | cons z u ih => simp [wordVal, ih, mul_assoc]

theorem wordVal_invWord {G : Type*} [Group G] (S : List G) :
    ∀ w : List ℤ, (∀ z ∈ w, z ≠ 0) → wordVal S (invWord w) = (wordVal S w)⁻¹ := by
  intro w
  induction w with
  | nil => intro _; simp [invWord, wordVal]
  | cons z w ih =>
    intro hw
    have hz : z ≠ 0 := hw z (by simp)
    have hw' : ∀ x ∈ w, x ≠ 0 := fun x hx => hw x (by simp [hx])
    have h1 : invWord (z :: w) = invWord w ++ [-z] := by simp [invWord]
    rw [h1, wordVal_append, ih hw']
    rcases lt_or_gt_of_ne hz with hneg | hpos
    · have h2 : ¬ 0 < z := by omega
      have h3 : 0 < -z := by omega
      have e1 : wordVal S [-z] = S.getD ((-z).toNat - 1) 1 := by
        simp only [wordVal, if_pos h3, mul_one]
      have e2 : wordVal S (z :: w) = (S.getD ((-z).toNat - 1) 1)⁻¹ * wordVal S w := by
        simp only [wordVal, if_neg h2]
      rw [e1, e2, mul_inv_rev, inv_inv]
    · have h2 : 0 < z := hpos
      have h3 : ¬ 0 < -z := by omega
      have e1 : wordVal S [-z] = (S.getD (z.toNat - 1) 1)⁻¹ := by
        simp only [wordVal, if_neg h3, neg_neg, mul_one]
      have e2 : wordVal S (z :: w) = S.getD (z.toNat - 1) 1 * wordVal S w := by
        simp only [wordVal, if_pos h2]
      rw [e1, e2, mul_inv_rev]

theorem wordVal_conjWord {G : Type*} [Group G] (S : List G) {g : List ℤ} (hg : ∀ z ∈ g, z ≠ 0)
    (w : List ℤ) : wordVal S (conjWord g w) = wordVal S g * wordVal S w * (wordVal S g)⁻¹ := by
  rw [conjWord, wordVal_append, wordVal_append, wordVal_invWord S g hg]

variable {D : PairData} {S : List (Equiv.Perm (Fin D.n))}

theorem memW_sound (hS : Sound D S) (hSide : checkSide D = true)
    {memW : List (List (List Int))} (h : checkMemW D memW = true) {k : ℕ} (hk : k < memW.length)
    {w : List Int} (hw : w ∈ memW.getD k []) : wordVal S w ∈ pairSide D S k := by
  simp only [checkMemW, Bool.and_eq_true, decide_eq_true_eq, allBelow_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  have hk' : k < D.sideW.length := lt_of_lt_of_le hk hlen
  have hfound := (List.all_eq_true.1 (hall k hk)) w hw
  have hrep : TabRep (wT D w) (wordVal S w) := wordT_rep S D.gT (giT D) hS.rep hS.gi w
  have hE : enumOK D.n (sideGens D k) (sideEnum D k) = true := by
    simp only [checkSide, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hSide
    exact (hSide.2 k hk').1
  exact (CFSG.AGLEmbedding.MaxD2.found_iff_mem hE (enum_pairSide hS hSide hk') hrep).1 hfound

end CFSG.StandardType.TitsOvergroup
