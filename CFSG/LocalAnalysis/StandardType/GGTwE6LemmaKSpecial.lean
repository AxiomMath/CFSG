module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKSylow
public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKRefl

public noncomputable section

namespace CFSG.StandardType.TwE6LemmaK

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.AGLEmbedding.R3
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.HardMathSupport.Timmesfeld.SporadicRank
open scoped Matrix

private lemma lemKTab_lengths {s : List Int × List Int × List Nat × List Nat}
    (hs : s ∈ lemKTab) : s.1.length = 6 ∧ s.2.1.length = 6 := by
  simp only [lemKTab, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> decide

private lemma lemKDot_vecList6 (a : List Int) (y : Fin 6 → ZMod 3) (ha : a.length = 6) :
    lemKDot a (vecList6 y) = ∑ i : Fin 6, a.getD i.val 0 * ((y i).val : ℤ) := by
  simp only [lemKDot, vecList6]
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · rw [List.length_zipWith, List.length_ofFn, List.length_ofFn, ha, Nat.min_self]
  · intro k h1 h2
    rw [List.getElem_zipWith, List.getElem_ofFn, List.getElem_ofFn]
    have hk : k < a.length := by rw [ha]; exact h2
    rw [List.getD_eq_getElem a 0 hk]

private lemma cast_lemKDot (a : List Int) (y : Fin 6 → ZMod 3) (ha : a.length = 6) :
    ((lemKDot a (vecList6 y) : ℤ) : ZMod 3)
      = ∑ i : Fin 6, ((a.getD i.val 0 : ℤ) : ZMod 3) * y i := by
  rw [lemKDot_vecList6 a y ha, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

private lemma sum_eq_zero_of_lemKDot {a : List Int} (ha : a.length = 6) {y : Fin 6 → ZMod 3}
    (h : lemKDot a (vecList6 y) % 3 = 0) :
    (∑ i : Fin 6, ((a.getD i.val 0 : ℤ) : ZMod 3) * y i) = 0 := by
  have h0 : ((lemKDot a (vecList6 y) : ℤ) : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.dvd_of_emod_eq_zero h
  rw [← cast_lemKDot a y ha]
  exact h0

private lemma sum_eq_zero_of_coord {a : List Int} {f : Fin Tag.E6.rank → ℤ}
    (ha : a.length = 6) (hcoord : ∀ i : Fin 6, f (e6Idx i) = a.getD i.val 0)
    {y : Fin 6 → ZMod 3} (h : lemKDot a (vecList6 y) % 3 = 0) :
    ∑ i : Fin 6, ((f (e6Idx i) : ℤ) : ZMod 3) * y i = 0 := by
  have h0 := sum_eq_zero_of_lemKDot ha h
  simpa only [hcoord] using h0

private lemma vecList6_mem_lemKFix {A : List Nat} {p : WeylGroup Tag.E6}
    (hAw : toMatL 3 6 A = e6WeylMat p) {Y : Set (Fin 6 → ZMod 3)}
    (hfix : ∀ y ∈ Y, e6WeylMat p *ᵥ y = y) {y : Fin 6 → ZMod 3} (hy : y ∈ Y) :
    vecList6 y ∈ lemKFix A := by
  refine List.mem_filter.2 ⟨vecList6_mem y, ?_⟩
  rw [beq_iff_eq, matVecA6_toArray]
  have hm : matVecL 3 6 A (vecList6 y) ∈ allVecs 3 6 :=
    (mem_allVecs 3 6 _).2 ⟨length_matVecL 3 6 A _, lt_matVecL (by norm_num) 6 A _⟩
  refine vecOf_inj hm (vecList6_mem y) ?_
  rw [vecOf_matVecL, vecOf_vecList6, hAw]
  exact hfix y hy

section Special


theorem lemKP_special {p : WeylGroup Tag.E6} (hp : p ∈ lemKP) (Y : Set (Fin 6 → ZMod 3))
    (hY : 81 ≤ Nat.card Y) (hfix : ∀ y ∈ Y, e6WeylMat p *ᵥ y = y) :
    p = 1 ∨ ∃ a b : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 a ∧ IsRoot Tag.E6 b ∧
      p = rootReflection a * rootReflection b ∧
      (∀ y ∈ Y, ∑ i : Fin 6, ((a (e6Idx i) : ℤ) : ZMod 3) * y i = 0) ∧
      (∀ y ∈ Y, ∑ i : Fin 6, ((b (e6Idx i) : ℤ) : ZMod 3) * y i = 0) := by
  obtain ⟨A, hA, hAw⟩ := mem_e6SylMats.1 (mem_lemKP.1 hp)
  have hsub : Y ⊆ fixMat6 (toMatL 3 6 A) := by
    intro y hy
    show toMatL 3 6 A *ᵥ y = y
    rw [hAw]
    exact hfix y hy
  have hcard : Nat.card Y ≤ nfix6 A :=
    (Nat.card_mono (Set.toFinite _) hsub).trans (card_fixMat6_le A)
  have hbig : ¬ nfix6 A < 81 := by
    intro hlt
    omega
  rcases lemKFacts.cases A hA with hmid | hsmall | htab
  · left
    apply e6WeylMat_injective
    rw [← hAw, hmid, toMatL_midL, map_one]
  · exact absurd hsmall hbig
  · obtain ⟨s, hs, hdisj⟩ := htab
    obtain ⟨a, b, har, hbr, hac, hbc, hAm, hBm⟩ := lemKTab_spec s hs
    have hlen := lemKTab_lengths hs
    have hveca : ∀ y ∈ Y, vecList6 y ∈ lemKFix A := fun y hy =>
      vecList6_mem_lemKFix hAw hfix hy
    rcases hdisj with hA1 | hA2
    · refine Or.inr ⟨a, b, har, hbr, ?_, ?_, ?_⟩
      · apply e6WeylMat_injective
        rw [← hAw, hA1, toMatL_mmulL, hAm, hBm, map_mul]
      · intro y hy
        exact sum_eq_zero_of_coord hlen.1 hac
          (lemKFacts.fix_orth s hs A (Or.inl hA1) (vecList6 y) (hveca y hy)).1
      · intro y hy
        exact sum_eq_zero_of_coord hlen.2 hbc
          (lemKFacts.fix_orth s hs A (Or.inl hA1) (vecList6 y) (hveca y hy)).2
    · refine Or.inr ⟨b, a, hbr, har, ?_, ?_, ?_⟩
      · apply e6WeylMat_injective
        rw [← hAw, hA2, toMatL_mmulL, hBm, hAm, map_mul]
      · intro y hy
        exact sum_eq_zero_of_coord hlen.2 hbc
          (lemKFacts.fix_orth s hs A (Or.inr hA2) (vecList6 y) (hveca y hy)).2
      · intro y hy
        exact sum_eq_zero_of_coord hlen.1 hac
          (lemKFacts.fix_orth s hs A (Or.inr hA2) (vecList6 y) (hveca y hy)).1

end Special

end CFSG.StandardType.TwE6LemmaK
