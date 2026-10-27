module

public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Set.Disjoint
public import CFSG.LocalAnalysis.StandardType.GGReeB2CoverZero
public import CFSG.LocalAnalysis.StandardType.GGReeB2Resolve

open scoped Pointwise

public section

namespace CFSG.StandardType.ReeB2Fixed

private theorem neg_mem_units (e : ℕ) {x : ZMod (2 ^ e - 1)} (hx : x ∈ units e) :
    -x ∈ units e := by
  simp only [units, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (neg_neg 1)
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl (neg_neg (R e))))

private theorem neg_mem_lam (e : ℕ) (B : Finset (Fin e)) {x : ZMod (2 ^ e - 1)}
    (hx : x ∈ Lam e B) : -x ∈ Lam e B := by
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨fun j => -c j, fun j hj => neg_mem_units e (hc j hj), ?_⟩
  simp only [neg_mul, Finset.sum_neg_distrib]

theorem not_disjoint_of_syncFree (e : ℕ) (he : Odd e) (h3 : 3 ≤ e) (A B : Finset (Fin e))
    (hI : IndepSigma e A) (h : ∀ p, ¬ SyncAt e A B p) : ¬ Disjoint (Lam e A) (Lam e B) := by
  have hcover : ∀ p : Fin e, p ∈ resolve e A B ∨ succσ e p ∈ resolve e A B := by
    intro p
    by_cases hA : p ∈ A
    · by_cases hB : p ∈ B
      · have hσA : succσ e p ∉ A := hI p hA
        by_cases hσB : succσ e p ∈ B
        · right
          exact Finset.mem_union_left _
            (Finset.mem_symmDiff.mpr (Or.inr ⟨hσB, hσA⟩))
        · right
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨p, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hA, hB⟩, hσB⟩
      · left
        exact Finset.mem_union_left _
          (Finset.mem_symmDiff.mpr (Or.inl ⟨hA, hB⟩))
    · by_cases hB : p ∈ B
      · left
        exact Finset.mem_union_left _
          (Finset.mem_symmDiff.mpr (Or.inr ⟨hB, hA⟩))
      · right
        have hsymm : succσ e p ∈ symmDiff A B := by
          by_cases hσA : succσ e p ∈ A
          · have hσB : succσ e p ∉ B :=
              fun hσB => h p ⟨hA, hB, ⟨fun _ => hσB, fun _ => hσA⟩⟩
            exact Finset.mem_symmDiff.mpr (Or.inl ⟨hσA, hσB⟩)
          · by_cases hσB : succσ e p ∈ B
            · exact Finset.mem_symmDiff.mpr (Or.inr ⟨hσB, hσA⟩)
            · exact (h p ⟨hA, hB,
                ⟨fun hσ => absurd hσ hσA, fun hσ => absurd hσ hσB⟩⟩).elim
        exact Finset.mem_union_left _ hsymm
  have h0J : (0 : ZMod (2 ^ e - 1)) ∈ Lam e (resolve e A B) :=
    zero_mem_lam_of_cover e he h3 (resolve e A B) hcover
  have h0 : (0 : ZMod (2 ^ e - 1)) ∈ Lam e A + Lam e B :=
    lam_resolve_subset e he h3 A B hI h0J
  obtain ⟨y, hyA, z, hzB, hyz⟩ := Set.mem_add.mp h0
  have hyB : y ∈ Lam e B := by
    have hy_eq : y = -z := by
      rw [← sub_eq_zero, sub_eq_add_neg, neg_neg]
      exact hyz
    rw [hy_eq]
    exact neg_mem_lam e B hzB
  exact Set.not_disjoint_iff.mpr ⟨y, hyA, hyB⟩

end CFSG.StandardType.ReeB2Fixed
