module
public import CFSG.Sporadic.HNSchreier.ArchKernelChecks

public section
namespace CFSG.Sporadic.HNSchreier.Native.Kernel

theorem allInKernel_eq_true {lo hi : Nat} {p : Nat → Bool} :
    allInKernel lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true := by
  rw [← allIn_kernel]
  unfold CFSG.Sporadic.Th.Native.allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hlo hhi
    have := h ⟨i - lo, by omega⟩ (List.mem_finRange _)
    simpa [Nat.add_sub_cancel' hlo] using this
  · rintro h ⟨k, hk⟩ _
    exact h (lo + k) (by omega) (by omega)

theorem allInKernel_split (lo mid hi : Nat) (p : Nat → Bool)
    (hlo : lo ≤ mid) (hhi : mid ≤ hi) :
    allInKernel lo hi p = true ↔
      allInKernel lo mid p = true ∧ allInKernel mid hi p = true := by
  simp only [allInKernel_eq_true]
  constructor
  · intro h
    exact ⟨fun i hl hm => h i hl (by omega), fun i hm hh => h i (by omega) hh⟩
  · rintro ⟨hl, hr⟩ i hi1 hi2
    by_cases hm : i < mid
    · exact hl i hi1 hm
    · exact hr i (by omega) hi2

end CFSG.Sporadic.HNSchreier.Native.Kernel
