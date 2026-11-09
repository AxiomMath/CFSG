module

public import CFSG.Milestones.ASVolI.C31.J4NP.FinalNative

public section

namespace CertificateChecks.Batch7954

def orMask : List Nat → Nat → Nat
  | [], m => m
  | x :: l, m => orMask l (m ||| 1 <<< x)

theorem testBit_orMask : ∀ (l : List Nat) (m k : Nat), (orMask l m).testBit k = true →
    m.testBit k = true ∨ k ∈ l
  | [], _, _, h => Or.inl h
  | x :: l, m, k, h => by
    rcases testBit_orMask l _ k h with h' | h'
    · rw [Nat.testBit_or, Bool.or_eq_true] at h'
      rcases h' with h' | h'
      · exact Or.inl h'
      · rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at h'
        exact Or.inr (List.mem_cons.2 (Or.inl (of_decide_eq_true h').symm))
    · exact Or.inr (List.mem_cons_of_mem _ h')

theorem cover_of_mask (cs : List Nat)
    (h : (List.range' 1 1327).all (fun k => (orMask (cs ++ (CFSG.ASVolI.burnsideJ4NP_vjIdsLit ++
      CFSG.ASVolI.burnsideJ4NP_m4IdsLit)) 0).testBit k) = true) :
    CFSG.ASVolI.burnsideJ4NP_idsCoverWith cs = true := by
  unfold CFSG.ASVolI.burnsideJ4NP_idsCoverWith
  rw [List.all_eq_true] at h ⊢
  intro k hk
  rcases testBit_orMask _ 0 k (h k hk) with h0 | hm
  · simp at h0
  · simpa [List.mem_append, or_assoc] using hm

end CertificateChecks.Batch7954

namespace Certificates

theorem certificate7954 : CFSG.ASVolI.burnsideJ4NP_idsCoverOK () = true := by
  unfold CFSG.ASVolI.burnsideJ4NP_idsCoverOK
  exact CertificateChecks.Batch7954.cover_of_mask _ (by decide +kernel)

end Certificates
