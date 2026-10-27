module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrOddC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S16Pack

@[expose] def triOkB (L : List (ℕ × ℕ × ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun t _ r => Nat.blt t.1 t.2.1 && Nat.blt t.2.1 t.2.2 && Nat.blt t.2.2 256 && r) L

theorem triOk_of_triOkB {L : List (ℕ × ℕ × ℕ)} (h : triOkB L = true) :
    ∀ t ∈ L, t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < 256 := by
  induction L with
  | nil => simp
  | cons s L ih =>
    have h' : (Nat.blt s.1 s.2.1 && Nat.blt s.2.1 s.2.2 && Nat.blt s.2.2 256 && triOkB L) =
      true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2⟩
    · exact ih h'.2 t ht

theorem codeTriple4_mem (hlen : s16c11_fr_trips4.length = 1071) (k : Fin 1071) :
    s16c11_fr_codeTriple4 k ∈ s16c11_fr_trips4 := by
  have hk : k.1 < s16c11_fr_trips4.length := by
    rw [hlen]
    exact k.2
  rw [s16c11_fr_codeTriple4, List.getD_eq_getElem (l := s16c11_fr_trips4) (d := (0, 0, 0))
    (hn := hk)]
  exact List.getElem_mem hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S16Pack
