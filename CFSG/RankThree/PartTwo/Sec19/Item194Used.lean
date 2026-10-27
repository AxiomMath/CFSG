module

public import CFSG.RankThree.PartTwo.Sec19.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Item194Used : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Sec19Std G →
    ∀ A M H : Subgroup G, IsE27 A → M ∈ scriptM (gamma 2 A : Set G) →
      H ∈ scriptM (A : Set G) → H ≠ M →
      (scriptJ M H).Nonempty ∧
      ∀ K ∈ scriptJ M H,
        IsList194 (K ⧸ CFSG.pCore 2 K) ∧
        ((IsEmpty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
            IsProperParabolic (starIm K H)) ∨
          (Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
            Sec4.IsExtOf (starIm K H) (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2))))

theorem item194Used_of_item194 (h194 : Item194) : Item194Used := by
  intro G _ _ hG A M H hA hM hH hHM
  obtain ⟨hJ, hall, -⟩ := h194 G hG A M H hA hM hH hHM
  exact ⟨hJ, fun K hK => ⟨(hall K hK).2.1, (hall K hK).2.2.1⟩⟩

end CFSG.RankThree.PartTwo.Sec19
