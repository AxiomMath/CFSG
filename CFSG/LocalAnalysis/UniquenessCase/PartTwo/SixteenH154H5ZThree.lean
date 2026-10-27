module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZWorld
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Kbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_L3World_three {U : Type} [CommGroup U] [Finite U] {N L : Subgroup (MulAut U)}
    (h : s16h_L3World N L)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L ⊤ (fixV L) 3) :
    Nat.card ↥(irrSet L) = 3 ∨
      ∃ r : ↥N →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2),
        (∀ a : ↥N, r a = 1 ↔ ∀ J ∈ irrSet L, J.map (a : MulAut U).toMonoidHom = J) ∧
        ∀ u v : Fin 3 → ZMod 2, u ≠ 0 → v ≠ 0 →
          ∃ a : ↥N, ((r a : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec u = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 N
  have hThree : ThreeNat N L T :=
    { elem := h.elem, le := h.le, normal := h.normal, sylow := hT, quasi := h.quasi,
      comm := h.comm, sum := ⟨3, Or.inl ⟨h.sl3, hsum⟩⟩, faithful := h.faithful
      trans := fun I₁ hI₁ I₂ hI₂ => by
        obtain ⟨g, hg, hI⟩ := h.trans I₁ hI₁ I₂ hI₂
        exact ⟨g, Subgroup.mem_inf.2 ⟨hg, h.normal hg⟩, hI⟩ }
  rcases hThree.card_irrSet_eq with h3 | h7
  · exact Or.inl h3
  · exact Or.inr (hThree.exists_fano_rep h7)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
