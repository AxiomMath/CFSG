module

public import CFSG.Permutation.FiveTransitive.Degree53EvenSevenEntrance
public import CFSG.Permutation.FiveTransitive.Degree53TwoSevenGeneralEven

public section

namespace CFSG

namespace FiveTransitive.Degree53SixteenEntrance
open MulAction FixedNormalizerAction

theorem exists_subgroup
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ H : Subgroup (Equiv.Perm X), H ≤ P ∧
      IsMultiplyPretransitive H X 5 ∧ ¬ alternatingGroup X ≤ H ∧ H ≤ alternatingGroup X ∧
      ∃ Q : Subgroup H, IsPGroup 2 Q ∧ Nat.card Q = 16 ∧
        Nat.card (Fixed (X := X) Q) = 7 ∧ Image (X := X) Q = ⊤ ∧
        ∃ x : X, Nat.card (orbit Q x) = 16 ∧
          ∀ y : X, y ∉ orbit Q x → Nat.card (orbit Q y) ≤ 2 := by
  classical
  obtain ⟨H,hHP,hH5,hHnot,heven,Q,hQ,_,hF,him⟩ :=
    Degree53EvenSevenEntrance.exists_subgroup P hcard h5 hnotAlt
  have hHA : H ≤ alternatingGroup X := by
    intro g hg
    exact Equiv.Perm.mem_alternatingGroup.mpr (heven ⟨g,hg⟩)
  have hAlt : let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
      alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q := by
    rw [him]
    exact le_top
  have hcardQ := Degree53TwoSevenGeneralEven.card_eq_sixteen H hcard hH5 hHnot hHA Q hQ hF hAlt
  obtain ⟨x,hx,_,_,hsmall⟩ :=
    Degree53TwoSevenGeneralData.exists_orbit_data H hcard hH5 hHnot Q hQ hF hAlt
  exact ⟨H,hHP,hH5,hHnot,hHA,Q,hQ,hcardQ,hF,him,x,hx,hsmall⟩

end FiveTransitive.Degree53SixteenEntrance

end CFSG
