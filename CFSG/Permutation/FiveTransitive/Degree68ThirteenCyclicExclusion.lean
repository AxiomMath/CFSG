module

public import CFSG.Permutation.FiveTransitive.Degree68ThirteenThreeObstruction
public import CFSG.Permutation.FiveTransitive.Degree68ThreeNoSixFixed

public section

namespace CFSG

namespace FiveTransitive.Degree68ThirteenCyclicExclusion
open MulAction Subgroup FixedNormalizerAction

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) [IsCyclic Q] (hQ : IsPGroup 13 Q)
    (hF : Nat.card (Fixed (X := X) Q) = 3)
    (himage : Image (X := X) Q = ⊤) : False := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let F := Fixed (X := X) Q
  let rho := toPermHom (Normalizer Q) F
  have hrho : Function.Surjective rho := MonoidHom.range_eq_top.mp himage
  have hd := FiveTransitive.CyclicNormalizerThreeImage.three_dvd_centralizer_card Q hF rho hrho
  let C := Subgroup.centralizer (Q : Set P)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 hd
  let i : C →* Normalizer Q := Subgroup.inclusion (Subgroup.centralizer_le_normalizer (Q : Set P))
  let g : Normalizer Q := i z
  have hg : orderOf g = 3 := (orderOf_injective i (Subgroup.inclusion_injective _) z).trans hz
  have hcomm : ∀ q : Q, g.val * q.val = q.val * g.val := by
    intro q
    exact (z.property q.val q.property).symm
  have hcases := Degree68ThreeNoSixFixed.fixed_card_cases P hcard h5 hnotAlt g.val
    ((Subgroup.orderOf_coe g).trans hg)
  have hfixed : Nat.card (fixedPoints Q X) = 3 := by
    rw [← fixed_eq Q]
    exact hF
  exact Degree68ThirteenThreeObstruction.false_of_fixed_counts P hcard Q hQ hfixed
    g hg hcomm (by rcases hcases with h | h <;> omega)

end FiveTransitive.Degree68ThirteenCyclicExclusion

end CFSG
