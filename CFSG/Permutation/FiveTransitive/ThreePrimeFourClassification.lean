module

public import CFSG.Permutation.FiveTransitive.ThreePrimeFourFiveFixer
public import CFSG.Permutation.FiveTransitive.ThreePrimeFourAmbientPGroup
public import CFSG.Permutation.FiveTransitive.ThreePrimeFourCentralizer

public section

namespace CFSG

namespace FiveTransitive.ThreePrimeFourClassification

open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X] {p : ℕ}
    (hp : p.Prime) (hp17 : 17 ≤ p)
    (P : Subgroup (Equiv.Perm X)) (hn : Fintype.card X = 3 * p + 4)
    (h5 : IsMultiplyPretransitive P X 5)
    (hclass : ∀ (F : Type) [Fintype F] [DecidableEq F]
      (J : Subgroup (Equiv.Perm F)),
      5 ≤ Fintype.card F → Fintype.card F < Fintype.card X →
      IsMultiplyPretransitive J F 5 →
      Nat.card J = (Fintype.card F).factorial ∨
      (7 ≤ Fintype.card F ∧ Nat.card J = (Fintype.card F).factorial / 2) ∨
      (Fintype.card F = 12 ∧ Nat.card J = 95040) ∨
      (Fintype.card F = 24 ∧ Nat.card J = 244823040)) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  have hfree := ThreePrimeFourFiveFixer.not_dvd_five_fixer hp hp17 P hn h5 hnotAlt hclass
  obtain ⟨u,_,ht,hfixed,himage⟩ :=
    ThreePrimeFourAmbientPGroup.exists_generator hp hp17 P hn h5 hfree
  exact ThreePrimeFourCentralizer.excluded hp hp17 P hn h5 hnotAlt u ht hfixed himage

end FiveTransitive.ThreePrimeFourClassification

end CFSG
