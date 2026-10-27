module

public import CFSG.Permutation.FiveTransitive.Degree36TwoOrbitObstruction
public import CFSG.Permutation.FiveTransitive.Degree36TwoOrbitGeometry
public import CFSG.Permutation.FiveTransitive.Degree36TwoGroupBound
public import CFSG.Permutation.FiveTransitive.Degree36FiveFreeFixed

public section

namespace CFSG

namespace FiveTransitive.Degree36TwoSubgroupExclusion

open MulAction FixedNormalizerAction

private theorem exists_five_free_outside
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (Q : Subgroup P)
    (hF : Nat.card (Fixed (X := X) Q) = 6) (him : Image (X := X) Q = ⊤)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) = 1) :
    ∃ g : Normalizer Q, orderOf g = 5 ∧
      ∀ x : X, x ∉ fixedPoints Q X → g.val • x ≠ x := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := Normalizer Q
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite _
  let rho : N →* Equiv.Perm F := MulAction.toPermHom N F
  change Nat.card F = 6 at hF
  change rho.range = ⊤ at him
  have hdiv : 5 ∣ Nat.card rho.range := by
    rw [him,Subgroup.card_top,Nat.card_perm,hF]
    norm_num [Nat.factorial]
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
    (hdiv.trans (Subgroup.card_range_dvd rho))
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  have hglobal := hfive g.val (by simpa only [Subgroup.orderOf_coe] using hg)
  let _ : Subsingleton (Function.fixedPoints g.val.val) :=
    Finite.card_le_one_iff_subsingleton.mp (by omega)
  obtain ⟨y,hy⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 5) (n := 1)
    (by rw [← Nat.card_eq_fintype_card,hF]; decide)
    (show (rho g) ^ 5 ^ 1 = 1 by rw [pow_one,← map_pow,hg5,map_one])
  have hyfix : g.val • y.val = y.val := congrArg Subtype.val hy
  refine ⟨g,hg,?_⟩
  intro x hx hgx
  have he : x = y.val := congrArg Subtype.val (Subsingleton.elim
    (⟨x,hgx⟩ : Function.fixedPoints g.val.val) ⟨y.val,hyfix⟩)
  apply hx
  rw [he]
  exact (show (F : Set X) = fixedPoints Q X from fixed_eq Q) ▸ y.property

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q) (hlarge : 4 < Nat.card Q)
    (hF : Nat.card (Fixed (X := X) Q) = 6) (him : Image (X := X) Q = ⊤) : False := by
  have hfive := Degree36FiveFreeFixed.fixed_card_eq_one P hcard h5 hnotAlt
  obtain ⟨g,hg,hfree⟩ := exists_five_free_outside P Q hF him hfive
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  have hX : Nat.card X = 36 := by rwa [Nat.card_eq_fintype_card]
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by
    rw [← fixed_eq Q]
    exact hF
  exact Degree36TwoOrbitObstruction.excluded_of_orbit_data P hcard Q hlarge hF him
    (Degree36TwoGroupBound.fixed_card_le_sixteen P hcard h5 hnotAlt Q hQ) hfive
    (Degree36TwoOrbitGeometry.orbit_card_two_or_four hX.le Q hQ g hg5 hfree)
    (Degree36TwoOrbitGeometry.family_card_cases hX Q hQ hfixed g hg5 hfree)

end FiveTransitive.Degree36TwoSubgroupExclusion

end CFSG
