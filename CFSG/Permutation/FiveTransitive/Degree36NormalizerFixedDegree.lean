module

public import CFSG.Permutation.FiveTransitive.Degree36FiveFreeFixed
import CFSG.Permutation.FiveTransitive.Degree58SylowPrimeFixed

public section

namespace CFSG

namespace FiveTransitive.Degree36NormalizerFixedDegree

open MulAction FixedNormalizerAction

theorem fixed_six_and_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P)
    (hN5 : IsMultiplyPretransitive (Normalizer Q) (Fixed (X := X) Q) 5)
    (hcases : Nat.card (Fixed (X := X) Q) = 6 ∨
      Nat.card (Fixed (X := X) Q) = 8 ∨ Nat.card (Fixed (X := X) Q) = 12) :
    Nat.card (Fixed (X := X) Q) = 6 ∧ Image (X := X) Q = ⊤ := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := Normalizer Q
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite _
  let rho : N →* Equiv.Perm F := toPermHom N F
  change Nat.card F = 6 ∨ Nat.card F = 8 ∨ Nat.card F = 12 at hcases
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 5 (FiveTransitive.Degree58SylowPrimeFixed.five_dvd_card hN5 (by change 5 ≤ Nat.card F; omega))
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  have hglobal := Degree36FiveFreeFixed.fixed_card_eq_one P hcard h5 hnotAlt g.val
    (by simpa only [Subgroup.orderOf_coe] using hg)
  let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : Function.fixedPoints g.val.val => z.val) h
    change x.val.val = y.val.val at hh
    exact Subtype.ext (Subtype.ext hh)
  have hlocal := Nat.card_le_card_of_injective f hf
  rw [hglobal] at hlocal
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 5 = 1 := by
    funext x
    change ((rho g) ^ 5) x = x
    rw [← map_pow,hg5,map_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 5) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 5 = Fintype.card (Function.fixedPoints (rho g)) % 5 at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card] at hm
  have hF : Nat.card F = 6 := by omega
  refine ⟨hF,?_⟩
  apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
  change IsMultiplyPretransitive rho.range F (Nat.card F - 1)
  rw [hF]
  change IsMultiplyPretransitive rho.range F 5
  rw [isMultiplyPretransitive_iff]
  intro a b
  obtain ⟨g,hg⟩ := hN5.exists_smul_eq a b
  exact ⟨⟨rho g,⟨g,rfl⟩⟩,hg⟩

end FiveTransitive.Degree36NormalizerFixedDegree

end CFSG
