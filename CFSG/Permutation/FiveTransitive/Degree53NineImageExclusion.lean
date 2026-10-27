module

public import CFSG.Permutation.FiveTransitive.Degree53FiveFree

public section

namespace CFSG

namespace FiveTransitive.Degree53NineImageExclusion
open MulAction FixedNormalizerAction

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hF : Nat.card (Fixed (X := X) Q) = 9)
    (hdiv : 5 ∣ Nat.card (Image (X := X) Q)) : False := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite F
  let N := Normalizer Q
  let rho : N →* Equiv.Perm F := toPermHom N F
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
    (hdiv.trans (Subgroup.card_range_dvd rho))
  have hglobal := Degree53FiveFree.fixed_card_eq_three P hcard h5 hnotAlt g.val
    ((Subgroup.orderOf_coe g).trans hg)
  let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg
      (fun z : Function.fixedPoints g.val.val => z.val) h))
  have hle := Nat.card_le_card_of_injective f hf
  rw [hglobal] at hle
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 5 = 1 := by
    funext x
    change ((rho g) ^ 5) x = x
    rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 5) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 5 = Fintype.card (Function.fixedPoints (rho g)) % 5 at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card] at hm
  change Nat.card F = 9 at hF
  rw [hF] at hm
  omega

end FiveTransitive.Degree53NineImageExclusion

end CFSG
