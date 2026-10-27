module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.SixFixedFourGlobalExterior

open MulAction FixedNormalizerAction

theorem exists_fixed_exterior
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (Q : Subgroup P)
    (hF : Nat.card (Fixed (X := X) Q) = 6)
    (g : Normalizer Q) (hg : g ^ 5 = 1)
    (hglobal : Nat.card (Function.fixedPoints g.val.val) = 4) :
    ∃ x : X, x ∉ fixedPoints Q X ∧ g.val • x = x := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let F := Fixed (X := X) Q
  let N := Normalizer Q
  let _ : Fintype F := Fintype.ofFinite _
  let rho : N →* Equiv.Perm F := toPermHom N F
  by_contra hn
  have hsub : Function.fixedPoints g.val.val ⊆ fixedPoints Q X := by
    intro x hx
    by_contra hnot
    exact hn ⟨x,hnot,hx⟩
  have hfixeq : (F : Set X) = fixedPoints Q X := fixed_eq Q
  let E : Function.fixedPoints (rho g) ≃ Function.fixedPoints g.val.val :=
    { toFun := fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨⟨x.val,hfixeq.symm ▸ hsub x.property⟩,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let f : Function.End F := (rho g).toFun
  have hf : f ^ 5 = 1 := by
    funext x
    change (rho g ^ 5) x = x
    rw [← map_pow,hg,map_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1)
    (by simpa only [pow_one] using hf)
  change Fintype.card F % 5 = Fintype.card (Function.fixedPoints (rho g)) % 5 at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,Nat.card_congr E,hglobal] at hm
  change Nat.card F = 6 at hF
  rw [hF] at hm
  norm_num at hm

end FiveTransitive.SixFixedFourGlobalExterior

end CFSG
