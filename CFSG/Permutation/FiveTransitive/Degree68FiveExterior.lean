module

public import CFSG.Permutation.FiveTransitive.Degree58FiveOrbitSevenFixed
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree68FiveExterior
open MulAction FixedNormalizerAction

private theorem card_eq_twenty_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q) (hF : Nat.card (fixedPoints Q X) = 8)
    (g : Normalizer Q) (hg : orderOf g = 7) :
    Nat.card {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x} = 25 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite _
  let rho : Normalizer Q →* Equiv.Perm F := toPermHom (Normalizer Q) F
  have hfixeq : (F : Set X) = fixedPoints Q X := fixed_eq Q
  have hFc : Nat.card F = 8 := by rw [hfixeq]; exact hF
  have hg7 : g ^ 7 = 1 := hg ▸ pow_orderOf_eq_one g
  have hsmall (x : X) : Nat.card (orbit Q x) < 125 := by
    have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := X),hcard] at hb
    omega
  have hm5 := Degree58FiveOrbitSevenFixed.fixed_congruence Q hQ hsmall g.val g.property
    (congrArg Subtype.val hg7)
  rw [← hfixeq] at hm5
  let Efix : Function.fixedPoints (rho g) ≃ {x : F // g.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change Nat.card (Function.fixedPoints g.val.val) % 5 =
    Nat.card {x : F // g.val.val x.val = x.val} % 5 at hm5
  rw [← Nat.card_congr Efix] at hm5
  have hlocal_bound : Nat.card (Function.fixedPoints (rho g)) ≤ 8 := by
    have hh := Nat.card_le_card_of_injective
      (fun x : Function.fixedPoints (rho g) => x.val) Subtype.val_injective
    rwa [hFc] at hh
  have hne : g.val.val ≠ 1 := by
    intro he
    have hh : g = 1 := Subtype.ext (Subtype.ext he)
    rw [hh,orderOf_one] at hg
    omega
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt
    g.val.property hne
  rw [hcard] at hb
  have hglobal_bound : Nat.card (Function.fixedPoints g.val.val) ≤ 34 := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.val.sum_cycleType,hcard]
    omega
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 7 = 1 := by
    funext x
    change ((rho g) ^ 7) x = x
    rw [← map_pow,hg7,map_one]
    rfl
  have hmL := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 7) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 7 = Fintype.card (Function.fixedPoints (rho g)) % 7 at hmL
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hFc] at hmL
  let b : Function.End X := g.val.val.toFun
  have hb7 : b ^ 7 = 1 := by
    funext x
    change (g ^ 7).val.val x = x
    rw [hg7]
    rfl
  have hmG := Equiv.Perm.card_fixedPoints_modEq (f := b) (p := 7) (n := 1)
    (by simpa only [pow_one] using hb7)
  change Fintype.card X % 7 = Fintype.card (Function.fixedPoints g.val.val) % 7 at hmG
  rw [hcard,← Nat.card_eq_fintype_card] at hmG
  let B := {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x}
  let E : Function.fixedPoints (rho g) ⊕ B ≃ Function.fixedPoints g.val.val :=
    { toFun := fun t => match t with
        | Sum.inl x => ⟨x.val.val,congrArg Subtype.val x.property⟩
        | Sum.inr x => ⟨x.val,x.property.2⟩
      invFun := fun x => if hx : x.val ∈ fixedPoints Q X then
        Sum.inl ⟨⟨x.val,hfixeq.symm ▸ hx⟩,Subtype.ext x.property⟩
        else Sum.inr ⟨x.val,hx,x.property⟩
      left_inv := by
        intro t
        cases t with
        | inl x =>
          have hx : x.val.val ∈ fixedPoints Q X := hfixeq ▸ x.val.property
          simp only [hx,↓reduceDIte]
        | inr x =>
          simp only [x.property.1,↓reduceDIte]
          rfl
      right_inv := by
        intro x
        dsimp only
        split_ifs <;> rfl }
  have he := Nat.card_congr E
  rw [Nat.card_sum] at he
  change Nat.card B = 25
  omega

theorem exists_invariant_type
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q) (hF : Nat.card (fixedPoints Q X) = 8)
    (g : Normalizer Q) (hg : orderOf g = 7) :
    ∃ T : SubMulAction Q X, Nat.card T = 25 ∧
      (∀ x : T, x.val ∉ fixedPoints Q X) ∧ (∀ x : T, g.val • x.val = x.val) := by
  classical
  let T : SubMulAction Q X :=
    { carrier := {x : X | x ∉ fixedPoints Q X ∧ g.val • x = x}
      smul_mem' := by
        intro q x hx
        refine ⟨?_,?_⟩
        · intro hh
          have he : q • x = x := by simpa only [inv_smul_smul] using (hh q⁻¹).symm
          exact hx.1 (he ▸ hh)
        · have hsmall : Nat.card (orbit Q x) < 125 := by
            have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
            rw [Nat.card_eq_fintype_card (α := X),hcard] at hb
            omega
          exact Degree58FiveOrbitSevenFixed.fixes_preserved_orbit Q hQ g.val g.property
            (congrArg Subtype.val (hg ▸ pow_orderOf_eq_one g)) x hsmall
            (by rw [hx.2]; exact mem_orbit_self x) (q • x) (mem_orbit_iff.mpr ⟨q,rfl⟩) }
  exact ⟨T,card_eq_twenty_five P hcard h5 hnotAlt Q hQ hF g hg,
    fun x => x.property.1,fun x => x.property.2⟩

end FiveTransitive.Degree68FiveExterior

end CFSG
