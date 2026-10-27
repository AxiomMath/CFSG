module

public import CFSG.Permutation.FiveTransitive.Degree67TwoEntrance
public import CFSG.Permutation.FiveTransitive.Degree67FiveFree

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoFiveLifts

open MulAction FixedNormalizerAction

private theorem exists_prime_exterior_le_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (Q : Subgroup P)
    (hF : Nat.card (Fixed (X := X) Q) = 5)
    (hAlt : let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
      alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hglobal_bound : ∀ g : P, orderOf g = p →
      Nat.card (Function.fixedPoints g.val) ≤ if p = 3 then 4 else 2) :
    ∃ g : Normalizer Q, orderOf g = p ∧
      Nat.card {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x} ≤ 2 := by
  classical
  let _ : Fact (Nat.Prime p) := ⟨by rcases hp with rfl | rfl <;> decide⟩
  let N := Normalizer Q
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  change alternatingGroup F ≤ rho.range at hAlt
  change Nat.card F = 5 at hF
  have hdiv : p ∣ Nat.card rho.range :=
    (SylowFixedActionCore.odd_prime_dvd_alternating_card F (Fact.out : Nat.Prime p)
      (by rcases hp with rfl | rfl <;> decide)
      (by rw [← Nat.card_eq_fintype_card,hF]; omega)).trans (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) p
    (hdiv.trans (Subgroup.card_range_dvd rho))
  have hgp : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
  have hglobal := hglobal_bound g.val ((Subgroup.orderOf_coe g).trans hg)
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : Function.fixedPoints g.val.val => z.val) h
    change x.val.val = y.val.val at hh
    exact Subtype.ext (Subtype.ext hh)
  have hle := Nat.card_le_card_of_injective f hf
  have hle4 : Nat.card (Function.fixedPoints (rho g)) ≤ 4 := by
    split_ifs at hglobal <;> omega
  let a : Function.End F := (rho g).toFun
  have ha : a ^ p = 1 := by
    funext x
    change ((rho g) ^ p) x = x
    rw [← map_pow,hgp,map_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := p) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % p = Fintype.card (Function.fixedPoints (rho g)) % p at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hm
  have hlocal : p = 3 → 2 ≤ Nat.card (Function.fixedPoints (rho g)) := by
    intro hp3
    rw [hp3] at hm
    omega
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
  refine ⟨g,hg,?_⟩
  change Nat.card B ≤ 2
  rcases hp with rfl | rfl
  · simp only [ite_true] at hglobal
    have hl := hlocal rfl
    omega
  · change Nat.card (Function.fixedPoints g.val.val) ≤ 2 at hglobal
    omega

theorem exists_normalizers
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (SylowFixedActionCore.sylowFixedPoints X P s S) = 5) :
    ∃ g3 g5 : SylowFixedActionCore.sylowNormalizer X P s S,
      g3 ^ 3 = 1 ∧ g5 ^ 5 = 1 ∧
      Nat.card {x : X // x ∉ fixedPoints (SylowFixedActionCore.sylowImage X P s S) X ∧
        g3.val • x = x} ≤ 2 ∧
      Nat.card {x : X // x ∉ fixedPoints (SylowFixedActionCore.sylowImage X P s S) X ∧
        g5.val • x = x} ≤ 2 := by
  have hAlt := Degree67TwoEntrance.alternating_image P hcard h5 s hs S
  obtain ⟨g3,hg3,h3⟩ := exists_prime_exterior_le_two P
    (SylowFixedActionCore.sylowImage X P s S) hF hAlt 3 (Or.inl rfl)
    (by simpa using Degree67FiveFree.three_fixed_card_le_four P hcard h5 hnotAlt)
  obtain ⟨g5,hg5,hfive⟩ := exists_prime_exterior_le_two P
    (SylowFixedActionCore.sylowImage X P s S) hF hAlt 5 (Or.inr rfl)
    (by intro g hg; simpa using (Degree67FiveFree.fixed_card_eq_two P hcard h5 hnotAlt g hg).le)
  exact ⟨g3,g5,hg3 ▸ pow_orderOf_eq_one g3,hg5 ▸ pow_orderOf_eq_one g5,h3,hfive⟩

end FiveTransitive.Degree67TwoFiveLifts

end CFSG
