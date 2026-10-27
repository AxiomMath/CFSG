module

public import CFSG.Permutation.FiveTransitive.Degree60ThreeFixed
public import CFSG.Permutation.FiveTransitive.ThreeGroupOrbitFiveFixed

public section

namespace CFSG

namespace FiveTransitive.Degree60ThreeConditional

open MulAction SylowFixedActionCore

private theorem fixed_six_excluded_of_five_fixed_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (_hnotAlt : ¬ alternatingGroup X ≤ P)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) = 0 ∨ Nat.card (Function.fixedPoints g.val) = 5)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s))
    (hF6 : Nat.card (sylowFixedPoints X P s S) = 6) : False := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  have hF : Nat.card F = 6 := hF6
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have himage : alternatingGroup F ≤ (toPermHom N F).range := by
    apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F
    · rw [← Nat.card_eq_fintype_card,hF]; omega
    · rw [← Nat.card_eq_fintype_card,hF]; omega
    · rw [← Nat.card_eq_fintype_card,hF]; omega
    · rw [← Nat.card_eq_fintype_card,hF]; omega
    · intro a b ha hb
      obtain ⟨g,hg⟩ := hN5 a b ha hb
      exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,hg⟩
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hd : 5 ∣ Nat.card rho.range := by
    apply dvd_trans (b := Nat.card (alternatingGroup F))
    · rw [nat_card_alternatingGroup,hF]
      norm_num [Nat.factorial]
    · exact Subgroup.card_dvd_of_le himage
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
    (hd.trans (Subgroup.card_range_dvd rho))
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  have hglobal := hfive g.val ((Subgroup.orderOf_coe g).trans hg)
  have hsmall (x : X) : Nat.card (orbit Q x) < 81 := by
    have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := X),hcard] at hb
    omega
  have hm3 := ThreeGroupOrbitFiveFixed.fixed_congruence Q hQ hsmall
    g.val g.property (congrArg Subtype.val hg5)
  rw [← hfixeq] at hm3
  change Nat.card (Function.fixedPoints g.val.val) % 3 =
    Nat.card {x : F // g.val.val x.val = x.val} % 3 at hm3
  let e : Function.fixedPoints (rho g) ≃ {x : F // g.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e] at hm3
  change Nat.card (Function.fixedPoints g.val.val) % 3 =
    Nat.card (Function.fixedPoints (rho g)) % 3 at hm3
  let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : Function.fixedPoints g.val.val => z.val) h
    change x.val.val = y.val.val at hh
    exact Subtype.ext (Subtype.ext hh)
  have hle := Nat.card_le_card_of_injective f hf
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 5 = 1 := by
    funext x
    change ((rho g) ^ 5) x = x
    rw [← map_pow,hg5,map_one]
    rfl
  have hm5 := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 5) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 5 = Fintype.card (Function.fixedPoints (rho g)) % 5 at hm5
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hm5
  rcases hglobal with hglobal | hglobal <;> omega

theorem fixed_card_eq_twelve_of_five_fixed_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) = 0 ∨ Nat.card (Function.fixedPoints g.val) = 5)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 12 := by
  rcases Degree60ThreeFixed.three_fixed_card_cases P hcard h5 hnotAlt s hs S hS with h | h
  · exact (fixed_six_excluded_of_five_fixed_cases P hcard h5 hnotAlt hfive s hs S h).elim
  · exact h

end FiveTransitive.Degree60ThreeConditional

end CFSG
