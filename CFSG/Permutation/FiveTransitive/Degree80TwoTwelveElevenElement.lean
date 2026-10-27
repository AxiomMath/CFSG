module

public import CFSG.Permutation.FiveTransitive.Degree80LargePrimeFixity

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoTwelveElevenElement
open MulAction SylowFixedActionCore

theorem exists_eleven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 12) :
    ∃ g : sylowNormalizer X P s S, orderOf g = 11 ∧
      Nat.card (Function.fixedPoints g.val.val) = 3 ∧
      Nat.card (Function.fixedPoints (toPermHom (sylowNormalizer X P s S)
        (sylowFixedPoints X P s S) g)) = 1 := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  change Nat.card F = 12 at hF
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 : IsMultiplyPretransitive N F 5 :=
    FiveTransitive.isMultiplyPretransitive_of_explicit N F 5
      (sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S)
  have hd := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive N F 5
    (by rw [← Nat.card_eq_fintype_card,hF]; decide) hN5
  rw [← Nat.card_eq_fintype_card,hF] at hd
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 11
    ((by norm_num : 11 ∣ (12 : ℕ).descFactorial 5).trans hd)
  have hg5 : g ^ 11 = 1 := hg ▸ pow_orderOf_eq_one g
  have hglobal := Degree80LargePrimeFixity.eleven_fixed_card_eq_three P hcard h5 hnotAlt g.val
    ((Subgroup.orderOf_coe g).trans hg)
  let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : Function.fixedPoints g.val.val => z.val) h
    change x.val.val = y.val.val at hh
    exact Subtype.ext (Subtype.ext hh)
  have hle := Nat.card_le_card_of_injective f hf
  rw [hglobal] at hle
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 11 = 1 := by
    funext x
    change ((rho g) ^ 11) x = x
    rw [← map_pow,hg5,map_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 11) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 11 = Fintype.card (Function.fixedPoints (rho g)) % 11 at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hm
  have hlocal : Nat.card (Function.fixedPoints (rho g)) = 1 := by omega
  exact ⟨g,hg,hglobal,hlocal⟩

end FiveTransitive.Degree80TwoTwelveElevenElement

end CFSG
