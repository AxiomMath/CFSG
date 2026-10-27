module

public import CFSG.Permutation.FiveTransitive.Degree67FiveTwelveOrder
public import CFSG.Permutation.FiveTransitive.Degree67FiveThreeAut
public import CFSG.Permutation.FiveTransitive.CentralizingFixedPointCongruence

public section

namespace CFSG

namespace FiveTransitive.Degree67FiveTwelveExclusion

open MulAction Subgroup SylowFixedActionCore

theorem fixed_ne_twelve
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hthree : ∀ g : P, orderOf g = 3 → Nat.card (Function.fixedPoints g.val) ≤ 4)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) :
    Nat.card (sylowFixedPoints X P s S) ≠ 12 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro hF12
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  have hF : Nat.card F = 12 := hF12
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hQcard : Nat.card Q ≤ 5 := by
    have he : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
    rw [he]
    exact Degree67FiveTwelveOrder.sylow_card_le_five P hcard h5 hnotAlt s hs S hF12
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hI : Nat.card rho.range = 95040 := Degree67FiveImage.card_eq_95040 P hcard h5 hnotAlt s hs S hF12
  have hd : 3 ∣ Nat.card rho.range := by rw [hI]; norm_num
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 3
    (hd.trans (Subgroup.card_range_dvd rho))
  have haut : Q.normalizerMonoidHom g = 1 :=
    Degree67FiveThreeAut.eq_one hQ hQcard _
      (by rw [← map_pow,← hg,pow_orderOf_eq_one,map_one])
  have hcomm : ∀ q : Q, g.val * q.val = q.val * g.val := by
    intro q
    have hh : g.val * q.val * g.val⁻¹ = q.val :=
      congrArg Subtype.val (DFunLike.congr_fun haut q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using
      congrArg (fun a : P => a * g.val) hh
  have hglobal := hthree g.val ((Subgroup.orderOf_coe g).trans hg)
  have hm5 := CentralizingFixedPointCongruence.card_modEq P Q hQ g.val hcomm
  rw [← hfixeq] at hm5
  let e : Function.fixedPoints (rho g) ≃ {x : F // g.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e] at hm5
  change Nat.card (Function.fixedPoints g.val.val) % 5 =
    Nat.card (Function.fixedPoints (rho g)) % 5 at hm5
  let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : Function.fixedPoints g.val.val => z.val) h
    change x.val.val = y.val.val at hh
    exact Subtype.ext (Subtype.ext hh)
  have hle := Nat.card_le_card_of_injective f hf
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 3 = 1 := by
    funext x
    change ((rho g) ^ 3) x = x
    rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
    rfl
  have hm7 := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 3) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 3 = Fintype.card (Function.fixedPoints (rho g)) % 3 at hm7
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hm7
  let b : Function.End X := g.val.val.toFun
  have hb : b ^ 3 = 1 := by
    funext x
    change (g ^ 3).val.val x = x
    rw [← hg,pow_orderOf_eq_one]
    rfl
  have hglobalmod := Equiv.Perm.card_fixedPoints_modEq (f := b) (p := 3) (n := 1)
    (by simpa only [pow_one] using hb)
  change Fintype.card X % 3 = Fintype.card (Function.fixedPoints g.val.val) % 3 at hglobalmod
  rw [hcard,← Nat.card_eq_fintype_card] at hglobalmod
  omega

end FiveTransitive.Degree67FiveTwelveExclusion

end CFSG
