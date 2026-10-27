module

public import CFSG.Permutation.FiveTransitive.CentralizingFixedPointCongruence
public import CFSG.Permutation.FiveTransitive.Degree52FiveSylowData
public import CFSG.Permutation.FiveTransitive.FiveGroupSmallSevenAutomorphism

public section

namespace CFSG

namespace FiveTransitive.Degree52FiveFreeCore

open MulAction Subgroup SylowFixedActionCore

private theorem sylow_card_eq_one_of_seven_fixed_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 3)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) : Nat.card S = 1 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  by_contra hS
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨hF,hAlt⟩ := Degree52FiveSylowData.five_fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 7 at hF
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hfixed : Nat.card (fixedPoints Q X) = 7 := by rwa [← hfixeq]
  have hQcard := Degree52FiveGroupBound.card_le_six_hundred_twenty_five
    P hcard h5 hnotAlt Q hQ hfixed.ge
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hd : 7 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7) (by decide)
      (by rw [← Nat.card_eq_fintype_card,hF])).trans (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 7
    (hd.trans (Subgroup.card_range_dvd rho))
  have haut : Q.normalizerMonoidHom g = 1 :=
    FiveGroupSmallSevenAutomorphism.eq_one hQ hQcard _
      (by rw [← map_pow,← hg,pow_orderOf_eq_one,map_one])
  have hcomm : ∀ q : Q, g.val * q.val = q.val * g.val := by
    intro q
    have hh : g.val * q.val * g.val⁻¹ = q.val :=
      congrArg Subtype.val (DFunLike.congr_fun haut q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using
      congrArg (fun a : P => a * g.val) hh
  have hglobal := hseven g.val ((Subgroup.orderOf_coe g).trans hg)
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
  rw [hglobal] at hm5
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
  have ha : a ^ 7 = 1 := by
    funext x
    change ((rho g) ^ 7) x = x
    rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
    rfl
  have hm7 := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 7) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 7 = Fintype.card (Function.fixedPoints (rho g)) % 7 at hm7
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hm7
  omega

theorem not_dvd_five_fixer_of_seven_fixed_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 3)
    (s : Set X) (hs : s.ncard = 5) : ¬ 5 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hd
  let S : Sylow 5 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 5 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  rw [sylow_card_eq_one_of_seven_fixed_three P hcard h5 hnotAlt hseven s hs S] at hdiv
  norm_num at hdiv

end FiveTransitive.Degree52FiveFreeCore

end CFSG
