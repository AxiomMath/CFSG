module

public import CFSG.Permutation.FiveTransitive.Degree28SmallTwoFiveOrbit
public import CFSG.Permutation.FiveTransitive.Degree28SmallTwoFiveFixed
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree28SmallTwoFiveCentralization

open MulAction FixedNormalizerAction

theorem centralizes
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q) (hQcard : Nat.card Q ≤ 16)
    (hsix : Nat.card (Fixed (X := X) Q) = 6)
    (z : Normalizer Q) (hz : orderOf z = 5)
    (hrho : toPermHom (Normalizer Q) (Fixed (X := X) Q) z ≠ 1) :
    Q.normalizerMonoidHom z = 1 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  by_contra hnontriv
  let N := Normalizer Q
  let _ : MulDistribMulAction N Q := MulDistribMulAction.compHom Q Q.normalizerMonoidHom
  let A := Subgroup.zpowers z
  have hA : IsPGroup 5 A := IsPGroup.iff_card.mpr ⟨1,by
    rw [Nat.card_zpowers,hz,pow_one]⟩
  have hmove : ∃ a : A, ∃ q : Q, a • q ≠ q := by
    have hm : ∃ q : Q, Q.normalizerMonoidHom z q ≠ q := by
      by_contra hn
      push Not at hn
      apply hnontriv
      apply DFunLike.ext
      intro q
      exact hn q
    obtain ⟨q,hq⟩ := hm
    exact ⟨⟨z,Subgroup.mem_zpowers z⟩,q,hq⟩
  have hcompat : ∀ (a : A) (q : Q) (x : X), a • (q • x) = (a • q) • (a • x) := by
    intro a q x
    change a.val.val • ((q : P) • x) =
      (Q.normalizerMonoidHom a.val q : P) • (a.val.val • x)
    rw [Q.normalizerMonoidHom_apply_apply_coe,mul_smul,mul_smul,inv_smul_smul]
  have hsmall := Degree28SmallTwoFiveOrbit.exterior_fixed_subsingleton hA hQ hQcard
    hmove hcompat (by rw [Nat.card_eq_fintype_card,hcard]; norm_num)
  have hfixed : fixedPoints A X = Function.fixedPoints z.val.val := by
    ext x
    constructor
    · intro hx
      exact hx (⟨z,Subgroup.mem_zpowers z⟩ : A)
    · intro hx a
      have hzmem : z ∈ stabilizer N x := hx
      exact (Subgroup.zpowers_le.mpr hzmem) a.property
  rw [hfixed] at hsmall
  have hout : (Function.fixedPoints z.val.val \ fixedPoints Q X).ncard ≤ 1 :=
    Set.ncard_le_one_iff_subsingleton.mpr hsmall
  have hglobal := Degree28SmallTwoFiveFixed.global_fixed_eq_three P hcard h5 hnotAlt
    z.val ((Subgroup.orderOf_coe z).trans hz)
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite F
  let rho := toPermHom (Normalizer Q) F
  have hzpow : z ^ 5 = 1 := by rw [← hz,pow_orderOf_eq_one]
  have hrhoorder : orderOf (rho z) = 5 := orderOf_eq_prime
    (by rw [← map_pow,hzpow,map_one]) hrho
  have hlocal := Degree28SmallTwoFiveFixed.local_fixed_eq_one
    (by rw [← Nat.card_eq_fintype_card]; exact hsix) (rho z) hrhoorder
  let E : ↥(Function.fixedPoints z.val.val ∩ fixedPoints Q X) ≃ Function.fixedPoints (rho z) :=
    { toFun := fun x => ⟨⟨x.val,by change x.val ∈ Fixed (X := X) Q; rw [fixed_eq]; exact x.property.2⟩,Subtype.ext x.property.1⟩
      invFun := fun x => ⟨x.val.val,congrArg Subtype.val x.property,by
        rw [← fixed_eq Q]; exact x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hinter : (Function.fixedPoints z.val.val ∩ fixedPoints Q X).ncard = 1 := by
    rw [← Nat.card_coe_set_eq,Nat.card_congr E,hlocal]
  have hsum := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (Function.fixedPoints z.val.val) (fixedPoints Q X)
  rw [Nat.card_coe_set_eq] at hglobal
  rw [hinter,hglobal] at hsum
  omega

end FiveTransitive.Degree28SmallTwoFiveCentralization

end CFSG
