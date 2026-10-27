module

public import CFSG.Permutation.FiveTransitive.Degree43ThreeGroupSmallSevenAut
public import CFSG.Permutation.FiveTransitive.ThreeGroupNineNormalizer
public import CFSG.Permutation.FiveTransitive.CoprimeCentralizerOrbit

public section

namespace CFSG

namespace FiveTransitive.ThreeGroupNineSevenNormalizer

open MulAction

private theorem eq_one
    {X : Type*} [Finite X] (hX : Nat.card X = 9)
    (Q : Subgroup (Equiv.Perm X)) (hQ : IsPGroup 3 Q)
    (htrans : IsPretransitive Q X)
    (g : Subgroup.normalizer (Q : Set (Equiv.Perm X))) (hg : g ^ 7 = 1) : g = 1 := by
  classical
  have hQbound := ThreeGroupNineNormalizer.card_le_eighty_one hX Q hQ
  have ha : Q.normalizerMonoidHom g = 1 :=
    Degree43ThreeGroupSmallSevenAut.eq_one Q hQ (hQbound.trans (by norm_num)) _
      (by rw [← map_pow,hg,map_one])
  have hcomm (q : Q) : Commute g.val q.val := by
    have hh := congrArg Subtype.val (DFunLike.congr_fun ha q)
    rw [Q.normalizerMonoidHom_apply_apply_coe] at hh
    exact (mul_inv_eq_iff_eq_mul).mp hh
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨q,hq⟩ := htrans.exists_smul_eq x (g.val • x)
  have hgp : g.val ^ 7 = 1 := congrArg Subtype.val hg
  have hcop : (orderOf q.val).Coprime (orderOf g.val) := by
    rw [Subgroup.orderOf_coe]
    exact Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hgp)
      (hQ.orderOf_coprime (by decide : Nat.Coprime 3 7) q)
  exact CoprimeCentralizerOrbit.fixed_of_commute g.val q.val (hcomm q) hcop x hq.symm

theorem perm_eq_one
    {X : Type*} [Finite X] (hX : Nat.card X = 9)
    (Q : Subgroup (Equiv.Perm X)) (hQ : IsPGroup 3 Q)
    (htrans : IsPretransitive Q X)
    (g : Equiv.Perm X) (hgN : g ∈ Subgroup.normalizer (Q : Set (Equiv.Perm X)))
    (hg : g ^ 7 = 1) : g = 1 := by
  exact congrArg Subtype.val (eq_one hX Q hQ htrans ⟨g,hgN⟩ (Subtype.ext hg))

end FiveTransitive.ThreeGroupNineSevenNormalizer

end CFSG
