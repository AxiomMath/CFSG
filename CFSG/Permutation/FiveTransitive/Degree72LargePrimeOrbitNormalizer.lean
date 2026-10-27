module

public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeOrbitImage
public import CFSG.Permutation.FiveTransitive.CoprimeCentralizerOrbit
public import Mathlib.GroupTheory.Perm.Subgroup

public section

namespace CFSG

namespace FiveTransitive.Degree72LargePrimeOrbitNormalizer
open MulAction

theorem perm_eq_one
    {X : Type*} [Finite X]
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p.Coprime q)
    (hqpred : ¬ q ∣ p - 1) (hX : Nat.card X ≤ p)
    (T : Subgroup (Equiv.Perm X)) (hT : IsPGroup p T)
    (htrans : IsPretransitive T X)
    (g : Equiv.Perm X) (hgN : g ∈ Subgroup.normalizer (T : Set (Equiv.Perm X)))
    (hg : g ^ q = 1) : g = 1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card T ∣ p := by
    have h := Degree72LargePrimeOrbitImage.image_card_dvd_prime p hp hT hX
    have he := Equiv.Perm.subgroupOfMulAction T X
    rwa [← Nat.card_congr he.toEquiv] at h
  let _ : IsCyclic T := isCyclic_of_card_dvd_prime hcard
  have haut : ¬ q ∣ Nat.card (MulAut T) := by
    rw [IsCyclic.card_mulAut T]
    rcases hp.eq_one_or_self_of_dvd _ hcard with hc | hc
    · rw [hc,Nat.totient_one]
      exact hq.not_dvd_one
    · rw [hc,Nat.totient_prime hp]
      exact hqpred
  let a := T.normalizerMonoidHom ⟨g,hgN⟩
  have ha : a = 1 := by
    have haq : a ^ q = 1 := by
      rw [← map_pow,show (⟨g,hgN⟩ : Subgroup.normalizer (T : Set (Equiv.Perm X))) ^ q = 1 from Subtype.ext hg,map_one]
    by_contra hn
    exact haut ((orderOf_eq_prime haq hn) ▸ orderOf_dvd_natCard a)
  have hcomm (t : T) : Commute g t.val := by
    have hh := congrArg (fun f : MulAut T => (f t).val) ha
    change (T.normalizerMonoidHom ⟨g,hgN⟩ t : Equiv.Perm X) = t.val at hh
    rw [T.normalizerMonoidHom_apply_apply_coe] at hh
    exact (mul_inv_eq_iff_eq_mul).mp hh
  apply Equiv.ext
  intro x
  obtain ⟨t,ht⟩ := htrans.exists_smul_eq x (g x)
  have hcop : (orderOf t.val).Coprime (orderOf g) := by
    rw [Subgroup.orderOf_coe]
    exact Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hg) (hT.orderOf_coprime hpq t)
  exact CoprimeCentralizerOrbit.fixed_of_commute g t.val (hcomm t) hcop x ht.symm

end FiveTransitive.Degree72LargePrimeOrbitNormalizer

end CFSG
