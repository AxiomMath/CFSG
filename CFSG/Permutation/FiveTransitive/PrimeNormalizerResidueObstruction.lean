module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.CentralizingFixedPointCongruence
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG

namespace FiveTransitive.PrimeNormalizerResidueObstruction

open MulAction FixedNormalizerAction

theorem perm_fixed_card_modEq
    {Y : Type*} [Finite Y] {q : ℕ} [Fact q.Prime]
    (a : Equiv.Perm Y) (ha : a ^ q = 1) :
    Nat.card Y ≡ Nat.card (Function.fixedPoints a) [MOD q] := by
  classical
  let _ : Fintype Y := Fintype.ofFinite Y
  let f : Function.End Y := a.toFun
  have hf : f ^ q = 1 := by
    funext y
    change (a ^ q) y = y
    rw [ha]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := q) (n := 1)
    (by simpa only [pow_one] using hf)
  change Fintype.card Y % q = Fintype.card (Function.fixedPoints a) % q at hm
  change Nat.card Y % q = Nat.card (Function.fixedPoints a) % q
  simpa only [Nat.card_eq_fintype_card] using hm

private theorem centralizes
    {G : Type*} [Group G] [Finite G]
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (Q : Subgroup G) (hQcard : Nat.card Q = p) (haut : ¬ q ∣ p - 1)
    (z : Normalizer Q) (hz : z ^ q = 1) :
    ∀ u : Q, z.val * u.val = u.val * z.val := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact q.Prime := ⟨hq⟩
  let _ : IsCyclic Q := isCyclic_of_prime_card hQcard
  have hAut : Nat.card (MulAut Q) = p - 1 := by
    rw [IsCyclic.card_mulAut Q,hQcard,Nat.totient_prime hp]
  have ha : Q.normalizerMonoidHom z = 1 := by
    by_contra hn
    have hpow : Q.normalizerMonoidHom z ^ q = 1 := by
      rw [← map_pow,hz,map_one]
    have ho : orderOf (Q.normalizerMonoidHom z) = q := orderOf_eq_prime hpow hn
    apply haut
    rw [← hAut,← ho]
    exact orderOf_dvd_natCard _
  intro u
  have hh := congrArg (fun f : MulAut Q => (f u).val) ha
  rw [Q.normalizerMonoidHom_apply_apply_coe] at hh
  exact (mul_inv_eq_iff_eq_mul).mp hh

theorem excluded
    {X : Type*} [Finite X]
    (P : Subgroup (Equiv.Perm X))
    (p q r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : q.Prime) (hqr : q ≤ r) (hr4 : r ≤ 4)
    (Q : Subgroup P) (hQcard : Nat.card Q = p)
    (hfixed : Nat.card (Fixed (X := X) Q) = r)
    (himage : Image (X := X) Q = ⊤)
    (haut : ¬ q ∣ p - 1)
    (hglobal : ∀ z : P, orderOf z = q →
      Nat.card (Function.fixedPoints z.val) ≤ 4)
    (hmod : Nat.card X % q ≠ r % q) : False := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact q.Prime := ⟨hq⟩
  let F := Fixed (X := X) Q
  let N := Normalizer Q
  let rho := toPermHom N F
  have hd : q ∣ Nat.card rho.range := by
    change q ∣ Nat.card (Image (X := X) Q)
    rw [himage,Subgroup.card_top,Nat.card_perm,hfixed]
    exact Nat.dvd_factorial hq.pos hqr
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) q
    (hd.trans (Subgroup.card_range_dvd rho))
  have hzpow : z ^ q = 1 := hz ▸ pow_orderOf_eq_one z
  have hcomm := centralizes p q hp hq Q hQcard haut z hzpow
  have hQ : IsPGroup p Q := IsPGroup.of_card (n := 1) (by simpa using hQcard)
  let a := rho z
  have hapow : a ^ q = 1 := by rw [← map_pow,hzpow,map_one]
  have hzP : orderOf z.val = q := (Subgroup.orderOf_coe z).trans hz
  have hzX : z.val.val ^ q = 1 := by
    have hh : z.val ^ q = 1 := hzP ▸ pow_orderOf_eq_one z.val
    exact congrArg Subtype.val hh
  let E : Function.fixedPoints a ≃ {x : F // z.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hm := CentralizingFixedPointCongruence.card_modEq P Q hQ z.val hcomm
  rw [← fixed_eq Q] at hm
  change Nat.card (Function.fixedPoints z.val.val) % p =
    Nat.card {x : F // z.val.val x.val = x.val} % p at hm
  rw [← Nat.card_congr E] at hm
  have hl : Nat.card (Function.fixedPoints a) ≤ r := by
    rw [← hfixed]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hg := hglobal z.val hzP
  have heq : Nat.card (Function.fixedPoints z.val.val) =
      Nat.card (Function.fixedPoints a) := by
    rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at hm
    exact hm
  have hmX := perm_fixed_card_modEq z.val.val hzX
  have hmF := perm_fixed_card_modEq a hapow
  change Nat.card X % q = Nat.card (Function.fixedPoints z.val.val) % q at hmX
  change Nat.card F % q = Nat.card (Function.fixedPoints a) % q at hmF
  rw [hfixed] at hmF
  exact hmod (hmX.trans ((congrArg (· % q) heq).trans hmF.symm))

end FiveTransitive.PrimeNormalizerResidueObstruction

end CFSG
