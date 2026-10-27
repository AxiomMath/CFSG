module

public import CFSG.Permutation.FiveTransitive.NormalizerLargeOrbit
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree52ThreeLargeOrbit

open MulAction

private theorem large_orbit_card_le_five
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (hX : Nat.card X ≤ 52) :
    Nat.card {O : orbitRel.Quotient Q X // 9 ≤ Nat.card O.orbit} ≤ 5 := by
  classical
  let B := {O : orbitRel.Quotient Q X // 9 ≤ Nat.card O.orbit}
  let e (b : B) : Fin 9 ↪ b.val.orbit :=
    (Fin.castLEEmb b.property).trans (Finite.equivFin b.val.orbit).symm.toEmbedding
  let f : B × Fin 9 → X := fun p => (e p.1 p.2).val
  have hf : Function.Injective f := by
    intro a b hab
    have ha : (Quotient.mk'' (f a) : orbitRel.Quotient Q X) = a.1.val :=
      orbitRel.Quotient.mem_orbit.mp (e a.1 a.2).property
    have hb : (Quotient.mk'' (f b) : orbitRel.Quotient Q X) = b.1.val :=
      orbitRel.Quotient.mem_orbit.mp (e b.1 b.2).property
    have he : a.1 = b.1 := Subtype.ext (ha.symm.trans ((congrArg Quotient.mk'' hab).trans hb))
    rcases a with ⟨a,i⟩
    rcases b with ⟨b,j⟩
    dsimp only at he
    subst b
    have hij : i = j := (e a).injective (Subtype.ext hab)
    subst j
    rfl
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,Nat.card_fin] at hh
  change Nat.card B ≤ 5
  omega

theorem fixes_large_orbit
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (hX : Nat.card X ≤ 52)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 7 = 1)
    (O : orbitRel.Quotient Q X) (hO : 9 ≤ Nat.card O.orbit) :
    NormalizerOrbitHom.toPermHom (Y := X) Q g O = O := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let B := {O : orbitRel.Quotient Q X // 9 ≤ Nat.card O.orbit}
  let f := NormalizerOrbitHom.toPermHom (Y := X) Q
  let a : Equiv.Perm B := (f g).subtypePerm (by
    intro o
    rw [NormalizerLargeOrbit.card_orbit_eq])
  have hpow (n : ℕ) (b : B) : ((a ^ n) b).val = (f g ^ n) b.val := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply,pow_succ',Equiv.Perm.mul_apply]
      change f g (((a ^ n) b).val) = _
      rw [ih]
  have ha5 : a ^ 7 = 1 := by
    apply Equiv.ext
    intro b
    apply Subtype.ext
    rw [hpow,← map_pow,hg,map_one]
    rfl
  have hB : Nat.card B ≤ 5 := large_orbit_card_le_five Q hX
  have haone : a = 1 := by
    by_contra hn
    have ho : orderOf a = 7 := orderOf_eq_prime ha5 hn
    have hd : 7 ∣ (Nat.card B).factorial := by
      rw [← Nat.card_perm]
      exact ho ▸ orderOf_dvd_natCard a
    have hh := hd.trans (Nat.factorial_dvd_factorial hB)
    norm_num [Nat.factorial] at hh
  exact congrArg (fun b : Equiv.Perm B => (b ⟨O,hO⟩).val) haone

end FiveTransitive.Degree52ThreeLargeOrbit

end CFSG
