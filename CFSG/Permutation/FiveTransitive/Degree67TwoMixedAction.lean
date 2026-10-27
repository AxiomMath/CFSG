module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoMixedAction
open MulAction NormalizerOrbitFamily

@[expose] def orbitAction {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (O : orbitRel.Quotient Q X) : SubMulAction Q X where
  carrier := O.orbit
  smul_mem' := by
    intro q x hx
    rw [orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq'] at hx ⊢
    obtain ⟨r,hr⟩ := mem_orbit_iff.mp hx
    exact mem_orbit_iff.mpr ⟨q * r,by rw [mul_smul,hr]⟩

@[expose] def mixedHom {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (p : Family (X := X) Q 2) (a : Fin 4 ↪ Family (X := X) Q 4) :
    Q →* (Equiv.Perm (orbitAction Q p.val) ×
      (∀ i : Fin 4, Equiv.Perm (orbitAction Q (a i).val))) :=
  (MulAction.toPermHom Q (orbitAction Q p.val)).prod
    (MonoidHom.pi (fun i => MulAction.toPermHom Q (orbitAction Q (a i).val)))

theorem card_orbitAction {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (m : ℕ) (O : Family (X := X) Q m) :
    Nat.card (orbitAction Q O.val) = m := by
  exact O.property

theorem range_isPGroup {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (p : Family (X := X) Q 2) (a : Fin 4 ↪ Family (X := X) Q 4) :
    IsPGroup 2 (mixedHom Q p a).range := by
  exact hQ.of_surjective (mixedHom Q p a).rangeRestrict (mixedHom Q p a).rangeRestrict_surjective

theorem range_card_le {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (p : Family (X := X) Q 2) (a : Fin 4 ↪ Family (X := X) Q 4) :
    Nat.card (mixedHom Q p a).range ≤ 8192 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp (range_isPGroup Q hQ p a)
  have hd := Subgroup.card_subgroup_dvd_card (mixedHom Q p a).range
  rw [Nat.card_prod,Nat.card_perm,card_orbitAction,Nat.card_pi] at hd
  simp only [Nat.card_perm,card_orbitAction,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hd
  rw [he] at hd
  have he13 : e ≤ 13 := by
    by_contra hn
    have h16384 : 16384 ∣ 2 ^ e := pow_dvd_pow 2 (by omega : 14 ≤ e)
    have hh := h16384.trans hd
    norm_num [Nat.factorial] at hh
  rw [he]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) he13

end FiveTransitive.Degree67TwoMixedAction

end CFSG
