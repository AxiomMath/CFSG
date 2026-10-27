module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.NormalizerRigidOrbitResidueSum
open MulAction NormalizerOrbitFamily
open scoped BigOperators

theorem sum_le
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (p : ℕ) [Fact p.Prime] (Q : Subgroup G)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ p = 1)
    (s : Finset ℕ)
    (hfix : ∀ m ∈ s, ∀ O : Family (X := X) Q m,
      NormalizerOrbitFamily.toPermHom (X := X) Q m g O = O →
      ∀ x : O.val.orbit, g.val • x.val = x.val) :
    (∑ m ∈ s, m * (Nat.card (Family (X := X) Q m) % p)) ≤ Nat.card (fixedBy X g.val) := by
  classical
  let B (m : s) := Family (X := X) Q m.val
  let sigma (m : s) := NormalizerOrbitFamily.toPermHom (X := X) Q m.val
  let Z (m : s) := Function.fixedPoints (sigma m g)
  let e (m : s) (O : Z m) : Fin m.val ↪ O.val.val.orbit :=
    (Fin.castLEEmb O.val.property.ge).trans (Finite.equivFin _).symm.toEmbedding
  let f : (Σ m : s, Z m × Fin m.val) → fixedBy X g.val := fun t =>
    ⟨(e t.1 t.2.1 t.2.2).val,
      hfix t.1.val t.1.property t.2.1.val t.2.1.property (e t.1 t.2.1 t.2.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hpoint := congrArg Subtype.val hab
    have ha : (Quotient.mk'' (f a).val : orbitRel.Quotient Q X) = a.2.1.val.val :=
      orbitRel.Quotient.mem_orbit.mp (e a.1 a.2.1 a.2.2).property
    have hb : (Quotient.mk'' (f b).val : orbitRel.Quotient Q X) = b.2.1.val.val :=
      orbitRel.Quotient.mem_orbit.mp (e b.1 b.2.1 b.2.2).property
    have horb := ha.symm.trans ((congrArg Quotient.mk'' hpoint).trans hb)
    have hm : a.1 = b.1 := Subtype.ext (a.2.1.val.property.symm.trans
      ((congrArg (fun O : orbitRel.Quotient Q X => Nat.card O.orbit) horb).trans b.2.1.val.property))
    rcases a with ⟨m,a,i⟩
    rcases b with ⟨n,b,j⟩
    dsimp only at hm
    subst n
    have he : a = b := Subtype.ext (Subtype.ext horb)
    subst b
    have hij : i = j := (e m a).injective (Subtype.ext hpoint)
    subst j
    rfl
  have hmod (m : s) : Nat.card (B m) % p ≤ Nat.card (Z m) := by
    let _ : Fintype (B m) := Fintype.ofFinite _
    let a : Function.End (B m) := (sigma m g).toFun
    have ha : a ^ p = 1 := by
      funext x
      change ((sigma m g) ^ p) x = x
      rw [← map_pow,hg,map_one]
      rfl
    have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := p) (n := 1)
      (by simpa only [pow_one] using ha)
    change Fintype.card (B m) % p = Fintype.card (Z m) % p at hm
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card] at hm
    rw [hm]
    exact Nat.mod_le _ _
  have hprod := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sigma] at hprod
  simp only [Nat.card_prod,Nat.card_fin] at hprod
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun m _ =>
    Nat.mul_le_mul_left m.val (hmod m))
  have hsum : (∑ m : s, m.val * (Nat.card (B m) % p)) ≤ Nat.card (fixedBy X g.val) :=
    hle.trans (by simpa only [Nat.mul_comm] using hprod)
  change (∑ m : s, m.val * (Nat.card (Family (X := X) Q m.val) % p)) ≤
    Nat.card (fixedBy X g.val) at hsum
  rw [Finset.sum_coe_sort s (fun m : ℕ => m * (Nat.card (Family (X := X) Q m) % p))] at hsum
  exact hsum

end FiveTransitive.NormalizerRigidOrbitResidueSum

end CFSG
