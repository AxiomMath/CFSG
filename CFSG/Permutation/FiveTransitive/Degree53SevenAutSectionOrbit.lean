module

public import CFSG.Permutation.FiveTransitive.NormalizerLargeOrbit
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.Degree53SevenAutSectionOrbit

open MulAction Subgroup

private theorem normalizer_preserves
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (x : X) (hx : Nat.card (orbit Q x) = 16)
    (hsmall : ∀ y : X, y ∉ orbit Q x → Nat.card (orbit Q y) ≤ 2)
    (g : normalizer (Q : Set G)) (y : X) (hy : y ∈ orbit Q x) :
    g.val • y ∈ orbit Q x := by
  let f := NormalizerOrbitHom.toPermHom (Y := X) Q g
  have hgx : g.val • x ∈ orbit Q x := by
    have hc := NormalizerLargeOrbit.card_orbit_eq Q g (Quotient.mk'' x)
    change Nat.card (orbit Q (g.val • x)) = Nat.card (orbit Q x) at hc
    by_contra hn
    have hh := hsmall (g.val • x) hn
    omega
  have he : f (Quotient.mk'' x) = Quotient.mk'' x := Quotient.sound hgx
  exact Quotient.exact ((congrArg f (Quotient.sound hy)).trans he)

theorem centralizer_prime_free
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (Q : Subgroup P)
    (x : X) (hx : Nat.card (orbit Q x) = 16)
    (hsmall : ∀ y : X, y ∉ orbit Q x → Nat.card (orbit Q y) ≤ 2)
    {p : ℕ} [Fact p.Prime] (hp16 : ¬ p ∣ 16)
    (hglobal : ∀ g : P, orderOf g = p → Nat.card (Function.fixedPoints g.val) < 16) :
    ¬ p ∣ Nat.card (centralizer (Q : Set P)) := by
  classical
  intro hd
  let C := centralizer (Q : Set P)
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := C) p hd
  let O : SubMulAction C X :=
    { carrier := orbit Q x
      smul_mem' := by
        intro z y hy
        exact normalizer_preserves Q x hx hsmall
          ⟨z.val,centralizer_le_normalizer (Q : Set P) z.property⟩ y hy }
  have hO : Nat.card O = 16 := hx
  let A := zpowers c
  have hA : IsPGroup p A := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hc,pow_one])
  have hm : Nat.card O % p = Nat.card (fixedPoints A O) % p := hA.card_modEq_card_fixedPoints O
  have hne : Nat.card (fixedPoints A O) ≠ 0 := by
    intro he
    rw [hO,he,Nat.zero_mod] at hm
    exact hp16 (Nat.dvd_of_mod_eq_zero hm)
  let y : fixedPoints A O := Classical.choice
    (Finite.card_pos_iff.mp (Nat.pos_of_ne_zero hne))
  have hcy : c.val • y.val.val = y.val.val :=
    congrArg Subtype.val (y.property ⟨c,mem_zpowers c⟩)
  obtain ⟨q,hq⟩ := mem_orbit_iff.mp y.val.property
  change q.val • x = y.val.val at hq
  have hcx : c.val • x = x := by
    apply (toPerm q.val).injective
    change q.val • (c.val • x) = q.val • x
    calc
      q.val • (c.val • x) = c.val • (q.val • x) := by
        rw [← mul_smul,← mul_smul,c.property q.val q.property]
      _ = q.val • x := by rw [hq]; exact hcy
  have hfix : ∀ w ∈ orbit Q x, c.val • w = w := by
    intro w hw
    obtain ⟨r,hr⟩ := mem_orbit_iff.mp hw
    rw [← hr]
    change c.val • (r.val • x) = r.val • x
    rw [← mul_smul,← c.property r.val r.property,mul_smul,hcx]
  let f : O → Function.fixedPoints c.val.val := fun w => ⟨w.val,hfix w.val w.property⟩
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun z : Function.fixedPoints c.val.val => z.val) he)
  have hle := Nat.card_le_card_of_injective f hf
  have hlt := hglobal c.val ((Subgroup.orderOf_coe c).trans hc)
  omega

end FiveTransitive.Degree53SevenAutSectionOrbit

end CFSG
