module

public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG

namespace FiveTransitive.AbelianSixteenExceptionalOrbit

open MulAction

private theorem orbit_card_four
    {G Y : Type*} [CommGroup G] [Finite G] [Finite Y] [MulAction G Y]
    (x : G) (hx : orderOf x = 4)
    (hfree : ∀ (q : Subgroup.zpowers x) (t : Y), q • t = t → q = 1)
    (hbound : ∀ g : G, g ≠ 1 → (fixedBy Y g).ncard ≤ 4)
    (u : G) (hu : u ≠ 1) (t : Y) (hut : u • t = t) :
    (orbit G t).ncard = 4 := by
  let f : Subgroup.zpowers x → orbit G t := fun q =>
    ⟨q.val • t, mem_orbit_iff.mpr ⟨q.val, rfl⟩⟩
  have hf : Function.Injective f := by
    intro q r he
    have h : q • t = r • t := congrArg Subtype.val he
    have hi : (r⁻¹ * q) • t = t := by rw [mul_smul, h, inv_smul_smul]
    exact (inv_mul_eq_one.mp (hfree _ t hi)).symm
  have hlo := Nat.card_le_card_of_injective f hf
  have hcard : Nat.card (Subgroup.zpowers x) = 4 := by
    rw [Nat.card_zpowers, hx]
  rw [hcard, Nat.card_coe_set_eq] at hlo
  have hsub : orbit G t ⊆ fixedBy Y u := by
    intro z hz
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hz
    change u • (g • t) = g • t
    rw [← mul_smul, mul_comm u g, mul_smul, hut]
  have hhi := (Set.ncard_le_ncard hsub).trans (hbound u hu)
  omega

private theorem unique_nonfree_orbit
    {G Y : Type*} [CommGroup G] [Finite G] [Finite Y] [MulAction G Y]
    (hG : Nat.card G = 16) (x : G) (hx : orderOf x = 4)
    (hfree : ∀ (q : Subgroup.zpowers x) (t : Y), q • t = t → q = 1)
    (hsquare : ∀ (g : G) (t : Y), g • t = t → g ^ 2 = 1)
    (hbound : ∀ g : G, g ≠ 1 → (fixedBy Y g).ncard ≤ 4)
    (u v : G) (hu : u ≠ 1) (hv : v ≠ 1)
    (s t : Y) (hus : u • s = s) (hvt : v • t = t) :
    orbit G s = orbit G t := by
  classical
  have hs := orbit_card_four x hx hfree hbound u hu s hus
  have ht := orbit_card_four x hx hfree hbound v hv t hvt
  rcases (orbit.eq_or_disjoint (G := G) s t) with he | hd
  · exact he
  exfalso
  have hcard (z : Y) (hz : (orbit G z).ncard = 4) :
      Nat.card (stabilizer G z) = 4 := by
    let _ : Fintype G := Fintype.ofFinite _
    let _ : Fintype (orbit G z) := Fintype.ofFinite _
    let _ : Fintype (stabilizer G z) := Fintype.ofFinite _
    have h := card_orbit_mul_card_stabilizer_eq_card_group G z
    simp only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hz, hG] at h
    omega
  have hinf (g : G) (hgs : g • s = s) (hgt : g • t = t) : g = 1 := by
    by_contra hn
    have hsub : orbit G s ∪ orbit G t ⊆ fixedBy Y g := by
      intro z hz
      rcases hz with hz | hz
      · obtain ⟨k, rfl⟩ := mem_orbit_iff.mp hz
        change g • (k • s) = k • s
        rw [← mul_smul, mul_comm g k, mul_smul, hgs]
      · obtain ⟨k, rfl⟩ := mem_orbit_iff.mp hz
        change g • (k • t) = k • t
        rw [← mul_smul, mul_comm g k, mul_smul, hgt]
    have hle := (Set.ncard_le_ncard hsub).trans (hbound g hn)
    rw [Set.ncard_union_eq hd, hs, ht] at hle
    omega
  let f : stabilizer G s × stabilizer G t → G := fun p => p.1.val * p.2.val
  have hf : Function.Injective f := by
    rintro ⟨a,b⟩ ⟨c,d⟩ he
    change a.val * b.val = c.val * d.val at he
    have he' : c.val⁻¹ * a.val = d.val * b.val⁻¹ := by
      calc
        c.val⁻¹ * a.val = c.val⁻¹ * (a.val * b.val) * b.val⁻¹ := by group
        _ = d.val * b.val⁻¹ := by rw [he]; group
    have heq : c.val⁻¹ * a.val = 1 := hinf _
      (by change (c⁻¹ * a).val • s = s; exact (c⁻¹ * a).property)
      (by rw [he']; change (d * b⁻¹).val • t = t; exact (d * b⁻¹).property)
    have hac : a = c := Subtype.ext (inv_mul_eq_one.mp heq).symm
    have hbd : b = d := Subtype.ext (mul_left_cancel (by simpa only [hac] using he))
    exact Prod.ext hac hbd
  have hsur : Function.Surjective f := (hf.bijective_of_nat_card_le (by
    rw [Nat.card_prod, hcard s hs, hcard t ht, hG])).surjective
  obtain ⟨⟨a,b⟩, hab⟩ := hsur x
  have hx2 : x ^ 2 = 1 := by
    rw [← hab]
    change (a.val * b.val) ^ 2 = 1
    rw [mul_pow, hsquare a.val s a.property, hsquare b.val t b.property, one_mul]
  have hh := orderOf_dvd_of_pow_eq_one hx2
  rw [hx] at hh
  norm_num at hh

theorem semiregular_off_fixed
    {G Y : Type*} [CommGroup G] [Finite G] [Finite Y] [MulAction G Y]
    (hG : Nat.card G = 16) (x : G) (hx : orderOf x = 4)
    (hfree : ∀ (q : Subgroup.zpowers x) (t : Y), q • t = t → q = 1)
    (hsquare : ∀ (g : G) (t : Y), g • t = t → g ^ 2 = 1)
    (hbound : ∀ g : G, g ≠ 1 → (fixedBy Y g).ncard ≤ 4)
    (u : G) (hu : u ≠ 1) (hfour : (fixedBy Y u).ncard = 4) :
    ∀ (g : G) (t : Y), t ∉ fixedBy Y u → g • t = t → g = 1 := by
  obtain ⟨s, hs⟩ := Set.nonempty_of_ncard_ne_zero (by omega : (fixedBy Y u).ncard ≠ 0)
  intro g t ht hgt
  by_contra hg
  have he := unique_nonfree_orbit hG x hx hfree hsquare hbound u g hu hg s t hs hgt
  have hmem : t ∈ orbit G s := he.symm ▸ mem_orbit_self t
  obtain ⟨k, hk⟩ := mem_orbit_iff.mp hmem
  apply ht
  change u • t = t
  rw [← hk, ← mul_smul, mul_comm u k, mul_smul, hs]

end FiveTransitive.AbelianSixteenExceptionalOrbit

end CFSG
