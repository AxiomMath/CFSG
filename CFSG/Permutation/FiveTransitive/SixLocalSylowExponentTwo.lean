module

public import CFSG.Permutation.FiveTransitive.FourCycleFixer
public import CFSG.Permutation.FiveTransitive.NormalizerInvariantSylow
public import CFSG.Permutation.FiveTransitive.SixFixedNormalizerSquare

public section

namespace CFSG

namespace FiveTransitive.SixLocalSylowExponentTwo

open MulAction FixedSetNormalizerPerm

@[expose] def EvenSixLocal
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] : Prop :=
  ∀ (s : Set X), s.ncard = 4 → ∀ S : Sylow 2 (fixingSubgroup G s),
    let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
    (fixedPoints Q X).ncard = 6 ∧
    ∀ (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)),
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPerm G X Q a ha).sign = 1

private theorem orderOf_ne_four
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hlocal : EvenSixLocal G X) (Q : Subgroup G)
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1)
    (a : Q) : orderOf a ≠ 4 := by
  intro ha4
  have haG : orderOf (a : G) = 4 := (Subgroup.orderOf_coe a).trans ha4
  have hpow4 : (a : G) ^ 4 = 1 := by rw [← haG]; exact pow_orderOf_eq_one _
  have hpow2 : a ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ha4] at hd
    norm_num at hd
  have hnoNew : ∀ x : X, (a : G) ^ 2 • x = x → (a : G) • x = x := by
    intro x hx
    have hfix : x ∈ fixedPoints Q X := by
      by_contra hn
      exact hpow2 (hfree (a ^ 2) x hn hx)
    exact mem_fixedPoints.mp hfix a
  have hex : ∃ x : X, (a : G) ^ 2 • x ≠ x := by
    by_contra! hn
    have h : (a : G) ^ 2 = 1 := FaithfulSMul.eq_of_smul_eq_smul (α := X)
      (by intro x; simpa only [one_smul] using hn x)
    apply hpow2
    apply Subtype.ext
    exact h
  obtain ⟨x, hx⟩ := hex
  obtain ⟨s, hs, hxs, hnorm⟩ := FourCycleFixer.exists_four_set G X (a : G) hpow4 x hx
  obtain ⟨S, hS⟩ := NormalizerInvariantSylow.exists_of_order_pow 2 G
    (fixingSubgroup G s) (a : G) hnorm 2 (by simpa using haG)
  let R := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
  obtain ⟨hcard, heven⟩ := hlocal s hs S
  have hxR : x ∈ fixedPoints R X := by
    rw [mem_fixedPoints]
    intro q
    obtain ⟨r, hr, hqr⟩ := Subgroup.mem_map.mp q.property
    change (q : G) • x = x
    rw [← hqr]
    exact (mem_fixingSubgroup_iff G).mp r.property x hxs
  exact hx (SixFixedNormalizerSquare.square_fixes_common_fixed_set G X R
    (a : G) hS hcard hpow4 hnoNew (heven (a : G) hS) x hxR)

private theorem square_eq_one_of_no_order_four
    (Q : Type*) [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (hno4 : ∀ q : Q, orderOf q ≠ 4) (q : Q) : q ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ q
  have hklt : k < 2 := by
    by_contra hn
    have hd : 4 ∣ orderOf q := by
      rw [hk]
      exact Nat.pow_dvd_pow 2 (by omega : 2 ≤ k)
    exact hno4 (q ^ (orderOf q / 4))
      (orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos q)) hd)
  have hd : orderOf q ∣ 2 := by
    rw [hk]
    have hk1 : k ≤ 1 := by omega
    exact Nat.pow_dvd_pow 2 hk1
  exact orderOf_dvd_iff_pow_eq_one.mp hd

theorem square_eq_one_and_commute
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hlocal : EvenSixLocal G X) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1) :
    (∀ q : Q, q * q = 1) ∧ (∀ q r : Q, q * r = r * q) := by
  have hsq (q : Q) : q * q = 1 := by
    simpa only [pow_two] using square_eq_one_of_no_order_four Q hQ
      (orderOf_ne_four G X hlocal Q hfree) q
  refine ⟨hsq, ?_⟩
  have hinv (q : Q) : q = q⁻¹ := eq_inv_iff_mul_eq_one.mpr (hsq q)
  intro q r
  calc
    q * r = (q * r)⁻¹ := hinv (q * r)
    _ = r⁻¹ * q⁻¹ := mul_inv_rev q r
    _ = r * q := by rw [← hinv q, ← hinv r]

end FiveTransitive.SixLocalSylowExponentTwo

end CFSG
