module

public import CFSG.Permutation.FiveTransitive.NormalizerFixedComplement
public import CFSG.Permutation.FiveTransitive.ThreeSwapExplicitElements
public import CFSG.Permutation.FiveTransitive.ThreeSwapLocalFixedCounts

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicTwoComplementCounts

open MulAction FixedNormalizerAction

theorem free_zpowers_of_square
    {H Y : Type*} [Group H] [Finite H] [MulAction H Y]
    (x a : H) (ha : a ^ 2 = 1) (hane : a ≠ 1) (hx : x ^ 2 = a)
    (hafree : ∀ t : Y, a • t ≠ t) :
    orderOf x = 4 ∧ ∀ (q : Subgroup.zpowers x) (t : Y), q • t = t → q = 1 := by
  classical
  have hx4 : x ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hx, ha]
  have horder : orderOf x = 4 := orderOf_eq_prime_pow (p := 2) (n := 1)
    (by change x ^ 2 ≠ 1; rwa [hx]) hx4
  refine ⟨horder, ?_⟩
  intro q t hqt
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp q.property)
  have hn4 : n < 4 := by simpa only [Finset.mem_range, horder] using hn
  have hfix : x ^ n • t = t := by rw [he]; exact hqt
  have hfix2 : (x ^ n) ^ 2 • t = t := by simp only [pow_two, mul_smul, hfix]
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn' with rfl | rfl | rfl | rfl
  · apply Subtype.ext
    exact he.symm.trans (pow_zero x)
  · exact False.elim (hafree t (by simpa only [pow_one, hx] using hfix2))
  · exact False.elim (hafree t (by simpa only [hx] using hfix))
  · have he6 : (x ^ 3) ^ 2 = a := by
      rw [← pow_mul, show 3 * 2 = 4 + 2 from rfl, pow_add, hx4, one_mul, hx]
    exact False.elim (hafree t (by simpa only [he6] using hfix2))

theorem counts
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (B : Subgroup (Normalizer Q)) (hcomm : IsMulCommutative B)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (hm : B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ThreeSwapTwoGroup.subgroup e)
    (hk : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (a : Inside Q) (hane : a ≠ 1)
    (x y z : B)
    (hx : toPermHom (Normalizer Q) (Fixed (X := X) Q) x.val = Equiv.swap (e 0) (e 1))
    (hy : toPermHom (Normalizer Q) (Fixed (X := X) Q) y.val = Equiv.swap (e 2) (e 3))
    (hz : toPermHom (Normalizer Q) (Fixed (X := X) Q) z.val = Equiv.swap (e 4) (e 5))
    (hx2 : x.val ^ 2 = a.val) (hy2 : y.val ^ 2 = a.val) (hz2 : z.val ^ 2 = a.val) :
    orderOf x = 4 ∧
    (∀ (q : Subgroup.zpowers x) (t : NormalizerFixedComplement.Domain (X := X) Q),
      q • t = t → q = 1) ∧
    (∀ (g : B) (t : NormalizerFixedComplement.Domain (X := X) Q), g • t = t → g ^ 2 = 1) ∧
    (∀ g : B, g ≠ 1 →
      (fixedBy (NormalizerFixedComplement.Domain (X := X) Q) g).ncard ≤ 4) := by
  classical
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  let _ : CommGroup B := { (inferInstance : Group B) with mul_comm := isMulCommutative_iff.mp hcomm }
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let D := NormalizerFixedComplement.Domain (X := X) Q
  have hIB : Inside Q ≤ B := fun q hq => (hk.ge hq).1
  have hIsq (q : Inside Q) : q.val ^ 2 = 1 := by
    apply Subtype.ext
    have hh : (⟨q.val.val, q.property⟩ : Q) ^ 2 = 1 := by
      rw [← hQ]; exact pow_card_eq_one'
    exact congrArg (fun q : Q => q.val) hh
  let aB : B := ⟨a.val, hIB a.property⟩
  have haB2 : aB ^ 2 = 1 := Subtype.ext (hIsq a)
  have haBne : aB ≠ 1 := fun h => hane (Subtype.ext (congrArg (fun u : B => u.val) h))
  have hafree (t : D) : aB • t ≠ t := by
    intro h
    exact hane (NormalizerFixedComplement.free_inside Q hfree a t h)
  have hxsq : x ^ 2 = aB := Subtype.ext hx2
  have hysq : y ^ 2 = aB := Subtype.ext hy2
  have hzsq : z ^ 2 = aB := Subtype.ext hz2
  have hfour := free_zpowers_of_square x aB haB2 haBne hxsq hafree
  have hsquare (g : B) (t : D) (hgt : g • t = t) : g ^ 2 = 1 := by
    have hfg : f g.val ∈ ThreeSwapTwoGroup.subgroup e := hm.le ⟨g.val, g.property, rfl⟩
    have hfg2 : (f g.val) ^ 2 = 1 := congrArg Subtype.val ((ThreeSwapTwoGroup.isTwoGroup e).2 ⟨f g.val, hfg⟩)
    have hgI : g.val ^ 2 ∈ Inside Q := hk.le ⟨B.pow_mem g.property 2, by
      change f (g.val ^ 2) = 1
      rw [map_pow, hfg2]⟩
    have hfix : (⟨g.val ^ 2, hgI⟩ : Inside Q) • t = t := by
      change (g ^ 2) • t = t
      simp only [pow_two, mul_smul, hgt]
    exact Subtype.ext (congrArg (fun q : Inside Q => q.val) (NormalizerFixedComplement.free_inside Q hfree _ t hfix))
  have same_square (g w : B) (he : f g.val = f w.val) : g ^ 2 = w ^ 2 := by
    have hkq : (g * w⁻¹).val ∈ Inside Q := hk.le ⟨(g * w⁻¹).property, by
      change f (g.val * w.val⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]⟩
    have hh : (g * w⁻¹) ^ 2 = 1 := Subtype.ext (hIsq ⟨_, hkq⟩)
    rw [mul_pow, inv_pow] at hh
    exact mul_inv_eq_one.mp hh
  have nofix (g : B) (hg2 : g ^ 2 = aB) : (fixedBy D g).ncard = 0 := by
    apply (Set.ncard_eq_zero (Set.toFinite _)).mpr
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact haBne (hg2.symm.trans (hsquare g t ht))
  refine ⟨hfour.1, hfour.2, hsquare, ?_⟩
  intro g hgne
  have hgim : f g.val ∈ ThreeSwapTwoGroup.subgroup e := hm.le ⟨g.val, g.property, rfl⟩
  obtain ⟨b,c,d,hbits⟩ := ThreeSwapExplicitElements.exists_bits e ⟨f g.val, hgim⟩
  have htriple : (x * y * z) ^ 2 = aB := by rw [mul_pow, mul_pow, hxsq, hysq, hzsq, ← pow_two, haB2, one_mul]
  have hpairs := ThreeSwapLocalFixedCounts.pair_counts hseven e
  have hdouble (hh : f g.val = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) ∨
      f g.val = Equiv.swap (e 0) (e 1) * Equiv.swap (e 4) (e 5) ∨
      f g.val = Equiv.swap (e 2) (e 3) * Equiv.swap (e 4) (e 5)) : (fixedBy D g).ncard ≤ 4 := by
    by_cases hne : (fixedBy D g).Nonempty
    · obtain ⟨t, ht⟩ := hne
      have horder : orderOf g.val.val = 2 := orderOf_eq_prime
        (congrArg (fun u : B => u.val.val) (hsquare g t ht))
        (fun hh => hgne (Subtype.ext (Subtype.ext hh)))
      have hloc : (fixedBy X g.val.val ∩ fixedPoints Q X).ncard = 3 := by
        rw [← FixedNormalizerLocalCard.fixed_card Q g.val]
        rcases hh with hh | hh | hh
        · rw [hh]; exact hpairs.1
        · rw [hh]; exact hpairs.2.1
        · rw [hh]; exact hpairs.2.2
      have hsum := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X g.val.val) (fixedPoints Q X)
      have hbound := hmax g.val.val horder
      have hcount : (fixedBy D g).ncard = (fixedBy X g.val.val \ fixedPoints Q X).ncard := by
        rw [← Nat.card_coe_set_eq]
        exact NormalizerFixedComplement.fixed_card Q g.val
      omega
    · have hzero : (fixedBy D g).ncard = 0 := (Set.ncard_eq_zero (Set.toFinite _)).mpr (Set.not_nonempty_iff_eq_empty.mp hne)
      omega
  cases b <;> cases c <;> cases d <;> simp only [Bool.false_eq_true, if_false, if_true, one_mul, mul_one] at hbits
  · have hgI : g.val ∈ Inside Q := hk.le ⟨g.property, hbits⟩
    have hnil : (fixedBy D g).ncard = 0 := by
      apply (Set.ncard_eq_zero (Set.toFinite _)).mpr
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hgne (Subtype.ext (congrArg (fun q : Inside Q => q.val) (NormalizerFixedComplement.free_inside Q hfree ⟨g.val, hgI⟩ t ht)))
    rw [hnil]
    omega
  · rw [nofix g ((same_square g z (hbits.trans hz.symm)).trans hzsq)]; omega
  · rw [nofix g ((same_square g y (hbits.trans hy.symm)).trans hysq)]; omega
  · exact hdouble (Or.inr (Or.inr hbits))
  · rw [nofix g ((same_square g x (hbits.trans hx.symm)).trans hxsq)]; omega
  · exact hdouble (Or.inr (Or.inl hbits))
  · exact hdouble (Or.inl hbits)
  · have him : f g.val = f (x * y * z).val := by
      change f g.val = f (x.val * y.val * z.val)
      rw [map_mul, map_mul, hx, hy, hz]
      exact hbits
    rw [nofix g ((same_square g (x * y * z) him).trans htriple)]; omega

end FiveTransitive.CyclicTwoComplementCounts

end CFSG
