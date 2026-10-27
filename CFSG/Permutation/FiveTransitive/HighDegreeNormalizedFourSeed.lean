module

public import CFSG.Permutation.FiveTransitive.InvolutionTwoOrbitFourSet
public import CFSG.Permutation.FiveTransitive.HighDegreeCommutingInvolution
public import CFSG.Permutation.FiveTransitive.CommutingFourSeed
public import CFSG.Permutation.FiveTransitive.SetwisePGroupSylowCorrection
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

open scoped Pointwise

namespace FiveTransitive.HighDegreeNormalizedFourSeed

open MulAction FixedNormalizerAction

private theorem exists_of_involution
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (y : X), y ∉ fixedPoints Q X → q • y = y → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (a : Q) (ha : orderOf a.val = 2) :
    ∃ n : Normalizer Q, orderOf n.val = 2 ∧ n.val ∉ Q ∧
      4 ≤ (fixedBy X n.val \ fixedPoints Q X).ncard ∧
      (fixedBy X n.val ∩ fixedPoints Q X).ncard ≤ 3 ∧
      ∃ T : Set X, T.ncard = 4 ∧ T ⊆ (fixedPoints Q X)ᶜ ∧
        ∀ y ∈ T, n.val • y = y := by
  have ha2 : a.val ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a.val
  have hfixa : fixedPoints Q X = fixedBy X a.val := by
    ext y
    constructor
    · intro hy
      exact hy a
    · intro hy
      by_contra hout
      have he : a.val = 1 := congrArg Subtype.val (hfree a y hout hy)
      rw [he, orderOf_one] at ha
      omega
  have hFcard : (fixedBy X a.val).ncard = 7 := by
    rw [← hfixa, ← Nat.card_coe_set_eq]
    exact hseven
  obtain ⟨T, hTcard, hTout, hTstable⟩ := InvolutionTwoOrbitFourSet.exists_set a.val ha2 (by
    rw [hFcard, Nat.card_eq_fintype_card]
    omega)
  obtain ⟨L, hL, hLmem⟩ := CommutingFourSeed.exists_pair_group a.val 1
    (by simpa only [pow_two] using ha2) (one_mul 1) (by simp)
  have hLpreserves : ∀ l : G, l ∈ L → ∀ y ∈ T, l • y ∈ T := by
    intro l hl y hy
    rcases (hLmem l).mp hl with rfl | rfl | rfl | rfl
    · simpa only [one_smul] using hy
    · exact hTstable y hy
    · simpa only [one_smul] using hy
    · simpa only [mul_one] using hTstable y hy
  obtain ⟨u, _, hu, huT, hua⟩ := HighDegreeCommutingInvolution.exists_of_five_transitive
    G X hcard h5 T hTcard L hL hLpreserves
  have hu2 : u ^ 2 = 1 := by simpa only [hu] using pow_orderOf_eq_one u
  have hcomm : Commute u a.val := hua a.val ((hLmem a.val).mpr (Or.inr (Or.inl rfl)))
  obtain ⟨H, hH, hHmem⟩ := CommutingFourSeed.exists_pair_group a.val u
    (by simpa only [pow_two] using ha2) (by simpa only [pow_two] using hu2) hcomm.symm.eq
  have haH : a.val ∈ H := (hHmem a.val).mpr (Or.inr (Or.inl rfl))
  have huH : u ∈ H := (hHmem u).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hpreserves : ∀ h : H, ∀ y : X,
      y ∈ fixedPoints Q X ↔ h.val • y ∈ fixedPoints Q X := by
    intro h y
    rw [hfixa]
    have hc : Commute h.val a.val := by
      rcases (hHmem h.val).mp h.property with hh | hh | hh | hh
      · rw [hh]; exact Commute.one_left _
      · rw [hh]
      · rw [hh]; exact hcomm
      · rw [hh]; exact (Commute.refl a.val).mul_left hcomm
    have hs : h.val • fixedBy X a.val = fixedBy X a.val := by
      simpa only [zpow_one] using (smul_zpow_fixedBy_eq_of_commute (α := X) hc.symm (1 : ℤ))
    exact (smul_mem_of_set_mem_fixedBy (show fixedBy X a.val ∈ fixedBy (Set X) h.val from hs)).symm
  obtain ⟨k, hk⟩ := SetwisePGroupSylowCorrection.exists_correction
    (fixedPoints Q X) S H hH hpreserves
  have hnN : k.val * u * k.val⁻¹ ∈ Normalizer Q := by simpa only [hS] using (hk ⟨u, huH⟩).1
  let n : Normalizer Q := ⟨k.val * u * k.val⁻¹, hnN⟩
  have hnorder : orderOf n.val = 2 :=
    (orderOf_injective (MulAut.conj k.val).toMonoidHom (MulAut.conj k.val).injective u).trans hu
  let T' : Set X := (fun y : X => k.val • y) '' T
  have hT'card : T'.ncard = 4 := by
    rw [Set.ncard_image_of_injective T (MulAction.injective k.val)]
    exact hTcard
  have hT'out : T' ⊆ (fixedPoints Q X)ᶜ := by
    rintro _ ⟨y, hy, rfl⟩ hky
    have hinv : k.val⁻¹ • (k.val • y) = k.val • y :=
      (mem_fixingSubgroup_iff G).mp ((fixingSubgroup G (fixedPoints Q X)).inv_mem k.property) _ hky
    have he : y = k.val • y := by simpa only [inv_smul_smul] using hinv
    apply hTout hy
    rw [← hfixa, he]
    exact hky
  have hT'fix : ∀ y ∈ T', n.val • y = y := by
    rintro _ ⟨y, hy, rfl⟩
    change (k.val * u * k.val⁻¹) • (k.val • y) = k.val • y
    simp only [mul_smul, inv_smul_smul, huT y hy]
  have hfour : 4 ≤ (fixedBy X n.val \ fixedPoints Q X).ncard := by
    rw [← hT'card]
    exact Set.ncard_le_ncard (fun y hy => ⟨hT'fix y hy, hT'out hy⟩)
  have hlocal : (fixedBy X n.val ∩ fixedPoints Q X).ncard ≤ 3 := by
    have hsum := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X n.val) (fixedPoints Q X)
    have hbound := hmax n.val hnorder
    omega
  have hnQ : n.val ∉ Q := by
    intro hn
    obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hT'card]; decide)
    have he : n.val = 1 := congrArg Subtype.val (hfree ⟨n.val, hn⟩ y (hT'out hy) (hT'fix y hy))
    rw [he, orderOf_one] at hnorder
    omega
  exact ⟨n, hnorder, hnQ, hfour, hlocal, T', hT'card, hT'out, hT'fix⟩

theorem exists_normalized_seed
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (y : X), y ∉ fixedPoints Q X → q • y = y → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q) :
    ∃ n : Normalizer Q, orderOf n.val = 2 ∧ n.val ∉ Q ∧
      4 ≤ (fixedBy X n.val \ fixedPoints Q X).ncard ∧
      (fixedBy X n.val ∩ fixedPoints Q X).ncard ≤ 3 ∧
      ∃ T : Set X, T.ncard = 4 ∧ T ⊆ (fixedPoints Q X)ᶜ ∧
        ∀ y ∈ T, n.val • y = y := by
  let _ : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  obtain ⟨j, hj⟩ := hQ.exists_card_eq
  have hjpos : 0 < j := by
    have hc := Finite.one_lt_card (α := Q)
    rw [hj] at hc
    by_contra hh
    have he : j = 0 := by omega
    rw [he, pow_zero] at hc
    omega
  have hd : 2 ∣ Nat.card Q := by
    rw [hj]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 hd
  have ha' : orderOf a.val = 2 := (orderOf_injective Q.subtype Subtype.val_injective a).trans ha
  exact exists_of_involution hcard h5 hmax Q hseven hfree S hS a ha'

end FiveTransitive.HighDegreeNormalizedFourSeed

end CFSG
