module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin1

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.At

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

@[expose] def invStab (x y : Fin 5) : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun g => orth.act g (ep x y) = ep x y ∧ g ^ 2 = 1

theorem pow_six_of_fix : ∀ x y : Fin 5, x ≠ y → ∀ g : Perm (Fin 5),
    orth.act g (ep x y) = ep x y → g ^ 6 = 1 := by
  decide +kernel

theorem subsets_invStab : ∀ x y : Fin 5, x ≠ y → ∀ F ∈ (invStab x y).powerset,
    (1 ∈ F ∧ ∀ a ∈ F, ∀ b ∈ F, a * b ∈ F) → F.card ≤ 4 ∧ (3 ≤ F.card → swap x y ∈ F) := by
  unfold invStab; decide +kernel

theorem sq_eq_one_of_fix {X : Subgroup (Perm (Fin 5))} (hX : IsPGroup 2 X) {x y : Fin 5}
    (hxy : x ≠ y) (hfix : ∀ g ∈ X, orth.act g (ep x y) = ep x y) {g : Perm (Fin 5)}
    (hg : g ∈ X) : g ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hX ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h6 := pow_six_of_fix x y hxy g (hfix g hg)
  have d1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have d2 : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp d1
  have hi1 : i ≤ 1 := by
    by_contra h
    have h4 : 2 ^ 2 ∣ 2 ^ i := Nat.pow_dvd_pow 2 (by omega)
    rw [← hio] at h4
    have := h4.trans d2
    omega
  have : orderOf g ∣ 2 := by
    rw [hio]
    exact (Nat.pow_dvd_pow 2 hi1).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem card_le_four_of_fix {X : Subgroup (Perm (Fin 5))} (hX : IsPGroup 2 X) {x y : Fin 5}
    (hxy : x ≠ y) (hfix : ∀ g ∈ X, orth.act g (ep x y) = ep x y) :
    Nat.card X ≤ 4 ∧ (3 ≤ Nat.card X → swap x y ∈ X) := by
  classical
  let F : Finset (Perm (Fin 5)) := (invStab x y).filter fun g => g ∈ X
  have hF : Nat.card X = F.card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    simp only [F, invStab, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hg => ⟨⟨hfix g hg, sq_eq_one_of_fix hX hxy hfix hg⟩, hg⟩, fun h => h.2⟩
  have key := subsets_invStab x y hxy F
    (Finset.mem_powerset.mpr (Finset.filter_subset _ _)) ⟨?_, ?_⟩
  · rw [hF]
    refine ⟨key.1, fun h => ?_⟩
    have := key.2 (hF ▸ h)
    exact (Finset.mem_filter.mp this).2
  · refine Finset.mem_filter.mpr ⟨?_, X.one_mem⟩
    simp only [invStab, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [map_one]; rfl, one_pow 2⟩
  · intro a ha b hb
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨?_, X.mul_mem ha2 hb2⟩
    simp only [invStab, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [act_mul_apply, hfix b hb2, hfix a ha2],
      sq_eq_one_of_fix hX hxy hfix (X.mul_mem ha2 hb2)⟩

theorem relIndex_inf_le_two {X E : Subgroup (Perm (Fin 5))} (hX : IsPGroup 2 X) {x y : Fin 5}
    (hxy : x ≠ y) (hfix : ∀ g ∈ X, orth.act g (ep x y) = ep x y) (hE : swap x y ∈ E) :
    (X ⊓ E).relIndex X ≤ 2 := by
  obtain ⟨h4, h3⟩ := card_le_four_of_fix hX hxy hfix
  have hpos : 0 < Nat.card X := Nat.card_pos
  have hmul := Subgroup.relIndex_mul_card (H := X ⊓ E) (K := X)
  by_cases hc : 3 ≤ Nat.card X
  · have hs := h3 hc
    have hle : Subgroup.zpowers (swap x y) ≤ (X ⊓ E) ⊓ X :=
      Subgroup.zpowers_le.mpr ⟨⟨hs, hE⟩, hs⟩
    have hord : Nat.card (Subgroup.zpowers (swap x y)) = 2 := by
      rw [Nat.card_zpowers]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime (by rw [pow_two]; exact swap_mul_self x y) ?_
      intro h
      have := congrArg (fun f => f x) h
      simp only [swap_apply_left, Perm.coe_one, id_eq] at this
      exact hxy this.symm
    have hc2 := Subgroup.card_le_of_le hle
    rw [hord] at hc2
    by_contra hgt
    have hgt := Nat.lt_of_not_le hgt
    nlinarith
  · have := Subgroup.relIndex_dvd_card (H := X ⊓ E) (K := X)
    exact (Nat.le_of_dvd hpos this).trans (by omega)

end CFSG.Quasithin.F53.Stellmacher.S35.At
