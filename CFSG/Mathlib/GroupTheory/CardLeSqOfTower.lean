module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG

private theorem card_le_mul_card_inf_ker_of_cyclic_image {G C : Type*} [Group G] [Group C]
    {p : ℕ} (hp : 0 < p) {A : Subgroup G} [Finite A] (hA : ∀ x ∈ A, x ^ p = 1)
    (α : G →* C) {c : C} (hα : ∀ x ∈ A, α x ∈ Subgroup.zpowers c) :
    Nat.card A ≤ p * Nat.card (A ⊓ α.ker : Subgroup G) := by
  let β : A →* C := α.comp A.subtype
  have hβ : β.range ≤ Subgroup.zpowers c := by
    rintro _ ⟨x, rfl⟩
    exact hα x x.2
  have : Finite β.range :=
    (MonoidHom.finite_iff_finite_ker_range β).mp (inferInstance : Finite A) |>.2
  have hrange : Nat.card β.range ≤ p := by
    classical
    have : Fintype β.range := Fintype.ofFinite β.range
    rcases eq_or_ne β.range ⊥ with hbot | hne
    · rw [hbot, Subgroup.card_bot]; exact hp
    · obtain ⟨y₀, hy₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      obtain ⟨k₀, hk₀⟩ := Subgroup.mem_zpowers_iff.mp (hβ y₀.2)
      have hk₀ne : k₀ ≠ 0 := fun h =>
        hy₀ (Subtype.ext (by rw [← hk₀, h, zpow_zero]; rfl))
      have hex : ∃ n : ℕ, 0 < n ∧ c ^ (n : ℤ) ∈ β.range := by
        obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k₀
        · exact ⟨n, Nat.pos_of_ne_zero fun h => hk₀ne (by simp [hn, h]),
            by rw [← hn]; exact hk₀.symm ▸ y₀.2⟩
        · refine ⟨n, Nat.pos_of_ne_zero fun h => hk₀ne (by simp [hn, h]), ?_⟩
          have hneg : (n : ℤ) = -k₀ := by rw [hn]; ring
          rw [hneg, zpow_neg]
          exact β.range.inv_mem (hk₀.symm ▸ y₀.2)
      obtain ⟨hdpos, hdmem⟩ := Nat.find_spec hex
      have hm0 : (Nat.find hex : ℤ) ≠ 0 := by exact_mod_cast hdpos.ne'
      have hgen : ∀ x : β.range, ∃ j : ℤ, (c ^ (Nat.find hex : ℤ)) ^ j = (x : C) := by
        intro x
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hβ x.2)
        have hmul : (Nat.find hex : ℤ) * (j / (Nat.find hex : ℤ)) + j % (Nat.find hex : ℤ) = j :=
          Int.mul_ediv_add_emod j (Nat.find hex : ℤ)
        have hzero : j % (Nat.find hex : ℤ) = 0 := by
          by_contra hr
          have hpos : 0 < j % (Nat.find hex : ℤ) :=
            lt_of_le_of_ne (Int.emod_nonneg _ hm0) (Ne.symm hr)
          have hlt : j % (Nat.find hex : ℤ) < (Nat.find hex : ℤ) :=
            Int.emod_lt_of_pos _ (by exact_mod_cast hdpos)
          have hB : c ^ (j % (Nat.find hex : ℤ)) =
              ((c ^ (Nat.find hex : ℤ)) ^ (j / (Nat.find hex : ℤ)))⁻¹ * c ^ j := by
            have hsplit : c ^ j = (c ^ (Nat.find hex : ℤ)) ^ (j / (Nat.find hex : ℤ)) *
                c ^ (j % (Nat.find hex : ℤ)) := by
              conv_lhs => rw [← hmul]
              rw [zpow_add, zpow_mul]
            rw [hsplit, inv_mul_cancel_left]
          have hmem : c ^ (j % (Nat.find hex : ℤ)) ∈ β.range := by
            rw [hB]
            exact β.range.mul_mem
              (β.range.inv_mem (β.range.zpow_mem hdmem _)) (hj.symm ▸ x.2)
          have hnat : (j % (Nat.find hex : ℤ)).natAbs < Nat.find hex := by
            have : ((j % (Nat.find hex : ℤ)).natAbs : ℤ) < (Nat.find hex : ℤ) := by
              rw [Int.natAbs_of_nonneg hpos.le]; exact hlt
            exact_mod_cast this
          exact Nat.find_min hex hnat ⟨Int.natAbs_pos.mpr (ne_of_gt hpos),
            by rw [Int.natAbs_of_nonneg hpos.le]; exact hmem⟩
        have hmul' : (Nat.find hex : ℤ) * (j / (Nat.find hex : ℤ)) = j :=
          Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hzero)
        exact ⟨j / (Nat.find hex : ℤ), by rw [← zpow_mul, hmul']; exact hj⟩
      let z : β.range := ⟨c ^ (Nat.find hex : ℤ), hdmem⟩
      have htop : Subgroup.zpowers z = ⊤ := (Subgroup.eq_top_iff' _).mpr fun x => by
        obtain ⟨j, hj⟩ := hgen x
        exact Subgroup.mem_zpowers_iff.mpr ⟨j, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hj)⟩
      have hzcard : orderOf z = Nat.card β.range := by
        have h1 : orderOf z = Nat.card (Subgroup.zpowers z) := by
          rw [Nat.card_eq_fintype_card, Fintype.card_zpowers]
        rw [h1, htop, Subgroup.card_top]
      have hzpow : z ^ p = 1 := by
        obtain ⟨x, hx⟩ := hdmem
        apply Subtype.ext
        show (c ^ (Nat.find hex : ℤ)) ^ p = 1
        rw [← hx, ← map_pow β x p, show x ^ p = 1 from Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA x x.2), map_one]
      calc Nat.card β.range = orderOf z := hzcard.symm
        _ ≤ p := orderOf_le_of_pow_eq_one hp hzpow
  have hker : β.ker = (A ⊓ α.ker).subgroupOf A := by
    ext x
    change α (x : G) = 1 ↔ ((x : G) ∈ A ∧ α (x : G) = 1)
    simp
  have hcardker : Nat.card β.ker = Nat.card (A ⊓ α.ker : Subgroup G) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc
    Nat.card A = Nat.card β.ker * Nat.card β.range :=
      (Subgroup.card_ker_mul_card_range β).symm
    _ ≤ Nat.card β.ker * p := Nat.mul_le_mul_left _ hrange
    _ = p * Nat.card (A ⊓ α.ker : Subgroup G) := by rw [hcardker, mul_comm]

theorem card_le_sq_of_two_cyclic_layers {G : Type*} [Group G] {p : ℕ} (hp : 0 < p)
    {N J S A : Subgroup G} [N.Normal] {φ₀ g : G} (hJn : (J.subgroupOf S).Normal) (hg : g ∈ S)
    (hgen : ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) (hJ : J ≤ N ⊔ Subgroup.zpowers φ₀) (hAS : A ≤ S)
    (hexp : ∀ x ∈ A, x ^ p = 1) (hAN : A ⊓ N = ⊥) : Nat.card A ≤ p ^ 2 := by
  by_cases hfin : Finite A
  · let := hfin
    have : (J.subgroupOf S).Normal := hJn
    have hcyc : ∀ x ∈ A.subgroupOf S,
        QuotientGroup.mk' (J.subgroupOf S) x ∈
          Subgroup.zpowers (QuotientGroup.mk' (J.subgroupOf S) ⟨g, hg⟩) := by
      intro x hx
      obtain ⟨k, hk⟩ := hgen x.1 x.2
      have h1 : QuotientGroup.mk' (J.subgroupOf S) ((⟨g, hg⟩ : S) ^ k * x) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        simpa [Subgroup.mem_subgroupOf] using hk
      rw [map_mul, map_zpow] at h1
      have h2 : QuotientGroup.mk' (J.subgroupOf S) x =
          (QuotientGroup.mk' (J.subgroupOf S) ⟨g, hg⟩) ^ (-k) := by
        rw [eq_inv_of_mul_eq_one_right h1, zpow_neg]
      exact h2.symm ▸ Subgroup.zpow_mem_zpowers _ _
    have hA' : ∀ x ∈ A.subgroupOf S, x ^ p = 1 := fun x hx =>
      Subtype.ext (by simpa using hexp x.1 hx)
    have : Finite (A.subgroupOf S) :=
      Finite.of_equiv A (Subgroup.subgroupOfEquivOfLe hAS).toEquiv.symm
    have h1 : Nat.card A ≤ p * Nat.card (A ⊓ J : Subgroup G) := by
      have h := card_le_mul_card_inf_ker_of_cyclic_image hp hA'
        (QuotientGroup.mk' (J.subgroupOf S)) hcyc
      have hinf : A.subgroupOf S ⊓ J.subgroupOf S = (A ⊓ J).subgroupOf S := by
        ext x; simp [Subgroup.mem_subgroupOf]
      rw [QuotientGroup.ker_mk', hinf] at h
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hAS)).toEquiv] at h
    have h2 : Nat.card (A ⊓ J : Subgroup G) ≤ p := by
      have : Finite (A ⊓ J : Subgroup G) :=
        Finite.of_injective (Subgroup.inclusion inf_le_left)
          (Subgroup.inclusion_injective inf_le_left)
      have hmap : (N ⊔ Subgroup.zpowers φ₀).map (QuotientGroup.mk' N) =
          Subgroup.zpowers (QuotientGroup.mk' N φ₀) := by
        rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, MonoidHom.map_zpowers, bot_sup_eq]
      have hα : ∀ x ∈ A ⊓ J,
          QuotientGroup.mk' N x ∈ Subgroup.zpowers (QuotientGroup.mk' N φ₀) := by
        intro x hx
        exact hmap ▸ Subgroup.mem_map_of_mem _ (hJ (Subgroup.mem_inf.mp hx).2)
      have h := card_le_mul_card_inf_ker_of_cyclic_image (A := A ⊓ J) hp
        (fun x hx => hexp x (Subgroup.mem_inf.mp hx).1) (QuotientGroup.mk' N) hα
      have hbot : (A ⊓ J) ⊓ (QuotientGroup.mk' N).ker = ⊥ := by
        rw [QuotientGroup.ker_mk',
          show A ⊓ J ⊓ N = A ⊓ N ⊓ J by ac_rfl, hAN, bot_inf_eq]
      rwa [hbot, Subgroup.card_bot, mul_one] at h
    exact le_trans h1 (by simpa [pow_two] using Nat.mul_le_mul_left p h2)
  · have : Infinite A := not_finite_iff_infinite.mp hfin
    simp

end CFSG

end
