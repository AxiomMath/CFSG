module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace CFSG
end CFSG
open CFSG

open Subgroup

section Oddness

/-- If `m` is odd and `n ∣ m`, then `n` is odd. -/
public theorem CFSG.odd_of_card_dvd {n m : ℕ} (hm : Odd m) (hdvd : n ∣ m) : Odd n :=
  hm.of_dvd_nat hdvd

end Oddness

section StrictInequalities

variable {G : Type*} [Group G] [Finite G]

/-- If `H` is a non-trivial normal subgroup, then `|G/H| < |G|`. -/
public lemma CFSG.natCard_quotient_lt_natCard_of_ne_bot (H : Subgroup G) [H.Normal] (hH : H ≠ ⊥) :
    Nat.card (G ⧸ H) < Nat.card G := by
  have hH_one_lt : 1 < Nat.card H := (Subgroup.one_lt_card_iff_ne_bot (H := H)).2 hH
  have hcard_mul : Nat.card G = Nat.card (G ⧸ H) * Nat.card H := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G) (s := H))
  have hlt : Nat.card (G ⧸ H) * 1 < Nat.card (G ⧸ H) * Nat.card H :=
    Nat.mul_lt_mul_of_pos_left hH_one_lt (Nat.card_pos (α := G ⧸ H))
  simpa [hcard_mul] using hlt

/-- If `H < K` are subgroups of a finite group, then `|H| < |K|`. -/
public lemma CFSG.natCard_lt_of_subgroup_lt {H K : Subgroup G} (hHK : H < K) :
    Nat.card H < Nat.card K := by
  let HK : Subgroup K := H.subgroupOf K
  have hHK_card : Nat.card HK = Nat.card H := natCard_subgroupOf_eq H K hHK.1
  have hHK_ne_top : HK ≠ ⊤ := by
    intro htop
    apply hHK.2
    intro x hx
    have hx_top : (⟨x, hx⟩ : K) ∈ (⊤ : Subgroup K) := by simp
    have hx_HK : (⟨x, hx⟩ : K) ∈ HK := by simp [htop]
    simpa [HK, Subgroup.mem_subgroupOf] using hx_HK
  have hle : Nat.card HK ≤ Nat.card K := Subgroup.card_le_card_group (H := HK)
  have hne : Nat.card HK ≠ Nat.card K := by
    intro hEq
    exact hHK_ne_top ((Subgroup.card_eq_iff_eq_top (H := HK)).1 hEq)
  have hlt : Nat.card HK < Nat.card K := lt_of_le_of_ne hle hne
  simpa [hHK_card] using hlt

end StrictInequalities

section QuotientCardinalities

variable {G : Type*} [Group G] [Finite G]

/-- For a normal subgroup `N`, `|K.map (mk' N)|` divides `|K|`. -/
public lemma CFSG.natCard_map_mk'_dvd_card (K N : Subgroup G) [N.Normal] :
    Nat.card (K.map (QuotientGroup.mk' N)) ∣ Nat.card K := by
  rw [natCard_map_mk'_eq K N]
  exact ⟨Nat.card (N.subgroupOf K), by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := K) (s := N.subgroupOf K))⟩

/-- If `N ≠ ⊥` and `N ≤ K`, then `|K.map (mk' N)| < |K|`. -/
public lemma CFSG.natCard_map_mk'_lt_of_ne_bot (K N : Subgroup G) [N.Normal] (hN_le_K : N ≤ K)
    (hN_ne_bot : N ≠ ⊥) :
    Nat.card (K.map (QuotientGroup.mk' N)) < Nat.card K := by
  have hNsub_ne_bot : N.subgroupOf K ≠ ⊥ := by
    intro hbot
    apply hN_ne_bot
    ext x
    constructor
    · intro hx
      have hx_sub : (⟨x, hN_le_K hx⟩ : K) ∈ N.subgroupOf K := by
        simpa [Subgroup.mem_subgroupOf] using hx
      have hx_bot : (⟨x, hN_le_K hx⟩ : K) ∈ (⊥ : Subgroup K) := by simpa [hbot] using hx_sub
      simpa using hx_bot
    · intro hx
      have hx_one : x = 1 := by simpa using hx
      simp [hx_one]
  calc
    Nat.card (K.map (QuotientGroup.mk' N)) = Nat.card (K ⧸ N.subgroupOf K) :=
      natCard_map_mk'_eq K N
    _ < Nat.card K := natCard_quotient_lt_natCard_of_ne_bot (N.subgroupOf K) hNsub_ne_bot

omit [Finite G] in
/-- If `K.IsComplement' R` and `N ≤ K`, then `|R.map (mk' N)| = |R|`. -/
public theorem CFSG.natCard_map_mk'_eq_of_le_isComplement' (K R N : Subgroup G) [N.Normal]
    (hN_le_K : N ≤ K) (hKR : K.IsComplement' R) :
    Nat.card (R.map (QuotientGroup.mk' N)) = Nat.card R := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hq_inj : Function.Injective (q ∘ R.subtype) := by
    intro a b hab
    apply Subtype.ext
    change q (a : G) = q (b : G) at hab
    have habN : (a : G)⁻¹ * (b : G) ∈ N := QuotientGroup.eq.mp hab
    have habK : (a : G)⁻¹ * (b : G) ∈ K := hN_le_K habN
    have habR : (a : G)⁻¹ * (b : G) ∈ R := R.mul_mem (R.inv_mem a.property) b.property
    have hab_one : (a : G)⁻¹ * (b : G) = 1 := (Subgroup.disjoint_def.mp hKR.disjoint) habK habR
    have := congrArg (fun t : G => (a : G) * t) hab_one
    have hab_eq : (b : G) = a := by simpa [mul_assoc] using this
    exact hab_eq.symm
  let f : R → R.map q := fun r => ⟨q r, ⟨r, r.property, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact hq_inj (by simpa [f] using congrArg Subtype.val hab)
  have hf_surj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rcases hx with ⟨r, hrR, rfl⟩
    exact ⟨⟨r, hrR⟩, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm

omit [Finite G] in
/-- If `p` is prime and `|R| = p`, then `|R.map (mk' N)|` is also prime (when `N ≤ K`). -/
public theorem CFSG.prime_card_map_mk'_of_le_isComplement' (K R N : Subgroup G) [N.Normal]
    (hN_le_K : N ≤ K) (hKR : K.IsComplement' R) (hR_prime : Nat.Prime (Nat.card R)) :
    Nat.Prime (Nat.card (R.map (QuotientGroup.mk' N))) := by
  rw [natCard_map_mk'_eq_of_le_isComplement' K R N hN_le_K hKR]
  exact hR_prime

/-- Coprimality of `|K|` and `|R|` lifts to their images under `mk' N`. -/
public theorem CFSG.coprime_card_map_mk'_of_le_isComplement' (K R N : Subgroup G) [N.Normal]
    (hN_le_K : N ≤ K) (hKR : K.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R)) :
    Nat.Coprime (Nat.card (K.map (QuotientGroup.mk' N))) (Nat.card (R.map (QuotientGroup.mk' N))) := by
  rw [natCard_map_mk'_eq_of_le_isComplement' K R N hN_le_K hKR]
  exact Nat.Coprime.of_dvd_left (natCard_map_mk'_dvd_card K N) hcop

omit [Finite G] in
/-- Coprimality of `|K|` and `|R|` gives coprimality of `|H.subgroupOf (H ⊔ R)|` and
  `|R.subgroupOf (H ⊔ R)|` when `H ≤ K`. -/
public theorem CFSG.coprime_card_subgroupOf_sup_of_le (H K R : Subgroup G) (hH_le_K : H ≤ K)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R)) :
    Nat.Coprime (Nat.card (H.subgroupOf (H ⊔ R))) (Nat.card (R.subgroupOf (H ⊔ R))) := by
  rw [natCard_subgroupOf_eq H (H ⊔ R) le_sup_left, natCard_subgroupOf_eq R (H ⊔ R) le_sup_right]
  have hHdvd : Nat.card H ∣ Nat.card K := by
    rw [← natCard_subgroupOf_eq H K hH_le_K]
    exact Subgroup.card_subgroup_dvd_card (H.subgroupOf K)
  exact Nat.Coprime.of_dvd_left hHdvd hcop

end QuotientCardinalities

section FieldCharacteristics

variable {F : Type*} [Field F]

/-- Given a characteristic condition on `|G|`, the same condition holds for any divisor `n`. -/
public theorem CFSG.hchar_of_card_dvd {G : Type*} [Group G] [Finite G]
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G))) {n : ℕ}
    (hdvd : n ∣ Nat.card G) :
    ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) n) := by
  rcases hchar with hchar0 | ⟨hprime, hcop⟩
  · exact Or.inl hchar0
  · exact Or.inr ⟨hprime, Nat.Coprime.of_dvd_right hdvd hcop⟩

/-- The cardinality of `G` is nonzero in `F` under the usual characteristic/coprime condition. -/
public theorem CFSG.card_ne_zero_of_char_condition {G : Type*} [Group G] [Finite G]
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G))) :
    (Nat.card G : F) ≠ 0 := by
  intro hcard
  cases hchar with
  | inl hchar0 =>
      have hdiv : ringChar F ∣ Nat.card G := ringChar.dvd hcard
      rw [hchar0] at hdiv
      have hcard_eq_zero : Nat.card G = 0 := by simpa using hdiv
      have hcard_pos : 0 < Nat.card G := Nat.card_pos
      exact (Nat.ne_of_gt hcard_pos) hcard_eq_zero
  | inr hcharp =>
      have hdiv : ringChar F ∣ Nat.card G := ringChar.dvd hcard
      exact (hcharp.1.coprime_iff_not_dvd.mp hcharp.2) hdiv

end FieldCharacteristics
