module

public import Mathlib.GroupTheory.Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

theorem eq_bot_of_datum_order_216 {C : Type} [Group C] [Finite C] (hC : Nat.card C = 216)
    (hZ : Nat.card (Subgroup.center C) = 3)
    (hO2 : ∀ N : Subgroup C, N.Normal → IsPGroup 2 N → N = ⊥) {R P : Subgroup C} (hPR : P ≤ R)
    (hnorm : ∀ c : C, ∀ r ∈ R, c * r * c⁻¹ ∈ R) (hZR : Subgroup.center C ≤ R)
    (h9 : ¬ 9 ∣ Nat.card R) (hP2 : IsPGroup 2 P) : P = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup C := Subgroup.center C with hZdef
  have hRd : Nat.card R ∣ 216 := hC ▸ Subgroup.card_subgroup_dvd_card R
  have h3 : 3 ∣ Nat.card R := hZ ▸ Subgroup.card_dvd_of_le hZR
  have hcases : Nat.card R = 3 ∨ Nat.card R = 6 ∨ Nat.card R = 12 ∨ Nat.card R = 24 := by
    have key : ∀ n ∈ Finset.range 217, n ∣ 216 → 3 ∣ n → ¬ 9 ∣ n →
        n = 3 ∨ n = 6 ∨ n = 12 ∨ n = 24 := by decide +kernel
    exact key _ (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hRd)))
      hRd h3 h9
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card R = 3 * 2 ^ a := by
    rcases hcases with h | h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
    · exact ⟨3, by omega⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := R) 2 (n := a)
    (by rw [ha]; exact Dvd.intro_left 3 rfl)
  let K' : Subgroup C := K.map R.subtype
  have hK'card : Nat.card K' = 2 ^ a := by
    rw [Subgroup.card_map_of_injective R.subtype_injective, hK]
  have hK'2 : IsPGroup 2 K' := IsPGroup.of_card hK'card
  have hK'R : K' ≤ R := Subgroup.map_subtype_le K
  have hdisj : Disjoint K' Z := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxZ
    have h1 : x ^ (2 ^ a) = 1 := by
      have := pow_card_eq_one' (G := K') (x := ⟨x, hxK⟩)
      rw [hK'card] at this
      exact congrArg Subtype.val this
    have h3' : x ^ 3 = 1 := by
      have := pow_card_eq_one' (G := Z) (x := ⟨x, hxZ⟩)
      rw [hZ] at this
      exact congrArg Subtype.val this
    have hcop : Nat.Coprime (2 ^ a) 3 := Nat.Coprime.pow_left a (by norm_num)
    have h4 : x ^ Nat.gcd (2 ^ a) 3 = 1 := pow_gcd_eq_one.mpr ⟨h1, h3'⟩
    rw [hcop, pow_one] at h4
    exact h4
  have hZnorm : Z ≤ Subgroup.normalizer (K' : Set C) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hc := Subgroup.mem_center_iff.mp hz x
    have : z * x * z⁻¹ = x := by rw [← hc, mul_inv_cancel_right]
    rw [this]
  have hsupcard : Nat.card (K' ⊔ Z : Subgroup C) = 2 ^ a * 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer K' Z hZnorm hdisj,
      hK'card, hZ]
  have hsupR : K' ⊔ Z = R :=
    Subgroup.eq_of_le_of_card_ge (sup_le hK'R hZR) (by rw [hsupcard, ha, mul_comm])
  have hel : ∀ h ∈ R, (∃ k : ℕ, h ^ 2 ^ k = 1) → h ∈ K' := by
    rintro h hhR ⟨k, hk⟩
    have hsup : h ∈ K' ⊔ Z := hsupR ▸ hhR
    obtain ⟨q, hq, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hsup
    have hqz : Commute q z := Subgroup.mem_center_iff.mp hz q
    rw [hqz.mul_pow] at hk
    have hzn : z ^ 2 ^ k ∈ K' := by
      have : z ^ 2 ^ k = (q ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right hk
      rw [this]
      exact K'.inv_mem (K'.pow_mem hq _)
    have hz1 : z ^ 2 ^ k = 1 :=
      Subgroup.disjoint_def.mp hdisj hzn (Subgroup.pow_mem _ hz _)
    have hz3 : z ^ 3 = 1 := by
      have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
      rw [hZ] at this
      exact congrArg Subtype.val this
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have h4 : z ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.mpr ⟨hz1, hz3⟩
    rw [hcop, pow_one] at h4
    rw [h4, mul_one]
    exact hq
  have hnormK : K'.Normal := by
    refine ⟨fun n hn c => ?_⟩
    have hnR : n ∈ R := hK'R hn
    have hn2 : n ^ 2 ^ a = 1 := by
      have := pow_card_eq_one' (G := K') (x := ⟨n, hn⟩)
      rw [hK'card] at this
      exact congrArg Subtype.val this
    exact hel _ (hnorm c n hnR) ⟨a, by rw [conj_pow, hn2]; simp⟩
  have hbot : K' = ⊥ := hO2 K' hnormK hK'2
  rw [eq_bot_iff]
  intro p hp
  obtain ⟨k, hk⟩ := hP2 ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have := hel p (hPR hp) ⟨k, hk'⟩
  rw [hbot] at this
  exact this

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
