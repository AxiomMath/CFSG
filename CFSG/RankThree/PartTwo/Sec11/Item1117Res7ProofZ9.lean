module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Res6ProofCanon

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1117Res7Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

variable {G : Type} [Group G]

theorem pow_conj_mul_inv_eq {v a : G} (hκ : v * (v * a * v⁻¹ * a⁻¹) = (v * a * v⁻¹ * a⁻¹) * v) :
    ∀ n : ℕ, v ^ n * a * (v ^ n)⁻¹ * a⁻¹ = (v * a * v⁻¹ * a⁻¹) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := pow_conj_mul_inv_eq hκ n
    have hc : Commute v (v * a * v⁻¹ * a⁻¹) := hκ
    have e1 : v ^ n * a * (v ^ n)⁻¹ = (v * a * v⁻¹ * a⁻¹) ^ n * a := by
      rw [← ih]; group
    calc v ^ (n + 1) * a * (v ^ (n + 1))⁻¹ * a⁻¹
        = v * (v ^ n * a * (v ^ n)⁻¹) * v⁻¹ * a⁻¹ := by rw [pow_succ', mul_inv_rev]; group
      _ = (v * (v * a * v⁻¹ * a⁻¹) ^ n * v⁻¹) * (v * a * v⁻¹ * a⁻¹) := by rw [e1]; group
      _ = (v * a * v⁻¹ * a⁻¹) ^ (n + 1) := by
        rw [(hc.pow_right n).eq, mul_inv_cancel_right, pow_succ]

theorem mem_of_pow_three_eq_one [Finite G] {A : Subgroup G} {v e : G}
    (hAc : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u) (hA3 : ∀ u ∈ A, u ^ 3 = 1) (heA : e ∈ A)
    (hve : v * e = e * v) (hvA : v ∈ Subgroup.normalizer (A : Set G))
    (hcomm : ∀ a ∈ A, v * a * v⁻¹ * a⁻¹ ∈ Subgroup.zpowers e) (hv9 : orderOf v = 9)
    (hv3 : v ^ 3 ∈ Subgroup.zpowers e) {z : G} (hz : z ∈ A ⊔ Subgroup.zpowers v)
    (hz3 : z ^ 3 = 1) : z ∈ A := by
  have heZ : Subgroup.zpowers e ≤ A := Subgroup.zpowers_le.mpr heA
  have hcv : ∀ t ∈ Subgroup.zpowers e, v * t = t * v := fun t ht => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact (Commute.zpow_right (show Commute v e from hve) k).eq
  have hmem : z ∈ (A : Set G) * (Subgroup.zpowers v : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A _ (Subgroup.zpowers_le.mpr hvA)]
    exact hz
  obtain ⟨a, ha, t, ht, rfl⟩ := Set.mem_mul.mp hmem
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, v ^ n = t := (mem_powers_iff_mem_zpowers).mpr ht
  have hκ1 := hcomm a ha
  have hκn : v ^ n * a * (v ^ n)⁻¹ * a⁻¹ ∈ Subgroup.zpowers e := by
    rw [pow_conj_mul_inv_eq (hcv _ hκ1) n]
    exact Subgroup.pow_mem _ hκ1 n
  have hκA : v ^ n * a * (v ^ n)⁻¹ * a⁻¹ ∈ A := heZ hκn
  have hκv : v ^ n * (v ^ n * a * (v ^ n)⁻¹ * a⁻¹) = (v ^ n * a * (v ^ n)⁻¹ * a⁻¹) * v ^ n := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hκn
    rw [← hk]
    exact (Commute.zpow_right (Commute.pow_left (show Commute v e from hve) n) k).eq
  have hcube : (a * v ^ n) ^ 3 = a ^ 3 * (v ^ n) ^ 3 :=
    Item1117Res6Proof.mul_pow_three_of_central (k := v ^ n * a * (v ^ n)⁻¹ * a⁻¹)
      (by group) (hAc a ha _ hκA) hκv (hA3 _ hκA)
  rw [hcube, hA3 a ha, one_mul, ← pow_mul] at hz3
  have h9 : 9 ∣ n * 3 := hv9 ▸ orderOf_dvd_of_pow_eq_one hz3
  obtain ⟨m, rfl⟩ : 3 ∣ n := by omega
  refine A.mul_mem ha ?_
  rw [pow_mul]
  exact A.pow_mem (heZ hv3) m

theorem exists_pow_three_eq [Finite G] {B K : Subgroup G} {c : G} (hK3 : ∀ k ∈ K, k ^ 3 = 1)
    (hKB : ∀ k ∈ K, ∀ b ∈ B, k * b = b * k) (hKc : ∀ k ∈ K, k * c = c * k)
    (hcB : ∀ b ∈ B, c * b * c⁻¹ * b⁻¹ ∈ K) (hcN : c ∈ Subgroup.normalizer (B : Set G))
    (hc3 : c ^ 3 = 1) {q : G} (hq : q ∈ B ⊔ Subgroup.zpowers c) : ∃ b ∈ B, q ^ 3 = b ^ 3 := by
  have hpow : ∀ b ∈ B, ∀ n : ℕ, c ^ n * b * (c ^ n)⁻¹ * b⁻¹ ∈ K := by
    intro b hb n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : c ^ n * b * (c ^ n)⁻¹ = (c ^ n * b * (c ^ n)⁻¹ * b⁻¹) * b := by group
      have e1 : c ^ (n + 1) * b * (c ^ (n + 1))⁻¹ * b⁻¹ =
          (c ^ n * b * (c ^ n)⁻¹ * b⁻¹) * (c * b * c⁻¹ * b⁻¹) := by
        calc c ^ (n + 1) * b * (c ^ (n + 1))⁻¹ * b⁻¹
            = c * (c ^ n * b * (c ^ n)⁻¹) * c⁻¹ * b⁻¹ := by rw [pow_succ', mul_inv_rev]; group
          _ = (c * (c ^ n * b * (c ^ n)⁻¹ * b⁻¹)) * b * c⁻¹ * b⁻¹ := by rw [hc]; group
          _ = (c ^ n * b * (c ^ n)⁻¹ * b⁻¹) * (c * b * c⁻¹ * b⁻¹) := by rw [← hKc _ ih]; group
      rw [e1]
      exact K.mul_mem ih (hcB b hb)
  have hmem : q ∈ (B : Set G) * (Subgroup.zpowers c : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left B _ (Subgroup.zpowers_le.mpr hcN)]
    exact hq
  obtain ⟨b, hb, t, ht, rfl⟩ := Set.mem_mul.mp hmem
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, c ^ n = t := (mem_powers_iff_mem_zpowers).mpr ht
  refine ⟨b, hb, ?_⟩
  have hκ := hpow b hb n
  have hcube : (b * c ^ n) ^ 3 = b ^ 3 * (c ^ n) ^ 3 :=
    Item1117Res6Proof.mul_pow_three_of_central (k := c ^ n * b * (c ^ n)⁻¹ * b⁻¹)
      (by group) (hKB _ hκ b hb).symm ((Commute.pow_right (hKc _ hκ) n).eq.symm) (hK3 _ hκ)
  rw [hcube, ← pow_mul, mul_comm n 3, pow_mul, hc3, one_pow, mul_one]

theorem conj_mem_zpowers_of_isSylowOf [Finite G] {Q N : Subgroup G} {x e v : G}
    (hQ : IsSylowOf 3 Q N) (hxN : ∀ y ∈ N, x * y * x⁻¹ ∈ N)
    (hNe : N ≤ Subgroup.centralizer ({e} : Set G))
    (hcube : ∀ q ∈ Q, q ^ 3 ∈ Subgroup.zpowers e) (hvQ : v ∈ Q)
    (hev : e ∈ Subgroup.zpowers (v ^ 3)) : x * e * x⁻¹ ∈ Subgroup.zpowers e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ'N : Q.map (MulAut.conj x).toMonoidHom ≤ N := by
    rintro _ ⟨y, hy, rfl⟩
    exact hxN y (hQ.le hy)
  have hQ's : IsSylowOf 3 (Q.map (MulAut.conj x).toMonoidHom) N :=
    CFSG.ABGLocalTools.isSylowOf_of_card hQ'N (by
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hQ.card_eq])
  obtain ⟨k, hkN, hk⟩ := hQ.exists_mem_conj hQ's
  have hq : k⁻¹ * (x * v * x⁻¹) * k ∈ Q := (hk _).mp ⟨v, hvQ, rfl⟩
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hev
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hcube _ hq)
  have hke : Commute k e := Subgroup.mem_centralizer_singleton_iff.mp (hNe hkN)
  have h2 : (x * v * x⁻¹) ^ 3 = e ^ j := by
    have h1 : x * v * x⁻¹ = k * (k⁻¹ * (x * v * x⁻¹) * k) * k⁻¹ := by group
    rw [h1, conj_pow, ← hj, (hke.zpow_right j).eq, mul_inv_cancel_right]
  have h3 : x * e * x⁻¹ = ((x * v * x⁻¹) ^ 3) ^ i := by
    rw [← hi, conj_pow, conj_zpow]
  rw [h3, h2, ← zpow_mul]
  exact Subgroup.zpow_mem_zpowers e _

end CFSG.RankThree.PartTwo.Sec11.Item1117Res7Proof
