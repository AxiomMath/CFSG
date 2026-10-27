module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S13a
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xe
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112_inf_eq_bot {D : Data G} {Ch : Choice2011 G} (h847 : R847Four D)
    (hsig : D.sig.Nonempty) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hLp : IsL2Odd (Bar2 L) p) :
    c.B ⊓ L = ⊥ := by
  by_contra hne
  have hodd : Odd (Nat.card ↥(c.B ⊓ L)) :=
    Odd.of_dvd_nat (uc22s13xe_odd_card_B c) (Subgroup.card_dvd_of_le inf_le_left)
  have h1 : Nat.card ↥(c.B ⊓ L) ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd h1
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrd
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrd)
  have hxBL := Subgroup.mem_inf.1 x.2
  have hXB : Subgroup.zpowers (x : G) ≤ c.B := Subgroup.zpowers_le.2 hxBL.1
  have hXL : Subgroup.zpowers (x : G) ≤ L := Subgroup.zpowers_le.2 hxBL.2
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  obtain ⟨q, hq⟩ := hsig
  exact s21_2 D Ch hH c _ hXB
    (h847 L hL _ hXL r hr hr2 hXcard q hq (thin8_of_isL2Odd_bar2 hp hp2 hLp))

theorem uc22s2112_le_normalizer_inf {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hBL : c.B ≤ normalizer (L : Set G)) (hmeet : c.B ⊓ L = ⊥) :
    c.B ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hperm, -, -⟩ := c.hB
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hBodd := uc22s13xe_odd_card_B c
  have key : ∀ b ∈ c.B, ∀ s ∈ D.T ⊓ L, b * s * b⁻¹ ∈ D.T ⊓ L := by
    intro b hb s hs
    obtain ⟨hsT, hsL⟩ := Subgroup.mem_inf.1 hs
    have h1 : s * b⁻¹ ∈ (c.B : Set G) * (D.T : Set G) := by
      rw [hperm]
      exact Set.mul_mem_mul hsT (c.B.inv_mem hb)
    obtain ⟨b₁, hb₁, t, ht, hbt⟩ := h1
    replace hbt : b₁ * t = s * b⁻¹ := hbt
    have hb'B : b * b₁ ∈ c.B := c.B.mul_mem hb hb₁
    have hy : b * s * b⁻¹ = b * b₁ * t := by
      rw [mul_assoc b b₁ t, hbt, mul_assoc]
    have hyL : b * s * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hBL hb) s).1 hsL
    have hb'N : b * b₁ ∈ normalizer (L : Set G) := hBL hb'B
    have hpow : ∀ n : ℕ, (b * b₁) ^ n * t ^ n ∈ L := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have e : (b * b₁) ^ (n + 1) * t ^ (n + 1) =
            ((b * b₁) * ((b * b₁) ^ n * t ^ n) * (b * b₁)⁻¹) * ((b * b₁) * t) := by
          group
        rw [e]
        exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 hb'N _).1 ih) (hy ▸ hyL)
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    have htk : t ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hb'k : (b * b₁) ^ (2 ^ k) ∈ L := by
      simpa [htk] using hpow (2 ^ k)
    have hodd' : Odd (orderOf (b * b₁)) := by
      refine Odd.of_dvd_nat hBodd ?_
      rw [← Subgroup.orderOf_mk (b * b₁) hb'B]
      exact orderOf_dvd_natCard _
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime ((Nat.coprime_two_left.2 hodd').pow_left k)
    have hb'L : b * b₁ ∈ L := hm ▸ L.pow_mem hb'k m
    have hb'1 : b * b₁ = 1 := by
      have h2 : b * b₁ ∈ c.B ⊓ L := Subgroup.mem_inf.2 ⟨hb'B, hb'L⟩
      rw [hmeet] at h2
      exact Subgroup.mem_bot.1 h2
    rw [hy, hb'1, one_mul]
    refine Subgroup.mem_inf.2 ⟨ht, ?_⟩
    have h3 := hyL
    rwa [hy, hb'1, one_mul] at h3
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact key b hb s
  · intro hs
    have h4 := key b⁻¹ (c.B.inv_mem hb) _ hs
    simpa [mul_assoc] using h4

end CFSG.LocalAnalysis.UniquenessCase.UC22
