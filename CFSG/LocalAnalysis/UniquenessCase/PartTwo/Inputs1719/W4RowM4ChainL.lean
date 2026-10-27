module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Chain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open ArithmeticFunction

private theorem m4_mem_sup_zpowers_iff {G : Type*} [Group G] {L : Subgroup G} {t g : G}
    (ht2 : t * t = 1) (hn : t ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ L ⊔ Subgroup.zpowers t ↔ g ∈ L ∨ g * t ∈ L := by
  constructor
  · intro hg
    let S : Subgroup G :=
      { carrier := (L : Set G) ∪ (fun x => x * t) '' (L : Set G)
        one_mem' := Or.inl L.one_mem
        mul_mem' := by
          rintro x y (hx | ⟨a, ha, rfl⟩) (hy | ⟨b, hb, rfl⟩)
          · exact Or.inl (L.mul_mem hx hy)
          · exact Or.inr ⟨x * b, L.mul_mem hx hb, by group⟩
          · exact Or.inr ⟨a * (t * y * t⁻¹),
              L.mul_mem ha ((Subgroup.mem_normalizer_iff.1 hn y).1 hy), by group⟩
          · refine Or.inl ?_
            have h1 : t * b * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hn b).1 hb
            have he : (a * t) * (b * t) = a * (t * b * t⁻¹) := by
              rw [show (a * t) * (b * t) = a * (t * b * t⁻¹) * (t * t) by group,
                ht2, mul_one]
            rw [he]
            exact L.mul_mem ha h1
        inv_mem' := by
          rintro x (hx | ⟨a, ha, rfl⟩)
          · exact Or.inl (L.inv_mem hx)
          · refine Or.inr ⟨t * a⁻¹ * t⁻¹,
              (Subgroup.mem_normalizer_iff.1 hn a⁻¹).1 (L.inv_mem ha), ?_⟩
            have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
            rw [mul_inv_rev, ht1]
            exact (show t * a⁻¹ = (t * a⁻¹ * t) * t by
              rw [mul_assoc, ht2, mul_one]).symm }
    have hLS : L ≤ S := fun x hx => Or.inl hx
    have htS : t ∈ S := Or.inr ⟨1, L.one_mem, one_mul t⟩
    have hKS : L ⊔ Subgroup.zpowers t ≤ S := sup_le hLS (Subgroup.zpowers_le.2 htS)
    rcases hKS hg with hgL | ⟨a, ha, hge⟩
    · exact Or.inl hgL
    · right
      rw [← hge, mul_assoc, ht2, mul_one]
      exact ha
  · rintro (hg | hg)
    · exact Subgroup.mem_sup_left hg
    · have : g = (g * t) * t := by rw [mul_assoc, ht2, mul_one]
      rw [this]
      exact (L ⊔ Subgroup.zpowers t).mul_mem (Subgroup.mem_sup_left hg)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

private theorem m4_cardFactors_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    cardFactors a ≤ cardFactors b := by
  rcases h with ⟨c, rfl⟩
  have ha : a ≠ 0 := fun h0 => hb (by rw [h0, zero_mul])
  have hc : c ≠ 0 := fun h0 => hb (by rw [h0, mul_zero])
  rw [cardFactors_mul ha hc]
  omega

theorem card_sup_zpowers_dvd_two_mul {G : Type*} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (ht2 : t * t = 1) (hn : t ∈ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(L ⊔ Subgroup.zpowers t) ∣ 2 * Nat.card ↥L := by
  have hrel : L.relIndex (L ⊔ Subgroup.zpowers t) ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    refine ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t), fun b hb => ?_⟩
    rcases (m4_mem_sup_zpowers_iff ht2 hn).1 hb with hbL | hbt
    · exact Or.inr hbL
    · exact Or.inl hbt
  have hcard : Nat.card ↥(L ⊔ Subgroup.zpowers t) =
      L.relIndex (L ⊔ Subgroup.zpowers t) * Nat.card ↥L := by
    have h := Subgroup.relIndex_mul_card (H := L) (K := L ⊔ Subgroup.zpowers t)
    rw [inf_eq_left.mpr (le_sup_left : L ≤ L ⊔ Subgroup.zpowers t)] at h
    exact h.symm
  rw [hcard]
  exact mul_dvd_mul_right hrel (Nat.card L)

theorem le_mParam_of_chain_L {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hn : (L.subgroupOf Y).Normal)
    (hF : Fstar Y = L) (hq : IsQuasisimple ↥L) (hO2 : O2Trivial L)
    (hY : ∃ t ∈ Y, orderOf t = 2) {E : Subgroup (MulAut W)} (hEL : E ≤ L) {c : ℕ}
    (hE : 2 ^ ((c - 1) * (cardFactors (Nat.card L) + 1)) < (fixV E).index) :
    c ≤ E3.mParam Y := by
  refine le_mParam_of_index_sq hW hY fun t ht ht2 => ?_
  set K : Subgroup (MulAut W) := L ⊔ Subgroup.zpowers t with hK
  have hLK : L ≤ K := le_sup_left
  have htK : t ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hKY : K ≤ Y := sup_le hLY (Subgroup.zpowers_le.2 ht)
  have hYnorm : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hn
  have hnK : (L.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLK).mpr (hKY.trans hYnorm)
  have hC : ∀ y ∈ K, y ∈ Subgroup.centralizer (L : Set (MulAut W)) → y ∈ L :=
    fun y hy hyc => mem_of_mem_centralizer_of_fstar_eq hLY hF (hKY hy) hyc
  have ht2' : t * t = 1 := by
    simpa [← pow_two, ht2] using pow_orderOf_eq_one t
  have hdiv : Nat.card K ∣ 2 * Nat.card L :=
    card_sup_zpowers_dvd_two_mul ht2' (hYnorm ht)
  have hΩK : cardFactors (Nat.card K) ≤ cardFactors (Nat.card L) + 1 := by
    have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
    have h2L0 : 2 * Nat.card L ≠ 0 := mul_ne_zero (by norm_num) hL0
    have hle := m4_cardFactors_le_of_dvd h2L0 hdiv
    rw [cardFactors_mul (by norm_num : (2 : ℕ) ≠ 0) hL0,
      cardFactors_apply_prime Nat.prime_two] at hle
    omega
  have hchain := index_fixV_le_pow_cardFactors_of_cent hLK hnK hC hq hO2 htK ht2
  obtain ⟨m, hm⟩ := CFSG.QuasithinUnique.Setup.X1.index_fixV_eq_two_pow hW (Subgroup.zpowers t)
  have hEL' : (fixV E).index ≤ (fixV L).index := index_fixV_le_of_le hEL
  rw [hm, ← pow_mul] at hchain
  have hchain' : (fixV L).index ≤ 2 ^ (m * (cardFactors (Nat.card L) + 1)) :=
    hchain.trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left m hΩK))
  have hlt2 : 2 ^ ((c - 1) * (cardFactors (Nat.card L) + 1)) <
      2 ^ (m * (cardFactors (Nat.card L) + 1)) :=
    hE.trans_le (hEL'.trans hchain')
  have hcm : c ≤ m := by
    by_contra hle
    have hle' : m ≤ c - 1 := by omega
    have hmono : m * (cardFactors (Nat.card L) + 1) ≤
        (c - 1) * (cardFactors (Nat.card L) + 1) := Nat.mul_le_mul_right _ hle'
    have hpow : 2 ^ (m * (cardFactors (Nat.card L) + 1)) ≤
        2 ^ ((c - 1) * (cardFactors (Nat.card L) + 1)) :=
      Nat.pow_le_pow_right (by norm_num) hmono
    omega
  rw [hm, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
