module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bF
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bR
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bOmega
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bY
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bStruct
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem level1_holds
    (h45 : Sec4.Item4_5) (h41 : Sec4.Item4_1LargePrime)
    (hKF : KFacts.OutFixCentralThreeAbelian46Rank) (h49 : Sec4.Item4_9) (h47 : Sec4.Item4_7W)
    (h423 : Sec4.Item4_23) (hAlt : Sec4.Step463Alt) : PieceLevel1 := by
  unfold PieceLevel1
  intro G _ _ A c L E hcfg hE
  have hD := hcfg.hD
  obtain ⟨hcE, hcomm, -⟩ := struct_holds G A c L E hcfg
  obtain ⟨a, haA, ha1, ha2⟩ := Item131bProof.exists_even_theta hD
  have haE : a ∉ E := fun h => by
    have hodd := hcfg.hodd a h ha1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ha2)
  have ha3 : a ^ 3 = 1 := hD.isElemAbelian.2 a haA
  have hcomm' : ∀ e ∈ E, a * e * a⁻¹ * e⁻¹ ∈ Subgroup.zpowers c := hcomm a haA
  have hac : a * c = c * a := hD.commute haA hD.mem_A
  have hFE : partTwoF G = partTwoE G :=
    (hD.toTheoremFourHyp.partTwoF_eq_partTwoE hD.partTwoS_eq).1
  obtain ⟨F, hFe, hF27, haF, hcF, hFa, hFF, hFT, hEF, hFEn, hFcomm, hFEcard, hFgen⟩ :=
    exists_F hFE hcfg.hEe hcfg.hE27 hE hcE haE ha3 hcomm' hac ha2
  have hc3 : c ^ 3 = 1 := hcfg.hEe.2 c hcE
  have hc1 : c ≠ 1 := hD.ne_one
  obtain ⟨b, R, hbE, hbF, hbc, hR1, hR2, hRa, hRb, hFR, hRc⟩ :=
    exists_bR hcfg.hEe hcfg.hE27 hE hFe hF27 haF hcF hcE hc3 hc1 hFa hcomm' hac hFEcard hFgen ha2
  have hb1 : b ≠ 1 := fun h => hbc (h ▸ one_mem _)
  have hb3 : orderOf b = 3 := orderOf_eq_prime (hFe.2 b hbF) hb1
  have hco : orderOf c = 3 := hD.orderOf_eq
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 (fun h => haE (h ▸ one_mem _))
  have hacz : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm1 : Commute c a := hac.symm
    rw [(hcomm1.zpow_right k).eq]
    simp only [mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers a k
  have haz : a ∉ Subgroup.zpowers c := fun h =>
    haE ((Subgroup.zpowers_le.mpr hcE) h)
  have hinf : Subgroup.zpowers c ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxc, hxa⟩ := Subgroup.mem_inf.mp hx
    by_contra hx1
    have hx1' : x ≠ 1 := fun h => hx1 (by simpa using h)
    have hxo : orderOf x = 3 := by
      have hd : orderOf x ∣ 3 := by
        simpa [Nat.card_zpowers, hco] using Subgroup.orderOf_dvd_natCard _ hxc
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1'
      · exact h
    have heq : Subgroup.zpowers x = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxc)
        (by simp [Nat.card_zpowers, hco, hxo])
    exact haz (by
      have : a ∈ Subgroup.zpowers x := by
        have heq' : Subgroup.zpowers x = Subgroup.zpowers a :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxa)
            (by simp [Nat.card_zpowers, hao, hxo])
        rw [heq']
        exact Subgroup.mem_zpowers a
      rwa [heq] at this)
  have hB9 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) = 9 := by
    have h := Sec6.card_sup_mul_card_inf hacz
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hco, hao,
      sup_comm] at h
    omega
  have hbB : b ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
    intro hb
    have hle : Subgroup.zpowers c ≤ (Subgroup.zpowers a ⊔ Subgroup.zpowers c) ⊓ E :=
      le_inf le_sup_right (Subgroup.zpowers_le.mpr hcE)
    have hdvd : Nat.card ((Subgroup.zpowers a ⊔ Subgroup.zpowers c) ⊓ E : Subgroup G) ∣ 9 := by
      rw [← hB9]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h3 : 3 ∣ Nat.card ((Subgroup.zpowers a ⊔ Subgroup.zpowers c) ⊓ E : Subgroup G) := by
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hco] at this
    have hne9 : Nat.card ((Subgroup.zpowers a ⊔ Subgroup.zpowers c) ⊓ E : Subgroup G) ≠ 9 := by
      intro h9
      have hall : (Subgroup.zpowers a ⊔ Subgroup.zpowers c) ⊓ E =
          Subgroup.zpowers a ⊔ Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, hB9])
      have : a ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers c) ⊓ E := by
        rw [hall]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
      exact haE this.2
    have h3' : Nat.card ((Subgroup.zpowers a ⊔ Subgroup.zpowers c) ⊓ E : Subgroup G) = 3 := by
      have hdvd2 : Nat.card ((Subgroup.zpowers a ⊔ Subgroup.zpowers c) ⊓ E : Subgroup G) ∣ 3 ^ 2 := by
        norm_num
        exact hdvd
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd2
      interval_cases k
      · omega
      · exact hk'
      · exact absurd (by simpa using hk') hne9
    have heq : Subgroup.zpowers c = (Subgroup.zpowers a ⊔ Subgroup.zpowers c) ⊓ E :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h3', Nat.card_zpowers, hco])
    have hbmem : b ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers c) ⊓ E := ⟨hb, hbE⟩
    rw [← heq] at hbmem
    exact hbc hbmem
  have hodd_b := hcfg.hodd b hbE hb1
  have hstar := not_starConditionAt hFe hF27 haF hbF hcF hb1 hB9 hbB hR1 hR2 hRa hRb hFR hRc
    hodd_b
  have hΩ : Subgroup.zpowers b ∈ omegaA F :=
    zpowers_mem_omegaA_iff.mpr ⟨hbF, by rw [Nat.card_zpowers, hb3], hstar⟩
  obtain ⟨Y, hYl, hEY, hlist⟩ := exists_Y h45 h41 hKF h49 h47 h423 hAlt hD.toPartTwoStanding
    hcfg.hEe hcfg.hE27 hbE hFF hF27 haF hbF hcF hb1 hB9 hbB hR1 hR2 hRa hRb hFR hRc hodd_b
  have hDb : Sec13Data G F b Y := ⟨hD.toPartTwoStanding, hD.partTwoS_eq, hFF, hFT, hΩ, hYl⟩
  exact ⟨F, a, b, R, Y, ⟨hcfg, hE, hDb, hcE, hbE, hcF, haF, haE, haA, hbc, hEF, hFEn, hFcomm,
    hFEcard, hFgen, hEY, hR1, hR2, hRa, hRb, hFR, hRc, hlist⟩⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
