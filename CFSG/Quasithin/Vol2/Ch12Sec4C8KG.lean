module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8T
public import CFSG.Quasithin.EmptyFaithful.T1515eC
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Excl
public import CFSG.Quasithin.Background.FFC4Rank
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace KG1248

theorem card_psl3_mul_gcd {X : Type} [Group X] {p f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 p f) :
    Nat.card X * Nat.gcd 3 (p ^ f - 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, ← hK]
  exact card_statedProj_statedSL_three_mul_gcd K

theorem lt_card_carrier
    {s : TauCeti.SporadicName} (hs : Ch1.IsLemma115SporadicName s) :
    168 < Nat.card (NativeSporadic.Carrier s) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show Nat.card (NativeSporadic.Carrier .M11) = 7920 from CFSG.Sporadic.Mathieu.card_M11]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .M12) = 95040 from CFSG.Sporadic.Mathieu.card_M12]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .M22) = 443520 from
      CFSG.Sporadic.Mathieu.card_M22]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .M23) = 10200960 from
      CFSG.Sporadic.Schreier.m23_card]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .M24) = 244823040 from
      CFSG.Sporadic.Mathieu.card_M24]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .J2) = 604800 from CFSG.Sporadic.J2.card_J2]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 from
      CFSG.Sporadic.J4.card_J4]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .HS) = 44352000 from CFSG.Sporadic.HS.card_HS]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .He) = 4030387200 from CFSG.Sporadic.He.card_He]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 from
      CFSG.Sporadic.Ru.card_Ru]
    norm_num

theorem l3Free_5616 : L3Free1515e 5616 0 :=
  L3Free1515e.of_check (B := 18) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

end KG1248

open KG1248

theorem l32ListFact1248 :
    L32ListFact1248 := by
  intro Y _ _ K z _ h hZ hcases
  have h168 : (Subgroup.center ↥K).index = 168 := by
    have hc := card_psl3_mul_gcd h
    norm_num at hc
    exact hc
  have hsimple : IsSimpleGroup ↥K → Subgroup.center ↥K = ⊥ := by
    intro hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with hb | ht
    · exact hb
    · rw [ht, Subgroup.index_top] at h168
      omega
  have hZO : Subgroup.center ↥K ≤ CFSG.pCore 2 ↥K := by
    unfold CFSG.pCore
    exact le_sSup ⟨inferInstance, hZ⟩
  rcases hcases with ⟨hs, -, -⟩ | ⟨-, hZeq, hLie, -⟩ | ⟨φ, -, -, -, -⟩ | ⟨φ, -, -, -, -⟩ |
    ⟨hE, -⟩ | ⟨⟨s, hs, ⟨e⟩⟩, -⟩
  · exact hsimple hs
  · exfalso
    have hidx : (CFSG.pCore 2 ↥K).index = 20160 ∨ (CFSG.pCore 2 ↥K).index = 251596800 := by
      rcases hLie with hL | hG
      · left
        have hc := card_psl3_mul_gcd hL
        norm_num at hc
        change Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 20160
        omega
      · exact Or.inr (Id2519.card_of_g2_four hG)
    rw [← hZeq, h168] at hidx
    omega
  · exfalso
    have h1 : (Subgroup.center ↥K).index = 360 :=
      (Nat.card_congr φ.toEquiv).trans Id2519.card_alternatingGroup_six
    omega
  · exfalso
    have h1 : (Subgroup.center ↥K).index = 2520 :=
      (Nat.card_congr φ.toEquiv).trans Id2519.card_alternatingGroup_seven
    omega
  · rcases hE with hL | ⟨p, -, hL⟩
    · exact hsimple (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 3 1 hL).2
    · exact hsimple (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hL).2
  · exfalso
    have hdvd : (CFSG.pCore 2 ↥K).index ∣ (Subgroup.center ↥K).index :=
      Subgroup.index_dvd_of_le hZO
    have hc : (CFSG.pCore 2 ↥K).index = Nat.card (NativeSporadic.Carrier s) :=
      Nat.card_congr e.toEquiv
    rw [hc, h168] at hdvd
    have h1 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 := lt_card_carrier hs
    omega

theorem l33ExclusionFact : L33ExclusionFact := by
  intro X _ _ h
  have hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
    obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank (by norm_num) h
    rcases hr with ⟨-, ⟨h3, -⟩ | ⟨-, hfr⟩ | h4⟩ | ⟨h5, -⟩ | ⟨h5, -⟩ | h4 <;>
      first | omega | (simp at h3) | (simp at h5)
  have hcard : Nat.card X = 5616 := by
    have hc := card_psl3_mul_gcd h
    norm_num at hc
    exact hc
  exact A318Exclusion.of_card (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 3 1 h).2 hr hcard
    l3Free_5616

theorem hatA67Fact1248 : HatA67Fact1248 := by
  intro X _ _ _ hc hA
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (QuotientGroup.mk' (Subgroup.center X)).ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  have hcard : Nat.card X = 1080 ∨ Nat.card X = 7560 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hc]
    rcases hA with hA | hA <;> obtain ⟨e⟩ := hA
    · left
      rw [Nat.card_congr e.toEquiv, Id2519.card_alternatingGroup_six]
    · right
      rw [Nat.card_congr e.toEquiv, Id2519.card_alternatingGroup_seven]
  refine ⟨?_, fun s q => ⟨fun h => ?_, fun h => H13.L34.not_isSLEps3_of_card_hat hcard s q h⟩⟩
  · apply FFC.ThreeRank2.pRank_two_le
    refine FFC.ThreeRank2.of_surjective_pgroup_ker (QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _) hp ?_
    rcases hA with hA | hA <;> obtain ⟨e⟩ := hA
    · exact (FFC.threeRank2_alt (by norm_num)).of_mulEquiv e.symm
    · exact (FFC.threeRank2_alt (by norm_num)).of_mulEquiv e.symm
  · obtain ⟨p, k, -, -, rfl, hX⟩ := h
    have hs : IsSimpleGroup X := by
      cases s
      · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 p k hX).2
      · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 p k hX).2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hb | ht
    · rw [hb, Subgroup.card_bot] at hc
      omega
    · rw [ht, Subgroup.card_top] at hc
      omega

end CFSG.Quasithin.H13
