module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7E
public import CFSG.Quasithin.Background.A3Structure318
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.EmptyFaithful.R3c2Theta
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.Quasithin.Vol2.Ch10SecQ34LH
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch1Inputs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem one_lt_pRank_subgroupOf {H J : Subgroup G} (hJ : J ∈ cComp H)
    (hY : IsAlt 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨
      IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7))) :
    1 < CFSG.Open.pRank 3 (J.subgroupOf H) := by
  rw [Ch11.SecA.pRank_subgroupOf_eq (le_of_mem_cComp hJ) Nat.prime_three (by norm_num)]
  have := (threeRank2_A7 hY).pRank_two_le
  omega

theorem normal_subgroupOf (h38 : A38ForSQTK) {H J : Subgroup G} (hH : SQTKGroup ↥H)
    (hJ : J ∈ cComp H) (hY : IsAlt 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨
      IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7))) :
    (J.subgroupOf H).Normal :=
  A318.normal_of_pRank_gt_one hH (h38 _ (SQTKHyp.of_sqtkGroup ↥H hH)) (subgroupOf_mem_cComp hJ)
    Nat.prime_three (by norm_num) (one_lt_pRank_subgroupOf hJ hY)

theorem mem_of_orderOf_eq_three (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {H J : Subgroup G} (hH : SQTKGroup ↥H) (hJ : J ∈ cComp H)
    (hY : IsAlt 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨
      IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7)))
    {y : G} (hyH : y ∈ H) (hy3 : orderOf y = 3) : y ∈ J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLH : J ≤ H := le_of_mem_cComp hJ
  have hSQ := SQTKHyp.of_sqtkGroup ↥H hH
  have hLc := subgroupOf_mem_cComp hJ
  obtain ⟨e₀⟩ := Ch11.SecA.quotPCore_subgroupOf_equiv (L := J) hLH
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm (isQuasisimple_A7 hY)
  have hr := one_lt_pRank_subgroupOf hJ hY
  have hconc := a318 hF hH (h36 _ hSQ) (h38 _ hSQ) hLc hQ' Nat.prime_three (by norm_num) hr
  have hk : ∀ x : ↥J, QuotientGroup.mk' (CFSG.pCore 2 ↥J) x = 1 →
      (⟨x, hLH x.2⟩ : ↥H) ∈ CFSG.pPrimeCore 3 ↥H := by
    intro x hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    have hxG : (x : G) ∈ pCoreOf 2 J := by
      exact ⟨x, hx, rfl⟩
    have hxH : (x : G) ∈ pCoreOf 2 H :=
      A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hJ) hxG
    have hxP : (⟨x, hLH x.2⟩ : ↥H) ∈ CFSG.pCore 2 ↥H :=
      (SecB.C10P34.mem_pCoreOf_iff (hLH x.2)).mp hxH
    have hcop : Nat.Coprime 3 (Nat.card ↥(CFSG.pCore 2 ↥H)) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥H))
      rw [hk]
      exact Nat.Coprime.pow_right _ (by norm_num)
    exact CFSG.le_pPrimeCore_of_normal_coprime CFSG.pCore_normal hcop hxP
  obtain ⟨π, hπ⟩ := R3c2.exists_surjection_starImage hLH (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
    (QuotientGroup.mk'_surjective _) hk
  have hns : ¬ Subsingleton ↥(starImage 3 (J.subgroupOf H)) := by
    intro hsub
    have hle : J.subgroupOf H ≤ CFSG.pPrimeCore 3 ↥H := by
      intro k hk'
      have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) k ∈ starImage 3 (J.subgroupOf H) :=
        ⟨k, hk', rfl⟩
      have h1 := congrArg Subtype.val (hsub.elim ⟨_, hmem⟩ 1)
      exact (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥H) k).1 h1
    have h3J : 3 ∣ Nat.card ↥(J.subgroupOf H) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv,
        Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥J)]
      rcases card_A7 hY with h | h <;> rw [h] <;> exact Dvd.dvd.mul_right (by norm_num) _
    have h3 := h3J.trans (Subgroup.card_dvd_of_le hle)
    have hc := (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H))
    exact absurd (Nat.Coprime.eq_one_of_dvd hc h3) (by norm_num)
  have hcard := card_quot_A7 hY π hπ hns
  have hy'3 : orderOf (⟨y, hyH⟩ : ↥H) = 3 := by rw [← Subgroup.orderOf_coe]; exact hy3
  suffices hmem : (⟨y, hyH⟩ : ↥H) ∈ J.subgroupOf H from Subgroup.mem_subgroupOf.mp hmem
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, -, h3⟩
  · rw [h1]
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by rw [hy'3, pow_one]⟩
  · exfalso
    obtain ⟨s, q, hmod, hPSL, -⟩ := h2
    exact not_case2_of_card hcard s q hmod hPSL
  · rcases h3 with hθ | h3b
    · rw [hθ]
      exact Subgroup.subset_closure ⟨Subgroup.mem_top _, hy'3⟩
    · exfalso
      obtain ⟨s, q, x, hSL, -⟩ := h3b
      exact not_isSLEps3_of_card hcard s q hSL

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K7
