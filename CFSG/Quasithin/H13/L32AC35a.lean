module

public import CFSG.Quasithin.H13.L32A707c
public import CFSG.Quasithin.H13.L32AC47a
public import CFSG.Quasithin.H13.L32ACSk

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem isSz_of_coprime_three (h76 : Lemma14_7_6) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (h3 : ¬ 3 ∣ Nat.card ↥(modO2Image H K)) : ∃ n : ℕ, IsSz n (cStar K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 := h76 G T L V H S
  have hK3 : Nat.Coprime (Nat.card ↥(modO2Image H K)) 3 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3 |>.symm
  have hA := CFSG.Quasithin.lemma_1_2_1_four_strong S.hyp.fsu.qtke S.hyp.fsu.simple
    S.hyp.fsu.nonabelian h36 S.hz.1.2 hK
  obtain ⟨e⟩ := modO2_mulEquiv hK
  have hKsub : IsSubnormal (modO2Image H K) ⊤ := subnormal_of_mem_cComp (modO2Image_mem_cComp hK)
  have hsz : ∃ n : ℕ, IsSz n (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases hA.1 with ⟨-, -, hlistK⟩ | ⟨-, hZ3, -⟩ | h3' | h4
    · obtain ⟨f, -, -, hf⟩ := hlist _ hlistK h3
      exact ⟨f, isSz_congr e.symm hf⟩
    · exfalso
      apply h3
      rw [← hZ3]
      exact Subgroup.card_subgroup_dvd_card _
    · exact absurd (fitting_eq_bot_of_coprime_three hF3 hKsub hK3)
        (fitting_ne_bot_coprime_six (Or.inl h3')).1
    · exact absurd (fitting_eq_bot_of_coprime_three hF3 hKsub hK3)
        (fitting_ne_bot_coprime_six (Or.inr h4)).1
  obtain ⟨n, hn⟩ := hsz
  exact ⟨n, isSz_congr (cStarEquiv K).symm hn⟩

omit [Finite G] in
theorem card_modO2Image_dvd {K : Subgroup G} (hKH : K ≤ H) :
    Nat.card ↥(modO2Image H K) ∣ Nat.card ↥K := by
  have h1 := Subgroup.card_map_dvd (H := K.subgroupOf H) (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at h1

theorem lemma14_7_34_of (h76 : Lemma14_7_6) (h33 : Lemma14_7_33) (h36 : A36ForSQTK)
    (hlist : SQTKList3Dvd) : Lemma14_7_34 := by
  intro G _ _ T L V H S K hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hup : CFSG.Open.pRank 3 K ≤ 2 := by
    have h1 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hKH
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) ≤ 2 :=
      stronglyQuasithin_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hz.1.2 3 Nat.prime_three (by norm_num)
    rw [pRank_top_subtype] at h2
    omega
  have h3K : 3 ∣ Nat.card ↥K := by
    by_contra h3
    obtain ⟨n, hn⟩ := isSz_of_coprime_three h76 h36 hlist S hK
      (fun h => h3 (h.trans (card_modO2Image_dvd hKH)))
    exact h33 G T L V H S K hK n hn
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3K
  have hx' : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hE : IsElemAbelian 3 (Subgroup.zpowers (x : G)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      show (a : G) * b = b * a
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hx3 : (x : G) ^ 3 = 1 := by
        rw [← hx']
        exact pow_orderOf_eq_one _
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have hcard : Nat.card ↥(Subgroup.zpowers (x : G)) = 3 ^ 1 := by
    rw [Nat.card_zpowers, pow_one, hx']
  have hlow := CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.zpowers_le.mpr x.2) hE hcard
  omega

theorem pPrimeCore_star_eq_bot (h76 : Lemma14_7_6) (h33 : Lemma14_7_33) (h36 : A36ForSQTK)
    (hlist : SQTKList3Dvd) (S : Setting147 G T L V H) :
    CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hX
  have hN3 : Nat.Coprime (Nat.card ↥(CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))) 3 :=
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H ⧸ CFSG.pCore 2 ↥H)).symm
  have hF3 := h76 G T L V H S
  have hNn : (CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).Normal := CFSG.pPrimeCore_normal
  have hNsolv : ¬ Group.IsSolvable ↥(CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    intro hs
    have hsub : IsSubnormal (CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) ⊤ :=
      IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤)
    have hF := fitting_eq_bot_of_coprime_three hF3 hsub hN3
    exact hX (Subgroup.eq_bot_of_card_eq _
      ((CFSG.fitting_eq_bot_iff_card_eq_one_of_solvable _).mp hF))
  obtain ⟨J, hJ, hJN⟩ := exists_cComp_le_of_not_solvable le_top inferInstance hNsolv
  obtain ⟨K, hK, hKJ⟩ := exists_cComp_modO2Image_eq hJ
  have hK3 : ¬ 3 ∣ Nat.card ↥(modO2Image H K) := by
    rw [hKJ]
    intro h
    have h1 := h.trans (Subgroup.card_dvd_of_le hJN)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3.symm h1
  obtain ⟨n, hn⟩ := isSz_of_coprime_three h76 h36 hlist S hK hK3
  exact h33 G T L V H S K hK n hn

end CFSG.Quasithin.H13.L32A.C
