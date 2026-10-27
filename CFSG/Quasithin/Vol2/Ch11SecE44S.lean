module

public import CFSG.Quasithin.Vol2.Ch11SecE44
public import CFSG.Quasithin.Vol2.Ch11SecBHBCore
public import CFSG.Quasithin.Vol2.Ch11SecB21OddS
public import CFSG.Quasithin.Vol2.Ch11SecE44Nat
public import CFSG.Quasithin.Vol2.Ch11SecE44Pre

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

@[expose] def Stmt11_4_4S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → KOf L V₁ V₁ = LOf L V₁ →
      ∀ z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G), z ≠ 1 →
        ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
          H ≤ Subgroup.centralizer ({z} : Set G) →
          ∀ K : Subgroup G, K ∈ cComp H → H = K ⊔ T →
            ¬ E2.E22LieCases H T (H ⊓ Subgroup.normalizer (L : Set G)) K

theorem stmt11_4_4S_of (hT : Facts44) (hF43 : Facts43) (hP : SecB.PointFacts)
    (hNS : SecB.FactNotSmall443) (hFB : SecB.FactBorelComm) (h4413 : H13.Stmt4_4_13Lie)
    (h442 : TmpL4_4_2) (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (h331 : Stmt3_3_1)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1104 : Stmt11_0_4) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1)
    (h1142 : Stmt11_4_2) : Stmt11_4_4S := by
  intro G _ _ T L I n V₁ h hV₁ hKL z hz hz1 H hH hHz K hKc hHK hlie
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.fsu.simple
  set M := Subgroup.normalizer (L : Set G) with hM
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hTH : T ≤ H := hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hns : ¬ Group.IsSolvable ↥H := fun hsol => not_isSolvable_of_mem_cComp hKc
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKH)
      (Subgroup.inclusion_injective hKH))
  have hKperf : ⁅K, K⁆ = K := (show quasithinIsCComponent K H from hKc).2.1
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hcV := (h1141 G T L I n V₁ X h hV₁ hX).1.1
  have hzV₁ := mem_V₁_of_mem_centralizer hF43 h1102 h hcV hV₁ hz.1 hz.2
  have hL₁z := lOf_mem_cComp_centralizer hF43 h1102 h1110 h1111 h1142 h hcV hV₁ hKL hz hz1
  have hzK := (kOf_le_centralizer_of hP hF43 h1102 h1142 h hcV hV₁ hz hz1).2
  rw [hKL] at hzK
  have hHL₁ : H ≤ Subgroup.normalizer (LOf L V₁ : Set G) := hHz.trans hzK
  have hKL₁ : ¬ K ≤ LOf L V₁ := by
    intro hle
    apply hH.2.1
    rw [hHK]
    exact sup_le (hle.trans ((perfectCore_le _).trans (inf_le_left.trans Subgroup.le_normalizer)))
      h.normal
  have hz2 : z ^ 2 = 1 := (SecA.isElemAbelian_fsuV h).2 z hz.1
  have hGz : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
    have hzle : Subgroup.zpowers z ≤ Subgroup.centralizer ({z} : Set G) :=
      (Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    have hzO : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf 2 hzle
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hzle).mpr
          (normalizer_zpowers_eq_centralizer hz2).ge)
        ((SecA.isPGroup_fsuV h).to_le ((Subgroup.zpowers_le).mpr hz.1))
    intro h0
    rw [h0] at hzO
    exact hz1 (Subgroup.mem_bot.mp (hzO (Subgroup.mem_zpowers z)))
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := hTH.trans hHz
  have hLocal := (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  have hcomm := commutator_le_of_cComp hLocal h37 h39 hGz
    (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTz) hHz hTH hKc hL₁z hKL₁
  obtain ⟨B, hB, hBab, hTB⟩ := SecB.derivedHallBorel_core hFB h.fsu.sylow hTH h.normal
    (SecA.isUniqueMaxOver_of_isHStar h331 h hH) hns hKc hHK hlie
  have hBH : B ≤ H := hB.1.trans inf_le_left
  have hBM : B ≤ M := hB.1.trans inf_le_right
  have hBS := le_sectionCentralizer_of_le hHK hKperf hT2 hHL₁ hcomm hBH hB.2.1
  have hBz : B ≤ Subgroup.centralizer ({z} : Set G) := hBH.trans hHz
  have hBV := le_normalizer_fsuV_of_le h1103 h hz.1 hz1 hBM hBz
  have hcop : Nat.Coprime (Nat.card B) (2 ^ n - 1) := by
    apply Nat.coprime_of_dvd
    intro p hp hpB hpq
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hxp⟩ := exists_prime_orderOf_dvd_card' p hpB
    have hxM : (x : G) ∈ M := hBM x.2
    have hxord : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hxp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hB.2.1) (even_iff_two_dvd.mpr hpB)
    have hxO : (x : G) ∈ oPrimeResidualOf p M :=
      Subgroup.subset_closure ⟨hxM, 1, by rw [pow_one]; exact hxord⟩
    have hxL : (x : G) ∈ L := by
      rcases SecA.kind_cases h1102 h with hk | hk | hk
      · by_cases h3 : 3 < p
        · rwa [(h1104 G T L I n h).1 p hp (Or.inr ⟨hk, hpq, h3⟩)] at hxO
        · have hp3 : p = 3 := by
            have := hp.two_le
            interval_cases p
            · exact absurd rfl hp2
            · rfl
          subst hp3
          exact (h1104 G T L I n h).2 hk (even_of_three_dvd hpq) _ hxM hxord (Or.inl (hBV x.2))
      · rwa [(h1104 G T L I n h).1 p hp (Or.inl ⟨Or.inl hk, dvd_two_pow_two_mul hpq⟩)] at hxO
      · rwa [(h1104 G T L I n h).1 p hp (Or.inl ⟨Or.inr hk, dvd_two_pow_two_mul hpq⟩)] at hxO
    obtain ⟨a, ha⟩ := isTwo_of_mem_L hT h1102 h hcV hV₁ hzV₁ hz1 hxL (hBz x.2) (hBS x.2)
    have hpa : p ∣ 2 ^ a := hxord ▸ orderOf_dvd_of_pow_eq_one ha
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpa))
  have hBC : B ≤ Subgroup.centralizer (fsuV T I : Set G) := fun b hb => by
    have hbd : orderOf b ∣ Nat.card B := Subgroup.orderOf_dvd_natCard B hb
    exact mem_centralizer_of_odd hT h1102 h hcV hV₁ (hBM hb) (hBV hb) (hBS hb)
      ⟨orderOf b, hB.2.1.of_dvd_nat hbd, Nat.Coprime.coprime_dvd_left hbd hcop,
        pow_orderOf_eq_one b⟩
  have hBbot : B = ⊥ := by
    have := SecB.inf_centralizer_hall_eq_botS h4413 h442 hNS h331 h3228 h hH hKc hHK hlie hB
      hBab hTB
    rwa [inf_eq_left.mpr hBC] at this
  have hHM2 : IsPGroup 2 ↥(H ⊓ M) := by
    obtain ⟨k, hk⟩ := hB.2.2
    rw [hBbot, Subgroup.relIndex_bot_left] at hk
    exact IsPGroup.of_card hk
  have hMK2 : IsPGroup 2 ↥(E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)) := by
    have h1 : IsPGroup 2 ↥(((H ⊓ M) ⊓ K).subgroupOf H) := fun x => by
      obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem hHM2
        ((inf_le_left : (H ⊓ M) ⊓ K ≤ H ⊓ M) (Subgroup.mem_subgroupOf.mp x.2))
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
    exact h1.map _
  obtain ⟨m, hm2, htype, hBor⟩ := hlie.exists_borel
  have htype' : IsPSL 2 2 m ↥(E2.star (H ⊓ M) H K) ∨ IsSz m ↥(E2.star (H ⊓ M) H K) ∨
      IsPSU 3 2 m ↥(E2.star (H ⊓ M) H K) ∨ IsPSL 3 2 m ↥(E2.star (H ⊓ M) H K) ∨
      E2.IsSp4Prime m ↥(E2.star (H ⊓ M) H K) := by
    rcases htype with ⟨-, h' | h' | h'⟩ | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · right; right; right; right
      rw [E2.IsSp4Prime]
      split_ifs with h1
      · omega
      · exact h'
  exact hT.borel _ _ _ m hm2 htype' hBor hMK2

end CFSG.Quasithin.Vol2.Ch11.SecE
