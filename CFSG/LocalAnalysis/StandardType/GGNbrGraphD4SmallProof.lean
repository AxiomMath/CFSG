module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4SmallProofTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGNbrGraphD4OddInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → LargeEvenTwoLocalRank 3 G ≤ 5 →
      ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
        ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
          GGMarkingAll (K := ↥K) fun lab _ _ I F θ => lab.tag = .D → lab.rank = 4 → Odd lab.n →
            (LargeEvenTwoLocalRank 3 G = 5 → 3 ∣ lab.n) →
            (LargeEvenTwoLocalRank 3 G = 4 → ∀ (b : G) (hb : b ∈ Bs),
              (∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨b, hN hb⟩ = u * f) →
                ggLAut K θ ⟨b, hN hb⟩ ∈ I) →
            ∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
              ggLAut K θ ⟨b, hN hb⟩ = u * f

@[expose] def GGNbrGraphD4OddCentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → LargeEvenTwoLocalRank 3 G ≤ 5 →
      ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
        ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
          Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y →
          GGMarkingAll (K := ↥K) fun lab _ _ I F θ => lab.tag = .D → lab.rank = 4 → Odd lab.n →
            (LargeEvenTwoLocalRank 3 G = 5 → 3 ∣ lab.n) →
            (LargeEvenTwoLocalRank 3 G = 4 → ∀ (b : G) (hb : b ∈ Bs),
              (∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨b, hN hb⟩ = u * f) →
                ggLAut K θ ⟨b, hN hb⟩ ∈ I) →
            ∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
              ggLAut K θ ⟨b, hN hb⟩ = u * f

@[expose] def GGNbrD4BstarRankOddInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → LargeEvenTwoLocalRank 3 G ≤ 5 →
      ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K → Bs ≤ Subgroup.normalizer (K : Set G) →
        LargeEvenMarking ↥K (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n ∧
          (LargeEvenTwoLocalRank 3 G = 5 → 3 ∣ lab.n)) →
          27 * Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card ↥(Bs ⊓ K)

@[expose] def GGD4TwoLocalThree : LargeEvenRawCont :=
  fun R _ _ _ => ∃ E W : Subgroup R, IsElemAbelian 3 E ∧ Nat.card E = 27 ∧ IsPGroup 2 W ∧
    W ≠ ⊥ ∧ ∀ e ∈ E, ∀ w ∈ W, e * w * e⁻¹ ∈ W

@[expose] def GGD4TwoLocalThreeOddInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .D → lab.rank = 4 → Odd lab.n →
    LargeEvenLabelAll lab GGD4TwoLocalThree

section Config

variable {G : Type} [Group G] [Finite G]

theorem exists_field_of_five {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr 3 B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hperf : commutator K = ⊤) {R : Type} [Group R]
    {I F : Set (MulAut R)} (hKG : GGD4TrialityAutRankInn I F) (θ : K ⧸ Subgroup.center K ≃* R)
    (hm : 4 < LargeEvenTwoLocalRank 3 G) {b : G} (hb : b ∈ Bs)
    (hnot : ¬ ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨b, hN hb⟩ = u * f) :
    ∃ (b₁ : G) (hb₁ : b₁ ∈ Bs),
      (∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨b₁, hN hb₁⟩ = u * f) ∧
        ggLAut K θ ⟨b₁, hN hb₁⟩ ∉ I := by
  by_contra hno
  have h27 := hKG _ (isElemAbelian_range_ggBstarAut hC.2.1.2.1 hN θ) _ ⟨⟨b, hb⟩, rfl⟩ hnot (by
    rintro _ ⟨⟨b₁, hb₁⟩, rfl⟩ h
    by_contra hI
    exact hno ⟨b₁, hb₁, h, hI⟩)
  have h := three_pow_le_card_range_ggBstarAut hC hK hN hperf θ
  have h5 : 243 ≤ 3 ^ LargeEvenTwoLocalRank 3 G :=
    calc (243 : ℕ) = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ LargeEvenTwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem exists_card_bstar_inf_centralizer {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr 3 B x D J y K) :
    IsElemAbelian 3 (Bs ⊓ Subgroup.centralizer (K : Set G)) ∧ ∃ j : ℕ,
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) = 3 ^ j ∧ 1 ≤ j ∧
      (¬ Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y → 2 ≤ j) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBs : IsElemAbelian 3 Bs := hC.2.1.2.1
  have hyBs : y ∈ Bs := hC.2.1.1 hK.1.2.1
  have hy1 : y ≠ 1 := hK.1.2.2.1
  have hy3 : y ^ 3 = 1 := hBs.2 y hyBs
  have hyK : y ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hK.1.2.2.2.1 hk)
  have hDc := NbrGraphD4Small.isElemAbelian_of_le hBs
    (inf_le_left : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Bs)
  have hDc3 : IsPGroup 3 ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) :=
    fun g => ⟨1, Subtype.ext (by simpa using hDc.2 g g.2)⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hDc3
  have hyD : Subgroup.zpowers y ≤ Bs ⊓ Subgroup.centralizer (K : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hyBs, hyK⟩
  have hy : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
  have h3 : 3 ≤ 3 ^ j := by
    have := Subgroup.card_le_of_le hyD
    rwa [hy, hj] at this
  refine ⟨hDc, j, hj, ?_, fun hne => ?_⟩
  · by_contra h0
    have hj0 : j = 0 := by omega
    rw [hj0] at h3
    norm_num at h3
  · by_contra hlt
    have hj1 : j ≤ 1 := by omega
    have hle : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤
        Nat.card (Subgroup.zpowers y) := by
      rw [hj, hy]
      calc 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
        _ = 3 := by norm_num
    exact hne (Subgroup.eq_of_le_of_card_ge hyD hle).symm.le

theorem zpowers_facts {R : Type} [Group R] {φ : MulAut R} {E : Subgroup R} {w : R}
    (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) (hwφ : φ w = w) (hwE : ∀ e ∈ E, e * w = w * e) :
    IsPGroup 2 (Subgroup.zpowers w) ∧ Subgroup.zpowers w ≠ ⊥ ∧
      (∀ v ∈ Subgroup.zpowers w, φ v ∈ Subgroup.zpowers w) ∧
      ∀ e ∈ E, ∀ v ∈ Subgroup.zpowers w, e * v * e⁻¹ ∈ Subgroup.zpowers w := by
  refine ⟨fun g => ?_, fun h => hw1 ?_, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hj, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hw2, one_zpow]
  · rw [← Subgroup.mem_bot, ← h]
    exact Subgroup.mem_zpowers w
  · rintro _ ⟨n, rfl⟩
    exact ⟨n, by rw [map_zpow, hwφ]⟩
  · rintro e he _ ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    change w ^ n = e * w ^ n * e⁻¹
    rw [(Commute.zpow_right (hwE e he) n).eq, mul_inv_cancel_right]

end Config

section Certs


theorem isPGroup_two_center_of_marking_omegaPlus {H : Type} [Group H] [Finite H]
    (hmk : LargeEvenMarking H (fun lab _ _ _ _ _ => lab.tag = .D ∧ 4 ≤ lab.rank)) :
    IsPGroup 2 (Subgroup.center H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card (Subgroup.center H)) with
    ⟨k, hk⟩ | ⟨q, hq, hqd, hqo⟩
  · exact IsPGroup.of_card hk
  · exfalso
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hqo) even_two
    exact (Nat.Prime.coprime_iff_not_dvd hq).mp
      (coprime_card_center_of_marking_omegaPlus hq hq2 hmk) hqd

theorem ggNbrGraphD4SmallInput_of_odd (hKG : GGD4FieldFixLocalOddInput)
    (hR : GGNbrGraphD4OddInput) : GGNbrGraphD4SmallInput := by
  intro G _ _ B Bs x L D J hC hm y K hK hN P hP
  have hp : Nat.Prime 3 := Nat.prime_three
  have hBs : IsElemAbelian 3 Bs := hC.2.1.2.1
  have hyBs : y ∈ Bs := hC.2.1.1 hK.1.2.1
  have hy1 : y ≠ 1 := hK.1.2.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hK.1.2.2.2.1
  have hy3 : y ^ 3 = 1 := hBs.2 y hyBs
  have hyK : y ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hKy hk)
  obtain ⟨hDc, j, hj, hj1, -⟩ := exists_card_bstar_inf_centralizer hC hK
  obtain ⟨hperf, lab, hlab, hraw⟩ := hR G B Bs x L D J hC hm y K hK hN P hP
  by_cases hD : lab.tag = .D ∧ lab.rank = 4
  swap
  · refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hθP, -⟩
    exact ⟨hs, hna, θ, hθP, fun h1 h2 => absurd ⟨h1, h2⟩ hD⟩
  obtain ⟨ht, h4⟩ := hD
  have hZ2 : IsPGroup 2 (Subgroup.center K) :=
    isPGroup_two_center_of_marking_omegaPlus ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, ht, h4.ge⟩) hraw⟩
  have hall : LargeEvenLabelAll lab fun R _ I _ => I = LargeEvenInnSet R ∧
      (3 ∣ 2 ^ lab.n - 1 → GGTorusLift 3 4 R) :=
    largeEvenLabelAll_omegaPlus ht (by omega) fun 𝔽 _ _ _ h𝔽 => ⟨rfl, fun h3 => by
      rw [h4]
      exact TableBSymp.ggTorusLift_omegaPlus hp (by norm_num) (by rw [h𝔽]; exact h3)
        (by norm_num)⟩
  rcases Nat.even_or_odd lab.n with hev | hodd
  ·
    have h3 : 3 ∣ 2 ^ lab.n - 1 := by
      obtain ⟨k, hk⟩ := hev
      have h := Nat.sub_dvd_pow_sub_pow 4 1 k
      rw [one_pow, show (4 : ℕ) - 1 = 3 by norm_num,
        show (4 : ℕ) ^ k = 2 ^ (k + k) by rw [← two_mul, pow_mul]; norm_num] at h
      rw [hk]
      exact h
    have hraw' := largeEvenLabelAll_d4TrialityAutRankInn ht h4 _
      (largeEvenLabelAll_d4FieldFixTorus ht h4 hev _ (hall _ hraw))
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw'⟩
    rintro R _ I F ⟨⟨⟨⟨hs, hna, θ, hθP, -⟩, hI, hTL⟩, hFT⟩, hAR⟩
    subst hI
    refine ⟨hs, hna, θ, hθP, fun _ _ _ b hb => ?_⟩
    have h5 := succ_le_twoLocalRank_of_torusLift hp hKy hy3 hy1 hperf θ (hTL h3)
    by_contra hnot
    obtain ⟨b₁, hb₁, hIF, hnI⟩ := exists_field_of_five hC hK hN hperf hAR θ (by omega) hb hnot
    have hb₁3 : b₁ ^ 3 = 1 := hBs.2 b₁ hb₁
    have hφ3 : ggLAut K θ ⟨b₁, hN hb₁⟩ ^ 3 = 1 := ggLAut_pow_eq_one K θ (hN hb₁) hb₁3
    obtain ⟨E, W, hE, hE81, hEφ, hW2, hW1, hWφ, hWE⟩ := hFT hs hna _ hφ3 hnI hIF
    have h6 := NbrGraphD4Small.le_twoLocalRank_of_fix (k := 4) hperf hZ2
      (L45RankX.conj_injective_of_simple hs hna) (hN hb₁) hb₁3 hnI inf_le_right hDc hj
      (fun d hd => mul_comm_of_isElemAbelian hBs hb₁ hd.1) hE (by rw [hE81]; norm_num) hEφ hW2
      hW1 hWφ hWE
    omega
  ·
    have hraw' := hKG lab hlab ht h4 hodd _ (hall _ hraw)
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw'⟩
    rintro R _ I F ⟨⟨⟨hs, hna, θ, hθP, hθR⟩, hI, -⟩, hFix⟩
    subst hI
    refine ⟨hs, hna, θ, hθP, fun _ _ h5 => hθR ht h4 hodd h5 fun hm4 b₁ hb₁ hIF => ?_⟩
    by_contra hnI
    have hb₁3 : b₁ ^ 3 = 1 := hBs.2 b₁ hb₁
    have hφ3 : ggLAut K θ ⟨b₁, hN hb₁⟩ ^ 3 = 1 := ggLAut_pow_eq_one K θ (hN hb₁) hb₁3
    obtain ⟨E, w, hE, hE27, hEφ, hw2, hw1, hwφ, hwE⟩ := hFix hs hna _ hφ3 hnI hIF
    have h5' := L45KG.five_le_twoLocalRank_of_fix hperf hZ2
      (L45RankX.conj_injective_of_simple hs hna) (hN hb₁) hb₁3 hnI hyK hy3 hy1
      (mul_comm_of_isElemAbelian hBs hb₁ hyBs) hE hE27 hEφ hw2 hw1 hwφ hwE
    omega

theorem ggNbrGraphD4OddInput_of_cent (hKG : GGD4FieldFixLocalOddInput)
    (hTL : GGD4TwoLocalThreeOddInput) (hR : GGNbrGraphD4OddCentInput) :
    GGNbrGraphD4OddInput := by
  intro G _ _ B Bs x L D J hC hm y K hK hN P hP
  by_cases hc : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y
  · exact hR G B Bs x L D J hC hm y K hK hN hc P hP
  have hBs : IsElemAbelian 3 Bs := hC.2.1.2.1
  obtain ⟨hDc, j, hj, -, hj2⟩ := exists_card_bstar_inf_centralizer hC hK
  have hj2' := hj2 hc
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  by_cases hD : lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n
  swap
  · refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hθP⟩
    exact ⟨hs, hna, θ, hθP, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hD⟩
  obtain ⟨ht, h4, hodd⟩ := hD
  have hZ2 : IsPGroup 2 (Subgroup.center K) :=
    isPGroup_two_center_of_marking_omegaPlus ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, ht, h4.ge⟩) hraw⟩
  have hall : LargeEvenLabelAll lab fun R _ I _ => I = LargeEvenInnSet R :=
    largeEvenLabelAll_omegaPlus ht (by omega) fun _ _ _ _ _ => rfl
  have hraw' := largeEvenLabelAll_d4TrialityAutRankInn ht h4 _
    (hTL lab hlab ht h4 hodd _ (hKG lab hlab ht h4 hodd _ (hall _ hraw)))
  refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw'⟩
  rintro R _ I F ⟨⟨⟨⟨⟨hs, hna, θ, hθP⟩, hI⟩, hFix⟩, hLoc⟩, hAR⟩
  subst hI
  have hinj := L45RankX.conj_injective_of_simple hs hna
  refine ⟨hs, hna, θ, hθP, fun _ _ _ _ _ b hb => ?_⟩
  rcases Nat.lt_or_ge 4 (LargeEvenTwoLocalRank 3 G) with h5 | h4'
  ·
    by_contra hnot
    obtain ⟨b₁, hb₁, hIF, hnI⟩ := exists_field_of_five hC hK hN hperf hAR θ h5 hb hnot
    have hb₁3 : b₁ ^ 3 = 1 := hBs.2 b₁ hb₁
    have hφ3 : ggLAut K θ ⟨b₁, hN hb₁⟩ ^ 3 = 1 := ggLAut_pow_eq_one K θ (hN hb₁) hb₁3
    obtain ⟨E, w, hE, hE27, hEφ, hw2, hw1, hwφ, hwE⟩ := hFix hs hna _ hφ3 hnI hIF
    obtain ⟨hW2, hW1, hWφ, hWE⟩ := zpowers_facts hw2 hw1 hwφ hwE
    have h6 := NbrGraphD4Small.le_twoLocalRank_of_fix (k := 3) hperf hZ2 hinj (hN hb₁) hb₁3 hnI
      inf_le_right hDc hj (fun d hd => mul_comm_of_isElemAbelian hBs hb₁ hd.1) hE
      (by rw [hE27]; norm_num) hEφ hW2 hW1 hWφ hWE
    omega
  ·
    exfalso
    obtain ⟨E, W, hE, hE27, hW2, hW1, hWE⟩ := hLoc
    have h5' := NbrGraphD4Small.le_twoLocalRank_of_local (k := 3) hperf hZ2 θ hinj inf_le_right
      hDc hj hE (by rw [hE27]; norm_num) hW2 hW1 hWE
    omega

theorem ggNbrGraphD4SmallInput_of_cent (hKG : GGD4FieldFixLocalOddInput)
    (hTL : GGD4TwoLocalThreeOddInput) (hR : GGNbrGraphD4OddCentInput) :
    GGNbrGraphD4SmallInput :=
  ggNbrGraphD4SmallInput_of_odd hKG (ggNbrGraphD4OddInput_of_cent hKG hTL hR)

theorem ggNbrGraphD4Input_of_cent (hKG : GGD4FieldFixLocalOddInput)
    (hTL : GGD4TwoLocalThreeOddInput) (hR : GGNbrGraphD4OddCentInput) : GGNbrGraphD4Input :=
  ggNbrGraphD4Input_of_small (ggNbrGraphD4SmallInput_of_cent hKG hTL hR)

theorem ggNbrGraphD4Input_of_odd (hKG : GGD4FieldFixLocalOddInput)
    (hR : GGNbrGraphD4OddInput) : GGNbrGraphD4Input :=
  ggNbrGraphD4Input_of_small (ggNbrGraphD4SmallInput_of_odd hKG hR)

end Certs

theorem ggNbrGraphD4OddInput_of_small (h : GGNbrGraphD4SmallInput) : GGNbrGraphD4OddInput := by
  intro G _ _ B Bs x L D J hC hm y K hK hN P hP
  refine largeEvenMarking_mono ?_ (h G B Bs x L D J hC hm y K hK hN P hP)
  rintro lab R _ I F θ ⟨hθ, hQ⟩
  exact ⟨hθ, fun h1 h2 _ h5 _ => hQ h1 h2 h5⟩

theorem ggNbrGraphD4OddCentInput_of_odd (h : GGNbrGraphD4OddInput) :
    GGNbrGraphD4OddCentInput :=
  fun G _ _ B Bs x L D J hC hm y K hK hN _ => h G B Bs x L D J hC hm y K hK hN

theorem ggNbrGraphD4OddInput_of_bstarRank (hR : GGNbrD4BstarRankOddInput) :
    GGNbrGraphD4OddInput := by
  intro G _ _ B Bs x L D J hC hm y K hK hN P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  by_cases hD : lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n ∧
      (LargeEvenTwoLocalRank 3 G = 5 → 3 ∣ lab.n)
  · have hmark : LargeEvenMarking ↥K fun lab' _ _ _ _ _ => lab'.tag = .D ∧ lab'.rank = 4 ∧
        Odd lab'.n ∧ (LargeEvenTwoLocalRank 3 G = 5 → 3 ∣ lab'.n) :=
      ⟨hperf, lab, hlab, largeEvenRawDatum_mono
        (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, hD⟩) hraw⟩
    have h27 := hR G B Bs x L D J hC hm y K hK hN hmark
    have hraw' := largeEvenLabelAll_d4TrialityCentBound hD.1 hD.2.1 _ hraw
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw'⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hKG⟩
    exact ⟨hs, hna, θ, hθ, fun _ _ _ _ _ b hb =>
      exists_inner_mul_field_of_bstarRank hC.2.1.2.1 hN h27 hKG θ hb⟩
  · refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, hθ, fun h1 h2 h3 h5 _ => absurd ⟨h1, h2, h3, h5⟩ hD⟩

theorem ggNbrGraphD4OddInput_of_bstarRank' (hR : GGNbrD4BstarRankInput) :
    GGNbrGraphD4OddInput :=
  ggNbrGraphD4OddInput_of_small (ggNbrGraphD4SmallInput_of_bstarRank hR)

end CFSG.StandardType
