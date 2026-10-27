module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionDefs
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixKRank

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section SixFFAux

theorem sixFF_ff5_aux_odd_part (n : ℕ) (hn : n ≠ 0) :
    Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
  have he : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, hn⟩
  have h2 : Even ((2 ^ n) ^ 2) := Nat.even_pow.mpr ⟨he, two_ne_zero⟩
  have h4 : Even ((2 ^ n) ^ 4) := Nat.even_pow.mpr ⟨he, by norm_num⟩
  have p2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have p4 : 1 ≤ (2 ^ n) ^ 4 := Nat.one_le_pow _ _ (by positivity)
  apply Nat.odd_mul.mpr
  constructor
  · rw [Nat.odd_iff]
    have h := Nat.even_iff.mp h2
    generalize (2 ^ n) ^ 2 = a at h p2 ⊢
    omega
  · rw [Nat.odd_iff]
    have h := Nat.even_iff.mp h4
    generalize (2 ^ n) ^ 4 = a at h p4 ⊢
    omega

theorem sixFF_ff5_aux_pow_dvd (a q O : ℕ) (hq : 0 < q) (hO : Odd O) (h : 2 ^ a ∣ q ^ 4 * O) :
    2 ^ a ≤ q ^ 4 := by
  have hO2 : ¬ 2 ∣ O := by
    intro hd
    have := Nat.odd_iff.mp hO
    omega
  have hcop : Nat.Coprime (2 ^ a) O :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hO2)
  exact Nat.le_of_dvd (pow_pos hq 4) (hcop.dvd_of_dvd_mul_right h)

theorem sixFF_ff5_aux_pow_dvd_n (b n : ℕ) (hn : n ≠ 0) (h : 2 ^ b ∣ n) :
    2 ^ b ≤ 2 ^ (n.factorization 2) :=
  Nat.pow_le_pow_right (by norm_num)
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).mp h)

theorem sixFF_ff5_aux_inner_card {K : Type} [Field K] [CharP K 2]
    [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (H : Subgroup (MulAut (antiSp K)))
    (hH : H ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K))
    (a : ℕ) (ha : Nat.card H = 2 ^ a) : Nat.card H ≤ Nat.card K ^ 4 := by
  obtain ⟨hinj, -, -, -⟩ := even_symplectic_four_outer_involution_rank_and_perfect_residual hn hK
  have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K)) =
      Nat.card (antiSp K) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hdvd : Nat.card H ∣ Nat.card (antiSp K) := hinner ▸ Subgroup.card_dvd_of_le hH
  rw [card_antiSp rfl] at hdvd
  have hodd : Odd ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
    rw [hK]
    exact sixFF_ff5_aux_odd_part n (by omega)
  have hqpos : 0 < Nat.card K := by
    rw [hK]
    exact pow_pos (by norm_num) n
  rw [ha] at hdvd ⊢
  exact sixFF_ff5_aux_pow_dvd a _ _ hqpos hodd hdvd

theorem sixFF_ff5_aux_count {K : Type} [Field K] [CharP K 2]
    [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (Γ : Subgroup (MulAut (antiSp K))) (m : ℕ) (hm : Nat.card Γ = 2 ^ m)
    (hform : ∀ g ∈ Γ, ∃ a : antiSp K, ∃ k : ℕ, g = MulAut.conj a * frobAut K ^ k) :
    Nat.card Γ ≤ Nat.card K ^ 4 * 2 ^ (n.factorization 2) := by
  classical
  let θ : Γ →* CFSG.ComponentClassification.OuterAutomorphisms.Outer (antiSp K) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K))).comp
      Γ.subtype
  have hdec : Nat.card Γ = Nat.card θ.ker * Nat.card θ.range := by
    have hq := Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker, hq]
    ring
  have hdvdker : Nat.card θ.ker ∣ 2 ^ m := hm ▸ ⟨Nat.card θ.range, hdec⟩
  have hdvdrange : Nat.card θ.range ∣ 2 ^ m := hm ▸ ⟨Nat.card θ.ker, by rw [hdec, mul_comm]⟩
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdker
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdrange
  set Fq := (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K)))
    (frobAut K) with hFq
  have hrange : θ.range ≤ Subgroup.zpowers Fq := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨a, k, hg⟩ := hform g.1 g.2
    have h1 : θ g = Fq ^ k := by
      show QuotientGroup.mk' _ g.1 = _
      rw [hg, map_mul, map_pow]
      have : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K))
          (MulAut.conj a) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact ⟨a, rfl⟩
      rw [this, one_mul]
    rw [h1]
    exact Subgroup.npow_mem_zpowers _ _
  have hFqn : Fq ^ n = 1 := by
    rw [hFq, ← map_pow, FieldInvolution.frobAut_pow_eq_one hK, map_one]
  have hrangedvd : Nat.card θ.range ∣ n := by
    refine (Subgroup.card_dvd_of_le hrange).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hFqn
  have hbn : Nat.card θ.range ≤ 2 ^ (n.factorization 2) := by
    rw [hb]
    exact sixFF_ff5_aux_pow_dvd_n b n (by omega) (by rw [← hb]; exact hrangedvd)
  have hkerle : θ.ker.map Γ.subtype ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (antiSp K) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (antiSp K)) x.1 = 1 := hx
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  have hkercard : Nat.card (θ.ker.map Γ.subtype) = Nat.card θ.ker :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective Γ)
  have hkera : Nat.card θ.ker ≤ Nat.card K ^ 4 := by
    have := sixFF_ff5_aux_inner_card hn hK (θ.ker.map Γ.subtype) hkerle a
      (by rw [hkercard]; exact ha)
    rwa [hkercard] at this
  rw [hdec]
  exact Nat.mul_le_mul hkera hbn

theorem sixFF_ff5_aux_normalizer_inf {G : Type} [Group G] {A B : Subgroup G} {y : G}
    (hA : y ∈ normalizer (A : Set G)) (hB : y ∈ normalizer (B : Set G)) :
    y ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB x]

theorem sixFF_ff5_aux_normalizer_of_char {G : Type} [Group G] {R : Subgroup G} {J : Subgroup R}
    [J.Characteristic] {Q : Subgroup G} (hJ : J.map R.subtype = Q) {y : G} (hy : y ∈ R) :
    y ∈ normalizer (Q : Set G) := by
  have fwd : ∀ z ∈ R, ∀ x ∈ Q, z * x * z⁻¹ ∈ Q := by
    intro z hz x hx
    rw [← hJ] at hx ⊢
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj (⟨z, hz⟩ : R)) j, ?_, ?_⟩
    · have h := Subgroup.characteristic_iff_map_eq.mp ‹J.Characteristic›
        (MulAut.conj (⟨z, hz⟩ : R))
      rw [← h]
      exact Subgroup.mem_map_of_mem _ hj
    · simp [MulAut.conj_apply]
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fwd y hy x, fun hx => ?_⟩
  have h2 := fwd y⁻¹ (inv_mem hy) _ hx
  simpa [mul_assoc] using h2

end SixFFAux

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixFF_ff5_aux_Q_inf_L (hS : SCSetting L K n φ t i) : (P φ ⊔ zpowers t) ⊓ L = P φ := by
  apply le_antisymm
  · rintro x ⟨hxQ, hxL⟩
    obtain ⟨p, hp, c, hc, rfl⟩ := hS.fc.setup.mem_Q.mp hxQ
    have hpL : p ∈ L := pull_le φ _ hp
    have hcL : c ∈ L := by
      have := L.mul_mem (L.inv_mem hpL) hxL
      simpa using this
    have hc1 : c ∈ L ⊓ zpowers t := ⟨hcL, hc⟩
    rw [hS.fc.setup.L_inf_T, Subgroup.mem_bot] at hc1
    rw [hc1, mul_one]
    exact hp
  · exact le_inf le_sup_left (pull_le φ _)

theorem sixFF_ff5_aux_normalizes_Q
    (hS : SCSetting L K n φ t i) {R₁ : Subgroup G} (hRC : R₁ ≤ centralizer ({t} : Set G))
    (hR : IsPGroup 2 R₁) (hQR : P φ ⊔ zpowers t ≤ R₁) {y : G} (hy : y ∈ R₁) :
    y ∈ normalizer ((P φ ⊔ zpowers t : Subgroup G) : Set G) := by
  haveI := CFSG.LocalAnalysis.SymplecticFourRankThompson.rankThompson_characteristic (G := R₁)
  exact sixFF_ff5_aux_normalizer_of_char (hS.fc.setup.rankThompson_eq hRC hR hQR) hy

theorem sixFF_ff5
    (hS : SCSetting L K n φ t i) (f2 : FF2Concl n φ t i) : FF5Concl n φ t := by
  intro R hR hRC
  obtain ⟨Syl, hQSyl⟩ := sixK_k5_aux_sylow hS
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : Subgroup G, R₁ = (Syl : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype := ⟨_, rfl⟩
  rw [← hR₁] at hQSyl
  have hR₁C : R₁ ≤ centralizer ({t} : Set G) := hR₁ ▸ Subgroup.map_subtype_le _
  have hR₁2 : IsPGroup 2 R₁ := hR₁ ▸ Syl.isPGroup'.map _
  have hRle : Nat.card R ≤ Nat.card R₁ := by
    have hRc2 : IsPGroup 2 (R.subgroupOf (centralizer ({t} : Set G))) :=
      hR.of_equiv (subgroupOfEquivOfLe hRC).symm
    obtain ⟨Syl', hSyl'⟩ := hRc2.exists_le_sylow
    have h1 : Nat.card (R.subgroupOf (centralizer ({t} : Set G))) = Nat.card R :=
      Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv
    have h2 : Nat.card (R.subgroupOf (centralizer ({t} : Set G))) ≤ Nat.card Syl' :=
      Subgroup.card_le_of_le hSyl'
    have h3 : Nat.card Syl' = Nat.card Syl := by
      rw [Sylow.card_eq_multiplicity Syl', Sylow.card_eq_multiplicity Syl]
    have h4 : Nat.card R₁ = Nat.card Syl := by
      rw [hR₁]
      exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    omega
  have hRN : R₁ ≤ normalizer (L : Set G) := hR₁C.trans hS.fc.setup.cent_le
  let ρ : R₁ →* MulAut (antiSp K) := (FieldInvolution.transAct φ).comp (Subgroup.inclusion hRN)
  have hdec : Nat.card R₁ = Nat.card ρ.ker * Nat.card ρ.range := by
    have hq := Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker, hq]
    ring
  have hker : Nat.card ρ.ker ≤ 2 := by
    have hsub : ρ.ker.map R₁.subtype ≤ zpowers t := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      have hxL : (x : G) ∈ centralizer (L : Set G) :=
        (FieldInvolution.transAct_eq_one_iff φ (Subgroup.inclusion hRN x)).mp
          (MonoidHom.mem_ker.mp hx)
      rw [← hS.fc.setup.cent_inf]
      exact Subgroup.mem_inf.mpr ⟨hxL, hR₁C x.2⟩
    have hmap : Nat.card (ρ.ker.map R₁.subtype) = Nat.card ρ.ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective R₁)
    rw [← hmap]
    calc Nat.card (ρ.ker.map R₁.subtype) ≤ Nat.card (zpowers t) := Subgroup.card_le_of_le hsub
      _ = 2 := by rw [Nat.card_zpowers, hS.fc.setup.order_t]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR₁2
  have hdvdrange : Nat.card ρ.range ∣ 2 ^ m := by
    rw [← hm, hdec]
    exact dvd_mul_left _ _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdrange
  have hform : ∀ g ∈ ρ.range, ∃ a : antiSp K, ∃ k : ℕ, g = MulAut.conj a * frobAut K ^ k := by
    rintro _ ⟨y, rfl⟩
    have hyQ := sixFF_ff5_aux_normalizes_Q hS hR₁C hR₁2 hQSyl y.2
    have hyC : (y : G) ∈ centralizer ({t} : Set G) := hR₁C y.2
    have hyL : (y : G) ∈ normalizer (L : Set G) := hRN y.2
    have hyP : (y : G) ∈ normalizer (P φ : Set G) := by
      have h := sixFF_ff5_aux_normalizer_inf hyQ hyL
      rwa [sixFF_ff5_aux_Q_inf_L hS] at h
    have hyU1 := SingleComm.normalizer_Q_le_normalizer_U hS.fc i hS.ne_bot hS.eq_bot i hyQ
    have hyU2 := SingleComm.normalizer_Q_le_normalizer_U hS.fc i hS.ne_bot hS.eq_bot i.swap hyQ
    obtain ⟨p, -, j, -, k, -, hk⟩ := f2 (Subgroup.inclusion hRN y) hyC hyP hyU1 hyU2
    exact ⟨p * j, k, hk⟩
  have hcount := sixFF_ff5_aux_count hS.fc.setup.two_le hS.fc.setup.card_K ρ.range k hk hform
  calc Nat.card R ≤ Nat.card R₁ := hRle
    _ = Nat.card ρ.ker * Nat.card ρ.range := hdec
    _ ≤ 2 * (Nat.card K ^ 4 * 2 ^ (n.factorization 2)) := Nat.mul_le_mul hker hcount
    _ = 2 * Nat.card K ^ 4 * 2 ^ (n.factorization 2) := by ring

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
