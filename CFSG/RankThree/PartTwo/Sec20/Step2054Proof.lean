module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.RankThree.PartTwo.Sec18.Item182
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem item189_case_one (h189 : Sec18.Item189) {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20One G A M L N c T)
    (h3 : ∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n))) :
    kTwenty M c ∈ oTwoComponentsIn M ∧ ¬ kTwenty M c ≤ N ∧
      Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c)))) := by
  obtain ⟨H, hH18, hH187, hL, hN⟩ := exists_sec18H_of_ctx20One hT
  obtain ⟨⟨hKC, hKN⟩, -, hcase⟩ := h189 G A M H c hH18 hH187
  rw [← hL, ← hN] at hKN hcase
  refine ⟨hKC, hKN, ?_⟩
  rcases hcase with ⟨-, -, -, hpar⟩ | ⟨m, -, hm, ⟨e⟩, -⟩
  · exact hpar
  · obtain ⟨n, hn, ⟨e'⟩⟩ := h3
    exact absurd ⟨e.symm.trans e'⟩ (not_nonempty_projSL_two_equiv_three hm hn.pos)

theorem pCoreOf_centralizer_ne_bot (hO2 : Step189O2) {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20One G A M L N c T)
    (h3 : ∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n))) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) ≠ ⊥ := by
  intro h0
  obtain ⟨H, hH18, hH187, -, -⟩ := exists_sec18H_of_ctx20One hT
  obtain ⟨m, hm, ⟨e⟩⟩ := hO2 G A M H c hH18 hH187 h0
  obtain ⟨n, hn, ⟨e'⟩⟩ := h3
  exact not_nonempty_projSL_two_equiv_three hm hn.pos ⟨e.symm.trans e'⟩

theorem normalizer_zpowers_le (hO2 : Step189O2) {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20One G A M L N c T)
    (h3 : ∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n))) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ N := by
  obtain ⟨-, -, -, -, -, hch⟩ := hT.one
  exact hch (pCoreOf_centralizer_ne_bot hO2 hT h3)

theorem pCoreOf_kTwenty_le (h187 : Sec18.Item187) {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20One G A M L N c T) :
    CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hH18, hH187, hL, hN⟩ := exists_sec18H_of_ctx20One hT
  have hAM : A ≤ M := Sec18.sec18Std_le hH18.toSec18Std
  have hMN : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (kTwenty M c) : Set G) :=
    (le_normalizer_normalClosureIn M c).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hmem : CFSG.Open.pCoreOf 2 (kTwenty M c) ∈
      invariantPiSubgroups ⊤ (A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M)) (piCompl 3) := by
    rw [mem_invariantPiSubgroups_piCompl_iff Nat.prime_three]
    refine ⟨le_top, ?_, sup_le (hAM.trans hMN)
      (((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right).trans hMN)⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kTwenty M c)).exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have h := h187 G A M H c hH18 hH187 _ hmem
  rw [← hL, ← hN] at h
  exact h

theorem mem_of_centralizes_quotient (h187 : Sec18.Item187) (hO2 : Step189O2)
    {A M L N : Subgroup G} {c : G} {T : Subgroup G} (hT : Ctx20One G A M L N c T)
    (h3 : ∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n)))
    {q : G} (hqM : q ∈ M)
    (hq : ∀ k ∈ kTwenty M c, q * k * q⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 (kTwenty M c)) :
    q ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kTwenty M c with hKdef
  set O := CFSG.Open.pCoreOf 2 K with hOdef
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hc3 : c ^ 3 = 1 := hT.mem_partTwoE.1.2 c hcA
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMO : M ≤ Subgroup.normalizer (O : Set G) :=
    (le_normalizer_normalClosureIn M c).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hO2' : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := hO2'.exists_card_eq
    rw [hk]
    intro h3'
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3')
    omega
  have hcO : Subgroup.zpowers c ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.zpowers_le.mpr (hKM hcK)).trans hMO
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers c) (Subgroup.zpowers c ⊔ O) :=
    isSylowOf_sup_of_coprime (isPGroup_zpowers_of_pow_three hc3) hO3 hcO
  have hqY : q ∈ Subgroup.normalizer ((Subgroup.zpowers c ⊔ O : Subgroup G) : Set G) := by
    apply mem_normalizer_of_map_conj_le
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, Subgroup.mem_comap]
      change q * c * q⁻¹ ∈ Subgroup.zpowers c ⊔ O
      have hx := hq c hcK
      have : q * c * q⁻¹ = (q * c * q⁻¹ * c⁻¹) * c := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hx)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
    · refine le_trans ?_ le_sup_right
      rintro _ ⟨o, ho, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hMO hqM) o).mp ho
  obtain ⟨y, hy, w, hw, rfl⟩ := Sec18.exists_mul_of_isSylowOf hsyl
    (Subgroup.zpowers_le.mpr hqY) (Subgroup.mem_zpowers q)
  have hNc := normalizer_zpowers_le hO2 hT h3
  have hYN : Subgroup.zpowers c ⊔ O ≤ N :=
    sup_le ((Subgroup.zpowers_le.mpr (Subgroup.le_normalizer (Subgroup.mem_zpowers c))).trans hNc)
      (pCoreOf_kTwenty_le h187 hT)
  exact N.mul_mem (hYN hy) (hNc hw)

theorem sup_pCoreOf_eq_core (h321 : Sec3.Item321Split)
    {A M L N : Subgroup G} {c : G} {T : Subgroup G} (hT : Ctx20 G A M L N c T)
    (hKC : kTwenty M c ∈ oTwoComponentsIn M)
    (h2 : ∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G))
    (h3 : ∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n))) :
    kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kTwenty M c with hKdef
  have hM := hT.mem_scriptM.1
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hTM : T ≤ M := hT.sylow.le
  have hXM : K ⊔ T ≤ M := sup_le hKM hTM
  have hT2 : IsPGroup 2 T := hT.sylow.isPGroup
  have hT1 : T ≠ ⊥ := by
    intro hbot
    have := pCoreOf_le_of_isSylowOf hT.sylow
    rw [hbot, le_bot_iff] at this
    exact pCoreOf_ne_bot_of_isMaximalTwoLocal hM this
  have hF : CFSG.generalizedFitting ↥(K ⊔ T) = CFSG.pCore 2 ↥(K ⊔ T) := by
    obtain ⟨P, hP, hP2, hMP⟩ := hM.1
    exact generalizedFitting_eq_of_pCoreOf_le hT.charTwoType ⟨P, hP, hP2, hMP⟩ hXM
      ((pCoreOf_le_of_isSylowOf hT.sylow).trans le_sup_right)
  have hKX : K ∈ oTwoComponentsIn (K ⊔ T) := by
    obtain ⟨-, ⟨-, hsn, -⟩⟩ := mem_oTwoComponentsIn_iff.mp hKC
    exact Sec18.mem_oTwoComponentsIn_of_le hKC le_sup_left
      (Sec18.isSubnormal_subgroupOf_of_le hsn hXM)
  have hTX : CFSG.ABGLocalTools.IsSylowOf 2 T (K ⊔ T) := hT.sylow.of_le le_sup_right hXM
  obtain ⟨n, hn, hiso⟩ := h3
  rcases h321 G (K ⊔ T) K T n hF hKX (hXM.trans (le_normalizer_normalClosureIn M c)) hTX rfl hn
      hiso with (hJ | hV) | hLQ
  · exfalso
    have : (CFSG.higherElemThompson T 0).Characteristic := higherElemThompson_zero_characteristic
    refine h2 (CFSG.higherElemThompson T 0) this ?_ hJ
    intro hbot
    apply thompsonOf_ne_bot hT2 hT1
    rw [Sec3.thompsonOf, hbot, Subgroup.map_bot]
  · exfalso
    have : (CFSG.omegaOneCenter (⊤ : Subgroup T)).Characteristic :=
      omegaOneCenter_top_characteristic
    refine h2 (CFSG.omegaOneCenter (⊤ : Subgroup T)) this ?_ ?_
    · intro hbot
      apply omegaZOf_ne_bot hT2 hT1
      rw [Sec3.omegaZOf, hbot, Subgroup.map_bot]
    · have hZV := omegaZOf_le_omegaZOf_pCoreOf hF hTX
      have hKZ : K ≤ Subgroup.centralizer (Sec3.omegaZOf T : Set G) := by
        have h1 : ⁅Sec3.omegaZOf T, K⁆ = ⊥ :=
          le_bot_iff.mp (hV ▸ Subgroup.commutator_mono hZV le_rfl)
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
        exact Subgroup.le_centralizer_iff.mp h1
      refine sup_le (hKZ.trans (Subgroup.centralizer_le_normalizer _)) ?_
      exact Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  · exact hLQ

theorem sup_pCoreOf_eq (h321 : Sec3.Item321Split) (h189 : Sec18.Item189)
    {A M L N : Subgroup G} {c : G} {T : Subgroup G} (hT : Ctx20One G A M L N c T)
    (h2 : ∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G))
    (h3 : ∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n))) :
    kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T :=
  sup_pCoreOf_eq_core h321 hT.toCtx20 (item189_case_one h189 hT h3).1 h2 h3

theorem exists_isSylowOf_le_inf_core {M N : Subgroup G} {c : G}
    (hO2K : CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ N)
    (hpar : Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c))))) :
    ∃ S₀ : Subgroup G, S₀ ≤ kTwenty M c ⊓ N ∧
      CFSG.ABGLocalTools.IsSylowOf 2 S₀ (kTwenty M c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kTwenty M c with hKdef
  obtain ⟨-, S, hS⟩ := hpar
  have hodd : ¬ 2 ∣ (((K ⊓ N).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))).index := by
    intro h
    have hle : (S : Subgroup (K ⧸ CFSG.pCore 2 K)) ≤
        ((K ⊓ N).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) :=
      Subgroup.le_normalizer.trans hS
    exact S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hle))
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 K)).ker ≤ (K ⊓ N).subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine ⟨x.2, hO2K ?_⟩
    exact ⟨x, hx, rfl⟩
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker] at hodd
  obtain ⟨S₀, hS₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (K ⊓ N)
  exact ⟨S₀, hS₀.le, isSylowOf_of_le_of_not_dvd hS₀ inf_le_left hodd⟩

theorem exists_isSylowOf_le_inf (h187 : Sec18.Item187) {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20One G A M L N c T)
    (hpar : Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c))))) :
    ∃ S₀ : Subgroup G, S₀ ≤ kTwenty M c ⊓ N ∧
      CFSG.ABGLocalTools.IsSylowOf 2 S₀ (kTwenty M c) :=
  exists_isSylowOf_le_inf_core (pCoreOf_kTwenty_le h187 hT) hpar

theorem step2054_of (h321 : Sec3.Item321Split) (h187 : Sec18.Item187) (h189 : Sec18.Item189)
    (hO2 : Step189O2) : Step2054 := by
  intro G _ _ A M L N c T hT h2 h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kTwenty M c with hKdef
  set Q := CFSG.Open.pCoreOf 2 (K ⊔ T) with hQdef
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hTM : T ≤ M := hT.sylow.le
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowOf (hT.sylow.of_le le_sup_right (sup_le hKM hTM))
  have hXQ : K ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
    have hle : Q ⊓ K ≤ CFSG.Open.pCoreOf 2 K := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
      intro k hk
      exact mem_normalizer_inf_of_mem (hXQ (Subgroup.mem_sup_left hk))
        (Subgroup.le_normalizer hk)
    intro q hq k hk
    refine hle ⟨?_, ?_⟩
    · have h1 : k * q⁻¹ * k⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hXQ (Subgroup.mem_sup_left hk)) _).mp (Q.inv_mem hq)
      have : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
      rw [this]
      exact Q.mul_mem hq h1
    · have h1 : q * k * q⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hMK (hTM (hQT hq))) k).mp hk
      exact K.mul_mem h1 (K.inv_mem hk)
  have hCN : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ N := by
    intro k hk q hq
    apply mem_of_centralizes_quotient h187 hO2 hT h3
      (M.mul_mem (M.mul_mem (hKM hk) (hTM (hQT hq))) (M.inv_mem (hKM hk)))
    intro k' hk'
    have hk'' : k⁻¹ * k' * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk) hk') hk
    have h1 := hQK q hq _ hk''
    have h2 : k * (q * (k⁻¹ * k' * k) * q⁻¹ * (k⁻¹ * k' * k)⁻¹) * k⁻¹ ∈
        CFSG.Open.pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp
        ((le_normalizer_normalClosureIn M c).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _) (hKM hk)) _).mp h1
    have : k * q * k⁻¹ * k' * (k * q * k⁻¹)⁻¹ * k'⁻¹ =
        k * (q * (k⁻¹ * k' * k) * q⁻¹ * (k⁻¹ * k' * k)⁻¹) * k⁻¹ := by group
    rw [this]
    exact h2
  obtain ⟨-, -, hpar⟩ := item189_case_one h189 hT h3
  obtain ⟨S₀, hS₀N, hS₀⟩ := exists_isSylowOf_le_inf h187 hT hpar
  have hTK : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K :=
    hT.sylow.inf_of_le_normalizer hKM hMK
  obtain ⟨k, hk, hkS⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hTK hS₀
  have hLQ := sup_pCoreOf_eq h321 h189 hT h2 h3
  have hTkN : T.map (MulAut.conj k).toMonoidHom ≤ N := by
    rintro _ ⟨t, ht, rfl⟩
    have htX : t ∈ K ⊔ Q := by
      rw [hLQ]
      exact Subgroup.mem_sup_right ht
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K Q
      (le_sup_left.trans hXQ)] at htX
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp htX
    have haT : a ∈ T := by
      have : a = t * b⁻¹ := by rw [← hab]; group
      rw [this]
      exact T.mul_mem ht (T.inv_mem (hQT hb))
    have h1 : k * a * k⁻¹ ∈ N := hS₀N (hkS ▸ ⟨a, ⟨haT, ha⟩, rfl⟩) |>.2
    have h2 : k * b * k⁻¹ ∈ N := hCN k hk b hb
    change k * t * k⁻¹ ∈ N
    have : k * t * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by rw [← hab]; group
    rw [this]
    exact N.mul_mem h1 h2
  have hTkM := isSylowOf_map_conj hT.sylow (hKM hk)
  have hodd : ¬ 2 ∣ (M ⊓ N).relIndex M :=
    not_dvd_relIndex_of_isSylowOf_le hTkM (le_inf hTkM.le hTkN) inf_le_left
  refine ⟨hodd, ?_⟩
  have hNc := normalizer_zpowers_le hO2 hT h3
  have hCc : M ⊓ Subgroup.centralizer ({c} : Set G) ≤ M ⊓ N := by
    refine le_inf inf_le_left (inf_le_right.trans ?_)
    refine le_trans ?_ hNc
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, Subgroup.mem_comap]
      change x * c * x⁻¹ ∈ Subgroup.zpowers c
      rw [Subgroup.mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers c
    · rw [Subgroup.zpowers_le]
      refine ⟨c, Subgroup.mem_zpowers c, ?_⟩
      change x * c * x⁻¹ = c
      rw [Subgroup.mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
  obtain ⟨Sc, hSc⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (M ⊓ Subgroup.centralizer {c})
  obtain ⟨T', hT', hScT'⟩ := exists_isSylowOf_le hSc.isPGroup (hSc.le.trans hCc)
  have hT'M : CFSG.ABGLocalTools.IsSylowOf 2 T' M := isSylowOf_of_le_of_not_dvd hT' inf_le_left hodd
  refine ⟨T', ⟨⟨hT.toHyp201, hT'M, ?_⟩, hT.one⟩, hT'.le.trans inf_le_right⟩
  have heq : T' ⊓ Subgroup.centralizer {c} = Sc :=
    hSc.eq_of_le (le_inf hScT' (hSc.le.trans inf_le_right)) (inf_le_inf_right _ hT'M.le)
      (hT'M.isPGroup.to_le inf_le_left)
  rw [heq]
  exact hSc

end CFSG.RankThree.PartTwo.Sec20
