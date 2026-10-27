module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadDefs
import CFSG.RankThree.PartOne.KF.LayerCover
import CFSG.GroupTheory.SubgroupOfQuotientMapCentral
import CFSG.GroupTheory.CommutingConjugatePair
import CFSG.GroupTheory.ConjTransport
import CFSG.GroupTheory.OddKernelImage
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverSylow
import CFSG.LocalAnalysis.UniquenessCase.UC1K43Q8
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelNormalizers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G X : Type} [Group G] [Group X] [Finite G] [Finite X]

private theorem exists_pow_three_eq_zpowers {B : Subgroup G} (hB : Nat.card B = 3) :
    ∃ β : G, β ^ 3 = 1 ∧ B = Subgroup.zpowers β := by
  obtain ⟨β, -, hβord, hBz⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.K43.exists_generator_of_card_three hB
  exact ⟨β, by rw [← hβord]; exact pow_orderOf_eq_one β, hBz⟩

omit [Finite G] [Finite X] in
private theorem isCentralPQuot_three (ρ : G →* X) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center G) (hcop : Nat.Coprime (Nat.card ρ.ker) 6) :
    CFSG.RankThree.PartOne.KFU.IsCentralPQuot 3 ρ :=
  ⟨hρ, hker, hcop.symm.coprime_dvd_left (by norm_num)⟩

omit [Finite G] [Finite X] in
private theorem odd_card_ker_of_coprime (ρ : G →* X)
    (hcop : Nat.Coprime (Nat.card ρ.ker) 6) : Odd (Nat.card ρ.ker) :=
  Nat.coprime_two_right.mp (hcop.coprime_dvd_right (by norm_num))

omit [Finite G] [Finite X] in
private theorem map_subgroupOf_top_eq (ρ : G →* X) (K : Subgroup G) :
    Subgroup.map (ρ.comp (⊤ : Subgroup G).subtype) (K.subgroupOf ⊤) = K.map ρ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mp hy)
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, Subgroup.mem_top y⟩, hy, rfl⟩

omit [Finite X] in
private theorem map_centralizer_of_card_three (ρ : G →* X) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center G) (hcop : Nat.Coprime (Nat.card ρ.ker) 6)
    {B : Subgroup G} (hB : Nat.card B = 3) :
    Subgroup.centralizer ((B.map ρ : Subgroup X) : Set X) =
      (Subgroup.centralizer ((B : Subgroup G) : Set G)).map ρ := by
  obtain ⟨β, hβ3, hBz⟩ := exists_pow_three_eq_zpowers hB
  have hq := isCentralPQuot_three ρ hρ hker hcop
  have hBmap : B.map ρ = Subgroup.zpowers (ρ β) := by
    rw [hBz, MonoidHom.map_zpowers]
  rw [hBmap, hBz, CFSG.GroupTheory.centralizer_zpowers_eq β,
    CFSG.GroupTheory.centralizer_zpowers_eq (ρ β), hq.map_centralizer hβ3]

omit [Finite X] in
private theorem map_pCoreOf_of_central (ρ : G →* X) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center G) (hodd : Odd (Nat.card ρ.ker)) (Y : Subgroup G) :
    pCoreOf 2 (Y.map ρ) = (pCoreOf 2 Y).map ρ := by
  have hψ : Function.Surjective (ρ.comp (⊤ : Subgroup G).subtype) :=
    hρ.comp fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
  have hker' : (ρ.comp (⊤ : Subgroup G).subtype).ker = ρ.ker.subgroupOf ⊤ := by
    rw [← MonoidHom.comap_ker, Subgroup.comap_subtype]
  have hDK : ρ.ker ≤ Subgroup.centralizer (Y : Set G) :=
    hker.trans (Subgroup.center_le_centralizer (Y : Set G))
  have h := CFSG.GroupTheory.pCoreOf_map_subgroupOf_of_le_centralizer
    (X := ⊤) (D := ρ.ker) (ψ := ρ.comp (⊤ : Subgroup G).subtype)
    hψ hker' le_top le_top hDK hodd.coprime_two_right
  rwa [map_subgroupOf_top_eq, map_subgroupOf_top_eq] at h

omit [Finite X] in
private theorem eq_bot_of_map_eq_bot_of_isPGroup (ρ : G →* X)
    (hodd : Odd (Nat.card ρ.ker)) {P : Subgroup G} (hP : IsPGroup 2 P)
    (h : P.map ρ = ⊥) : P = ⊥ := by
  have hle : P ≤ ρ.ker := (Subgroup.map_eq_bot_iff P).mp h
  have hdis : P ⊓ ρ.ker = ⊥ :=
    CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hP hodd
  rwa [inf_eq_left.mpr hle] at hdis

private theorem exists_pow_mul_inv_eq_of_isPGroup {U : Type*} [Group U] {q z : U}
    (hcomm : Commute q z) {n m : ℕ} (hq : q ^ 2 ^ n = 1) (hz : z ^ m = 1)
    (hm : Odd m) : ∃ c, (q * z⁻¹) ^ c = q := by
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder (n := 2 ^ n) (m := m)
    (hm.coprime_two_right.symm.pow_left n) 1 0
  refine ⟨c, ?_⟩
  have hqpow : q ^ c = q := by
    rw [pow_eq_pow_mod c hq, hc1]
    rcases Nat.eq_or_lt_of_le (Nat.one_le_two_pow : 1 ≤ 2 ^ n) with h1 | h1
    · have hq1 : q = 1 := by
        rw [← h1, pow_one] at hq
        exact hq
      rw [← h1, Nat.mod_one, pow_zero, hq1]
    · rw [Nat.mod_eq_of_lt h1, pow_one]
  have hcz : z ^ c = 1 := by
    obtain ⟨t, ht⟩ := (Nat.modEq_zero_iff_dvd).mp hc2
    rw [ht, pow_mul, hz, one_pow]
  rw [hcomm.inv_right.mul_pow, hqpow, inv_pow, hcz, inv_one, mul_one]

omit [Finite G] [Finite X] in
private theorem map_inf_map_eq_bot_of_isPGroup (ρ : G →* X)
    (hker : ρ.ker ≤ Subgroup.center G) (hodd : Odd (Nat.card ρ.ker))
    {K Q : Subgroup G} (hQ : IsPGroup 2 Q) (hdis : K ⊓ Q = ⊥) :
    K.map ρ ⊓ Q.map ρ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨⟨k, hkK, rfl⟩, ⟨q, hqQ, hqk⟩⟩
  have hzmem : k⁻¹ * q ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqk, inv_mul_cancel]
  have hzc : k⁻¹ * q ∈ Subgroup.center G := hker hzmem
  obtain ⟨n, hn⟩ := hQ ⟨q, hqQ⟩
  have hqpow : q ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hzpow : (k⁻¹ * q) ^ Nat.card ρ.ker = 1 := by
    have h := pow_card_eq_one' (x := (⟨k⁻¹ * q, hzmem⟩ : ρ.ker))
    simpa using congrArg Subtype.val h
  have hcomm : Commute q (k⁻¹ * q) := Subgroup.mem_center_iff.mp hzc q
  obtain ⟨c, hc⟩ := exists_pow_mul_inv_eq_of_isPGroup hcomm hqpow hzpow hodd
  have hkq : q * (k⁻¹ * q)⁻¹ = k := by group
  rw [hkq] at hc
  have hqK : q ∈ K := by
    rw [← hc]
    exact K.pow_mem hkK c
  have hqbot : q = 1 := by
    have hmem : q ∈ (⊥ : Subgroup G) := by
      rw [← hdis]
      exact ⟨hqK, hqQ⟩
    exact Subgroup.mem_bot.mp hmem
  rw [← hqk, hqbot, map_one]

omit [Finite G] [Finite X] in
private theorem map_inf_map_eq_bot_of_ker_le (ρ : G →* X)
    {Q Y : Subgroup G} (hYker : ρ.ker ≤ Y) (hdis : Q ⊓ Y = ⊥) :
    Q.map ρ ⊓ Y.map ρ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨⟨q, hqQ, rfl⟩, ⟨y, hyY, hyq⟩⟩
  have hz : q⁻¹ * y ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyq, inv_mul_cancel]
  have hqy : q ∈ Y := by
    have hq : q = y * (q⁻¹ * y)⁻¹ := by group
    rw [hq]
    exact Y.mul_mem hyY (Y.inv_mem (hYker hz))
  have hqbot : q = 1 := by
    have hmem : q ∈ (⊥ : Subgroup G) := by
      rw [← hdis]
      exact ⟨hqQ, hqy⟩
    exact Subgroup.mem_bot.mp hmem
  rw [hqbot, map_one]

theorem kOf8103_map_of_central (ρ : G →* X) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center G) (hcop : Nat.Coprime (Nat.card ρ.ker) 6) {B : Subgroup G}
    (hB : Nat.card B = 3) : F08.KOf8103 ⊤ (B.map ρ) = (F08.KOf8103 ⊤ B).map ρ := by
  have hq := isCentralPQuot_three ρ hρ hker hcop
  obtain ⟨β, hβ3, hBz⟩ := exists_pow_three_eq_zpowers hB
  have hBmap : B.map ρ = Subgroup.zpowers (ρ β) := by
    rw [hBz, MonoidHom.map_zpowers]
  have hcen : Subgroup.centralizer ((B.map ρ : Subgroup X) : Set X) =
      (Subgroup.centralizer ((B : Subgroup G) : Set G)).map ρ := by
    rw [hBmap, hBz, CFSG.GroupTheory.centralizer_zpowers_eq β,
      CFSG.GroupTheory.centralizer_zpowers_eq (ρ β), hq.map_centralizer hβ3]
  have hY : ⊤ ⊓ Subgroup.centralizer ((B.map ρ : Subgroup X) : Set X) =
      (⊤ ⊓ Subgroup.centralizer ((B : Subgroup G) : Set G)).map ρ := by
    rw [top_inf_eq, top_inf_eq, hcen]
  change CFSG.inSubgroup CFSG.perfectResidual
      (⊤ ⊓ Subgroup.centralizer ((B.map ρ : Subgroup X) : Set X)) =
    (CFSG.inSubgroup CFSG.perfectResidual
      (⊤ ⊓ Subgroup.centralizer ((B : Subgroup G) : Set G))).map ρ
  rw [hY]
  exact (CFSG.RankThree.PartOne.KFU.map_inSubgroup_perfectResidual ρ _).symm

private theorem map_facts_of_central (ρ : G →* X) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center G) (hcop : Nat.Coprime (Nat.card ρ.ker) 6)
    (hodd : Odd (Nat.card ρ.ker)) {B : Subgroup G} (hB : Nat.card B = 3)
    {Y : Subgroup G} (hYtop : Y ≠ ⊤)
    (hYN : ∃ T : Sylow 2 G, Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ Y)
    (hYcen : Subgroup.centralizer ((B : Subgroup G) : Set G) ≤ Y)
    (hYp : pCoreOf 2 Y ≠ ⊥) (hYK : F08.KOf8103 ⊤ B ⊓ pCoreOf 2 Y = ⊥)
    (hYn : ∀ T : Sylow 2 G, pCoreOf 2 Y ≤ (T : Subgroup G) →
      Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ Y) :
    (Y.map ρ ≠ ⊤) ∧
      (∃ T₀ : Sylow 2 X, Subgroup.normalizer ((T₀ : Subgroup X) : Set X) ≤ Y.map ρ) ∧
      Subgroup.centralizer ((B.map ρ : Subgroup X) : Set X) ≤ Y.map ρ ∧
      pCoreOf 2 (Y.map ρ) ≠ ⊥ ∧
      F08.KOf8103 ⊤ (B.map ρ) ⊓ pCoreOf 2 (Y.map ρ) = ⊥ ∧
      ∀ T₀ : Sylow 2 X, pCoreOf 2 (Y.map ρ) ≤ (T₀ : Subgroup X) →
        Subgroup.normalizer ((T₀ : Subgroup X) : Set X) ≤ Y.map ρ := by
  obtain ⟨T, hTnorm⟩ := hYN
  have hkerY : ρ.ker ≤ Y :=
    (hker.trans (Subgroup.center_le_normalizer (T : Set G))).trans hTnorm
  have hpc : pCoreOf 2 (Y.map ρ) = (pCoreOf 2 Y).map ρ :=
    map_pCoreOf_of_central ρ hρ hker hodd Y
  have hK : F08.KOf8103 ⊤ (B.map ρ) = (F08.KOf8103 ⊤ B).map ρ :=
    kOf8103_map_of_central ρ hρ hker hcop hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro htop
    have hcomap : (Y.map ρ).comap ρ = Y := by
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerY]
    rw [htop, Subgroup.comap_top] at hcomap
    exact hYtop hcomap.symm
  · refine ⟨Sylow.mapSurjective hρ T, ?_⟩
    rw [Sylow.coe_mapSurjective,
      ← CFSG.ComponentClassification.OddKernelNormalizers.image ρ hρ hodd T T.isPGroup']
    exact Subgroup.map_mono hTnorm
  · rw [map_centralizer_of_card_three ρ hρ hker hcop hB]
    exact Subgroup.map_mono hYcen
  · rw [hpc]
    exact fun hbot => hYp (eq_bot_of_map_eq_bot_of_isPGroup ρ hodd
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hbot)
  · rw [hK, hpc]
    exact map_inf_map_eq_bot_of_isPGroup ρ hker hodd
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hYK
  · intro T₀ hle
    obtain ⟨T', hT'map⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.exists_sylow_map_eq (ℓ := 2) hρ T₀
    rw [← hT'map,
      ← CFSG.ComponentClassification.OddKernelNormalizers.image ρ hρ hodd T' T'.isPGroup']
    refine Subgroup.map_mono (hYn T' ?_)
    have hle' : (pCoreOf 2 Y).map ρ ≤ (T' : Subgroup G).map ρ := by
      rw [← hpc, hT'map]
      exact hle
    exact CFSG.GroupTheory.le_of_map_le_map_of_odd hker hodd
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hle'

theorem RadicalFacts.map_of_central (ρ : G →* X) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center G) (hcop : Nat.Coprime (Nat.card ρ.ker) 6) {B : Subgroup G}
    (hB : Nat.card B = 3) (h : RadicalFacts G B) : RadicalFacts X (B.map ρ) := by
  obtain ⟨Y₁, Y₂, hY, hinf₁, hinf₂, huniq⟩ := h
  have hodd : Odd (Nat.card ρ.ker) := odd_card_ker_of_coprime ρ hcop
  obtain ⟨h1top, h1N, h1cen, h1p, h1K, h1n⟩ := hY Y₁ (by simp)
  obtain ⟨h2top, h2N, h2cen, h2p, h2K, h2n⟩ := hY Y₂ (by simp)
  have h1ker : ρ.ker ≤ Y₁ := (hker.trans (Subgroup.center_le_normalizer
    ((h1N.choose : Sylow 2 G) : Set G))).trans h1N.choose_spec
  have h2ker : ρ.ker ≤ Y₂ := (hker.trans (Subgroup.center_le_normalizer
    ((h2N.choose : Sylow 2 G) : Set G))).trans h2N.choose_spec
  refine ⟨Y₁.map ρ, Y₂.map ρ, ?_, ?_, ?_, ?_⟩
  · rintro Y (rfl | rfl)
    · exact map_facts_of_central ρ hρ hker hcop hodd hB h1top h1N h1cen h1p h1K h1n
    · exact map_facts_of_central ρ hρ hker hcop hodd hB h2top h2N h2cen h2p h2K h2n
  · rw [map_pCoreOf_of_central ρ hρ hker hodd Y₁]
    exact map_inf_map_eq_bot_of_ker_le ρ h2ker hinf₁
  · rw [map_pCoreOf_of_central ρ hρ hker hodd Y₂]
    exact map_inf_map_eq_bot_of_ker_le ρ h1ker hinf₂
  · intro Z hZ hZN hZK
    obtain ⟨T₀, hN₀⟩ := hZN
    obtain ⟨T, hTmap⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.exists_sylow_map_eq (ℓ := 2) hρ T₀
    have hnorm : Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ Z.comap ρ := by
      rw [← Subgroup.map_le_iff_le_comap,
        CFSG.ComponentClassification.OddKernelNormalizers.image ρ hρ hodd T T.isPGroup',
        hTmap]
      exact hN₀
    have hZ' : Z.comap ρ ≠ ⊤ := by
      intro htop
      apply hZ
      rw [← Subgroup.map_comap_eq_self_of_surjective hρ Z, htop,
        Subgroup.map_top_of_surjective ρ hρ]
    have hKZ : F08.KOf8103 ⊤ B ⊔ B ≤ Z.comap ρ := by
      rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_sup,
        ← kOf8103_map_of_central ρ hρ hker hcop hB]
      exact hZK
    have hZmap : Z = (Z.comap ρ).map ρ :=
      (Subgroup.map_comap_eq_self_of_surjective hρ Z).symm
    rcases huniq (Z.comap ρ) hZ' ⟨T, hnorm⟩ hKZ with h1 | h2
    · exact Or.inl (by rw [hZmap, h1])
    · exact Or.inr (by rw [hZmap, h2])

theorem RadicalFacts.of_mulEquiv (φ : G ≃* X) {B : Subgroup G} (hB : Nat.card B = 3)
    (h : RadicalFacts G B) : RadicalFacts X (B.map φ.toMonoidHom) := by
  have hker : φ.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ.toMonoidHom).mpr φ.injective
  refine h.map_of_central φ.toMonoidHom φ.surjective ?_ ?_ hB
  · rw [hker]; exact bot_le
  · rw [hker, Subgroup.card_bot]; exact Nat.coprime_one_left 6

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
