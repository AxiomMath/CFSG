module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootTwoCoreStatement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearHullOvergroups
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNontrivialTwoCoreBorel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNontrivialTwoCoreBurnside
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNontrivialTwoCoreCount
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNontrivialTwoCoreFactor
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelSemilinear
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelStatement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_normalizer_hull
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hker : LinearPointKernelConclusion H z beta t) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hW₀1 : W₀ ≠ ⊥) :
    Subgroup.normalizer (W₀ : Set G) ≤
      Subgroup.normalizer (minimalLocalFailureProperPairHull H z beta t : Set G) := by
  obtain ⟨hlin, -, -, -, -, hJeq, -⟩ := hker
  obtain ⟨-, -, -, hover⟩ :=
    minimalLocalFailure_linear_hull_proper_overgroups_normalize_of_conclusions h hcomm hsmallerR1
      hbeta ht hproper hlin hexcl
  obtain ⟨hsimple, -⟩ := minimalLocalFailure_nonabelian_simple h
  have hKW : minimalLocalFailureProperPairHull H z beta t ≤ Subgroup.normalizer (W₀ : Set G) :=
    (Subgroup.le_centralizer_iff.mp hW₀).trans (Subgroup.centralizer_le_normalizer _)
  have hlt : Subgroup.normalizer (W₀ : Set G) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    have hn : W₀.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hsimple.eq_bot_or_eq_top_of_normal W₀ with hbot | htop'
    · exact hW₀1 hbot
    · apply h.local_datum.proper
      rw [eq_top_iff, ← htop']
      refine hW₀.trans ?_
      rw [hJeq]
      exact inf_le_left.trans (pairPointStabilizer_le_point H beta)
  exact (hover _ hKW hlt).2

theorem minimalLocalFailure_nontrivial_pair_two_core_forces_two_centralizer_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hker : LinearPointKernelConclusion H z beta t)
    (hinv : FinalChain.RootCentralizerInvolutionsConclusion H z beta t) :
    NontrivialPairTwoCoreConclusion H z beta t := by
  classical
  intro hcore
  have hM1 := fun {W₀ : Subgroup G} => normalizer_le_normalizer_hull h hcomm hsmallerR1 hbeta ht
    hproper hexcl hker (W₀ := W₀)
  obtain ⟨⟨k, _, _, hkq, ⟨ψ⟩⟩, -, hBidx, hNK, -, hJeq, hNC, hQJ, hJQ, hidx, ⟨f, hf⟩, -, hQM,
    hQCM, hCM, -, hodd⟩ := hker
  obtain ⟨-, ⟨e, hQe⟩, hQ4, -, hXB, -, -, hXcard, hXreg, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  have hk : Nat.card k = 2 ^ e := hkq.trans hQe
  obtain ⟨W, hWJ, hWcyc, hWodd, hWdvd, ⟨b, hJcard⟩, hWN⟩ :=
    exists_borel_complement_of_injective hk (ψ.toMonoidHom.comp f) (ψ.injective.comp hf) hcore
  clear hf f ψ
  obtain ⟨hQH, -, hQn, hQab, -, -, hzQ⟩ :=
    CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨-, -, -, -, -, -, -, -, -, hXK, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, hinvM⟩ := hinv
  unfold FinalChain.RootCentralizerTwoCoreConclusion
  set B := pairPointStabilizer H beta with hBdef
  set X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta) with hXdef
  set K := minimalLocalFailureProperPairHull H z beta t with hKdef
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  set J := Subgroup.centralizer (K : Set G) with hJdef
  set C := H ⊓ Subgroup.centralizer (Q : Set G) with hCdef
  set M := TwoCoreGrowth.pointTwoCoreImage H with hMdef
  set q := Nat.card Q with hqdef
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hJB : J ≤ B := by
    rw [hJeq]
    exact inf_le_left
  have hJH : J ≤ H := hJB.trans hBH
  have hJC : J ≤ C := le_inf hJH hJQ
  have hMH : M ≤ H := TwoCoreGrowth.pointTwoCoreImage_le H
  have hM2 : IsPGroup 2 M := TwoCoreGrowth.pointTwoCoreImage_isPGroup H
  have hMC : M ≤ C := le_inf hMH (Subgroup.le_centralizer_iff.mp hQCM)
  have hCH : C ≤ H := inf_le_left
  have hQC : Q ≤ C := le_inf hQH (Subgroup.le_centralizer_iff_isMulCommutative.mpr hQab.1)
  have hQn' : ∀ g ∈ H, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    conj_mem_of_normal_subgroupOf hQH hQn hg hy
  have hMn : ∀ g ∈ H, ∀ m ∈ M, g * m * g⁻¹ ∈ M := fun g hg m hm =>
    conj_mem_of_normal_subgroupOf hMH (TwoCoreGrowth.pointTwoCoreImage_normal H) hg hm
  have hCn : ∀ g ∈ H, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    obtain ⟨hcH, hcQ⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hg hcH) (H.inv_mem hg), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hc' := Subgroup.mem_centralizer_iff.mp hcQ _ (hQn' g⁻¹ (H.inv_mem hg) y hy)
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [hc']
      _ = g * c * g⁻¹ * y := by group
  have hHM : H ≤ Subgroup.normalizer (M : Set G) := le_normalizer_of_forall_conj_mem hMn
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_of_forall_conj_mem hQn'
  have hWC : W ≤ C := hWJ.trans hJC
  have hWcomm : ∀ a ∈ W, ∀ a' ∈ W, a * a' = a' * a := by
    intro a ha a' ha'
    have := hWcyc
    exact congrArg Subtype.val (isMulCommutative_iff.mp inferInstance ⟨a, ha⟩ ⟨a', ha'⟩)
  have hJNQ : J ≤ Subgroup.normalizer (Q : Set G) :=
    hJQ.trans (Subgroup.centralizer_le_normalizer _)
  have hQJcard : Nat.card (Q ⊔ J : Subgroup G) = q * Nat.card J := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hJNQ
    rwa [hQJ, Subgroup.card_bot, mul_one] at h1
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show (Q ⊔ J).relIndex C ∣ 2 ^ (e * 2) by rw [pow_mul, ← hQe]; exact hidx)
  have hCcard : Nat.card C = 2 ^ (c + e + b) * Nat.card W := by
    have h1 := Subgroup.relIndex_mul_card (Q ⊔ J) C
    rw [inf_eq_left.mpr (sup_le hQC hJC), hc, hQJcard, hQe, hJcard] at h1
    rw [← h1]
    ring
  have hNW₀ : ∀ W₀ : Subgroup G, W₀ ≤ W → W₀ ≠ ⊥ →
      C ⊓ Subgroup.normalizer (W₀ : Set G) ≤ Subgroup.centralizer (W₀ : Set G) := by
    intro W₀ hW₀W hW₀ g hg
    obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.mp hg
    have hgK : g ∈ Subgroup.normalizer (K : Set G) := hM1 (hW₀W.trans hWJ) hW₀ hgN
    have hgQJ : g ∈ ((Q ⊔ J : Subgroup G) : Set G) := by
      rw [SetLike.mem_coe, ← hNC]
      exact Subgroup.mem_inf.mpr ⟨hgK, hgC⟩
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Q J hJNQ] at hgQJ
    obtain ⟨y, hy, j, hj, rfl⟩ := hgQJ
    have hyW₀ : y ∈ Subgroup.centralizer (W₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.mp (hJQ (hWJ (hW₀W hw))) y hy).symm
    have hjN : j ∈ Subgroup.normalizer (W₀ : Set G) := by
      have h1 := Subgroup.mul_mem _
        (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hyW₀)) hgN
      rwa [inv_mul_cancel_left] at h1
    have hjW : j ∈ W := hWN W₀ hW₀W hW₀ (Subgroup.mem_inf.mpr ⟨hj, hjN⟩)
    have hjW₀ : j ∈ Subgroup.centralizer (W₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hWcomm w (hW₀W hw) j hjW
    exact Subgroup.mul_mem _ hyW₀ hjW₀
  have hMcard2 : Nat.card M = 2 ^ (c + e + b) := by
    have hCM' : Nat.card M = Nat.card (CFSG.pCore 2 C) := by
      rw [← hCM]
      exact Subgroup.card_map_of_injective C.subtype_injective
    rw [hCM']
    have hW'card : Nat.card (W.subgroupOf C) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv
    refine card_pCore_two_eq_of_odd_hall (W := W.subgroupOf C) (hW'card ▸ hWodd)
      (hW'card ▸ hCcard) ?_
    intro W₀ hW₀ hW₀1 g hg
    have hW₀GW : W₀.map C.subtype ≤ W := by
      rintro _ ⟨w, hw, rfl⟩
      exact hW₀ hw
    have hW₀G1 : W₀.map C.subtype ≠ ⊥ := by
      intro hbot
      exact hW₀1 ((Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp hbot)
    have hgN : (g : G) ∈ C ⊓ Subgroup.normalizer ((W₀.map C.subtype : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨g.2, Subgroup.le_normalizer_map C.subtype
        (Subgroup.mem_map_of_mem _ hg)⟩
    have hgC := hNW₀ _ hW₀GW hW₀G1 hgN
    rw [Subgroup.mem_centralizer_iff] at hgC ⊢
    intro w hw
    exact Subtype.ext (hgC w (Subgroup.mem_map_of_mem _ hw))
  have hcopMW : Nat.Coprime (Nat.card M) (Nat.card W) := by
    rw [hMcard2]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hWodd)
  have hMW : M ⊓ W = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcopMW).eq_bot
  have hMWC : M ⊔ W = C := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hMC hWC)
    have h1 := card_sup_mul_card_inf_of_le_normalizer ((hWC.trans hCH).trans hHM)
    rw [hMW, Subgroup.card_bot, mul_one, hMcard2] at h1
    rw [h1, hCcard]
  by_cases hW : W = ⊥
  · rw [hW, sup_bot_eq] at hMWC
    exact hMWC.symm
  exfalso
  have hMsolv : Group.IsSolvable M := by
    have : Group.IsNilpotent M := hM2.isNilpotent
    infer_instance
  have hNWK : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (K : Set G) := hM1 hWJ hW
  have hHMB : M ⊔ B = H := by
    apply le_antisymm (sup_le hMH hBH)
    intro g hg
    obtain ⟨n, hn, m, hm, rfl⟩ :=
      exists_normalizer_mul_of_hall hMC hWC hCH hCn hMn hMWC hMW hMsolv hcopMW hg
    obtain ⟨hnH, hnW⟩ := Subgroup.mem_inf.mp hn
    have hnQB : n ∈ Q ⊔ B := by
      rw [← hNK]
      exact Subgroup.mem_inf.mpr ⟨hNWK hnW, hnH⟩
    exact Subgroup.mul_mem _ (sup_le_sup_right hQM B hnQB) (Subgroup.mem_sup_left hm)
  set D := Nat.card (M ⊓ B : Subgroup G) with hDdef
  have hMcard : Nat.card M = q ^ 3 * D := by
    rw [← hBidx]
    exact card_eq_relIndex_mul_card_inf hHMB hBH (hBH.trans hHM)
  have hD : 0 < D := Nat.card_pos
  have hq4 : 4 ≤ q := hQ4
  have hQlt : Q < M := by
    refine lt_of_le_of_ne hQM fun hQMeq => ?_
    have h1 : q = q ^ 3 * D := by
      rw [← hMcard]
      exact congrArg (fun S : Subgroup G => Nat.card S) hQMeq
    have h2 : q * 1 < q * (q ^ 2 * D) := by
      apply Nat.mul_lt_mul_of_pos_left _ (by omega)
      have : 16 ≤ q ^ 2 := by nlinarith
      nlinarith
    rw [mul_one] at h2
    have h3 : q * (q ^ 2 * D) = q ^ 3 * D := by ring
    omega
  have hW1 : Nat.card W ≠ 1 := fun h1 => hW (Subgroup.card_eq_one.mp h1)
  obtain ⟨p, hp, hpW⟩ := Nat.exists_prime_and_dvd hW1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hWodd.not_two_dvd_nat hpW
  obtain ⟨⟨w, hwW⟩, hw⟩ := exists_prime_orderOf_dvd_card' p hpW
  have hwp : orderOf w = p := (Subgroup.orderOf_coe (⟨w, hwW⟩ : W)).trans hw
  have hpX : p ∣ Nat.card X := by
    rw [hXcard, ← hkq]
    exact hpW.trans hWdvd
  obtain ⟨⟨x, hxX⟩, hx⟩ := exists_prime_orderOf_dvd_card' p hpX
  have hxp : orderOf x = p := (Subgroup.orderOf_coe (⟨x, hxX⟩ : X)).trans hx
  have hxw : x * w = w * x := Subgroup.mem_centralizer_iff.mp (hWJ hwW) x (hXK hxX)
  have hz1 : z ≠ 1 := by
    intro hz
    have h1 := h.local_datum.distinguished_order
    rw [hz, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  have hzQ1 : z ∈ (Q : Set G) \ {1} := ⟨hzQ, hz1⟩
  have hxwinf : Subgroup.zpowers x ⊓ Subgroup.zpowers w = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyx, hyw⟩ := Subgroup.mem_inf.mp hy
    have hyX : y ∈ X := Subgroup.zpowers_le.mpr hxX hyx
    have hyQ : y ∈ Subgroup.centralizer (Q : Set G) := hJQ (hWJ (Subgroup.zpowers_le.mpr hwW hyw))
    exact (Subgroup.mem_bot).mpr (eq_one_of_regular_of_mem_centralizer hXreg hzQ1 hyX hyQ)
  obtain ⟨hEdec, hEcomm, hEexp, hEcard⟩ := sup_zpowers_of_commute hxp hwp hxw hxwinf
  set E := Subgroup.zpowers x ⊔ Subgroup.zpowers w with hEdef
  have hEH : E ≤ H := sup_le (Subgroup.zpowers_le.mpr (hBH (hXB hxX)))
    (Subgroup.zpowers_le.mpr (hJH (hWJ hwW)))
  have hdich : ∀ y ∈ E, y ≠ 1 → M ⊓ Subgroup.centralizer ({y} : Set G) ≤ Q ∨
      Q ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ := by
    intro y hy hy1
    obtain ⟨s, hs, r, hr, rfl⟩ := hEdec y hy
    have hrW : r ∈ W := Subgroup.zpowers_le.mpr hwW hr
    have hrJ : r ∈ J := hWJ hrW
    by_cases hs1 : s = 1
    · left
      rw [hs1, one_mul] at hy1 ⊢
      have hrodd : Odd (orderOf r) := hWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard W hrW)
      exact (hodd r hrJ hy1 hrodd).2.2.le
    · right
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨haQ, hay⟩ := Subgroup.mem_inf.mp ha
      rw [Subgroup.mem_centralizer_singleton_iff] at hay
      have hra : a * r = r * a := Subgroup.mem_centralizer_iff.mp (hJQ hrJ) a haQ
      have hsa : s⁻¹ * a * s = a := by
        have h1 : a * s * r = s * a * r := by
          calc a * s * r = a * (s * r) := by group
            _ = s * r * a := hay
            _ = s * (r * a) := by group
            _ = s * (a * r) := by rw [hra]
            _ = s * a * r := by group
        have h2 : a * s = s * a := mul_right_cancel h1
        rw [mul_assoc, h2, inv_mul_cancel_left]
      rw [Subgroup.mem_bot]
      by_contra ha1
      have hsX : s ∈ X := Subgroup.zpowers_le.mpr hxX hs
      obtain ⟨x₀, -, huniq⟩ := hXreg a ⟨haQ, ha1⟩ a ⟨haQ, ha1⟩
      have e1 := huniq ⟨s, hsX⟩ hsa
      have e2 := huniq 1 (by simp)
      exact hs1 (congrArg Subtype.val (e1.trans e2.symm))
  obtain ⟨v, hvM, hvQ, hv2, hvcomm⟩ := exists_involution_central_mod hp2 hQM hQlt hM2 hQCM
    hEcomm hEexp hEcard (hEH.trans hHM) (hEH.trans hHQ) hdich
  obtain ⟨u, huB, hu2, g, hgH, hgu⟩ := hinvM v hvM hvQ hv2
  have huM : u ∈ M := by
    have h1 := hMn g⁻¹ (H.inv_mem hgH) v hvM
    rwa [inv_inv, hgu] at h1
  have hucomm : ∀ m ∈ M, u * m * u⁻¹ * m⁻¹ ∈ Q := by
    intro m hm
    have h1 := hQn' g⁻¹ (H.inv_mem hgH) _ (hvcomm _ (hMn g hgH m hm))
    have heq : g⁻¹ * (v * (g * m * g⁻¹) * v⁻¹ * (g * m * g⁻¹)⁻¹) * g⁻¹⁻¹ =
        u * m * u⁻¹ * m⁻¹ := by
      rw [← hgu]
      group
    rwa [heq] at h1
  obtain ⟨hLu, -⟩ := proper_pair_hull_regular_complement_of_conclusions h hcomm hsmallerR1 hbeta
    ht hproper hexcl huB hu2
  have hCuK := FinalChain.centralizer_le_normalizer_of_localHull_eq hLu
  have hCMu : M ⊓ Subgroup.centralizer ({u} : Set G) ≤ Q ⊔ B := by
    intro g' hg'
    obtain ⟨hg'M, hg'u⟩ := Subgroup.mem_inf.mp hg'
    rw [← hNK]
    exact Subgroup.mem_inf.mpr ⟨hCuK hg'u, hMH hg'M⟩
  have hcount := card_le_of_conj_coset huM hu2 hucomm hCMu (hBH.trans hHQ) hQM
  rw [hMcard] at hcount
  have hlt : q * (q * D) < q ^ 3 * D := by
    have h1 : q * D < q * (q * D) := by
      have h2 : 0 < q * D := Nat.mul_pos (by omega) hD
      nlinarith
    calc q * (q * D) < q * (q * (q * D)) := Nat.mul_lt_mul_of_pos_left h1 (by omega)
      _ = q ^ 3 * D := by ring
  exact absurd hcount (not_le.mpr hlt)

end CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore
