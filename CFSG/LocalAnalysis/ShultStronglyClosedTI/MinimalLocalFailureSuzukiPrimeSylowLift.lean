module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPrimeSylowFixed
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairHullRegularComplement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiScalar

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ShultStronglyClosedTI.ProperPairModel CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_of_isSylowOf {ℓ : ℕ} [Fact ℓ.Prime] {H S : Subgroup G}
    (hS : IsSylowOf ℓ S H) {a : G} (haH : a ∈ H) (ha : ∃ n : ℕ, orderOf a = ℓ ^ n) :
    ∃ g ∈ H, g * a * g⁻¹ ∈ S := by
  obtain ⟨PH, hPH⟩ := hS
  obtain ⟨n, hn⟩ := ha
  have hz : IsPGroup ℓ (Subgroup.zpowers (⟨a, haH⟩ : H)) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hn])
  obtain ⟨P, hP⟩ := hz.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P PH
  have hmem : g * ⟨a, haH⟩ * g⁻¹ ∈ (PH : Subgroup H) := by
    rw [← hg, coe_smul_sylow']
    exact ⟨⟨a, haH⟩, hP (Subgroup.mem_zpowers _), rfl⟩
  refine ⟨g, g.2, ?_⟩
  rw [← hPH]
  exact ⟨_, hmem, rfl⟩

omit [Finite G] in
theorem card_hull_of_suzuki {K : Subgroup G} {q : ℕ}
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = q ∧ Nonempty (K ≃* suzukiGroup m k)) :
    Nat.card K = q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
  obtain ⟨m, k, _, _, hk, hkq, ⟨e⟩⟩ := hSz
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hk, ← hk, hkq]

theorem pow_dvd_ordProj_of_dvd_suzuki_order {ℓ q c n : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hq : q = 2 ^ n) (hq1 : 2 ≤ q) (hℓq : ℓ ∣ q - 1)
    (hdvd : ℓ ^ c ∣ q ^ 2 * (q - 1) * (q ^ 2 + 1)) :
    ℓ ^ c ∣ ℓ ^ (q - 1).factorization ℓ := by
  have hcop2 : Nat.Coprime ℓ 2 := (Nat.coprime_primes hℓ Nat.prime_two).mpr hℓ2
  have hcopq : Nat.Coprime ℓ (q ^ 2) := by
    rw [hq, ← pow_mul]
    exact Nat.Coprime.pow_right _ hcop2
  have hcopq' : Nat.Coprime ℓ (q ^ 2 + 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hℓ]
    intro h1
    have h2 : ℓ ∣ (q - 1) * (q + 1) := Dvd.dvd.mul_right hℓq _
    have h3 : q ^ 2 + 1 = (q - 1) * (q + 1) + 2 := by
      rcases q with _ | q
      · omega
      · simp only [Nat.add_sub_cancel]
        ring
    rw [h3] at h1
    have h4 := (Nat.dvd_add_right h2).mp h1
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h4)
  have h1 : ℓ ^ c ∣ q - 1 := by
    rw [mul_comm (q ^ 2), mul_assoc] at hdvd
    exact (Nat.Coprime.pow_left c (Nat.Coprime.mul_right hcopq hcopq')).dvd_of_dvd_mul_right hdvd
  exact (Nat.Prime.pow_dvd_iff_dvd_ordProj hℓ (by omega)).mp h1

theorem exists_scalar_lift_of_exclusion
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* suzukiGroup m k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    {r : ℕ} (hr : r.Prime)
    (hrN : r ∣ Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 -
      Nat.card (minimalLocalFailurePairActionPointHull H z) + 1)
    (hrB : ¬ r ∣ Nat.card (pairPointStabilizer H beta)) (R : Sylow r ↥H)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ∣ Nat.card (minimalLocalFailurePairActionPointHull H z) - 1) :
    ∃ g ∈ H, ∃ A : Subgroup G,
      A ≤ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) ⊔
        rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ∧ IsCyclic A ∧
      Nat.card A = ℓ ^ (Nat.card (minimalLocalFailurePairActionPointHull H z) - 1).factorization ℓ ∧
      A ≤ Subgroup.normalizer (rightConjugate ((R : Subgroup H).map H.subtype) g : Set G) ∧
      (∀ a ∈ A, a ≠ 1 → Nat.card (rightFixedSet H a) = 2 ∨
        Nat.card (rightFixedSet H a) = Nat.card (minimalLocalFailurePairActionPointHull H z) + 1) ∧
      ∀ a ∈ A, a ≠ 1 →
        rightConjugate ((R : Subgroup H).map H.subtype) g ⊓ Subgroup.centralizer ({a} : Set G) =
          ⊥ := by
  set B := pairPointStabilizer H beta with hBdef
  set X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta) with hXdef
  set K := minimalLocalFailureProperPairHull H z beta t with hKdef
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  set C := H ⊓ Subgroup.centralizer (Q : Set G) with hCdef
  set J₀ := Subgroup.centralizer (K : Set G) with hJdef
  set Rg := (R : Subgroup H).map H.subtype with hRg
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hHB, -, -, -, hCXset, hCXnormal, hFB, hJX, hXJ, hRC⟩ :=
    minimalLocalFailure_suzuki_scalar_preimage_of_conclusions h hcomm hsmallerR1 hbeta ht hproper
      hBinv hSz hexcl
  obtain ⟨m, -, _, _, -, -, hQcard, -⟩ :=
    proper_pair_suzuki_structure h hcomm hsmallerR1 hbeta ht hproper hSz
  obtain ⟨-, -, hQ4, -, hXB, -, hXcyc, hXcard, -, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, hHN, hHC⟩ := point_root_conj_mem h hcomm hbeta ht hproper
  have hJ : J₀ = B ⊓ Subgroup.centralizer (Q : Set G) :=
    hull_centralizer_eq_of_exclusion h hcomm hsmallerR1 hbeta ht hproper hBinv hSz hexcl
  have htwo := CyclicSemiregular.proper_pair_two_transitive h hcomm hsmallerR1 hbeta ht hproper
  have hXC := torus_inf_centralizer_eq_bot h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨u, huB, hu⟩ := hBinv
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨f, hf⟩⟩ :=
    proper_pair_hull_regular_complement_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hexcl
      huB hu
  have hKcard := card_hull_of_suzuki (K := K) (by
    obtain ⟨m', k', i1, i2, hk', hkq, he⟩ := hSz
    exact ⟨m', k', i1, i2, hk', hkq, he⟩)
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hXH : X ≤ H := hXB.trans hBH
  have hCH : C ≤ H := inf_le_left
  have hFH : C ⊔ X ≤ H := sup_le hCH hXH
  have hJC : J₀ ≤ C := by
    rw [hJ]
    exact fun x hx => ⟨hBH hx.1, hx.2⟩
  have hq4 : 4 ≤ Nat.card Q := hQ4
  have hqeven : Even (Nat.card Q) := by
    rw [hQcard]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    obtain ⟨w, hw⟩ := hqeven
    omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr (odd_suzuki_norm hqeven) (even_iff_two_dvd.mpr hrN)
  set mℓ := ℓ ^ (Nat.card Q - 1).factorization ℓ with hmℓdef
  have hmℓ : mℓ ∣ Nat.card Q - 1 := Nat.ordProj_dvd _ _
  set ρ := conjToAut Q H hHN with hρ
  have hker : ρ.ker = C.subgroupOf H := by rw [ker_conjToAut, inf_subgroupOf_self_left]
  have hρ1 : ∀ w : H, ρ w = 1 ↔ (w : G) ∈ C := fun w => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hdec : ∀ w ∈ J₀ ⊔ X, ∃ j ∈ J₀, ∃ x ∈ X, w = j * x := fun w hw => by
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left J₀ X
      (hXJ.trans (Subgroup.centralizer_le_normalizer _))] at hw
    obtain ⟨j, hj, x, hx, rfl⟩ := hw
    exact ⟨j, hj, x, hx, rfl⟩
  have hcommJX : ∀ j ∈ J₀, ∀ x ∈ X, Commute j x := fun j hj x hx =>
    (Subgroup.mem_centralizer_iff.mp (hXJ hx) j hj)
  have hpowJX : ∀ j ∈ J₀, ∀ x ∈ X, ∀ N : ℕ, (j * x) ^ N = 1 → j ^ N = 1 ∧ x ^ N = 1 := by
    intro j hj x hx N hN
    rw [(hcommJX j hj x hx).mul_pow] at hN
    have h1 : j ^ N ∈ J₀ ⊓ X := ⟨J₀.pow_mem hj N, by
      rw [eq_inv_of_mul_eq_one_left hN]; exact X.inv_mem (X.pow_mem hx N)⟩
    rw [hJX, Subgroup.mem_bot] at h1
    rw [h1, one_mul] at hN
    exact ⟨h1, hN⟩
  have hRgC : Rg ≤ C := hRC r hr hrB R
  obtain ⟨SC, hSC⟩ := (show IsSylowOf r Rg H from ⟨R, rfl⟩).of_le hRgC hCH
  obtain ⟨x₀, hx₀X, hx₀⟩ : ∃ x₀ ∈ X, orderOf x₀ = mℓ := by
    have : IsCyclic X := hXcyc
    obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := X)
    have hord : orderOf g₀ = Nat.card X := orderOf_eq_card_of_forall_mem_zpowers hg₀
    refine ⟨((g₀ ^ (orderOf g₀ / mℓ) : X) : G), (g₀ ^ (orderOf g₀ / mℓ)).2, ?_⟩
    rw [Subgroup.orderOf_coe, orderOf_pow_orderOf_div (by rw [hord]; exact Nat.card_pos.ne')
      (by rw [hord, hXcard]; exact hmℓ)]
  have hρx₀ : orderOf (ρ ⟨x₀, hXH hx₀X⟩) = mℓ := by
    rw [← hx₀, orderOf_eq_orderOf_iff]
    intro n
    rw [← map_pow, hρ1]
    constructor
    · intro hn
      have h1 : x₀ ^ n ∈ X ⊓ Subgroup.centralizer (Q : Set G) := ⟨X.pow_mem hx₀X n, hn.2⟩
      rwa [hXC, Subgroup.mem_bot] at h1
    · intro hn
      rw [Subgroup.coe_pow, Subgroup.coe_mk, hn]
      exact C.one_mem
  obtain ⟨c, hcC, hcN⟩ := exists_mul_mem_normalizer_of_sylow
    (fun y hy c hc => hHC y (hFH hy) c hc) SC hSC (Subgroup.mem_sup_right hx₀X)
  have hyF : c * x₀ ∈ C ⊔ X := Subgroup.mul_mem _ (Subgroup.mem_sup_left hcC)
    (Subgroup.mem_sup_right hx₀X)
  have hyH : c * x₀ ∈ H := hFH hyF
  have hρy : ρ ⟨c * x₀, hyH⟩ = ρ ⟨x₀, hXH hx₀X⟩ := by
    have h1 : (⟨c * x₀, hyH⟩ : H) = ⟨c, hCH hcC⟩ * ⟨x₀, hXH hx₀X⟩ := rfl
    rw [h1, map_mul, (hρ1 _).mpr hcC, one_mul]
  obtain ⟨b, v, hv, hyord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (c * x₀)).ne' ℓ
    hℓ.one_lt.ne'
  have hv0 : v ≠ 0 := fun h0 => hv (h0 ▸ dvd_zero ℓ)
  have haord : orderOf ((c * x₀) ^ v) = ℓ ^ b := by
    rw [orderOf_pow_of_dvd hv0 (by rw [hyord]; exact dvd_mul_left v _), hyord,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hv0)]
  have haH : (c * x₀) ^ v ∈ H := H.pow_mem hyH v
  have haF : (c * x₀) ^ v ∈ C ⊔ X := Subgroup.pow_mem _ hyF v
  have haN : (c * x₀) ^ v ∈ Subgroup.normalizer (Rg : Set G) := Subgroup.pow_mem _ hcN v
  have hρa : orderOf (ρ ⟨(c * x₀) ^ v, haH⟩) = mℓ := by
    have h1 : (⟨(c * x₀) ^ v, haH⟩ : H) = (⟨c * x₀, hyH⟩ : H) ^ v := rfl
    rw [h1, map_pow, hρy, Nat.Coprime.orderOf_pow, hρx₀]
    rw [hρx₀, hmℓdef]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hv)
  obtain ⟨SB, hSB⟩ := exists_isSylowOf ℓ B
  have hSBH : IsSylowOf ℓ SB H := by
    obtain ⟨hSB1, hSB2, hSB3⟩ := isSylowOf_iff.mp hSB
    refine isSylowOf_iff.mpr ⟨hSB1.trans hBH, hSB2, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex SB B H hSB1 hBH, Nat.Prime.dvd_mul hℓ, hHB,
      Nat.Prime.dvd_mul hℓ]
    rintro (h1 | h1 | h1)
    · exact hSB3 h1
    · have h2 : ℓ ∣ 2 := by
        rw [hQcard] at h1
        exact hℓ.dvd_of_dvd_pow (hℓ.dvd_of_dvd_pow h1)
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h2)
    · exact not_dvd_suzuki_norm_of_dvd_sub_one hℓ (by omega) hℓq h1
  obtain ⟨g, hgH, hga⟩ := exists_conj_mem_of_isSylowOf hSBH haH ⟨b, haord⟩
  set a' := g * (c * x₀) ^ v * g⁻¹ with ha'def
  have ha'H : a' ∈ H := H.mul_mem (H.mul_mem hgH haH) (H.inv_mem hgH)
  have ha'F : a' ∈ C ⊔ X := hCXnormal.conj_mem ⟨_, hFH haF⟩ haF ⟨g, hgH⟩
  have ha'JX : a' ∈ J₀ ⊔ X := by
    rw [← hFB]
    exact ⟨ha'F, hSB.le hga⟩
  have hρa' : orderOf (ρ ⟨a', ha'H⟩) = mℓ := by
    have h1 : (⟨a', ha'H⟩ : H) = ⟨g, hgH⟩ * ⟨(c * x₀) ^ v, haH⟩ * (⟨g, hgH⟩ : H)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hρa]
  have ha'ord' : orderOf a' = ℓ ^ b := by
    rw [ha'def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, haord]
  have ha'ord : orderOf a' = mℓ := by
    refine Nat.dvd_antisymm ?_ ?_
    · obtain ⟨j, hj, x, hx, hjx⟩ := hdec a' ha'JX
      have hpow : (j * x) ^ (ℓ ^ b) = 1 := by rw [← hjx, ← ha'ord', pow_orderOf_eq_one]
      obtain ⟨hj1, hx1⟩ := hpowJX j hj x hx _ hpow
      have hjm : orderOf j ∣ mℓ := by
        obtain ⟨c', -, hc'⟩ := (Nat.dvd_prime_pow hℓ).mp (orderOf_dvd_of_pow_eq_one hj1)
        rw [hc']
        refine pow_dvd_ordProj_of_dvd_suzuki_order hℓ hℓ2 hQcard (by omega) hℓq ?_
        rw [← hKcard, ← hc']
        refine (Subgroup.orderOf_dvd_natCard J₀ hj).trans ?_
        rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
        exact Subgroup.card_subgroup_dvd_card _
      have hxm : orderOf x ∣ mℓ := by
        obtain ⟨c', -, hc'⟩ := (Nat.dvd_prime_pow hℓ).mp (orderOf_dvd_of_pow_eq_one hx1)
        rw [hc']
        refine (Nat.Prime.pow_dvd_iff_dvd_ordProj hℓ (by omega)).mp ?_
        rw [← hc', ← hXcard]
        exact Subgroup.orderOf_dvd_natCard X hx
      rw [hjx]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [(hcommJX j hj x hx).mul_pow, orderOf_dvd_iff_pow_eq_one.mp hjm,
        orderOf_dvd_iff_pow_eq_one.mp hxm, one_mul]
    · rw [← hρa', ← Subgroup.orderOf_mk a' ha'H]
      exact orderOf_map_dvd ρ _
  have hRh2 : IsPGroup r (rightConjugate Rg g⁻¹) := (R.isPGroup'.map H.subtype).map _
  have hRhH : rightConjugate Rg g⁻¹ ≤ H := fun w hw => by
    rw [mem_rightConjugate_iff', inv_inv] at hw
    have := H.mul_mem (H.mul_mem hgH ((Subgroup.map_subtype_le _) hw)) (H.inv_mem hgH)
    rwa [show g * (g⁻¹ * w * g) * g⁻¹ = w by group] at this
  have hAH : Subgroup.zpowers a' ≤ H := Subgroup.zpowers_le.mpr ha'H
  have hfixA : ∀ a ∈ Subgroup.zpowers a', a ≠ 1 → Nat.card (rightFixedSet H a) = 2 ∨
      Nat.card (rightFixedSet H a) = Nat.card Q + 1 := by
    intro a ha ha1
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, hj, x, hx, hjx⟩ := hdec _ (Subgroup.zpow_mem _ ha'JX n)
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [mul_one] at hjx
      have h1 : ρ (⟨a', ha'H⟩ ^ n) = 1 := by
        rw [hρ1, Subgroup.coe_zpow, Subgroup.coe_mk, hjx]
        exact hJC hj
      rw [map_zpow, ← orderOf_dvd_iff_zpow_eq_one, hρa', ← ha'ord,
        orderOf_dvd_iff_zpow_eq_one] at h1
      exact ha1 h1
    rw [hjx]
    exact card_fixed_mul_torus_of_exclusion h hcomm hsmallerR1 hbeta ht hproper ⟨u, huB, hu⟩
      hexcl hj hx hx1
  refine ⟨g⁻¹, H.inv_mem hgH, Subgroup.zpowers a', Subgroup.zpowers_le.mpr ha'JX, inferInstance,
    by rw [Nat.card_zpowers, ha'ord], Subgroup.zpowers_le.mpr ?_, hfixA, ?_⟩
  · refine Subgroup.mem_normalizer_iff.mpr fun w => ?_
    rw [mem_rightConjugate_iff', mem_rightConjugate_iff', inv_inv,
      show g⁻¹ * (a' * w * a'⁻¹) * g =
        (c * x₀) ^ v * (g⁻¹ * w * g) * ((c * x₀) ^ v)⁻¹ by rw [ha'def]; group]
    exact Subgroup.mem_normalizer_iff.mp haN _
  · intro a ha ha1
    refine inf_centralizer_eq_bot_of_card_fixed hbeta htwo hr hr2 hrB hRhH hRh2 (hAH ha)
      (n := 2 * m + 1) ?_
    rcases hfixA a ha ha1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by rw [h1, hQcard])

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
