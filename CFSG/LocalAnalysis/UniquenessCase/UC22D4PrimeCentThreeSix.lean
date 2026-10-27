module

public import CFSG.LocalAnalysis.UniquenessCase.UC22D4PrimeCentRank
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixLocalCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice
open scoped MatrixGroups


theorem uc22d4_centShape_threeSix {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {r : ℕ} (hr : r.Prime)
    (hr3 : 3 < r) (hrd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hx : orderOf x = r) :
    Odd (Nat.card (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) ∨
      2 ≤ CFSG.Open.pRank ℓ
        (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact r.Prime := ⟨hr⟩
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) ℓ f
  have hFr : ∀ c : AlgebraicClosure K, Fr c = c ^ (ℓ ^ f) :=
    fun c => by rw [iterateFrobenius_def]
  have hq1 : (1 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) := by exact_mod_cast Nat.one_le_pow _ _ hℓ.pos
  have hd0 : 0 ≤ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1 := by
    rcases hε with rfl | rfl <;> nlinarith
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1 :=
    ⟨_, Int.toNat_of_nonneg hd0⟩
  have hrd' : r ∣ d := by
    rw [← hd] at hrd
    exact_mod_cast hrd
  obtain ⟨-, ⟨g, hgG, hFg⟩, -, hall⟩ :=
    triality_three_six_tori_Sylow_and_root_kernels hℓ hf K hK σ hσ (AlgebraicClosure K) Fr hFr hε hd
  obtain ⟨-, -, hp'⟩ := hall g hgG hFg
  obtain ⟨-, -, -, -, -, -, -, hsurv, hreg, -⟩ := hp' r hr hr3 hrd'
  obtain ⟨c, a, ha, ha1, hxa⟩ :=
    threeSix_conj_dichotomy hℓ hf K hK σ hσ (AlgebraicClosure K) Fr hFr hε hd hgG hFg hr hr3 hrd'
      x hx
  by_cases hemp : survivingRoots a = ∅
  ·
    left
    obtain ⟨hcent, hodd⟩ := hreg a ha ha1 hemp (c * x * c⁻¹) hxa
    exact odd_card_centralizer_of_conj c (by rw [hcent]; exact hodd)
  · right
    obtain ⟨i, hi⟩ : ∃ i, survivingRoots a = trialitySigma i := by
      by_contra hnot
      push Not at hnot
      have hnoline : ∀ i, rootDiagUnit TwistTag.D4.tag a ∉
          threeSixLine (AlgebraicClosure K) Fr ε r i :=
        fun i hi => hnot i ((hsurv a ha ha1).1 i hi)
      exact hemp ((hsurv a ha ha1).2 hnoline)
    obtain ⟨v, hv⟩ : ∃ v : WeylGroup Tag.D4,
        (fun α => v • α) '' d4A2Sigma = survivingRoots a := by
      obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ :=
        triality_three_six_unimodular_A2_root_partition
      obtain ⟨-, -, -, -, -, w, -, -, hw⟩ := hcomp i
      exact ⟨w, by rw [hi, d4A2Sigma_eq_trialityStdA2, ← hw]⟩
    obtain ⟨-, -, hR, hSL3, hU, -, -, -, -, hk, -⟩ :=
      triality_three_six_singular_fixed_centralizers hℓ hf K hK σ hσ (AlgebraicClosure K) Fr hFr
        hε hd g hgG hFg hr hr3 hrd' a ha.1 (orderOf_eq_prime ha.2 ha1) v hv (c * x * c⁻¹) hxa
    let y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := c * x * c⁻¹
    set R : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      ⁅centralizer ({y} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        centralizer ({y} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ with hRdef
    have hR' : R = threeSixSingularR (AlgebraicClosure K) K σ Fr ε v g := by
      rw [hRdef]
      exact hR
    have hRle : R ≤ centralizer ({y} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [hRdef]
      exact Subgroup.commutator_le_of_le le_rfl le_rfl
    have hyx : c⁻¹ * y * (c⁻¹)⁻¹ = x := by
      show c⁻¹ * (c * x * c⁻¹) * c = x
      group
    have hCy : (centralizer ({y} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map
        (MulAut.conj c⁻¹).toMonoidHom =
        centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [map_conj_centralizer_singleton_eq, hyx]
    have hle : CFSG.Open.pRank ℓ
        (centralizer ({y} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ≤
        CFSG.Open.pRank ℓ
          (centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
      have h := CFSG.SectionRank.pRank_le_map hℓ.one_lt (MulAut.conj c⁻¹).toMonoidHom
        (MulAut.conj c⁻¹).injective
        (centralizer ({y} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
      rwa [hCy] at h
    rcases hε with rfl | rfl
    ·
      have hk1 : Nat.card (RingHom.eqLocusField Fr (RingHom.id (AlgebraicClosure K))) = ℓ ^ f := hk
      have : Finite (RingHom.eqLocusField Fr (RingHom.id (AlgebraicClosure K))) :=
        Nat.finite_of_card_ne_zero (by rw [hk1]; exact pow_ne_zero _ hℓ.ne_zero)
      obtain ⟨e3, -⟩ := hSL3 rfl
      have eR : R ≃* SL(3, RingHom.eqLocusField Fr (RingHom.id (AlgebraicClosure K))) :=
        (MulEquiv.subgroupCongr hR').trans e3
      have h2 := uc22d4_le_pRank_of_sl3 hℓ hk1 hRle eR
      omega
    ·
      obtain ⟨U, hU, eU, -⟩ := hU rfl
      have eR : R ≃* U := (MulEquiv.subgroupCongr hR').trans eU
      have h2 := uc22d4_two_le_pRank_of_unitary hℓ hℓ2 hf U hU hRle eR
      omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
