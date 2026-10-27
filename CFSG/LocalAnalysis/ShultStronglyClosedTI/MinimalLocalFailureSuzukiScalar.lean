module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiScalarImage
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicSemiregular
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiScalarFactorization

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.Blueprint
open CFSG.ShultStronglyClosedTI.ProperPairModel
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_subgroupOf_self_left (H A : Subgroup G) :
    (H ⊓ A).subgroupOf H = A.subgroupOf H := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩

theorem minimalLocalFailure_suzuki_scalar_preimage_of_conclusions
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
      UnitaryFixedModelExcludedConclusion H z u) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    let q := Nat.card Q
    let C := H ⊓ Subgroup.centralizer (Q : Set G)
    let J₀ := Subgroup.centralizer (K : Set G)
    B.relIndex H = q ^ 3 * (q ^ 2 - q + 1) ∧
      (C : Set G) * (B : Set G) = (H : Set G) ∧ C ⊓ B = J₀ ∧
      (∃ _ : (C.subgroupOf H).Normal,
        CFSG.fittingSubgroup (↥H ⧸ C.subgroupOf H) =
          (X.subgroupOf H).map (QuotientGroup.mk' (C.subgroupOf H))) ∧
      (C : Set G) * (X : Set G) = ((C ⊔ X : Subgroup G) : Set G) ∧
      ((C ⊔ X).subgroupOf H).Normal ∧
      (C ⊔ X) ⊓ B = J₀ ⊔ X ∧ J₀ ⊓ X = ⊥ ∧ X ≤ Subgroup.centralizer (J₀ : Set G) ∧
      ∀ r : ℕ, r.Prime → ¬ r ∣ Nat.card B → ∀ R : Sylow r ↥H,
        (R : Subgroup ↥H).map H.subtype ≤ C := by
  intro B X K Q q C J₀
  obtain ⟨hHQ, hHN, hHC⟩ := point_root_conj_mem h hcomm hbeta ht hproper
  obtain ⟨-, hHB⟩ :=
    pair_stabilizer_relIndex_eq_of_exclusion h hcomm hsmallerR1 hbeta ht hproper hBinv hSz hexcl
  have hJ : J₀ = B ⊓ Subgroup.centralizer (Q : Set G) :=
    hull_centralizer_eq_of_exclusion h hcomm hsmallerR1 hbeta ht hproper hBinv hSz hexcl
  obtain ⟨m, -, _, _, -, -, hQcard, -⟩ :=
    proper_pair_suzuki_structure h hcomm hsmallerR1 hbeta ht hproper hSz
  obtain ⟨-, -, hQ4, -, hXB, -, -, hXcard, -, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, hKB, -, -, hBX, -⟩ :=
    minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, hfix, -⟩ :=
    CyclicSemiregular.minimalLocalFailure_proper_pair_cyclic_semiregularity h hcomm hsmallerR1
      hbeta ht hproper
  have hq4 : 4 ≤ q := hQ4
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hXH : X ≤ H := hXB.trans hBH
  have hXK : X ≤ K := by
    have : K ⊓ B = X := hKB
    rw [← this]
    exact inf_le_left
  have hXC := torus_inf_centralizer_eq_bot h hcomm hsmallerR1 hbeta ht hproper
  have hCB : C ⊓ B = J₀ := by
    rw [hJ]
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hBH hx.1, hx.2⟩, hx.1⟩⟩
  have hXJ : X ≤ Subgroup.centralizer (J₀ : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hy x (hXK hx)).symm
  have hJX : J₀ ⊓ X = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : x ∈ X ⊓ Subgroup.centralizer (Q : Set G) := ⟨hx.2, by
      rw [hJ] at hx
      exact hx.1.2⟩
    rwa [hXC] at hx'
  have hnormal : (C.subgroupOf H).Normal := ⟨fun n hn g => hHC g g.2 n hn⟩
  set ρ := conjToAut Q H hHN with hρ
  set π := ρ.rangeRestrict with hπ
  have hF := fittingSubgroup_point_image_eq_of_exclusion h hcomm hsmallerR1 hbeta ht hproper hBinv
    hSz hexcl hHN
  have hker : ρ.ker = C.subgroupOf H := by
    rw [ker_conjToAut, inf_subgroupOf_self_left]
  have hkerπ : π.ker = C.subgroupOf H := by rw [hπ, MonoidHom.ker_rangeRestrict, hker]
  let Φ : (↥H ⧸ C.subgroupOf H) ≃* ρ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ρ)
  have hΦ : Φ.toMonoidHom.comp (QuotientGroup.mk' (C.subgroupOf H)) = π := by
    ext g
    rfl
  have hFA : CFSG.fittingSubgroup (↥H ⧸ C.subgroupOf H) =
      (X.subgroupOf H).map (QuotientGroup.mk' (C.subgroupOf H)) := by
    apply Subgroup.map_injective (f := Φ.toMonoidHom) Φ.injective
    rw [map_fittingSubgroup_mulEquiv Φ, hF, Subgroup.map_map, hΦ]
  have hXCn : X ≤ Subgroup.normalizer (C : Set G) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hHC x (hXH hx) y hy, fun hy => by
      have := hHC x⁻¹ (H.inv_mem (hXH hx)) _ hy
      rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at this⟩
  have hCXset : (C : Set G) * (X : Set G) = ((C ⊔ X : Subgroup G) : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left C X hXCn).symm
  have hmemCX : ∀ g : H, (g : G) ∈ C ⊔ X ↔ π g ∈ (X.subgroupOf H).map π := by
    intro g
    constructor
    · intro hg
      rw [← SetLike.mem_coe, ← hCXset] at hg
      obtain ⟨c, hc, x, hx, hcx⟩ := hg
      refine ⟨⟨x, hXH hx⟩, hx, ?_⟩
      have hc' : π ⟨c, (inf_le_left : C ≤ H) hc⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hkerπ]
        exact hc
      have hg' : g = ⟨c, (inf_le_left : C ≤ H) hc⟩ * ⟨x, hXH hx⟩ := Subtype.ext hcx.symm
      rw [hg', map_mul, hc', one_mul]
    · rintro ⟨x, hx, hxg⟩
      have h1 : g * x⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxg, mul_inv_cancel]
      rw [hkerπ] at h1
      have h2 : (g : G) = (g * x⁻¹ : H) * x := by simp
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hx)
  have hCXnormal : ((C ⊔ X).subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hmemCX] at hn ⊢
    rw [← hF] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact (CFSG.fittingSubgroup_normal).conj_mem _ hn _
  have hHF : ∀ g ∈ H, ∀ c ∈ C ⊔ X, g * c * g⁻¹ ∈ C ⊔ X := fun g hg c hc => by
    have hcH : c ∈ H := (sup_le (inf_le_left : C ≤ H) hXH) hc
    exact hCXnormal.conj_mem ⟨c, hcH⟩ hc ⟨g, hg⟩
  have hqeven : Even q := by
    change Even (Nat.card Q)
    rw [hQcard]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  obtain ⟨ℓ, hℓ, hℓdvd⟩ := Nat.exists_prime_and_dvd (show q - 1 ≠ 1 by omega)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    obtain ⟨r, hr⟩ := hqeven
    omega
  have hℓB : ¬ ℓ ∣ B.relIndex H := by
    rw [hHB, Nat.Prime.dvd_mul hℓ]
    rintro (h1 | h1)
    · have h2 : ℓ ∣ 2 := by
        rw [hQcard] at h1
        exact hℓ.dvd_of_dvd_pow (hℓ.dvd_of_dvd_pow h1)
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h2)
    · exact not_dvd_suzuki_norm_of_dvd_sub_one hℓ (by omega) hℓdvd h1
  have hCBset : (C : Set G) * (B : Set G) = (H : Set G) :=
    point_eq_mul_of_frattini hbeta (hXcard ▸ hℓdvd) hℓB hXB hBX inf_le_left hXCn hHF hfix
  have hFB : (C ⊔ X) ⊓ B = J₀ ⊔ X := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_inf, ← hCXset, Set.inter_comm, ← Subgroup.inf_mul_assoc B C X hXB,
      inf_comm, hCB, Subgroup.coe_mul_of_right_le_normalizer_left J₀ X
        (hXJ.trans (Subgroup.centralizer_le_normalizer _))]
  have hsupH : (B.subgroupOf H) ⊔ (C.subgroupOf H) = ⊤ := by
    refine eq_top_iff.mpr fun g _ => ?_
    have hg : (g : G) ∈ (C : Set G) * (B : Set G) := by rw [hCBset]; exact g.2
    obtain ⟨c, hc, b, hb, hcb⟩ := hg
    have hg' : g = ⟨c, (inf_le_left : C ≤ H) hc⟩ * ⟨b, hBH hb⟩ := Subtype.ext hcb.symm
    rw [hg', sup_comm]
    exact Subgroup.mul_mem_sup hc hb
  have hCH : C.relIndex H = J₀.relIndex B := by
    have h1 := Subgroup.relIndex_sup_right (B.subgroupOf H) (C.subgroupOf H)
    rw [hsupH, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hBH] at h1
    change C.relIndex H = _ at h1
    rw [h1, ← hCB, Subgroup.inf_relIndex_right]
  have hcardA : Nat.card ρ.range = C.relIndex H := by
    rw [← Subgroup.index_ker, hker]
    rfl
  refine ⟨hHB, hCBset, hCB, ⟨hnormal, hFA⟩, hCXset, hCXnormal, hFB, hJX, hXJ, ?_⟩
  intro r hr hrB R
  have : Fact r.Prime := ⟨hr⟩
  have hR2 : IsPGroup r ((R : Subgroup H).map π) := R.isPGroup'.map π
  have hRbot : (R : Subgroup H).map π = ⊥ := by
    rcases hR2.card_eq_or_dvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      apply hrB
      refine h1.trans ((Subgroup.card_subgroup_dvd_card _).trans ?_)
      rw [hcardA, hCH]
      exact Subgroup.relIndex_dvd_card _ _
  rw [Subgroup.map_eq_bot_iff, hkerπ] at hRbot
  rintro _ ⟨x, hx, rfl⟩
  exact hRbot hx

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
