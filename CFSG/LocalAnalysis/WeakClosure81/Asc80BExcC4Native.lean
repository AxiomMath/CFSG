module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6C4Sub
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcC4Lift
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Fixed
import CFSG.LieType.SeitzGeneration.HyperExCubeTw
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6GraphConj

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6SignedGraph CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration (card_fixSubfield_sq)
open CFSG.ComponentClassification.Burgoyne.E2 (e6GraphSign twE6SignAut coe_twE6SignAut
  exists_unit_pow_sub_one_eq_neg_one twE6C4Sub twE6C4SubEquiv
  twE6C4Sub_le_graphFixedRootGroup twE6C4Sub_commute twE6C4Sub_conj_mem)

attribute [local instance] finite_modGL


private def conjMulAutOfMemNormalizer {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (hg : ∀ x : G, x ∈ H ↔ g * x * g⁻¹ ∈ H)
    (hgi : ∀ x : G, x ∈ H ↔ g⁻¹ * x * g ∈ H) : MulAut ↥H where
  toFun s := ⟨g * s * g⁻¹, (hg s).1 s.2⟩
  invFun s := ⟨g⁻¹ * s * g, (hgi s).1 s.2⟩
  left_inv s := Subtype.ext (by group)
  right_inv s := Subtype.ext (by group)
  map_mul' s t := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem exists_rElement_fixed_signedGraph_inv {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (h : ↥(adjointGroup TwistTag.E6.tag K)) (hh : h ^ 2 = 1)
    (hαh : (rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
      diagramConjAut TwistTag.E6 K) h = h) :
    ∃ u : ↥(adjointGroup TwistTag.E6.tag K), u ≠ 1 ∧
      (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧ Commute u h ∧
      (rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
        diagramConjAut TwistTag.E6 K) u = u := by
  classical
  have hA : twistA K = rootDiagUnit TwistTag.E6.tag (e6GraphSign K) *
      diagramMap TwistTag.E6 K := rfl
  have hαapp : ∀ g : adjointGroup TwistTag.E6.tag K,
      ((rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
        diagramConjAut TwistTag.E6 K) g : ModGL TwistTag.E6.tag K) =
        twistA K * g * (twistA K)⁻¹ := by
    intro g
    rw [MulAut.mul_apply, coe_rootDiagAut, coe_diagramConjAut, hA, mul_inv_rev]
    group
  have hhF : (h : ModGL TwistTag.E6.tag K) ∈ fixedGroup K := by
    rw [mem_fixedGroup]
    refine ⟨h.2, ?_⟩
    have h1 : ((rootDiagAut TwistTag.E6.tag K (e6GraphSign K) *
        diagramConjAut TwistTag.E6 K) h : ModGL TwistTag.E6.tag K) =
        (h : ModGL TwistTag.E6.tag K) := by
      rw [hαh]
    rw [hαapp] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have hN : (h : ModGL TwistTag.E6.tag K) ∈
      Subgroup.normalizer (rootGenerated K : Set (ModGL TwistTag.E6.tag K)) :=
    fixedGroup_le_normalizer hK hhF
  let β : MulAut ↥(rootGenerated K) := conjMulAutOfMemNormalizer (rootGenerated K)
    (h : ModGL TwistTag.E6.tag K) (Subgroup.mem_normalizer_iff.1 hN)
    (fun x => by simpa only [inv_inv] using
      Subgroup.mem_normalizer_iff.1 (inv_mem hN) x)
  have hβapp : ∀ s : ↥(rootGenerated K),
      (β s : ModGL TwistTag.E6.tag K) =
        (h : ModGL TwistTag.E6.tag K) * s * (h : ModGL TwistTag.E6.tag K)⁻¹ := fun s => rfl
  have hh2 : (h : ModGL TwistTag.E6.tag K) * (h : ModGL TwistTag.E6.tag K) = 1 := by
    have h := congrArg Subtype.val hh
    simpa [pow_two] using h
  have hhinv : (h : ModGL TwistTag.E6.tag K)⁻¹ = (h : ModGL TwistTag.E6.tag K) :=
    inv_eq_of_mul_eq_one_left hh2
  have hβ2 : β ^ 2 = 1 := by
    refine MulEquiv.ext fun s => ?_
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    refine Subtype.ext ?_
    show (h : ModGL TwistTag.E6.tag K) *
        ((h : ModGL TwistTag.E6.tag K) * (s : ModGL TwistTag.E6.tag K) *
          (h : ModGL TwistTag.E6.tag K)⁻¹) * (h : ModGL TwistTag.E6.tag K)⁻¹ =
      (s : ModGL TwistTag.E6.tag K)
    rw [hhinv]
    calc (h : ModGL TwistTag.E6.tag K) *
          ((h : ModGL TwistTag.E6.tag K) * (s : ModGL TwistTag.E6.tag K) *
            (h : ModGL TwistTag.E6.tag K)) * (h : ModGL TwistTag.E6.tag K)
        = ((h : ModGL TwistTag.E6.tag K) * (h : ModGL TwistTag.E6.tag K)) *
            (s : ModGL TwistTag.E6.tag K) *
              ((h : ModGL TwistTag.E6.tag K) * (h : ModGL TwistTag.E6.tag K)) := by group
      _ = (s : ModGL TwistTag.E6.tag K) := by rw [hh2]; group
  let hKft : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hpprime, hcardf⟩ :=
    @FiniteField.card K (inferInstance : Field K) hKft (ringChar K) (ringChar.charP K)
  have hcard : Nat.card K = (ringChar K) ^ (f : ℕ) := by
    rw [@Nat.card_eq_fintype_card K hKft]
    exact hcardf
  obtain ⟨-, hLie⟩ := rootGenerated_recognition (K := K) hpprime hK hcard
  obtain ⟨u, hu1, ⟨n, hun⟩, hβu⟩ :=
    exists_fixed_pElement_of_lieModel_psp (p := ringChar K) (f := (f : ℕ)) hK hLie β hβ2
  have hSle : rootGenerated K ≤ adjointGroup TwistTag.E6.tag K :=
    rootGenerated_le_fixedGroup.trans inf_le_left
  let u' : ↥(adjointGroup TwistTag.E6.tag K) := ⟨u.1, hSle u.2⟩
  have hcomm : Commute u' h := by
    have h1 : (β u : ModGL TwistTag.E6.tag K) = (u : ModGL TwistTag.E6.tag K) := by rw [hβu]
    rw [hβapp] at h1
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.1 h1).symm
  refine ⟨u', ?_, ⟨n, ?_⟩, hcomm, ?_⟩
  · intro h1
    have h2 : (u : ModGL TwistTag.E6.tag K) = 1 := congrArg Subtype.val h1
    exact hu1 (Subtype.ext h2)
  · have h := congrArg Subtype.val hun
    exact Subtype.ext (by simpa using h)
  · refine Subtype.ext ?_
    rw [hαapp, mul_inv_eq_iff_eq_mul]
    exact ((mem_fixedGroup.1 (rootGenerated_le_fixedGroup u.2)).2).symm


theorem exists_rElement_fixed_twE6SignAut_inv {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (q : ℕ) (hσ : ∀ c, σ c = c ^ q)
    (hK : Nat.card K = q ^ 2) (hK2 : ringChar K ≠ 2)
    (h : ↥(twistedE6RootGroup K σ)) (hh : h ^ 2 = 1)
    (hαh : twE6SignAut σ h = h) :
    ∃ u : ↥(twistedE6RootGroup K σ), u ≠ 1 ∧
      (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧
      Commute u h ∧ twE6SignAut σ u = u := by
  classical
  have hq2 : 2 ≤ q := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    rcases Nat.lt_or_ge q 2 with hq | hq
    · interval_cases q <;> simp_all
    · exact hq
  let hKft : Fintype K := Fintype.ofFinite K
  obtain ⟨f₀, hp, hcardf⟩ :=
    @FiniteField.card K (inferInstance : Field K) hKft (ringChar K) (ringChar.charP K)
  have hcardn : Nat.card K = (ringChar K) ^ (f₀ : ℕ) := by
    rw [@Nat.card_eq_fintype_card K hKft]
    exact hcardf
  have hq2eq : q ^ 2 = (ringChar K) ^ (f₀ : ℕ) := by rw [← hK, hcardn]
  have hdvd : q ∣ (ringChar K) ^ (f₀ : ℕ) := hq2eq ▸ dvd_pow_self q two_ne_zero
  obtain ⟨f, -, hqeq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hqeq
      omega
    · exact h0
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [hK, hqeq]
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := fun c => by rw [hσ c, hqeq]
  have hqodd : Odd q := by
    rw [hqeq]
    exact Odd.pow (hp.odd_of_ne_two hK2)
  obtain ⟨μ, hμ⟩ := exists_unit_pow_sub_one_eq_neg_one hqodd hK
  have hσμ : σ (μ : K) = -(μ : K) := by
    rw [hσ', ← hqeq]
    have hq1 : 1 ≤ q := by omega
    have hv : (μ : K) ^ (q - 1) = -1 := by simpa using congrArg Units.val hμ
    rw [show (μ : K) ^ q = (μ : K) ^ (q - 1) * (μ : K) by
      rw [← pow_succ, Nat.sub_add_cancel hq1], hv]
    ring
  have hJle : twE6C4Sub σ μ ≤ graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    twE6C4Sub_le_graphFixedRootGroup hK2 σ hσμ
  have hgA : twistA K * (h : ModGL TwistTag.E6.tag K) =
      (h : ModGL TwistTag.E6.tag K) * twistA K := by
    have h1 : (twE6SignAut σ h : ModGL TwistTag.E6.tag K) =
        twistA K * (h : ModGL TwistTag.E6.tag K) * (twistA K)⁻¹ :=
      coe_twE6SignAut hp hK2 hf hK' σ hσ' h
    rw [hαh] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1.symm
  have hN : (h : ModGL TwistTag.E6.tag K) ∈
      Subgroup.normalizer (twE6C4Sub σ μ : Set (ModGL TwistTag.E6.tag K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro j
    constructor
    · intro hj
      exact twE6C4Sub_conj_mem hK2 σ hσμ h.2 hgA hj
    · intro hj
      have hgA' : twistA K * (h : ModGL TwistTag.E6.tag K)⁻¹ =
          (h : ModGL TwistTag.E6.tag K)⁻¹ * twistA K := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, hgA, inv_mul_cancel_left]
      have h2 := twE6C4Sub_conj_mem hK2 σ hσμ (inv_mem h.2) hgA' hj
      have hval : (h : ModGL TwistTag.E6.tag K)⁻¹ *
          ((h : ModGL TwistTag.E6.tag K) * j * (h : ModGL TwistTag.E6.tag K)⁻¹) *
            (h : ModGL TwistTag.E6.tag K)⁻¹⁻¹ = j := by
        rw [inv_inv]
        group
      rw [hval] at h2
      exact h2
  let β : MulAut ↥(twE6C4Sub σ μ) := conjMulAutOfMemNormalizer (twE6C4Sub σ μ)
    (h : ModGL TwistTag.E6.tag K) (Subgroup.mem_normalizer_iff.1 hN)
    (fun x => by simpa only [inv_inv] using
      Subgroup.mem_normalizer_iff.1 (inv_mem hN) x)
  have hβapp : ∀ s : ↥(twE6C4Sub σ μ),
      (β s : ModGL TwistTag.E6.tag K) =
        (h : ModGL TwistTag.E6.tag K) * s * (h : ModGL TwistTag.E6.tag K)⁻¹ := fun s => rfl
  have hh2 : (h : ModGL TwistTag.E6.tag K) * (h : ModGL TwistTag.E6.tag K) = 1 := by
    have h := congrArg Subtype.val hh
    simpa [pow_two] using h
  have hhinv : (h : ModGL TwistTag.E6.tag K)⁻¹ = (h : ModGL TwistTag.E6.tag K) :=
    inv_eq_of_mul_eq_one_left hh2
  have hβ2 : β ^ 2 = 1 := by
    refine MulEquiv.ext fun s => ?_
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    refine Subtype.ext ?_
    show (h : ModGL TwistTag.E6.tag K) *
        ((h : ModGL TwistTag.E6.tag K) * (s : ModGL TwistTag.E6.tag K) *
          (h : ModGL TwistTag.E6.tag K)⁻¹) * (h : ModGL TwistTag.E6.tag K)⁻¹ =
      (s : ModGL TwistTag.E6.tag K)
    rw [hhinv]
    calc (h : ModGL TwistTag.E6.tag K) *
          ((h : ModGL TwistTag.E6.tag K) * (s : ModGL TwistTag.E6.tag K) *
            (h : ModGL TwistTag.E6.tag K)) * (h : ModGL TwistTag.E6.tag K)
        = ((h : ModGL TwistTag.E6.tag K) * (h : ModGL TwistTag.E6.tag K)) *
            (s : ModGL TwistTag.E6.tag K) *
              ((h : ModGL TwistTag.E6.tag K) * (h : ModGL TwistTag.E6.tag K)) := by group
      _ = (s : ModGL TwistTag.E6.tag K) := by rw [hh2]; group
  have hkcard : Nat.card (fixSubfield σ) = ringChar K ^ f :=
    card_fixSubfield_sq hp hf hK' σ hσ'
  have hLie0 : CFSG.Blueprint.LieModel
      (↥(rootGenerated (fixSubfield σ)) ⧸ Subgroup.center ↥(rootGenerated (fixSubfield σ)))
      .PSp 4 (ringChar K) f :=
    (rootGenerated_recognition (K := fixSubfield σ) hp hK2 hkcard).2
  let eJ : ↥(rootGenerated (fixSubfield σ)) ≃* ↥(twE6C4Sub σ μ) := twE6C4SubEquiv σ μ
  have hcenter : (Subgroup.center ↥(rootGenerated (fixSubfield σ))).map eJ.toMonoidHom =
      Subgroup.center ↥(twE6C4Sub σ μ) := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using Subgroup.map_center_eq eJ
  let eQ : (↥(rootGenerated (fixSubfield σ)) ⧸ Subgroup.center ↥(rootGenerated (fixSubfield σ))) ≃*
      (↥(twE6C4Sub σ μ) ⧸ Subgroup.center ↥(twE6C4Sub σ μ)) :=
    QuotientGroup.congr _ _ eJ hcenter
  have hLie : CFSG.Blueprint.LieModel
      (↥(twE6C4Sub σ μ) ⧸ Subgroup.center ↥(twE6C4Sub σ μ)) .PSp 4 (ringChar K) f :=
    CFSG.Blueprint.LieModel.of_mulEquiv eQ hLie0
  obtain ⟨u, hu1, ⟨n, hun⟩, hβu⟩ :=
    exists_fixed_pElement_of_lieModel_psp (p := ringChar K) (f := f) hK2 hLie β hβ2
  let u' : ↥(twistedE6RootGroup K σ) := ⟨u.1, hJle u.2⟩
  have hcomm : Commute u' h := by
    have h1 : (β u : ModGL TwistTag.E6.tag K) = (u : ModGL TwistTag.E6.tag K) := by rw [hβu]
    rw [hβapp] at h1
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.1 h1).symm
  refine ⟨u', ?_, ⟨n, ?_⟩, hcomm, ?_⟩
  · intro h1
    have h2 : (u : ModGL TwistTag.E6.tag K) = 1 := congrArg Subtype.val h1
    exact hu1 (Subtype.ext h2)
  · have h := congrArg Subtype.val hun
    exact Subtype.ext (by simpa using h)
  · refine Subtype.ext ?_
    rw [coe_twE6SignAut hp hK2 hf hK' σ hσ']
    rw [mul_inv_eq_iff_eq_mul]
    exact twE6C4Sub_commute σ μ u.2


end CFSG.LocalAnalysis.WeakClosure81
