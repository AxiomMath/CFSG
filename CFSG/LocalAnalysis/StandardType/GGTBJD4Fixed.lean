module

public import CFSG.LocalAnalysis.StandardType.GGTBJD4Diag
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmCorank
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmTorus
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmDiag
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmFix
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsDomain
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  Polynomial
open CFSG.StandardType.KGCentOm (kgcDiag)

theorem ggTBJD4_fixed_shape {p : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hp : p.Prime)
    (hpq : p ∣ Nat.card F - 1) {u : spinGroup (quadPlus 4 F)}
    (hu : u ∈ ggTorus (plusDatum 4 F (by norm_num))) (hu1 : u ≠ 1)
    (hx : OddOrderIsometry (quadPlus 4 F) p (spinAction (quadPlus 4 F) u))
    {J : Subgroup (spinGroup (quadPlus 4 F))}
    {T : Subgroup ((Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F))}
    (hT : ∀ z, z ∈ J ↔ spinAction (quadPlus 4 F) z ∈ T)
    (hL : FixedLayerListed (quadPlus 4 F) (spinAction (quadPlus 4 F) u))
    (hTq : CFSG.IsQuasisimple ↥T)
    (hTle : T ≤ supportedFixedDerived (quadPlus 4 F) (spinAction (quadPlus 4 F) u))
    (hTn : (T.subgroupOf
      (supportedFixedDerived (quadPlus 4 F) (spinAction (quadPlus 4 F) u))).Normal)
    (hcount : Set.ncard {h | h ∈ ggTorus (plusDatum 4 F (by norm_num)) ∧ h ^ p = 1 ∧
      h ∈ Subgroup.centralizer (J : Set (spinGroup (quadPlus 4 F)))} ≤ p) :
    Module.finrank F (fixedSpace (spinAction (quadPlus 4 F) u)) = 6 ∧
      T = supportedFixedDerived (quadPlus 4 F) (spinAction (quadPlus 4 F) u) ∧
      ∃ U : Submodule F (fixedSpace (spinAction (quadPlus 4 F) u)), Module.finrank F U = 3 ∧
        ∀ v ∈ U, ((quadPlus 4 F).comp (fixedSpace (spinAction (quadPlus 4 F) u)).subtype) v = 0 := by
  classical
  have hn4 : 3 ≤ 4 := by norm_num
  obtain ⟨a, hxa⟩ := jcoreOm_diag hn4 hu
  let w : Fin 4 ⊕ Fin 4 → F := fun c =>
    ((Sum.elim a (fun k => (a k)⁻¹) c : Fˣ) : F)
  have hxw : ∀ v c, spinAction (quadPlus 4 F) u v c = w c * v c := hxa
  have hw_inl : ∀ l, w (.inl l) = (a l : F) := fun _ => rfl
  have hw_inr : ∀ l, w (.inr l) = (((a l)⁻¹ : Fˣ) : F) := fun _ => rfl
  have hdim := jcoreOm_finrank_fixed hxa
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hdim
  have hm2le : 2 ≤ (Finset.univ.filter fun l => a l = 1).card := by
    have h3 := hL.1
    omega
  have hm4le : (Finset.univ.filter fun l => a l = 1).card ≤ 4 := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin 4)) (fun l => a l = 1)
    simpa using h
  have hmne4 : (Finset.univ.filter fun l => a l = 1).card ≠ 4 := by
    intro h4
    have hfull : (Finset.univ.filter fun l => a l = 1) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using h4)
    have ha1 : ∀ l, a l = 1 := by
      intro l
      have h := Finset.ext_iff.mp hfull l
      simpa using h
    have hx1 : spinAction (quadPlus 4 F) u = 1 := by
      refine LinearEquiv.ext fun v => funext fun c => ?_
      rw [hxw]
      have hwc : w c = 1 := by
        rcases c with l | l
        · rw [hw_inl l, ha1 l, Units.val_one]
        · rw [hw_inr l, ha1 l, inv_one, Units.val_one]
      rw [hwc, one_mul]
      simp
    exact hu1 (RootCentOmega.spinAction_quadPlus_injective (n := 4) (K := F)
      (by rw [hx1, map_one]))
  have key : ∀ {t : spinGroup (quadPlus 4 F)}, t ∈ ggTorus (plusDatum 4 F hn4) →
      (∀ c, w c = 1 → kgcDiag t c = 1) →
      t ∈ Subgroup.centralizer (J : Set (spinGroup (quadPlus 4 F))) := by
    intro t htT he
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hzT : spinAction (quadPlus 4 F) z ∈ T := (hT z).mp hz
    have hzB : spinAction (quadPlus 4 F) z ∈ supportedBlock (quadPlus 4 F)
        (spinAction (quadPlus 4 F) u) (X - C 1) := by
      simpa only [Polynomial.C_1] using
        supportedFixedDerived_le_supportedBlock (hTle hzT)
    have hzM : spinAction (quadPlus 4 F) z ∈ isometryCentralizer (quadPlus 4 F)
        (spinAction (quadPlus 4 F) u) := (mem_supportedBlock.mp hzB).1
    have hzg : ∀ c, w c ∉ ({1} : Set F) →
        spinAction (quadPlus 4 F) z (Pi.single c 1) = Pi.single c 1 := by
      intro c hc
      have hc1 : w c ≠ 1 := by simpa using hc
      exact ggTBJD4_supported_fix hxw one_ne_zero hzB hc1 (by simpa using hc1)
    have hcomm : Commute (spinAction (quadPlus 4 F) z)
        (spinAction (quadPlus 4 F) t) :=
      ggTBJD4_commute_of_diag (S := ({1} : Set F)) hxw
        (fun v c => KGCentOm.spinAction_apply_eq_kgcDiag_mul hn4 htT v c)
        (fun v => (mem_isometryCentralizer.mp hzM).2 v)
        (fun c hc => he c (by simpa using hc)) hzg
    apply RootCentOmega.spinAction_quadPlus_injective
    simpa only [map_mul] using hcomm.eq
  have hmne2 : (Finset.univ.filter fun l => a l = 1).card ≠ 2 := by
    intro h2
    have hcompl : (Finset.univ.filter fun l => a l ≠ 1).card = 2 := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 4)))
        (p := fun l => a l = 1)
      rw [h2] at h
      simp only [Finset.card_univ, Fintype.card_fin] at h
      change 2 + (Finset.univ.filter fun l => a l ≠ 1).card = 4 at h
      omega
    obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp hcompl
    have hmem : ∀ l, a l ≠ 1 ↔ l = i ∨ l = j := by
      intro l
      have h := Finset.ext_iff.mp hs l
      simpa using h
    have hai : a i ≠ 1 := (hmem i).mpr (Or.inl rfl)
    have haj : a j ≠ 1 := (hmem j).mpr (Or.inr rfl)
    have hdvd : p ∣ Nat.card Fˣ := by
      rw [Nat.card_units]
      exact hpq
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (hp := ⟨hp⟩) hdvd
    have hζne : ζ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hζ
      exact hp.ne_one hζ.symm
    have hζp : ζ ^ p = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hζ]
    have hζpF : (ζ : F) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hζp, Units.val_one]
    obtain ⟨ti, htiT, htiact⟩ :=
      KGCentOm.exists_mem_ggTorus_vec_eq_smul (n := 4) (K := F) hn4 (Pi.mulSingle i ζ)
    obtain ⟨tj, htjT, htjact⟩ :=
      KGCentOm.exists_mem_ggTorus_vec_eq_smul (n := 4) (K := F) hn4 (Pi.mulSingle j ζ)
    have hti_inl : ∀ l, kgcDiag ti (.inl l) =
        ((Pi.mulSingle i ζ : Fin 4 → Fˣ) l : F) := fun l =>
      KGCentOm.kgcDiag_eq_of_smul hn4 (k := l) (r := true) (htiact l).1
    have hti_inr : ∀ l, kgcDiag ti (.inr l) =
        (((Pi.mulSingle i ζ : Fin 4 → Fˣ) l : F))⁻¹ := fun l =>
      KGCentOm.kgcDiag_eq_of_smul hn4 (k := l) (r := false) (htiact l).2
    have hti_inl_one : ∀ l, l ≠ i → kgcDiag ti (.inl l) = 1 := fun l hl => by
      rw [hti_inl l, Pi.mulSingle_eq_of_ne hl, Units.val_one]
    have hti_inr_one : ∀ l, l ≠ i → kgcDiag ti (.inr l) = 1 := fun l hl => by
      rw [hti_inr l, Pi.mulSingle_eq_of_ne hl, Units.val_one, inv_one]
    have hti_i : kgcDiag ti (.inl i) = (ζ : F) := by
      rw [hti_inl i, Pi.mulSingle_eq_same]
    have hti_i_ne : kgcDiag ti (.inl i) ≠ 1 := by
      rw [hti_i]
      intro h
      exact hζne (Units.val_eq_one.mp h)
    have hti_one : ∀ c, w c = 1 → kgcDiag ti c = 1 := by
      intro c hc
      rcases c with l | l
      · have h1 : ((a l : Fˣ) : F) = 1 := by rw [← hw_inl l]; exact hc
        have hli : l ≠ i := by
          intro hli
          exact hai (by rw [hli] at h1; exact Units.val_eq_one.mp h1)
        exact hti_inl_one l hli
      · have h1 : (((a l)⁻¹ : Fˣ) : F) = 1 := by rw [← hw_inr l]; exact hc
        have hli : l ≠ i := by
          intro hli
          have hal : a l = 1 := inv_eq_one.mp (Units.val_eq_one.mp h1)
          rw [hli] at hal
          exact hai hal
        exact hti_inr_one l hli
    have hti_pow : ti ^ p = 1 := by
      refine KGCentOm.pow_eq_one_of_kgcDiag hn4 htiT (fun k => ?_)
      rw [hti_inl k]
      by_cases hki : k = i
      · rw [hki, Pi.mulSingle_eq_same, hζpF]
      · rw [Pi.mulSingle_eq_of_ne hki, Units.val_one, one_pow]
    have htj_inl : ∀ l, kgcDiag tj (.inl l) =
        ((Pi.mulSingle j ζ : Fin 4 → Fˣ) l : F) := fun l =>
      KGCentOm.kgcDiag_eq_of_smul hn4 (k := l) (r := true) (htjact l).1
    have htj_inr : ∀ l, kgcDiag tj (.inr l) =
        (((Pi.mulSingle j ζ : Fin 4 → Fˣ) l : F))⁻¹ := fun l =>
      KGCentOm.kgcDiag_eq_of_smul hn4 (k := l) (r := false) (htjact l).2
    have htj_inl_one : ∀ l, l ≠ j → kgcDiag tj (.inl l) = 1 := fun l hl => by
      rw [htj_inl l, Pi.mulSingle_eq_of_ne hl, Units.val_one]
    have htj_inr_one : ∀ l, l ≠ j → kgcDiag tj (.inr l) = 1 := fun l hl => by
      rw [htj_inr l, Pi.mulSingle_eq_of_ne hl, Units.val_one, inv_one]
    have htj_j : kgcDiag tj (.inl j) = (ζ : F) := by
      rw [htj_inl j, Pi.mulSingle_eq_same]
    have htj_j_ne : kgcDiag tj (.inl j) ≠ 1 := by
      rw [htj_j]
      intro h
      exact hζne (Units.val_eq_one.mp h)
    have htj_one : ∀ c, w c = 1 → kgcDiag tj c = 1 := by
      intro c hc
      rcases c with l | l
      · have h1 : ((a l : Fˣ) : F) = 1 := by rw [← hw_inl l]; exact hc
        have hlj : l ≠ j := by
          intro hlj
          exact haj (by rw [hlj] at h1; exact Units.val_eq_one.mp h1)
        exact htj_inl_one l hlj
      · have h1 : (((a l)⁻¹ : Fˣ) : F) = 1 := by rw [← hw_inr l]; exact hc
        have hlj : l ≠ j := by
          intro hlj
          have hal : a l = 1 := inv_eq_one.mp (Units.val_eq_one.mp h1)
          rw [hlj] at hal
          exact haj hal
        exact htj_inr_one l hlj
    have htj_pow : tj ^ p = 1 := by
      refine KGCentOm.pow_eq_one_of_kgcDiag hn4 htjT (fun k => ?_)
      rw [htj_inl k]
      by_cases hkj : k = j
      · rw [hkj, Pi.mulSingle_eq_same, hζpF]
      · rw [Pi.mulSingle_eq_of_ne hkj, Units.val_one, one_pow]
    have hti_cen := key (t := ti) htiT hti_one
    have htj_cen := key (t := tj) htjT htj_one
    have hsq := ggTBJD4_sq_le_ncard hn4 hp htiT htjT hti_pow htj_pow hti_cen htj_cen
      (m₁ := .inl i) (m₂ := .inl j) hti_i_ne (hti_inl_one j hij.symm) htj_j_ne
    have hle : p ^ 2 ≤ p := le_trans hsq hcount
    have h2p : 2 * p ≤ p ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right p hp.two_le
    have hlt : p < 2 * p := by
      simpa using Nat.mul_lt_mul_of_pos_right (by norm_num : 1 < 2) hp.pos
    exact (Nat.lt_irrefl p) (hlt.trans_le (le_trans h2p hle))
  have hmle3 : (Finset.univ.filter fun l => a l = 1).card ≤ 3 := by
    rcases Nat.lt_or_ge 3 (Finset.univ.filter fun l => a l = 1).card with h | h
    · have h4 : (Finset.univ.filter fun l => a l = 1).card = 4 := by omega
      exact absurd h4 hmne4
    · exact h
  have hm3 : (Finset.univ.filter fun l => a l = 1).card = 3 := by
    rcases Nat.eq_or_lt_of_le hmle3 with h | h
    · exact h
    · exfalso
      exact hmne2 (by omega)
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < (Finset.univ.filter fun l => a l = 1).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hk
  have hU := jcoreOm_singular_three (W := fixedSpace (spinAction (quadPlus 4 F) u))
    hij hik hjk fun l hl b => by
      rcases hl with rfl | rfl | rfl
      · exact jcoreOm_fixed_mem hxa hi b
      · exact jcoreOm_fixed_mem hxa hj b
      · exact jcoreOm_fixed_mem hxa hk b
  have hST : supportedFixedDerived (quadPlus 4 F) (spinAction (quadPlus 4 F) u) ≤ T :=
    jcoreOm_eq_of_normal (hx.isQuasisimple_supportedFixedDerived hU) hTq hTle hTn
  refine ⟨?_, ?_, hU⟩
  · rw [hdim, hm3]
  · exact le_antisymm hTle hST

end CFSG.StandardType

end
