module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import Certificates.Certificate8033
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddNormSylowPElement
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddNormSylowPSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutFrames
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddOrthogonalFrameBlock
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddOrthogonalComplement
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddPOmegaModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FundamentalOverModel
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitNormalizerGeometry
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalBlocks
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationAction
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce
import CFSG.ClassicalInvolution.Q3.Q3PlanParamsLift
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218X
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.AS81.Sec2 (conjSetStab conjPermHom)
open scoped MatrixGroups


theorem normSylowAt_pomega {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X)
    {t : StatedLieTag} {n r f : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hr2 : r ≠ 2) (hadm : StatedLieAdmissible t n r f)
    (hX : CFSG.Blueprint.LieModel X t n r f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    NormSylowAt X p := by
  classical
  have hpr : r.Prime := hadm.1
  have : Fact r.Prime := ⟨hpr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup X := hXs
  have hfund : IsFundTag t := by rcases ht with rfl | rfl | rfl <;> trivial
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by rcases ht with rfl | rfl | rfl <;> simp
  have : Finite (modelUniv t n r f hpr).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hr2 hpr hfund hadm
  have hFodd : Odd (Nat.card (GaloisField r f)) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hr2 hadm.2.1
  obtain ⟨D⟩ := exists_paired_orthogonal_model hr2 ht hadm
  refine normSylowAt_of_pPow hp ?_
  intro S hS y hyN ⟨j, hyj⟩ hyp
  have hSiff := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := S) (K := ⊤)).mp hS
  let P : Sylow 2 X :=
    hSiff.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hSiff.2.2)
  have hPcoe : (P : Subgroup X) = S := IsPGroup.toSylow_coe _ _
  have hyNP : y ∈ normalizer ((P : Subgroup X) : Set X) := hPcoe.symm ▸ hyN
  have hypP : y ^ p ∈ centralizer ((P : Subgroup X) : Set X) := hPcoe.symm ▸ hyp
  suffices hy1 : y = 1 by
    rw [hy1]
    exact Subgroup.one_mem _
  obtain ⟨ψ, ePair, hψ, hker, hePair⟩ :=
    exists_equiv_paired_funSet_of_orthogonal_model D hr2 hfund hadm hX hA1 P
  let Δ : Set (Subgroup X) := F14.FunSet (fundPred (r ^ f)) X (P : Subgroup X)
  have hconj : ∀ (g : X) {K : Subgroup X},
      fundPred (r ^ f) (⊤ : Subgroup X) K →
      fundPred (r ^ f) (⊤ : Subgroup X) (K.map (MulAut.conj g).toMonoidHom) :=
    fun g K h => CFSG.LocalAnalysis.UniquenessCase.isFundamentalOver_map_mulEquiv
      (MulAut.conj g) h
  have hSΔ : (P : Subgroup X) ≤ conjSetStab Δ := F14.sylow_le_conjSetStab_funSet hconj P
  have hyΔ : y ∈ conjSetStab Δ :=
    F14.le_conjSetStab_of_mapsTo_conj (H := normalizer ((P : Subgroup X) : Set X))
      (fun g hg K hK => F14.mem_funSet_map_conj_of_mem_normalizer hconj hg hK) hyNP
  have hyo : orderOf y ∣ p ^ j := orderOf_dvd_of_pow_eq_one hyj
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hyodd : Odd (orderOf y) := Odd.of_dvd_nat hpodd.pow hyo
  have hy3 : ¬ 3 ∣ orderOf y := fun h3 => by
    have h3p : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (h3.trans hyo)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p
    omega
  have hfix : ∀ J ∈ Δ, y ∈ normalizer (J : Set X) := by
    by_cases h4 : Δ.ncard ≤ 4
    · have hB : zpowers y ≤ conjSetStab Δ := (Subgroup.zpowers_le).mpr hyΔ
      have hcardB : Nat.card (zpowers y) = orderOf y := Nat.card_zpowers y
      have hbot := funSet_action_eq_bot_of_ncard_le_four Δ (zpowers y) hB
        (by rw [hcardB]; exact hyodd) (by rw [hcardB]; exact hy3) h4
      have hmem : conjPermHom (le_refl (conjSetStab Δ)) ⟨y, hyΔ⟩ ∈
          ((zpowers y).subgroupOf (conjSetStab Δ)).map
            (conjPermHom (le_refl (conjSetStab Δ))) :=
        Subgroup.mem_map_of_mem _ (by rw [Subgroup.mem_subgroupOf]; exact mem_zpowers y)
      rw [hbot] at hmem
      exact (CFSG.ComponentClassification.AS81.Sec2.conjPermHom_eq_one_iff
        (le_refl (conjSetStab Δ)) ⟨y, hyΔ⟩).mp (Subgroup.mem_bot.mp hmem)
    · have hlarge : 4 < Δ.ncard := by omega
      have hdim := finrank_ne_eight_of_large_paired_family D ePair hlarge
      have hblock := conjPermHom_mem_blockStab_of_paired_model_frames hr2 hfund hadm hA1 D.hm
        hFodd hdim D.π D.hker D.hscalar D.A D.horth D.R D.hR ψ hψ hker Δ ePair hePair
      obtain ⟨N, hN, h2N, ⟨e⟩⟩ := exists_twoKernel_quotient_perm_of_paired_conjPermHom ePair
        hblock (exists_paired_conjPermHom_of_orthogonal_model D hr2 hfund hadm ψ ePair hePair)
      exact mem_normalizer_of_conjSetStab_quot P hSΔ N h2N e hyΔ hyNP hyodd
  let J : Fin D.m × Bool → Subgroup X := fun k => (D.R k).map ψ
  have hJΔ : ∀ k, J k ∈ Δ := fun k => by
    have h := (ePair k).2
    rwa [hePair k] at h
  have hinj : ∀ k, D.R k ⊓ ψ.ker = ⊥ := fun k =>
    inf_ker_eq_bot_of_mem_fundamentalSubgroups hfund hadm hA1 ψ hker (D.hR k).1
  choose eR heR using fun k => pairedModel_exists_mulEquiv D hfund hadm hA1 k
  have hyC : ∀ k, y ∈ centralizer (((P : Subgroup X) ⊓ J k : Subgroup X) : Set X) := by
    intro k
    obtain ⟨eJ⟩ := nonempty_mulEquiv_map_of_inf_ker_eq_bot ψ (hinj k) (eR k)
    refine mem_centralizer_of_isSylowOf_sl2 hFodd (K := J k) (Q := (P : Subgroup X) ⊓ J k) eJ
      (hJΔ k).2 ?_ hp hp5 ?_
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        (Subgroup.mem_inf.mpr ⟨hyNP, hfix (J k) (hJΔ k)⟩)
    · exact Subgroup.centralizer_le (inf_le_left : (P : Subgroup X) ⊓ J k ≤ P) hypP
  choose Qs hQs using fun k => exists_sylow_of_isSylowOf_map ψ (hinj k) (eR k) (hJΔ k).2
  obtain ⟨yt, hψyt, hytodd⟩ := CFSG.ClassicalInvolution.Q3.exists_odd_orderOf_lift ψ hψ hyodd
  have hcen4 : ∀ z ∈ center (modelUniv t n r f hpr).K, z ^ 4 = 1 := fun z hz =>
    pairedModel_pow_four_eq_one_of_mem_center D hr2 hz
  have hcenOdd : ∀ z ∈ center (modelUniv t n r f hpr).K, Odd (orderOf z) → z = 1 := by
    intro z hz hzo
    have h1 : orderOf z ∣ 4 := orderOf_dvd_of_pow_eq_one (hcen4 z hz)
    have h2 : Nat.Coprime (orderOf z) 4 := by
      have := (Nat.coprime_two_right.mpr hzo).pow_right 2
      simpa using this
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)
  have hytp : yt ^ p ^ j = 1 := by
    have hk : yt ^ p ^ j ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hψyt, hyj]
    exact hcenOdd _ (hker hk) (Odd.of_dvd_nat hytodd (orderOf_pow_dvd _))
  let yh := D.π yt
  have hcommV : ∀ k, ∀ A ∈ (Qs k : Subgroup SL(2, GaloisField r f)),
      yh * (if k.2 then (D.A k.1).swap.La A else (D.A k.1).La A) =
        (if k.2 then (D.A k.1).swap.La A else (D.A k.1).La A) * yh := by
    intro k A hA
    obtain ⟨x, hxP, hxA⟩ := hQs k A hA
    have hxJ : ψ x ∈ J k := Subgroup.mem_map_of_mem ψ x.2
    have hc1 : Commute (ψ yt) (ψ x) := by
      rw [hψyt]
      exact ((Subgroup.mem_centralizer_iff.mp (hyC k)) (ψ x)
        (Subgroup.mem_inf.mpr ⟨hxP, hxJ⟩)).symm
    obtain ⟨a, ha⟩ := (Qs k).isPGroup' ⟨A, hA⟩
    have hxa : (x : (modelUniv t n r f hpr).K) ^ 2 ^ a = 1 := by
      have hA2 : A ^ 2 ^ a = 1 := congrArg Subtype.val ha
      have : eR k (x ^ 2 ^ a) = 1 := by rw [map_pow, hxA, hA2]
      have hx1 : x ^ 2 ^ a = 1 := (eR k).injective (by rw [this, map_one])
      exact congrArg Subtype.val hx1
    have hcen : yt * x * yt⁻¹ * (x : (modelUniv t n r f hpr).K)⁻¹ ∈
        center (modelUniv t n r f hpr).K := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hc1.eq]
      group
    have hcomm := commute_of_odd_of_pow_two_pow_of_mem_center hytodd hxa hcen
    have h := congrArg D.π hcomm.eq
    rw [map_mul, map_mul, heR k x, hxA] at h
    exact h
  have hyhO : yh ∈ TauCeti.QuadraticMap.orthogonalGroup D.Q :=
    pairedModel_range_le_orthogonalGroup D ⟨yt, rfl⟩
  have hyhodd : Odd (orderOf yh) := Odd.of_dvd_nat hytodd (orderOf_map_dvd _ _)
  have hspan : ∀ i, ∀ v ∈ (D.A i).span, yh v = v := fun i =>
    frame_apply_eq_self_of_commute_sylow hFodd (D.A i) (Qs (i, false)) (Qs (i, true)) hyhO
      hyhodd (fun A hA => by simpa using hcommV (i, false) A hA)
      (fun B hB => by simpa using hcommV (i, true) B hB)
  have hPK2 : IsPGroup 2 ((P : Subgroup X).comap ψ) := by
    intro g
    obtain ⟨a, ha⟩ := P.isPGroup' ⟨ψ g, g.2⟩
    refine ⟨a + 2, Subtype.ext ?_⟩
    have hg : (g : (modelUniv t n r f hpr).K) ^ 2 ^ a ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val ha
    have h4 := hcen4 _ (hker hg)
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, h4]
  have hPKi : ¬ 2 ∣ ((P : Subgroup X).comap ψ).index := by
    rw [Subgroup.index_comap_of_surjective _ hψ]
    exact P.not_dvd_index
  let PK : Sylow 2 (modelUniv t n r f hpr).K := hPK2.toSylow hPKi
  have hPKcoe : (PK : Subgroup (modelUniv t n r f hpr).K) = (P : Subgroup X).comap ψ :=
    IsPGroup.toSylow_coe _ _
  let G : Subgroup (D.V ≃ₗ[GaloisField r f] D.V) := D.π.range
  let T : Sylow 2 G := PK.mapSurjective (f := D.π.rangeRestrict) D.π.rangeRestrict_surjective
  have hTcoe : (T : Subgroup G) = (PK : Subgroup (modelUniv t n r f hpr).K).map
      D.π.rangeRestrict := Sylow.coe_mapSurjective _ _
  have hconjΔ : ∀ c ∈ (P : Subgroup X).comap ψ, ∀ k, ∃ k',
      ((D.R k).map ψ).map (MulAut.conj (ψ c)).toMonoidHom = (D.R k').map ψ := by
    intro c hc k
    have hcΔ : (ψ c)⁻¹ ∈ conjSetStab Δ := (conjSetStab Δ).inv_mem (hSΔ hc)
    have hmem : ((D.R k).map ψ).map (MulAut.conj (ψ c)).toMonoidHom ∈ Δ := by
      have h := (CFSG.ComponentClassification.AS81.Sec2.mem_conjSetStab.mp hcΔ (J k)).mp (hJΔ k)
      simpa only [CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate,
        inv_inv] using h
    refine ⟨ePair.symm ⟨_, hmem⟩, ?_⟩
    have h := hePair (ePair.symm ⟨_, hmem⟩)
    rw [Equiv.apply_symm_apply] at h
    exact h
  have hTA : ∀ s ∈ (T : Subgroup G), ∀ i, ∃ k,
      (s : D.V ≃ₗ[GaloisField r f] D.V) * (D.A i).La (-1) *
        (s : D.V ≃ₗ[GaloisField r f] D.V)⁻¹ = (D.A k).La (-1) := by
    intro s hs i
    rw [hTcoe] at hs
    obtain ⟨c, hc, rfl⟩ := hs
    rw [hPKcoe] at hc
    exact pairedModel_conj_La_neg_one D hr2 hfund hadm hA1 ψ hker (hconjΔ c hc) i
  let h : G := D.π.rangeRestrict yt
  have hN : h ∈ normalizer ((T : Subgroup G) : Set G) := by
    have hyt : yt ∈ normalizer (((PK : Subgroup (modelUniv t n r f hpr).K)) :
        Set (modelUniv t n r f hpr).K) := by
      rw [hPKcoe]
      refine Subgroup.le_normalizer_comap ψ ?_
      rw [Subgroup.mem_comap, hψyt]
      exact hyNP
    rw [hTcoe]
    exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hyt)
  have hhp : h ^ p ^ j = 1 := by
    rw [← map_pow, hytp, map_one]
  have h1 := eq_one_of_frames_of_mem_normalizer hFodd D.hQ D.hm D.A D.horth D.hfull G
    (pairedModel_range_le_orthogonalGroup D)
    (fun a b _ _ hab => pairedModel_reflection_mul_mem_range D a b hab) T hTA hp hp5 hhp hN
    hspan
  have hyt1 : yt = 1 := by
    have hk : yt ∈ D.π.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val h1
    exact hcenOdd yt (D.hker hk) hytodd
  rw [← hψyt, hyt1, map_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
