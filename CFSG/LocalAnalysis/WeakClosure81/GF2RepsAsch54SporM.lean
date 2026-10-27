module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.Monster.Schur.GmatStructureZ

import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporNineSub
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1
import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Blueprint
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.Schur CFSG.Monster.Visible

namespace SporM

theorem Gmat_inf_centralizer_Vmat :
    Gmat ⊓ Subgroup.centralizer (Vmat : Set (SpaceB ≃ₗ[ℚ] SpaceB)) = CVMat := by
  have hx : xmat ∈ Vmat := mem_Vmat.2 (.inr (.inl rfl))
  have hy : xmatTau ∈ Vmat := mem_Vmat.2 (.inr (.inr (.inl rfl)))
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hg, hc⟩
    have hH : g ∈ Hmat := by
      rw [← Gmat_inf_centralizer_xmat]
      exact ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 (hc xmat hx).symm⟩
    exact ⟨hH, mem_CyMat_of_comm hg (hc xmatTau hy).symm⟩
  · rintro ⟨hH, hC⟩
    refine ⟨Hmat_le_Gmat hH, fun v hv => ?_⟩
    have h1 : Commute xmat g := (Hmat_comm_xmat hH).symm
    have h2 : Commute xmatTau g := (CyMat_comm hC).symm
    rcases mem_Vmat.1 hv with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact h1
    · exact h2
    · have e : xmatTau2 = xmat * xmatTau := by
        rw [xmat_eq_xB, xmatTau_eq, xmatTau2_eq, xB_mul_yB]
      rw [e]
      exact h1.mul_left h2

theorem coe_mem_PMat_of_mem_centralizer {g : Gmat}
    (hg : g ∈ Subgroup.centralizer (Vmat.subgroupOf Gmat : Set Gmat)) :
    (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ PMat := by
  have h : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ CVMat := by
    rw [← Gmat_inf_centralizer_Vmat]
    refine ⟨g.2, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
    have hv' : (⟨v, Vmat_le_Gmat hv⟩ : Gmat) ∈ Vmat.subgroupOf Gmat :=
      Subgroup.mem_subgroupOf.2 hv
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hg _ hv')
  exact (le_sup_right : CVMat ≤ Qmat ⊔ CVMat) h

theorem coe_mem_PMat_of_mem_ker
    {g : Subgroup.normalizer (Vmat.subgroupOf Gmat : Set Gmat)}
    (hg : g ∈ (Vmat.subgroupOf Gmat).normalizerMonoidHom.ker) :
    ((g : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ PMat := by
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hg
  exact coe_mem_PMat_of_mem_centralizer hg

theorem PMat_le_normalizer_Vmat :
    PMat ≤ Subgroup.normalizer (Vmat : Set (SpaceB ≃ₗ[ℚ] SpaceB)) := by
  obtain ⟨-, -, -, -, -, -, -, hVQ, -, -, -⟩ :=
    CFSG.Monster.B.triality_four_group_spin_identification
  have hx : Subgroup.zpowers xmat ≤ Vmat := Subgroup.zpowers_le.2 (mem_Vmat.2 (.inr (.inl rfl)))
  refine sup_le (Subgroup.le_set_normalizer_iff.2 fun g hg v hv => ?_)
    (Subgroup.le_set_normalizer_iff.2 fun g hg v hv => ?_)
  · have h := Vmat.mul_mem (hx (comm_Qmat g hg v (hVQ hv))) hv
    rw [inv_mul_cancel_right] at h
    exact h
  · rw [← Gmat_inf_centralizer_Vmat] at hg
    rw [← Subgroup.mem_centralizer_iff.1 hg.2 v hv, mul_inv_cancel_right]
    exact hv

theorem tauB_mem_normalizer_Vmat :
    tauB ∈ Subgroup.normalizer (Vmat : Set (SpaceB ≃ₗ[ℚ] SpaceB)) := by
  refine Subgroup.mem_normalizer_iff.2 fun v => ⟨conj_tauB_mem_Vmat v, fun hv => ?_⟩
  have h := conj_tauB_mem_Vmat _ (conj_tauB_mem_Vmat _ hv)
  have h3 : tauB * tauB * tauB = 1 := by rw [← pow_three', tauB_pow_three]
  have e : tauB * (tauB * (tauB * v * tauB⁻¹) * tauB⁻¹) * tauB⁻¹ =
      tauB * tauB * tauB * v * (tauB * tauB * tauB)⁻¹ := by
    simp only [mul_inv_rev, mul_assoc]
  rw [e, h3, one_mul, inv_one, mul_one] at h
  exact h

theorem mem_normalizer_subgroupOf {g : Gmat}
    (hg : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Subgroup.normalizer (Vmat : Set (SpaceB ≃ₗ[ℚ] SpaceB))) :
    g ∈ Subgroup.normalizer (Vmat.subgroupOf Gmat : Set Gmat) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  exact hg h

theorem PMat_subgroupOf_le_normalizer :
    PMat.subgroupOf Gmat ≤ Subgroup.normalizer (Vmat.subgroupOf Gmat : Set Gmat) := fun _ hg =>
  mem_normalizer_subgroupOf (PMat_le_normalizer_Vmat (Subgroup.mem_subgroupOf.1 hg))

theorem Hmat_subgroupOf_sup_normalizer_Vmat :
    Hmat.subgroupOf Gmat ⊔ Subgroup.normalizer (Vmat.subgroupOf Gmat : Set Gmat) = ⊤ := by
  have hτ : (⟨tauB, tauB_mem_Gmat⟩ : Gmat) ∈
      Hmat.subgroupOf Gmat ⊔ Subgroup.normalizer (Vmat.subgroupOf Gmat : Set Gmat) :=
    Subgroup.mem_sup_right (mem_normalizer_subgroupOf tauB_mem_normalizer_Vmat)
  have hle : Subgroup.closure (insert tauB⁻¹ (Hmat : Set (SpaceB ≃ₗ[ℚ] SpaceB))) ≤
      (Hmat.subgroupOf Gmat ⊔ Subgroup.normalizer (Vmat.subgroupOf Gmat : Set Gmat)).map
        Gmat.subtype := by
    rw [Subgroup.closure_le]
    rintro f (rfl | hf)
    · exact Subgroup.mem_map.2 ⟨_, inv_mem hτ, rfl⟩
    · exact Subgroup.mem_map.2
        ⟨⟨f, Hmat_le_Gmat hf⟩, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hf), rfl⟩
  rw [closure_insert_tauB_inv_Hmat] at hle
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.1 (hle g.2)
  rwa [show s = g from Subtype.ext hsg] at hs

theorem tauB_not_mem_Hmat : tauB ∉ Hmat := fun h =>
  xmatTau_ne_xmat (by rw [xmatTau, Hmat_comm_xmat h, mul_inv_cancel_right])

theorem Hmat_subgroupOf_ne_top : Hmat.subgroupOf Gmat ≠ ⊤ := fun h => by
  have hτ : (⟨tauB, tauB_mem_Gmat⟩ : Gmat) ∈ Hmat.subgroupOf Gmat := by
    rw [h]
    exact Subgroup.mem_top _
  exact tauB_not_mem_Hmat (Subgroup.mem_subgroupOf.1 hτ)

theorem normalizer_Vmat_subgroupOf_ne_top :
    Subgroup.normalizer (Vmat.subgroupOf Gmat : Set Gmat) ≠ ⊤ := fun h => by
  have := generated_rational_group_finite_simple.2.1
  have : (Vmat.subgroupOf Gmat).Normal := Subgroup.normalizer_eq_top_iff.1 h
  rcases Subgroup.Normal.eq_bot_or_eq_top (Vmat.subgroupOf Gmat) with hb | ht
  · have hx : (⟨xmat, Vmat_le_Gmat (mem_Vmat.2 (.inr (.inl rfl)))⟩ : Gmat) ∈
        Vmat.subgroupOf Gmat := Subgroup.mem_subgroupOf.2 (mem_Vmat.2 (.inr (.inl rfl)))
    rw [hb, Subgroup.mem_bot] at hx
    exact xmat_ne_one (congrArg Subtype.val hx)
  · have hτ : (⟨tauB, tauB_mem_Gmat⟩ : Gmat) ∈ Vmat.subgroupOf Gmat := by
      rw [ht]
      exact Subgroup.mem_top _
    exact tauB_not_mem_Hmat (Vmat_le_Hmat (Subgroup.mem_subgroupOf.1 hτ))

theorem pow_three_eq_one_of_pow_nine_PMat
    (p : PMat) (hp : p ^ 9 = 1) : p ^ 3 = 1 := by
  let f : PMat →* NativeSporadic.M24 := autPermEquivM24.toMonoidHom.comp psiP
  have hf : Function.Surjective f := autPermEquivM24.surjective.comp psiP_surjective
  have hk : Nat.card f.ker = 2 ^ 36 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      CFSG.Sporadic.Mathieu.card_M24, natCard_PMat] at h
    refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 244823040) ?_
    rw [← h]
    norm_num
  exact pow_three_eq_one_of_pow_nine_of_ker f
    (by rw [hk]; exact Nat.Coprime.pow_left 36 (by decide)) pow_three_eq_one_of_pow_nine_M24 p hp

theorem not_hasCompFactor_isCalL0_Hmat :
    ¬ HasCompFactor (Hmat.subgroupOf Gmat) IsCalL0 := by
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have e : Gvis ⧸ rhoQvis ≃* NativeSporadic.Co1 :=
    CFSG.Monster.Existence.Co1Bridge.visQuotEquivCo1
  have : IsSimpleGroup (Gvis ⧸ rhoQvis) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co1.isSimpleGroup_Co1 e
  have : Finite rhoQvis :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Monster.Existence.natCard_rhoQvis]; norm_num)
  rintro ⟨L, _, hL, hcal⟩
  have hL' := (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
    (Subgroup.subgroupOfEquivOfLe Hmat_le_Gmat : Hmat.subgroupOf Gmat ≃* Gvis)).1 hL
  rcases isCompositionFactor_of_normal rhoQvis hL' with h1 | h2
  · exact not_isCalL0_of_isCompositionFactor_of_dvd hO (k := 25) (N := 2 ^ 25) (by decide +kernel)
      (dvd_of_eq CFSG.Monster.Existence.natCard_rhoQvis) h1 hcal
  · exact not_isCalL0_of_isCompositionFactor_of_isSimpleGroup hO (k := 21)
      (by rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Co1.card_Co1]; decide +kernel) h2 hcal

theorem not_hasCompFactor_isCalL0_normalizer_Vmat :
    ¬ HasCompFactor (Subgroup.normalizer (Vmat.subgroupOf Gmat : Set Gmat)) IsCalL0 := by
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  let ι : Subgroup.normalizer (Vmat.subgroupOf Gmat : Set Gmat) →* SpaceB ≃ₗ[ℚ] SpaceB :=
    Gmat.subtype.comp (Subgroup.normalizer (Vmat.subgroupOf Gmat : Set Gmat)).subtype
  have hι : Function.Injective ι := Gmat.subtype_injective.comp (Subgroup.subtype_injective _)
  rintro ⟨L, _, hL, hcal⟩
  rcases isCompositionFactor_of_normal (Vmat.subgroupOf Gmat).normalizerMonoidHom.ker hL with
    h1 | h2
  · refine not_hasCompFactor_isCalL0_of_dvd_of_forall_mem_pow_nine hO
      (k := 46) (N := 2 ^ 25 * (2 ^ 11 * 244823040)) (by decide +kernel)
      (A := (Vmat.subgroupOf Gmat).normalizerMonoidHom.ker) (fun g hg h9 => ?_) ?_
      ⟨L, _, h1, hcal⟩
    · have h := pow_three_eq_one_of_pow_nine_PMat ⟨ι g, coe_mem_PMat_of_mem_ker hg⟩
        (Subtype.ext (show ι g ^ 9 = 1 by rw [← map_pow, h9, map_one]))
      refine (map_eq_one_iff ι hι).1 ?_
      rw [map_pow]
      exact congrArg Subtype.val h
    · have h := Subgroup.card_dvd_of_le
        (show (Vmat.subgroupOf Gmat).normalizerMonoidHom.ker.map ι ≤ PMat from fun x hx => by
          obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
          exact coe_mem_PMat_of_mem_ker hg)
      rwa [Subgroup.card_map_of_injective hι, natCard_PMat] at h
  · have hV : Nat.card (Vmat.subgroupOf Gmat) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Vmat_le_Gmat).toEquiv]
      exact generated_rational_group_finite_centralizer.2.2.2.2.1
    refine not_isCalL0_of_isCompositionFactor_of_dvd hO (k := 3) (N := 24) (by decide +kernel)
      ?_ h2 hcal
    have hperm : Function.Injective (MulAut.toPerm (M := Vmat.subgroupOf Gmat)) :=
      fun a b hab => MulEquiv.ext fun x => Equiv.congr_fun hab x
    let φ : Subgroup.normalizer (Vmat.subgroupOf Gmat : Set Gmat) ⧸
        (Vmat.subgroupOf Gmat).normalizerMonoidHom.ker →* Equiv.Perm (Vmat.subgroupOf Gmat) :=
      (MulAut.toPerm (Vmat.subgroupOf Gmat)).comp
        (QuotientGroup.kerLift (Vmat.subgroupOf Gmat).normalizerMonoidHom)
    have hφ : Function.Injective φ :=
      hperm.comp (QuotientGroup.kerLift_injective (Vmat.subgroupOf Gmat).normalizerMonoidHom)
    have h := Subgroup.card_dvd_of_injective φ hφ
    rw [Nat.card_perm, hV, show (4 : ℕ).factorial = 24 from rfl] at h
    exact h

theorem exists_isSylowIn_le_PMat :
    ∃ T : Subgroup Gmat, IsSylowIn 2 T ⊤ ∧ T ≤ PMat.subgroupOf Gmat := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : Nat.card (PMat.subgroupOf Gmat) = 2 ^ 46 * 239085 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe PMat_le_Gmat).toEquiv, natCard_PMat]
    norm_num
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := PMat.subgroupOf Gmat) 2 (n := 46)
    (by rw [hP]; exact dvd_mul_right _ _)
  have hTc : Nat.card (K.map (PMat.subgroupOf Gmat).subtype) = 2 ^ 46 := by
    rw [Subgroup.card_map_of_injective (PMat.subgroupOf Gmat).subtype_injective, hK]
  have hidx : (K.map (PMat.subgroupOf Gmat).subtype).index =
      11482618231106483731969943632999939453125 := by
    have h := (K.map (PMat.subgroupOf Gmat).subtype).card_mul_index
    rw [hTc, natCard_Gmat_eq] at h
    refine Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ 46) (h.trans ?_)
    norm_num
  refine ⟨K.map (PMat.subgroupOf Gmat).subtype, ⟨le_top, IsPGroup.of_card hTc, ?_⟩,
    Subgroup.map_subtype_le K⟩
  rw [Subgroup.relIndex_top_right, hidx]
  norm_num

theorem exists_isLPair :
    ∃ T : Subgroup Gmat, IsSylowIn 2 T ⊤ ∧
      IsLPair IsCalL0 T (Hmat.subgroupOf Gmat)
        (Subgroup.normalizer (Vmat.subgroupOf Gmat : Set Gmat)) := by
  obtain ⟨T, hT, hTP⟩ := exists_isSylowIn_le_PMat
  exact ⟨T, hT,
    { le_left := fun _ hg =>
        Subgroup.mem_subgroupOf.2 (PMat_le_Hmat (Subgroup.mem_subgroupOf.1 (hTP hg)))
      le_right := hTP.trans PMat_subgroupOf_le_normalizer
      ne_top_left := Hmat_subgroupOf_ne_top
      ne_top_right := normalizer_Vmat_subgroupOf_ne_top
      not_left := not_hasCompFactor_isCalL0_Hmat
      not_right := not_hasCompFactor_isCalL0_normalizer_Vmat
      sup_eq_top := Hmat_subgroupOf_sup_normalizer_Vmat }⟩

end SporM

theorem asch54SporGenAt_m :
    Asch54SporGenAt .M := by
  obtain ⟨T, hT, h⟩ := SporM.exists_isLPair
  obtain ⟨e⟩ : Nonempty (Gmat ≃* TauCeti.SporadicName.M.Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  exact asch54SporGenAt_of_isLPair_of_card_outer_eq_one (C := Gmat) ⟨e.symm⟩
    (Nat.card_eq_one_iff_unique.2
      ⟨CFSG.ComponentClassification.BMCase.subsingleton_outer_of_inner
        CFSG.RankThree.PartOne.SPOR.allInner_Gmat, ⟨1⟩⟩) hT h

end CFSG.LocalAnalysis.WeakClosure81

end
