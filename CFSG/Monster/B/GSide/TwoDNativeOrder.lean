module

public import CFSG.Monster.B.CTIB.Rank2168Final
public import CFSG.Monster.B.GSide.CompletionFusion
public import CFSG.Monster.GMS.Leech.Involutions
public import CFSG.Monster.Existence.GMSBridge
public import CFSG.Monster.GMS.Griess13.ChecksUniqueness
public import CFSG.Sporadic.Co1.Module.Involutions
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3023
public import Certificates.Certificate3024
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3059
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate3080
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3121
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3175
public import Certificates.Certificate3176
public import Certificates.Certificate6007
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate8955
public import Certificates.Certificate16042
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069
public import CFSG.Monster.GMS.Leech.Data

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.TwoA CFSG.Monster.Visible
  CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.B.TwoA.Census
  CFSG.LocalAnalysis.ComponentInitial

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem natCard_centralizer_quotient_le {C : Type*} [Group C] [Finite C] {N : Subgroup C}
    [N.Normal] (hN : N ≤ Subgroup.center C) (x : C) :
    Nat.card (Subgroup.centralizer {(x : C ⧸ N)}) ≤ Nat.card (Subgroup.centralizer {x}) := by
  classical
  set q : C →* C ⧸ N := QuotientGroup.mk' N with hq
  set Hh : Subgroup C := (Subgroup.centralizer {(x : C ⧸ N)}).comap q with hHh
  have hNH : N ≤ Hh := fun n hn => by
    rw [hHh, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have : q n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [this, one_mul, mul_one]
  have hcard1 : Nat.card Hh = Nat.card (Subgroup.centralizer {(x : C ⧸ N)}) * Nat.card N := by
    have hsurj : Function.Surjective ((q.comp Hh.subtype).codRestrict
        (Subgroup.centralizer {(x : C ⧸ N)}) (fun h => Subgroup.mem_comap.1 h.2)) := by
      intro y
      obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (y : C ⧸ N)
      refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
      rw [hHh, Subgroup.mem_comap, hg]
      exact y.2
    have hker : ((q.comp Hh.subtype).codRestrict (Subgroup.centralizer {(x : C ⧸ N)})
        (fun h => Subgroup.mem_comap.1 h.2)).ker = N.subgroupOf Hh := by
      ext h
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        have h2 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).1 h2
      · intro h1
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h1)
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((q.comp Hh.subtype).codRestrict
        (Subgroup.centralizer {(x : C ⧸ N)}) (fun h => Subgroup.mem_comap.1 h.2)).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
  have hcomm : ∀ g : Hh, (g : C) * x * (g : C)⁻¹ * x⁻¹ ∈ N := by
    intro g
    have h1 : q g * q x = q x * q g :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 g.2)
    rw [← QuotientGroup.eq_one_iff]
    change q g * q x * (q g)⁻¹ * (q x)⁻¹ = 1
    rw [h1]
    group
  let f : Hh →* N :=
    { toFun := fun g => ⟨(g : C) * x * (g : C)⁻¹ * x⁻¹, hcomm g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hb := hN (hcomm b)
        have hb' : ∀ y : C, ((b : C) * x * (b : C)⁻¹ * x⁻¹) * y =
            y * ((b : C) * x * (b : C)⁻¹ * x⁻¹) := fun y => (Subgroup.mem_center_iff.1 hb y).symm
        simp only [Subgroup.coe_mul, mul_inv_rev]
        calc (a : C) * b * x * ((b : C)⁻¹ * (a : C)⁻¹) * x⁻¹
            = (a : C) * (((b : C) * x * (b : C)⁻¹ * x⁻¹) * x) * (a : C)⁻¹ * x⁻¹ := by group
          _ = (a : C) * (x * ((b : C) * x * (b : C)⁻¹ * x⁻¹)) * (a : C)⁻¹ * x⁻¹ := by rw [hb' x]
          _ = (a : C) * x * (((b : C) * x * (b : C)⁻¹ * x⁻¹) * (a : C)⁻¹) * x⁻¹ := by group
          _ = (a : C) * x * ((a : C)⁻¹ * ((b : C) * x * (b : C)⁻¹ * x⁻¹)) * x⁻¹ := by
              rw [hb' (a : C)⁻¹]
          _ = (a : C) * x * (a : C)⁻¹ * (((b : C) * x * (b : C)⁻¹ * x⁻¹) * x⁻¹) := by group
          _ = (a : C) * x * (a : C)⁻¹ * (x⁻¹ * ((b : C) * x * (b : C)⁻¹ * x⁻¹)) := by
              rw [hb' x⁻¹]
          _ = (a : C) * x * (a : C)⁻¹ * x⁻¹ * ((b : C) * x * (b : C)⁻¹ * x⁻¹) := by group) }
  have hkerf : Nat.card f.ker ≤ Nat.card (Subgroup.centralizer {x}) := by
    refine Nat.card_le_card_of_injective (fun g => ⟨((g : Hh) : C), ?_⟩) ?_
    · have h1 : f g = 1 := g.2
      have h2 := congrArg Subtype.val h1
      change (g : C) * x * (g : C)⁻¹ * x⁻¹ = 1 at h2
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 : (g : C) * x * (g : C)⁻¹ = x := mul_inv_eq_one.1 h2
      calc ((g : Hh) : C) * x = (g : C) * x * (g : C)⁻¹ * g := by group
        _ = x * g := by rw [h3]
    · intro a b h
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  have hcard2 : Nat.card Hh ≤ Nat.card (Subgroup.centralizer {x}) * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, mul_comm]
    refine Nat.mul_le_mul hkerf ?_
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_le_card_group _
  have hNpos : 0 < Nat.card N := Nat.card_pos
  rw [hcard1] at hcard2
  exact Nat.le_of_mul_le_mul_right hcard2 hNpos

theorem hGmat_mem_centralizer_xGmat :
    hGmat ∈ Subgroup.centralizer ({Existence.xGmat} : Set Gmat) :=
  Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_singleton_iff.1 xGmat_mem_centralizer_hGmat).symm

private def centXEquiv : Subgroup.centralizer ({Existence.xGmat} : Set Gmat) ≃* Gvis :=
  ((Subgroup.centralizer ({Existence.xGmat} : Set Gmat)).equivMapOfInjective Gmat.subtype
    Gmat.subtype_injective).trans (MulEquiv.subgroupCongr Existence.map_cent_xGmat)

private theorem coe_centXEquiv (y : Subgroup.centralizer ({Existence.xGmat} : Set Gmat)) :
    ((centXEquiv y : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = ((y : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) :=
  rfl

theorem hGmat_not_mem_leechQ :
    hGmat ∉ GMS.leechQ Existence.xGmat := by
  rintro ⟨y, hy, hyh⟩
  have hmap : (CFSG.pCore 2 (Subgroup.centralizer ({Existence.xGmat} : Set Gmat))).map
      centXEquiv.toMonoidHom = rhoQvis := by
    rw [CFSG.pCore_map_iso 2 centXEquiv, Existence.pCore_Gvis]
  have hmem : centXEquiv y ∈ rhoQvis := hmap ▸ ⟨y, hy, rfl⟩
  have hval : ((centXEquiv y : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) =
      (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) :=
    (coe_centXEquiv y).trans (congrArg (fun g : Gmat => (g : SpaceB ≃ₗ[ℚ] SpaceB)) hyh)
  exact cosetRep_one_not_mem_Qmat (hval ▸ (Subgroup.mem_subgroupOf.1 hmem))

theorem natCard_centralizer_xGmat_inf_hGmat_le :
    Nat.card ↥(Subgroup.centralizer ({Existence.xGmat} : Set Gmat) ⊓
      Subgroup.centralizer ({hGmat} : Set Gmat)) ≤ 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
  have hL := GMS.exists_leechSystem GMS.co1ModuleUniqueness
    Existence.gmsLeechCentralizer_xGmat
  obtain ⟨L⟩ := hL
  have hb := (L.involution_bounds hGmat_mem_centralizer_xGmat).1
  have h2 := L.orderOf_φ hGmat_mem_centralizer_xGmat orderOf_hGmat hGmat_not_mem_leechQ
  have hI := (GMS.co1InvolutionFacts.1 _ h2).1
  exact hb.trans ((Nat.mul_le_mul_left 2 hI).trans_eq (by norm_num))

theorem map_centralizer_xGmat_in_hGmat :
    (Subgroup.centralizer {(⟨Existence.xGmat, xGmat_mem_centralizer_hGmat⟩ :
        Subgroup.centralizer ({hGmat} : Set Gmat))}).map
      (Subgroup.centralizer ({hGmat} : Set Gmat)).subtype =
      Subgroup.centralizer ({Existence.xGmat} : Set Gmat) ⊓
        Subgroup.centralizer ({hGmat} : Set Gmat) := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg')), g'.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨g, h2⟩, Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 h1)), rfl⟩

theorem natCard_centralizer_octadT_le :
    Nat.card (Subgroup.centralizer {octadT} : Subgroup octadD) ≤ 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
  have h1 := natCard_centralizer_quotient_le (selfZpowers_le_center hGmat)
    (⟨Existence.xGmat, xGmat_mem_centralizer_hGmat⟩ : Subgroup.centralizer ({hGmat} : Set Gmat))
  have h2 : Nat.card (Subgroup.centralizer {(⟨Existence.xGmat, xGmat_mem_centralizer_hGmat⟩ :
      Subgroup.centralizer ({hGmat} : Set Gmat))}) =
      Nat.card ↥(Subgroup.centralizer ({Existence.xGmat} : Set Gmat) ⊓
        Subgroup.centralizer ({hGmat} : Set Gmat)) := by
    rw [← map_centralizer_xGmat_in_hGmat,
      Subgroup.card_map_of_injective (Subgroup.centralizer ({hGmat} : Set Gmat)).subtype_injective]
  exact h1.trans (h2.trans_le natCard_centralizer_xGmat_inf_hGmat_le)

theorem natCard_centralizer_octadV_le :
    Nat.card (Subgroup.centralizer {octadV} : Subgroup Dfull) ≤ 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
  rw [← Nat.card_congr centOctadVEquiv.toEquiv]
  exact natCard_centralizer_octadT_le

theorem exists_rank_2168_natCard_le :
    ∃ w : Sbp, orderOf w = 2 ∧ ((βr w) - 1).rank = 2168 ∧
    Nat.card (Subgroup.centralizer {w}) ≤ 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
  have htr := sylow_containing_subgroup_local_normal_two_transfer exists_sylow_le_Shat
    orderOf_octadV isCharacteristicP_octadV
  obtain ⟨s, ⟨g, hg⟩, hsS, ⟨R, hRT, hRn, hR2, hcen⟩, -, hcard⟩ := htr
  have hs2 : orderOf s = 2 := by
    have e := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) octadV
    rw [MulAut.conj_apply, inv_inv] at e
    exact (congrArg orderOf hg).trans (e.trans orderOf_octadV)
  have hw : sEquiv (sEquiv.symm ⟨s, hsS⟩) = ⟨s, hsS⟩ := sEquiv.apply_symm_apply _
  let e : Subgroup.centralizer {sEquiv.symm ⟨s, hsS⟩} ≃*
      (Shat ⊓ Subgroup.centralizer {s} : Subgroup Dfull) :=
    ((centralizerEquiv sEquiv _).trans (MulEquiv.subgroupCongr
      (congrArg (fun y : Shat => Subgroup.centralizer {y}) hw))).trans (centShatEquiv ⟨s, hsS⟩)
  have hw2 : orderOf (sEquiv.symm ⟨s, hsS⟩) = 2 :=
    (MulEquiv.orderOf_eq sEquiv.symm _).trans
      ((Subgroup.orderOf_coe (⟨s, hsS⟩ : Shat)).symm.trans hs2)
  have hrank := rank_of_local_witness native_rank_2158_distance_three_product_final.2.1 hw2
    (exists_selfCent_of_le e hRT hRn hR2 hcen)
    (ordProj_le_of_mulEquiv e.symm (hcard.trans_le ordProj_octadV_le))
  refine ⟨_, hw2, hrank, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  have hsub : Nat.card (Shat ⊓ Subgroup.centralizer {s} : Subgroup Dfull) ≤
      Nat.card (Subgroup.centralizer {s} : Subgroup Dfull) :=
    Subgroup.card_le_of_le inf_le_right
  have hconj : g⁻¹ * octadV * g⁻¹⁻¹ = s := by rw [inv_inv, hg]
  rw [← Nat.card_congr (centConjEquiv g⁻¹ hconj).toEquiv] at hsub
  exact hsub.trans natCard_centralizer_octadV_le

theorem natCard_centralizer_le_of_rank_2168
    {y : Sbp} (hy : orderOf y = 2)
    (hr : ((βr y) - 1).rank = 2168) :
    Nat.card (Subgroup.centralizer {y}) ≤ 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
  have hwit := exists_rank_2168_natCard_le
  obtain ⟨w, hw, hwr, hwc⟩ := hwit
  have hc : IsConj y w :=
    (isConj_rs_three_of_rank hy hr).trans (isConj_rs_three_of_rank hw hwr).symm
  obtain ⟨c, hc'⟩ := isConj_iff.1 hc
  rw [Nat.card_congr (centConjEquiv c hc').toEquiv]
  exact hwc

theorem natCard_centralizer_le_of_rankS_eq_2168
    {s : Shat} (hs : orderOf s = 2)
    (hrk : rankS s = 2168) :
    Nat.card (Subgroup.centralizer {s}) ≤ 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
  have hy : orderOf (sEquiv.symm s) = 2 := (orderOf_sEquiv_symm s).trans hs
  have h := natCard_centralizer_le_of_rank_2168 hy hrk
  have e : Subgroup.centralizer {sEquiv.symm s} ≃* Subgroup.centralizer {s} :=
    (centralizerEquiv sEquiv _).trans (MulEquiv.subgroupCongr
      (congrArg (fun y : Shat => Subgroup.centralizer {y}) (sEquiv.apply_symm_apply s)))
  rw [← Nat.card_congr e.toEquiv]
  exact h

theorem centralizer_eq_of_le_of_natCard
    {t : Shat} (ht : orderOf t = 2) (hrk : rankS t = 2168)
    {P : Subgroup Shat} (hP : P ≤ Subgroup.centralizer {t})
    (hcard : Nat.card P = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7) :
    Subgroup.centralizer {t} = P :=
  (Subgroup.eq_of_le_of_card_ge hP
    ((natCard_centralizer_le_of_rankS_eq_2168 ht hrk).trans hcard.ge)).symm

theorem centralizer_le_normalizer_of_le_of_natCard
    {t : Shat} (ht : orderOf t = 2)
    (hrk : rankS t = 2168) {P T : Subgroup Shat} (hP : P ≤ Subgroup.centralizer {t})
    (hcard : Nat.card P = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7)
    (hPT : P ≤ Subgroup.normalizer (T : Set Shat)) :
    Subgroup.centralizer {t} ≤ Subgroup.normalizer (T : Set Shat) :=
  (centralizer_eq_of_le_of_natCard ht hrk hP hcard).le.trans hPT

end CFSG.Monster.B.GSide
