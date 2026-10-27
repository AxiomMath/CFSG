module

public import CFSG.Monster.Existence.TwoPoint.ShapeOneGriess
public import CFSG.Monster.Existence.BabyW2
public import CFSG.Monster.Existence.NormalizerF
public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.Monster.GMS.BabyCover
import Mathlib.Tactic.Group
public import Certificates.Certificate43
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
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
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
public import Certificates.Certificate3175
public import Certificates.Certificate6006
public import Certificates.Certificate6007
public import Certificates.Certificate6009
public import Certificates.Certificate6010
public import Certificates.Certificate6011
public import Certificates.Certificate6012
public import Certificates.Certificate6013
public import Certificates.Certificate6014
public import Certificates.Certificate6015
public import Certificates.Certificate6016
public import Certificates.Certificate6017
public import Certificates.Certificate6018
public import Certificates.Certificate6021
public import Certificates.Certificate6022
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate6025
public import Certificates.Certificate6026
public import Certificates.Certificate16001
public import Certificates.Certificate16006
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16018
public import Certificates.Certificate16019
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16030
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate3024
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import Certificates.Certificate8955
public import CFSG.Monster.AxisCount.BabyCoverSpec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

section General

variable {G X : Type} [Group G] [Group X]

theorem natCard_cent2_eq_of_swap [Finite G] {a u : G} (hau : u * a = a * u)
    {π : ↥(cent a) →* X} (hπ : Function.Surjective π)
    (hker : ∀ c : ↥(cent a), π c = 1 ↔ (c : G) = 1 ∨ (c : G) = a) (ha1 : a ≠ 1)
    {g : G} (hg : g ∈ cent a) (hgu : g * u * g⁻¹ = a * u) :
    Nat.card ↥(cent2 a u) = Nat.card ↥(Subgroup.centralizer ({π (uIn hau)} : Set X)) := by
  have : Finite X := Finite.of_surjective π hπ
  set T := Subgroup.centralizer ({π (uIn hau)} : Set X) with hT
  set H : Subgroup G := (T.comap π).map (cent a).subtype with hHdef
  have hker2 : Nat.card π.ker = 2 := by
    rw [Nat.card_eq_two_iff' (1 : π.ker)]
    refine ⟨⟨⟨a, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩, (hker _).2 (Or.inr rfl)⟩, ?_, ?_⟩
    · intro h
      apply ha1
      have := congrArg (fun y : π.ker => ((y : ↥(cent a)) : G)) h
      simpa using this
    · intro y hy
      rcases (hker _).1 y.2 with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hy
      · exact Subtype.ext (Subtype.ext h)
  have hH : Nat.card H = 2 * Nat.card T := by
    rw [hHdef, Subgroup.card_map_of_injective (cent a).subtype_injective]
    have h1 : Nat.card (T.comap π) * (T.comap π).index = Nat.card ↥(cent a) :=
      Subgroup.card_mul_index _
    have h2 : Nat.card T * T.index = Nat.card X := Subgroup.card_mul_index _
    have h3 : (T.comap π).index = T.index := Subgroup.index_comap_of_surjective T hπ
    have h4 : Nat.card π.ker * Nat.card X = Nat.card ↥(cent a) :=
      Subgroup.card_ker_mul_card_of_surjective hπ
    have hpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [h3] at h1
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← h4, hker2, mul_assoc, h2]
  have hHu : H ⊓ cent u = cent2 a u := by
    ext c
    constructor
    · rintro ⟨⟨c', -, rfl⟩, hcu⟩
      exact ⟨c'.2, hcu⟩
    · rintro ⟨hca, hcu⟩
      refine ⟨⟨⟨c, hca⟩, ?_, rfl⟩, hcu⟩
      show π ⟨c, hca⟩ ∈ T
      rw [hT, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hcu)
  have horb : {z : G | ∃ h ∈ H, h * u * h⁻¹ = z}.ncard = 2 := by
    refine ncard_orbit_eq_two ha1 (g₀ := g) ?_ hgu ?_
    · refine ⟨⟨g, hg⟩, ?_, rfl⟩
      show π ⟨g, hg⟩ ∈ T
      rw [hT, Subgroup.mem_centralizer_singleton_iff]
      have hconj : (⟨g, hg⟩ : ↥(cent a)) * uIn hau * (⟨g, hg⟩ : ↥(cent a))⁻¹ =
          ⟨a, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ * uIn hau :=
        Subtype.ext hgu
      have hπa : π ⟨a, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = 1 :=
        (hker _).2 (Or.inr rfl)
      have := congrArg π hconj
      rw [map_mul, map_mul, map_mul, hπa, one_mul, map_inv] at this
      calc π ⟨g, hg⟩ * π (uIn hau) =
          π ⟨g, hg⟩ * π (uIn hau) * (π ⟨g, hg⟩)⁻¹ * π ⟨g, hg⟩ := by group
        _ = π (uIn hau) * π ⟨g, hg⟩ := by rw [this]
    · rintro h ⟨c, hc, rfl⟩
      obtain ⟨e, he, hce⟩ := conj_eq_or_of_mem_centralizer hau hker hc
      rcases he with rfl | rfl
      · left
        simpa using hce
      · right
        exact hce
  have key := card_inf_centralizer_mul_orbit H u
  rw [hHu, horb, hH] at key
  omega

end General

section MGriess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.LieType.Chevalley.C2E6Std MulOpposite

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] noncomputable def swapGriess : MGriess :=
  ⟨gLift swapAut, Gmat_le_AutO (Cgen_le (gLift_mem_Cgen fixesPair01_swapAut)).1⟩

theorem swapGriess_mem_cent : swapGriess ∈ cent tGriess := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  have h : gLift swapAut ∈ Subgroup.centralizer {tStar} :=
    (Cgen_le (gLift_mem_Cgen fixesPair01_swapAut)).2
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  exact h

theorem swapGriess_conj_uGriess : swapGriess * uGriess * swapGriess⁻¹ = tGriess * uGriess := by
  apply Subtype.ext
  show gLift swapAut * uStar * (gLift swapAut)⁻¹ = tStar * uStar
  rw [gLift_swap_conj_uStar, uStar_mul_tStar, tStar_mul_uStar]

theorem natCard_cent2_tGriess_uGriess :
    Nat.card ↥(cent2 tGriess uGriess) =
      Nat.card ↥(Subgroup.centralizer ({uBar} : Set Cbar)) := by
  have h := natCard_cent2_eq_of_swap uGriess_mul_tGriess centToDA_surjective centToDA_eq_one_iff
    tGriess_ne_one swapGriess_mem_cent swapGriess_conj_uGriess
  rw [centToDA_uIn] at h
  rw [h]
  exact Nat.card_congr centUHatEquivBar.toEquiv

theorem inv'_uBar : MulEquiv.inv' Cbar uBar = op uBar := by
  show op uBar⁻¹ = op uBar
  rw [uBar_inv]

theorem orderOf_op_uBar : orderOf (op uBar : Sbp) = 2 := by
  rw [← inv'_uBar, MulEquiv.orderOf_eq]
  exact orderOf_uBar

theorem rank_betaS_op_uBar :
    (((betaRow Dyadic.betaS (op uBar) : MatBˣ) : MatB) - 1).rank = 1860 := by
  have h := betaRow_eB (phiB uBar)
  rw [eB_phiB, uBar_inv, betaStd_eq_betaS] at h
  rw [h, CFSG.Monster.Existence.rank_conj_sub_one Tmat_mul_inv Tmat_inv_mul]
  exact rank_phiB_uBar_sub_one

noncomputable def centOpUBarEquiv :
    ↥(Subgroup.centralizer ({op uBar} : Set Sbp)) ≃*
      ↥(Subgroup.centralizer ({uBar} : Set Cbar)) :=
  (CTIB.centralizerEquiv (MulEquiv.inv' Cbar).symm (op uBar)).trans
    (MulEquiv.subgroupCongr (by rw [← inv'_uBar, MulEquiv.symm_apply_apply]))

theorem natCard_Eam :
    Nat.card ↥Amalgam.Eam = 4 * Nat.card stdGroup := by
  obtain ⟨h1, -, -, -, -, -, -, h8⟩ := CTIB.derivedCoverInput_holds
  have h := Subgroup.card_mul_index (commutator ↥Amalgam.Eam)
  rw [h1, h8] at h
  rw [← h, card_stdGroup]

theorem natCard_cent2_tGriess_uGriess_of
    (hC : CTIB.CentralizerInput) :
    Nat.card ↥(cent2 tGriess uGriess) = 4 * Nat.card stdGroup := by
  obtain ⟨Ψ⟩ := CTIB.centralizer_equiv_Eam hC
    (CTIB.isConj_labelS_of_rank orderOf_op_uBar rank_betaS_op_uBar)
  rw [natCard_cent2_tGriess_uGriess, ← Nat.card_congr centOpUBarEquiv.toEquiv,
    Nat.card_congr Ψ.toEquiv, natCard_Eam]

theorem twoPointShape_one_of_centralizerInput
    (hC : CTIB.CentralizerInput) :
    TwoPointShape (cent2 tGriess uGriess) 1 := by
  obtain ⟨K₀, -, -, hq, hZ₀, ⟨e₀⟩, -, -⟩ :=
    CTIB.native_rank_1860_unique_component hC (op uBar) orderOf_op_uBar rank_betaS_op_uBar
  set K := K₀.map centOpUBarEquiv.toMonoidHom with hK
  have eK : ↥K₀ ≃* ↥K := K₀.equivMapOfInjective _ centOpUBarEquiv.injective
  have hperf₀ : ⁅K₀, K₀⁆ = K₀ := by
    rw [← Subgroup.map_subtype_commutator, Group.isPerfect_def.1 hq.1, Subgroup.map_top,
      Subgroup.range_subtype]
  refine twoPointShape_tGriess_uGriess K ?_ ?_ ?_ (natCard_cent2_tGriess_uGriess_of hC)
  · rw [hK, ← Subgroup.map_commutator, hperf₀]
  · rw [← hZ₀]
    exact Nat.card_congr (Subgroup.centerCongr eK).symm.toEquiv
  · exact ⟨(QuotientGroup.congr _ _ eK.symm (center_map_mulEquiv eK.symm)).trans e₀⟩

end MGriess

end CFSG.Monster.Existence
