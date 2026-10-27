module

public import CFSG.Monster.B.GSide.HSylowBetaStruct
public import CFSG.Monster.B.CTIB.HOuter
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
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
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
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3175
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
public import Certificates.Certificate3050
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
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

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

section Labels

theorem clabel_injective' :
    Function.Injective clabel :=
  (global_label_of_ambient ambientRootOrbitsHyp).1

theorem clabelS_injective' :
    Function.Injective clabelS := fun _ _ h =>
  clabel_injective' (congrArg Subtype.val h)

theorem commute_clabelS_iff'
    (v : CVert) (s : Shat) : Commute s (clabelS v) ↔ s ∈ vStab v :=
  CTIB.commute_clabelS_iff clabel_injective' v s

theorem diam_le_three :
    ∀ v w : CVert, cgraph.dist v w ≤ 3 :=
  (diameter_three_rank_five_of_ambient ambientRootOrbitsHyp).1

theorem clabelS_mem_derivedStab_of_adj
    {v w : CVert} (hvw : cgraph.Adj v w) :
    clabelS w ∈ derivedStab v := by
  obtain ⟨ρ, iv, hρ⟩ := exists_isCompatLocal v
  have hw : clabelS w ∈ vStab v :=
    (commute_clabelS_iff' v _).1 (CTIB.commute_clabelS_of_adj hvw).symm
  have h := hρ.2.2.2.2 ⟨w, hvw⟩ ⟨clabelS w, hw⟩ (coe_clabelS w)
  have e : clabelS w = ((⟨clabelS w, hw⟩ : vStab v) : Shat) := rfl
  rw [e, coe_mem_derivedStab_iff_right hρ.1, h]
  rfl

theorem clabelS_mem_derivedStab_self'
    (v : CVert) : clabelS v ∈ derivedStab v := by
  obtain ⟨ρ, iv, hρ⟩ := exists_isCompatLocal v
  exact clabelS_mem_derivedStab_self hρ.1 hρ.2.1

theorem clabelS_not_mem_derivedStab_of_dist_three
    {v u : CVert} (h : cgraph.dist v u = 3) :
    clabelS u ∉ derivedStab v := by
  have h' := native_distance_three_label_is_outer_local_involution_final
    (mem_sphereDistThree.2 h)
  obtain ⟨hu, hout, -⟩ := h'
  have e : clabelS u = ((⟨clabelS u, hu⟩ : vStab v) : Shat) := rfl
  rw [e, coe_mem_derivedStab_iff]
  exact hout _ rfl

theorem clabelS_mem_vStab_of_dist3
    {v u : CVert} (h : cgraph.dist v u = 3) :
    clabelS u ∈ vStab v := by
  have h' := native_distance_three_label_is_outer_local_involution_final
    (mem_sphereDistThree.2 h)
  exact h'.1

theorem clabelS_mem_vStab_of_adj
    {v w : CVert} (hvw : cgraph.Adj v w) : clabelS w ∈ vStab v :=
  (commute_clabelS_iff' v _).1 (CTIB.commute_clabelS_of_adj hvw).symm

theorem yset_invariant
    {v u : CVert} (hvu : cgraph.dist v u = 3) {g : Shat}
    (hg : g ∈ vStab v ⊓ vStab u) {y : CVert} (hy : y ∈ cgraph.neighborSet u \ sphereFour v) :
    cvMul y g ∈ cgraph.neighborSet u \ sphereFour v := by
  have hT := native_distance_three_pair_two_local_root_orbits_final hvu
  exact hT.2.2.2.2.2.1 g hg y hy

theorem ncard_yset
    {v u : CVert} (hvu : cgraph.dist v u = 3) :
    (cgraph.neighborSet u \ sphereFour v).ncard = 69615 := by
  have hT := native_distance_three_pair_two_local_root_orbits_final hvu
  exact hT.2.2.2.2.2.2.2.2.1

theorem yset_eq_fixed
    {v u : CVert} (hvu : cgraph.dist v u = 3) :
    {z | z ∈ cgraph.neighborSet u ∧ cvMul z (clabelS v) = z} =
      cgraph.neighborSet u \ sphereFour v := by
  have hT := native_distance_three_pair_two_local_root_orbits_final hvu
  exact hT.2.2.2.2.2.2.2.2.2.2.1

theorem mem_yset_facts
    {v u w : CVert} (hvu : cgraph.dist v u = 3)
    (hw : w ∈ cgraph.neighborSet u \ sphereFour v) :
    cgraph.Adj u w ∧ cgraph.dist v w = 3 ∧ Commute (clabelS v) (clabelS w) := by
  have hw' : w ∈ {z | z ∈ cgraph.neighborSet u ∧ cvMul z (clabelS v) = z} := by
    rw [yset_eq_fixed hvu]
    exact hw
  have hc : Commute (clabelS v) (clabelS w) := (commute_clabelS_iff' w _).2 hw'.2
  have huw : cgraph.Adj u w := hw'.1
  have hne : v ≠ w := by
    rintro rfl
    rw [SimpleGraph.dist_comm, SimpleGraph.dist_eq_one_iff_adj.2 huw] at hvu
    exact absurd hvu (by norm_num)
  refine ⟨huw, ?_, hc⟩
  rcases CTIB.adj_or_dist_three_of_commute diam_le_three hne hc with h | h
  · exfalso
    have h1 := dist_le_add_one_of_adj (v := v) huw.symm
    rw [SimpleGraph.dist_eq_one_iff_adj.2 h] at h1
    omega
  · exact h

end Labels

section Classes

variable {u : CVert} {β : vStab cv0} {X : Subgroup (vStab cv0)}

@[expose] def hc5Ev
    (u : CVert) : Set Shat :=
  (fun w => clabelS cv0 * clabelS w) '' (cgraph.neighborSet cv0 \ sphereFour u)

@[expose] def hc5Eu
    (u : CVert) : Set Shat :=
  (fun w => clabelS u * clabelS w) '' (cgraph.neighborSet u \ sphereFour cv0)

theorem ncard_label_mul_image
    (p : CVert) (Y : Set CVert) :
    ((fun w => clabelS p * clabelS w) '' Y).ncard = Y.ncard :=
  Set.InjOn.ncard_image fun _ _ _ _ h => clabelS_injective' (mul_left_cancel h)

theorem ncard_hc5Ev
    (hvu : cgraph.dist cv0 u = 3) : (hc5Ev u).ncard = 69615 := by
  rw [hc5Ev, ncard_label_mul_image]
  exact ncard_yset (by rw [SimpleGraph.dist_comm]; exact hvu)

theorem ncard_hc5Eu
    (hvu : cgraph.dist cv0 u = 3) : (hc5Eu u).ncard = 69615 := by
  rw [hc5Eu, ncard_label_mul_image]
  exact ncard_yset hvu

theorem conj_label_mul
    {p w : CVert} {x : Shat} (hx : x ∈ vStab p) :
    x * (clabelS p * clabelS w) * x⁻¹ = clabelS p * clabelS (cvMul w x⁻¹) := by
  have hc : x * clabelS p = clabelS p * x := ((commute_clabelS_iff' p x).2 hx).eq
  rw [clabelS_cvMul, inv_inv]
  calc x * (clabelS p * clabelS w) * x⁻¹ = (x * clabelS p) * clabelS w * x⁻¹ := by group
    _ = (clabelS p * x) * clabelS w * x⁻¹ := by rw [hc]
    _ = clabelS p * (x * clabelS w * x⁻¹) := by group

theorem conj_mem_hc5Ev
    (hvu : cgraph.dist cv0 u = 3) {x : Shat} (hx : x ∈ vStab cv0 ⊓ vStab u)
    {z : Shat} (hz : z ∈ hc5Ev u) : x * z * x⁻¹ ∈ hc5Ev u := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hx' : x⁻¹ ∈ vStab u ⊓ vStab cv0 := ⟨(vStab u).inv_mem hx.2, (vStab cv0).inv_mem hx.1⟩
  exact ⟨cvMul w x⁻¹, yset_invariant (by rw [SimpleGraph.dist_comm]; exact hvu) hx' hw,
    (conj_label_mul hx.1).symm⟩

theorem conj_mem_hc5Eu
    (hvu : cgraph.dist cv0 u = 3) {x : Shat} (hx : x ∈ vStab cv0 ⊓ vStab u)
    {z : Shat} (hz : z ∈ hc5Eu u) : x * z * x⁻¹ ∈ hc5Eu u := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hx' : x⁻¹ ∈ vStab cv0 ⊓ vStab u := ⟨(vStab cv0).inv_mem hx.1, (vStab u).inv_mem hx.2⟩
  exact ⟨cvMul w x⁻¹, yset_invariant hvu hx' hw, (conj_label_mul hx.2).symm⟩

theorem isPGroup_map_X (hX : Nat.card X = 2 ^ 26) :
    IsPGroup 2 (X.map (vStab cv0).subtype) :=
  IsPGroup.of_card ((Subgroup.card_map_of_injective (vStab cv0).subtype_injective).trans hX)

theorem coe_mem_inf_of_mem_X
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) {x : Shat} (hx : x ∈ X.map (vStab cv0).subtype) :
    x ∈ vStab cv0 ⊓ vStab u := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y.2, (mem_centralizer_beta_iff hvu hβ).1 (hXβ hy)⟩

theorem exists_hc5ZP_Ev
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    ∃ w, cgraph.Adj cv0 w ∧ cgraph.dist u w = 3 ∧ Commute (clabelS u) (clabelS w) ∧
      ∃ a ∈ hc5ZP u X, (a : Shat) = clabelS cv0 * clabelS w := by
  have huv : cgraph.dist u cv0 = 3 := by rw [SimpleGraph.dist_comm]; exact hvu
  obtain ⟨z, ⟨w, hw, rfl⟩, hfix⟩ := exists_conj_fixed_of_odd (isPGroup_map_X hX)
    (Set.toFinite (hc5Ev u)) (by rw [ncard_hc5Ev hvu]; decide)
    fun x hx z hz => conj_mem_hc5Ev hvu (coe_mem_inf_of_mem_X hvu hβ hXβ hx) hz
  obtain ⟨hadj, hd, hc⟩ := mem_yset_facts huv hw
  have hmem : clabelS cv0 * clabelS w ∈ vStab cv0 :=
    (vStab cv0).mul_mem cV0.2 (clabelS_mem_vStab_of_adj hadj)
  refine ⟨w, hadj, hd, hc, ⟨_, hmem⟩, ?_, rfl⟩
  have hcomm : ∀ y ∈ X, (⟨_, hmem⟩ : vStab cv0) * y = y * ⟨_, hmem⟩ := fun y hy => by
    have h := hfix y ⟨y, hy, rfl⟩
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    calc clabelS cv0 * clabelS w * (y : Shat) =
        ((y : Shat) * (clabelS cv0 * clabelS w) * (y : Shat)⁻¹) * y := by rw [h]
      _ = y * (clabelS cv0 * clabelS w) := by group
  have hcu : Commute (clabelS cv0) (clabelS u) := by
    rw [← hβ, ← coe_cV0]
    exact Commute.map ((Subgroup.mem_center_iff.1 cV0_mem_center_H β).symm) (vStab cv0).subtype
  have hR : (⟨_, hmem⟩ : vStab cv0) ∈ Subgroup.centralizer {β} := by
    rw [mem_centralizer_beta_iff hvu hβ]
    exact (commute_clabelS_iff' u _).1 (hcu.mul_left hc.symm)
  have hsq : (⟨_, hmem⟩ : vStab cv0) * ⟨_, hmem⟩ = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    exact CTIB.mul_self_mul_of_commute (CTIB.commute_clabelS_of_adj hadj)
      (clabelS_mul_clabelS cv0) (clabelS_mul_clabelS w))
  have hXa := mem_X_of_commute hvu hβ hXβ hX hR hsq hcomm
  have hF : (⟨_, hmem⟩ : vStab cv0) ∈ hc5F u := by
    rw [mem_hc5F]
    refine ⟨⟨⟨hmem, (mem_centralizer_beta_iff hvu hβ).1 hR⟩, ?_⟩, ?_⟩
    · exact (derivedStab cv0).mul_mem (clabelS_mem_derivedStab_self' cv0)
        (clabelS_mem_derivedStab_of_adj hadj)
    · exact mul_mem_derivedStab (clabelS_mem_vStab_of_dist3 huv)
        (clabelS_mem_vStab_of_dist3 hd) (clabelS_not_mem_derivedStab_of_dist_three huv)
        (clabelS_not_mem_derivedStab_of_dist_three hd)
  exact mem_hc5ZP.2 ⟨⟨hXa, hF⟩, fun y hy => hcomm y hy.1⟩

theorem exists_hc5ZP_Eu
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    ∃ w, cgraph.Adj u w ∧ cgraph.dist cv0 w = 3 ∧ Commute (clabelS cv0) (clabelS w) ∧
      ∃ b ∈ hc5ZP u X, (b : Shat) = clabelS u * clabelS w := by
  obtain ⟨z, ⟨w, hw, rfl⟩, hfix⟩ := exists_conj_fixed_of_odd (isPGroup_map_X hX)
    (Set.toFinite (hc5Eu u)) (by rw [ncard_hc5Eu hvu]; decide)
    fun x hx z hz => conj_mem_hc5Eu hvu (coe_mem_inf_of_mem_X hvu hβ hXβ hx) hz
  obtain ⟨hadj, hd, hc⟩ := mem_yset_facts hvu hw
  have hmem : clabelS u * clabelS w ∈ vStab cv0 :=
    (vStab cv0).mul_mem (clabelS_mem_vStab_of_dist3 hvu)
      ((commute_clabelS_iff' cv0 _).1 hc.symm)
  refine ⟨w, hadj, hd, hc, ⟨_, hmem⟩, ?_, rfl⟩
  have hcomm : ∀ y ∈ X, (⟨_, hmem⟩ : vStab cv0) * y = y * ⟨_, hmem⟩ := fun y hy => by
    have h := hfix y ⟨y, hy, rfl⟩
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    calc clabelS u * clabelS w * (y : Shat) =
        ((y : Shat) * (clabelS u * clabelS w) * (y : Shat)⁻¹) * y := by rw [h]
      _ = y * (clabelS u * clabelS w) := by group
  have hR : (⟨_, hmem⟩ : vStab cv0) ∈ Subgroup.centralizer {β} := by
    rw [mem_centralizer_beta_iff hvu hβ]
    exact (commute_clabelS_iff' u _).1 ((Commute.refl _).mul_left
      (CTIB.commute_clabelS_of_adj hadj).symm)
  have hsq : (⟨_, hmem⟩ : vStab cv0) * ⟨_, hmem⟩ = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    exact CTIB.mul_self_mul_of_commute (CTIB.commute_clabelS_of_adj hadj)
      (clabelS_mul_clabelS u) (clabelS_mul_clabelS w))
  have hXb := mem_X_of_commute hvu hβ hXβ hX hR hsq hcomm
  have hF : (⟨_, hmem⟩ : vStab cv0) ∈ hc5F u := by
    rw [mem_hc5F]
    refine ⟨⟨⟨hmem, (mem_centralizer_beta_iff hvu hβ).1 hR⟩, ?_⟩, ?_⟩
    · exact mul_mem_derivedStab (clabelS_mem_vStab_of_dist3 hvu)
        (clabelS_mem_vStab_of_dist3 hd) (clabelS_not_mem_derivedStab_of_dist_three hvu)
        (clabelS_not_mem_derivedStab_of_dist_three hd)
    · exact (derivedStab u).mul_mem (clabelS_mem_derivedStab_self' u)
        (clabelS_mem_derivedStab_of_adj hadj)
  exact mem_hc5ZP.2 ⟨⟨hXb, hF⟩, fun y hy => hcomm y hy.1⟩

end Classes

end CFSG.Monster.B.GSide
