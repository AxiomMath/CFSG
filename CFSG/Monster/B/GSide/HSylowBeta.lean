module

public import CFSG.Monster.B.GSide.HSylowBetaRank
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
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3013
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
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
public import Certificates.Certificate3122
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3137
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
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate3951
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
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem inf_centralizer_eq_map_center (X : Subgroup G) :
    X ⊓ Subgroup.centralizer (X : Set G) = (Subgroup.center X).map X.subtype := by
  ext z
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, mem_center_map_subtype_iff]
  exact and_congr_right fun _ => ⟨fun h y hy => (h y hy).symm, fun h y hy => (h y hy).symm⟩

theorem isConj_mul_left_of_mem_center {z x y : G} (hz : z ∈ Subgroup.center G)
    (h : IsConj x y) : IsConj (z * x) (z * y) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  refine isConj_iff.2 ⟨g, ?_⟩
  have hgz : g * z = z * g := Subgroup.mem_center_iff.1 hz g
  calc g * (z * x) * g⁻¹ = (g * z) * x * g⁻¹ := by group
    _ = (z * g) * x * g⁻¹ := by rw [hgz]
    _ = z * (g * x * g⁻¹) := by group
    _ = z * y := by rw [hg]

theorem closure_pair_eq_set {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    (Subgroup.closure ({a, b} : Set G) : Set G) = {1, a, b, a * b} := by
  ext f
  constructor
  · intro hf
    rcases mem_closure_pair_cases ha hb hab hf with h | h | h | h <;> simp [h]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem natCard_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 4 := by
  have hab1 : a * b ≠ 1 := fun h => hne (by
    rw [mul_eq_one_iff_eq_inv] at h
    rw [h, inv_eq_of_mul_eq_one_right hb])
  have hab2 : a * b ≠ a := fun h => hb1 (by simpa using h)
  have hab3 : a * b ≠ b := fun h => ha1 (by simpa using h)
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, closure_pair_eq_set ha hb hab,
    Set.ncard_insert_of_notMem (by simp [ha1.symm, hb1.symm, hab1.symm]),
    Set.ncard_insert_of_notMem (by simp [hne, hab2.symm]),
    Set.ncard_insert_of_notMem (by simp [hab3.symm]), Set.ncard_singleton]

theorem mul_mul_comm_of_comm {f c b : G} (h1 : f * c = c * f) (h2 : f * b = b * f) :
    f * (c * b) = c * b * f := by
  rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]

theorem inv_mul_mul_eq_of_comm {f v : G} (h : f * v = v * f) : v⁻¹ * (f * v) = f := by
  rw [h, inv_mul_cancel_left]

end Generic

section Data

variable {u : CVert} {β : vStab cv0} {X : Subgroup (vStab cv0)}

theorem hc5_ab_basic
    {w w' : CVert} (hw : cgraph.Adj cv0 w) (hw' : cgraph.Adj u w')
    {a b : vStab cv0} (ha : a ∈ hc5ZP u X) (hb : b ∈ hc5ZP u X)
    (hae : (a : Shat) = clabelS cv0 * clabelS w) (hbe : (b : Shat) = clabelS u * clabelS w')
    (hra : rkH a = 2048) (hrb : rkH b = 2048) (hrca : rkH (cV0 * a) = 1860)
    (hrcb : rkH (cV0 * b) = 2168) :
    a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have hr1 : rkH 1 = 0 := by
    rw [rkH_eq_of_coe (Subgroup.coe_one (vStab cv0)), map_one]
    exact CTIB.rank_beta_one
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, (mem_hc5ZP.1 ha).2 b (mem_hc5ZP.1 hb).1, fun h => ?_,
    fun h => ?_, fun h => ?_⟩
  · rw [Subgroup.coe_mul, hae, Subgroup.coe_one]
    exact CTIB.mul_self_mul_of_commute (CTIB.commute_clabelS_of_adj hw)
      (clabelS_mul_clabelS cv0) (clabelS_mul_clabelS w)
  · rw [Subgroup.coe_mul, hbe, Subgroup.coe_one]
    exact CTIB.mul_self_mul_of_commute (CTIB.commute_clabelS_of_adj hw')
      (clabelS_mul_clabelS u) (clabelS_mul_clabelS w')
  · rw [h, hr1] at hra
    exact absurd hra (by norm_num)
  · rw [h, hr1] at hrb
    exact absurd hrb (by norm_num)
  · rw [h, hrcb] at hrca
    exact absurd hrca (by norm_num)

theorem hc5ZP_eq_closure
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) {a b : vStab cv0}
    (ha : a ∈ hc5ZP u X) (hb : b ∈ hc5ZP u X) (haa : a * a = 1) (hbb : b * b = 1)
    (hab : a * b = b * a) (hra : rkH a = 2048) (hrb : rkH b = 2048)
    (hrca : rkH (cV0 * a) = 1860) (hrcb : rkH (cV0 * b) = 2168) :
    hc5ZP u X = Subgroup.closure {a, b} := by
  refine le_antisymm (fun f hf => ?_) ((Subgroup.closure_le _).2 ?_)
  · have h' : f ∈ (Subgroup.closure ({a, b} : Set (vStab cv0)) : Set (vStab cv0)) := by
      rw [closure_pair_eq_set haa hbb hab]
      rcases hc5ZP_cases hvu hβ hXβ hX ha hb hra hrb hrca hrcb hbb hf with h | h | h | h <;>
        simp [h]
    exact h'
  · rintro x (rfl | rfl)
    · exact ha
    · exact hb

theorem hc5_commute_labels
    (hβ : (β : Shat) = clabelS u) (hXβ : X ≤ Subgroup.centralizer {β})
    {w w' : CVert} {a b : vStab cv0} (ha : a ∈ hc5ZP u X)
    (hae : (a : Shat) = clabelS cv0 * clabelS w) (hbe : (b : Shat) = clabelS u * clabelS w')
    (hab : a * b = b * a) : Commute (clabelS w') (clabelS w) := by
  have hc : ∀ y : vStab cv0, cV0 * y = y * cV0 := fun y =>
    (Subgroup.mem_center_iff.1 cV0_mem_center_H y).symm
  have hβa : β * a = a * β := (Subgroup.mem_centralizer_singleton_iff.1
    (hXβ (mem_hc5ZP.1 ha).1.1)).symm
  have hcomm : Commute (β * b) (cV0 * a) :=
    Commute.mul_left (Commute.mul_right (hc β).symm hβa) (Commute.mul_right (hc b).symm hab.symm)
  have e1 : ((β * b : vStab cv0) : Shat) = clabelS w' := by
    rw [Subgroup.coe_mul, hβ, hbe, ← mul_assoc, clabelS_mul_clabelS, one_mul]
  have e2 : ((cV0 * a : vStab cv0) : Shat) = clabelS w := by
    rw [Subgroup.coe_mul, coe_cV0, hae, ← mul_assoc, clabelS_mul_clabelS, one_mul]
  rw [← e1, ← e2]
  exact hcomm.map (vStab cv0).subtype

theorem hc5_data
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    ∃ (w w' : CVert) (a b : vStab cv0),
      cgraph.Adj cv0 w ∧ cgraph.Adj u w' ∧ cgraph.dist cv0 w' = 3 ∧
      Commute (clabelS u) (clabelS w) ∧ Commute (clabelS w') (clabelS w) ∧
      (a : Shat) = clabelS cv0 * clabelS w ∧ (b : Shat) = clabelS u * clabelS w' ∧
      hc5ZP u X = Subgroup.closure {a, b} ∧
      a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
      rkH a = 2048 ∧ rkH (cV0 * a) = 1860 ∧ rkH b = 2048 ∧ rkH (cV0 * b) = 2168 ∧
      rkH (a * b) = 2048 ∧ rkH (cV0 * (a * b)) = 2168 := by
  have h := exists_hc5_ab hvu hβ hXβ hX
  obtain ⟨w, w', a, b, hw, -, hcw, hw', hdw', -, ha, hae, hb, hbe, hra, hrca, hrb, hrcb⟩ := h
  have hbas := hc5_ab_basic hw hw' ha hb hae hbe hra hrb hrca hrcb
  obtain ⟨haa, hbb, hab, ha1, hb1, hne⟩ := hbas
  have hZPeq := hc5ZP_eq_closure hvu hβ hXβ hX ha hb haa hbb hab hra hrb hrca hrcb
  have hrab := rkH_mul_eq hvu hβ hXβ hX hw hcw ha hae haa
    (fun f hf => hc5ZP_cases hvu hβ hXβ hX ha hb hra hrb hrca hrcb hbb hf) hrca hrcb
  exact ⟨w, w', a, b, hw, hw', hdw', hcw, hc5_commute_labels hβ hXβ ha hae hbe hab, hae, hbe,
    hZPeq, haa, hbb, hab, ha1, hb1, hne, hra, hrca, hrb, hrcb, hrab.1, hrab.2⟩

theorem hc5_isConj_beta_a
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    {w w' : CVert} (hw : cgraph.Adj cv0 w) (hcw : Commute (clabelS u) (clabelS w))
    (hdw' : cgraph.dist cv0 w' = 3) (hww : Commute (clabelS w') (clabelS w)) {a b : vStab cv0}
    (hae : (a : Shat) = clabelS cv0 * clabelS w) (hbe : (b : Shat) = clabelS u * clabelS w')
    (hab : a * b = b * a) : IsConj (β * a) (β * (a * b)) := by
  have h := CTIB.exists_triple_cvMul hvu hw hcw hdw' hw hww
  obtain ⟨g, hg0, hgu, hgw⟩ := h
  have hgH : g ∈ vStab cv0 := mem_vStab.2 hg0
  have e1 : g⁻¹ * clabelS u * g = clabelS w' := by rw [← clabelS_cvMul, hgu]
  have e2 : g⁻¹ * clabelS cv0 * g = clabelS cv0 := by rw [← clabelS_cvMul, hg0]
  have e3 : g⁻¹ * clabelS w * g = clabelS w := by rw [← clabelS_cvMul, hgw]
  refine isConj_iff.2 ⟨⟨g, hgH⟩⁻¹, Subtype.ext ?_⟩
  rw [hab]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  rw [hβ, hae, hbe]
  calc g⁻¹ * (clabelS u * (clabelS cv0 * clabelS w)) * g =
      (g⁻¹ * clabelS u * g) * ((g⁻¹ * clabelS cv0 * g) * (g⁻¹ * clabelS w * g)) := by group
    _ = clabelS w' * (clabelS cv0 * clabelS w) := by rw [e1, e2, e3]
    _ = clabelS u * (clabelS u * clabelS w' * (clabelS cv0 * clabelS w)) := by
      rw [← mul_assoc (clabelS u) (clabelS u * clabelS w'), ← mul_assoc (clabelS u) (clabelS u),
        clabelS_mul_clabelS, one_mul]

theorem hc5_coset
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hu : u ∈ sphereDistThree cv0) {w w' : CVert} (hw : cgraph.Adj cv0 w)
    (hcw : Commute (clabelS u) (clabelS w)) (hdw' : cgraph.dist cv0 w' = 3)
    (hww : Commute (clabelS w') (clabelS w)) {a b : vStab cv0}
    (hae : (a : Shat) = clabelS cv0 * clabelS w) (hbe : (b : Shat) = clabelS u * clabelS w')
    (haa : a * a = 1) (hbb : b * b = 1) (hab : a * b = b * a) (hb1 : b ≠ 1)
    (hβbFA : β * b ∈ FA) :
    ∀ y ∈ Subgroup.closure ({a, b} : Set (vStab cv0)),
      ∃ w ∈ Subgroup.closure ({a, b} : Set (vStab cv0)), w ≠ y ∧ IsConj (β * y) (β * w) := by
  have h1 : IsConj (β * 1) (β * b) := by
    rw [mul_one]
    exact (mem_FA_iff_isConj hu β hβ (β * b)).1 hβbFA
  have h2 := hc5_isConj_beta_a hvu hβ hw hcw hdw' hww hae hbe hab
  have hma : a ∈ Subgroup.closure ({a, b} : Set (vStab cv0)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hmb : b ∈ Subgroup.closure ({a, b} : Set (vStab cv0)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  intro y hy
  rcases mem_closure_pair_cases haa hbb hab hy with hy1 | hy1 | hy1 | hy1 <;> rw [hy1]
  · exact ⟨b, hmb, hb1, h1⟩
  · exact ⟨a * b, Subgroup.mul_mem _ hma hmb, fun h => hb1 (by simpa using h), h2⟩
  · exact ⟨1, Subgroup.one_mem _, hb1.symm, h1.symm⟩
  · exact ⟨a, hma, fun h => hb1 (by simpa using h.symm), h2.symm⟩

end Data

section Clauses

variable {u : CVert} {β : vStab cv0} {X : Subgroup (vStab cv0)}

theorem rkH_of_mem_RA
    {y : vStab cv0} (h : y ∈ RA) : rkH y = 1860 := by
  obtain ⟨w, -, hw⟩ := h
  exact rkH_label hw

theorem not_mem_RA_of_rkH
    {y : vStab cv0} (h : rkH y ≠ 1860) : y ∉ RA := fun h' =>
  h (rkH_of_mem_RA h')

theorem not_mem_RB_of_rkH
    {y : vStab cv0} (h : rkH (cV0 * y) ≠ 1860) : y ∉ RB := fun h' =>
  h (rkH_of_mem_RA h')

theorem hc5_elem_facts
    {y : vStab cv0} (hyy : y * y = 1) (hyc : y ∈ commutator (vStab cv0))
    (hr : rkH y ≠ 1860) (hrc : rkH (cV0 * y) ≠ 1860) :
    y * y = 1 ∧ y ∈ commutator (vStab cv0) ∧ y ≠ cV0 ∧ y ∉ RA ∧ y ∉ RB :=
  ⟨hyy, hyc, fun h => hr (by rw [h, rkH_cV0]), not_mem_RA_of_rkH hr, not_mem_RB_of_rkH hrc⟩

theorem hc5_U_eq
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) {a b : vStab cv0}
    (hZPeq : hc5ZP u X = Subgroup.closure {a, b}) :
    X ⊓ Subgroup.centralizer X ⊓ ⁅X, X⁆ = Subgroup.closure {a, b} := by
  rw [inf_centralizer_eq_map_center, center_inf_commutator_eq hvu hβ hXβ hX, hZPeq]

theorem hc5_center_eq
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) {a b : vStab cv0}
    (hZPeq : hc5ZP u X = Subgroup.closure {a, b}) :
    X ⊓ Subgroup.centralizer X = Subgroup.closure {cV0, β} ⊔ Subgroup.closure {a, b} := by
  rw [inf_centralizer_eq_map_center]
  refine le_antisymm (fun z hz => ?_) (sup_le ?_ ?_)
  · have h := (mem_center_X_iff hvu hβ hXβ hX).1 (mem_center_map_subtype_iff.1 hz)
    obtain ⟨f, hf, v, hv, rfl⟩ := h
    rw [hZPeq] at hf
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hf) (Subgroup.mem_sup_left hv)
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact mem_center_map_subtype_iff.2 ⟨cV0_mem_X hvu hβ hXβ hX, fun y _ => (cV0_comm y).symm⟩
    · exact mem_center_map_subtype_iff.2 ⟨beta_mem_X hvu hβ hXβ hX, fun y hy =>
        (Subgroup.mem_centralizer_singleton_iff.1 (hXβ hy)).symm⟩
  · rw [← hZPeq]
    intro f hf
    exact mem_center_map_subtype_iff.2
      ((mem_center_X_iff hvu hβ hXβ hX).2 ⟨f, hf, 1, Subgroup.one_mem _, (mul_one f).symm⟩)

theorem hc5_closure_le_F {a b : vStab cv0} (hZPeq : hc5ZP u X = Subgroup.closure {a, b}) :
    Subgroup.closure ({a, b} : Set (vStab cv0)) ≤ hc5F u := by
  rw [← hZPeq]
  exact fun f hf => (mem_hc5ZP.1 hf).1.2

theorem hc5_inf_eq_bot
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    {a b : vStab cv0} (hZPeq : hc5ZP u X = Subgroup.closure {a, b}) :
    Subgroup.closure {cV0, β} ⊓ Subgroup.closure {a, b} = ⊥ := by
  refine eq_bot_iff.2 ((inf_le_inf_left _ (hc5_closure_le_F hZPeq)).trans ?_)
  rw [inf_comm, hc5F_inf_closure hβ hvu]

theorem hc5_cV0_mul_a
    {w : CVert} (hw : cgraph.Adj cv0 w) {a : vStab cv0}
    (hae : (a : Shat) = clabelS cv0 * clabelS w) : cV0 * a ∈ RA :=
  ⟨w, hw, by rw [Subgroup.coe_mul, coe_cV0, hae, ← mul_assoc, clabelS_mul_clabelS, one_mul]⟩

theorem hc5_beta_b
    {w' : CVert} (hβ : (β : Shat) = clabelS u) (hdw' : cgraph.dist cv0 w' = 3)
    {b : vStab cv0} (hbe : (b : Shat) = clabelS u * clabelS w') : β * b ∈ FA :=
  ⟨w', mem_sphereDistThree.2 hdw', by
    rw [Subgroup.coe_mul, hβ, hbe, ← mul_assoc, clabelS_mul_clabelS, one_mul]⟩

theorem hc5_four_facts
    {a b : vStab cv0} (hZPeq : hc5ZP u X = Subgroup.closure {a, b})
    (haa : a * a = 1) (hbb : b * b = 1) (hab : a * b = b * a) (hrb : rkH b = 2048)
    (hrcb : rkH (cV0 * b) = 2168) (hrab : rkH (a * b) = 2048)
    (hrcab : rkH (cV0 * (a * b)) = 2168) :
    ∀ y ∈ ({b, a * b, cV0 * b, cV0 * (a * b)} : Set (vStab cv0)),
      y * y = 1 ∧ y ∈ commutator (vStab cv0) ∧ y ≠ cV0 ∧ y ∉ RA ∧ y ∉ RB := by
  have hF := hc5_closure_le_F hZPeq
  have hma : a ∈ Subgroup.closure ({a, b} : Set (vStab cv0)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hmb : b ∈ Subgroup.closure ({a, b} : Set (vStab cv0)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hbc : b ∈ commutator (vStab cv0) := mem_commutator_of_mem_hc5F (hF hmb)
  have habc : a * b ∈ commutator (vStab cv0) :=
    mem_commutator_of_mem_hc5F (hF (Subgroup.mul_mem _ hma hmb))
  have hab2 : a * b * (a * b) = 1 := CTIB.mul_self_mul_of_commute hab haa hbb
  have hcm := cV0_mem_commutator
  intro y hy
  rcases hy with hy1 | hy1 | hy1 | hy1 <;> rw [hy1]
  · exact hc5_elem_facts hbb hbc (by rw [hrb]; decide) (by rw [hrcb]; decide)
  · exact hc5_elem_facts hab2 habc (by rw [hrab]; decide) (by rw [hrcab]; decide)
  · refine hc5_elem_facts (CTIB.mul_self_mul_of_commute (cV0_comm b).symm cV0_mul_self hbb)
      (Subgroup.mul_mem _ hcm hbc) (by rw [hrcb]; decide) ?_
    rw [cV0_mul_cV0_mul, hrb]
    decide
  · refine hc5_elem_facts (CTIB.mul_self_mul_of_commute (cV0_comm _).symm cV0_mul_self hab2)
      (Subgroup.mul_mem _ hcm habc) (by rw [hrcab]; decide) ?_
    rw [cV0_mul_cV0_mul, hrab]
    decide

theorem hc5_coset_c
    {a b : vStab cv0}
    (h : ∀ y ∈ Subgroup.closure ({a, b} : Set (vStab cv0)),
      ∃ w ∈ Subgroup.closure ({a, b} : Set (vStab cv0)), w ≠ y ∧ IsConj (β * y) (β * w)) :
    ∀ y ∈ Subgroup.closure ({a, b} : Set (vStab cv0)),
      ∃ w ∈ Subgroup.closure ({a, b} : Set (vStab cv0)), w ≠ y ∧
        IsConj (cV0 * β * y) (cV0 * β * w) := by
  intro y hy
  obtain ⟨w₀, hw₀, hne₀, hconj⟩ := h y hy
  refine ⟨w₀, hw₀, hne₀, ?_⟩
  rw [mul_assoc, mul_assoc]
  exact isConj_mul_left_of_mem_center cV0_mem_center_H hconj

theorem hc5_mem_U_iff
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) {z : vStab cv0} :
    z ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ ↔ z ∈ hc5ZP u X := by
  rw [center_inf_commutator_eq hvu hβ hXβ hX]

theorem hc5_mem_V_cases
    (hβ : (β : Shat) = clabelS u) {v : vStab cv0}
    (hv : v ∈ Subgroup.closure ({cV0, β} : Set (vStab cv0))) :
    v = 1 ∨ v = cV0 ∨ v = β ∨ v = cV0 * β :=
  mem_closure_pair_cases cV0_mul_self (beta_mul_self hβ) (cV0_comm β).symm hv

theorem hc5_mem_ab_cases {a b : vStab cv0} (haa : a * a = 1) (hbb : b * b = 1)
    (hab : a * b = b * a) {y : vStab cv0} (hy : y ∈ Subgroup.closure ({a, b} : Set (vStab cv0))) :
    y = 1 ∨ y = a ∨ y = b ∨ y = a * b :=
  mem_closure_pair_cases haa hbb hab hy

theorem hc5_center_cover
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    ∀ z ∈ X, (∀ y ∈ X, z * y = y * z) →
      z ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ ∨
      cV0⁻¹ * z ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ ∨
      β⁻¹ * z ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ ∨
      (cV0 * β)⁻¹ * z ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ := by
  intro z hz hzc
  have h := (mem_center_X_iff hvu hβ hXβ hX).1 ⟨hz, hzc⟩
  obtain ⟨f, hf, v, hv, rfl⟩ := h
  have hU := (hc5_mem_U_iff hvu hβ hXβ hX).2 hf
  have hfβ : f * β = β * f := Subgroup.mem_centralizer_singleton_iff.1
    (hXβ (mem_hc5ZP.1 hf).1.1)
  have hfc : f * cV0 = cV0 * f := cV0_comm f
  have hfcβ : f * (cV0 * β) = cV0 * β * f := mul_mul_comm_of_comm hfc hfβ
  have hcases := hc5_mem_V_cases hβ hv
  refine hcases.elim (fun hv1 => ?_) (fun h => h.elim (fun hv1 => ?_)
    (fun h => h.elim (fun hv1 => ?_) (fun hv1 => ?_)))
  · left
    have e : f * v = f := by rw [hv1]; exact mul_one f
    exact Eq.mpr (congrArg (· ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆) e) hU
  · right; left
    have e : cV0⁻¹ * (f * v) = f := by rw [hv1]; exact inv_mul_mul_eq_of_comm hfc
    exact Eq.mpr (congrArg (· ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆) e) hU
  · right; right; left
    have e : β⁻¹ * (f * v) = f := by rw [hv1]; exact inv_mul_mul_eq_of_comm hfβ
    exact Eq.mpr (congrArg (· ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆) e) hU
  · right; right; right
    have e : (cV0 * β)⁻¹ * (f * v) = f := by rw [hv1]; exact inv_mul_mul_eq_of_comm hfcβ
    exact Eq.mpr (congrArg (· ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆) e) hU

theorem hc5_not_mem_U
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    cV0 ∉ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ ∧
      β⁻¹ * cV0 ∉ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ := by
  have hnotF : ∀ v ∈ Subgroup.closure ({cV0, β} : Set (vStab cv0)), v ≠ 1 →
      v ∉ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ := by
    intro v hv hv1 hvU
    rw [center_inf_commutator_eq hvu hβ hXβ hX] at hvU
    have h : v ∈ hc5F u ⊓ Subgroup.closure {cV0, β} := ⟨(mem_hc5ZP.1 hvU).1.2, hv⟩
    rw [hc5F_inf_closure hβ hvu, Subgroup.mem_bot] at h
    exact hv1 h
  have hmc : cV0 ∈ Subgroup.closure ({cV0, β} : Set (vStab cv0)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hmβ : β ∈ Subgroup.closure ({cV0, β} : Set (vStab cv0)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hc1 : cV0 ≠ 1 := fun h => by
    have := orderOf_cV0
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hβc : β ≠ cV0 := fun h => by
    have h' := congrArg Subtype.val h
    rw [hβ, coe_cV0] at h'
    have h'' := clabelS_injective' h'
    rw [h'', SimpleGraph.dist_self] at hvu
    exact absurd hvu (by norm_num)
  refine ⟨hnotF _ hmc hc1, hnotF _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hmβ) hmc) ?_⟩
  intro h
  rw [inv_mul_eq_one] at h
  exact hβc h

theorem hc5_U_classes
    {w : CVert} (hw : cgraph.Adj cv0 w) {a b : vStab cv0}
    (hae : (a : Shat) = clabelS cv0 * clabelS w) (hZPeq : hc5ZP u X = Subgroup.closure {a, b})
    (haa : a * a = 1) (hbb : b * b = 1) (hab : a * b = b * a) (hrb : rkH b = 2048)
    (hrcb : rkH (cV0 * b) = 2168) (hrab : rkH (a * b) = 2048)
    (hrcab : rkH (cV0 * (a * b)) = 2168) :
    ∀ y ∈ Subgroup.closure ({a, b} : Set (vStab cv0)), y = 1 ∨ cV0 * y ∈ RA ∨
      (y * y = 1 ∧ y ∈ commutator (vStab cv0) ∧ y ∉ RA ∧ y ∉ RB ∧ y ≠ cV0 ∧
        rkH y = 2048 ∧ rkH (cV0 * y) = 2168) := by
  have h4 := hc5_four_facts hZPeq haa hbb hab hrb hrcb hrab hrcab
  have hb4 := h4 b (Set.mem_insert _ _)
  have hab4 := h4 (a * b) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  intro y hy
  rcases hc5_mem_ab_cases haa hbb hab hy with hy1 | hy1 | hy1 | hy1
  · exact Or.inl hy1
  · rw [hy1]
    exact Or.inr (Or.inl (hc5_cV0_mul_a hw hae))
  · rw [hy1]
    obtain ⟨h1, h2, h3, h5, h6⟩ := hb4
    exact Or.inr (Or.inr ⟨h1, h2, h5, h6, h3, hrb, hrcb⟩)
  · rw [hy1]
    obtain ⟨h1, h2, h3, h5, h6⟩ := hab4
    exact Or.inr (Or.inr ⟨h1, h2, h5, h6, h3, hrab, hrcab⟩)

theorem hc5_U_classes'
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) {w : CVert}
    (hw : cgraph.Adj cv0 w) {a b : vStab cv0} (hae : (a : Shat) = clabelS cv0 * clabelS w)
    (hZPeq : hc5ZP u X = Subgroup.closure {a, b}) (haa : a * a = 1) (hbb : b * b = 1)
    (hab : a * b = b * a) (hrb : rkH b = 2048) (hrcb : rkH (cV0 * b) = 2168)
    (hrab : rkH (a * b) = 2048) (hrcab : rkH (cV0 * (a * b)) = 2168) :
    ∀ y ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆, y = 1 ∨ cV0 * y ∈ RA ∨
      (y * y = 1 ∧ y ∈ commutator (vStab cv0) ∧ y ∉ RA ∧ y ∉ RB ∧ y ≠ cV0 ∧
        rkH y = 2048 ∧ rkH (cV0 * y) = 2168) := by
  have h := hc5_U_classes hw hae hZPeq haa hbb hab hrb hrcb hrab hrcab
  intro y hy
  have hy' := (hc5_mem_U_iff hvu hβ hXβ hX).1 hy
  rw [hZPeq] at hy'
  exact h y hy'

theorem hc5_coset_U
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) {a b : vStab cv0}
    (hZPeq : hc5ZP u X = Subgroup.closure {a, b})
    (h : ∀ y ∈ Subgroup.closure ({a, b} : Set (vStab cv0)),
      ∃ w ∈ Subgroup.closure ({a, b} : Set (vStab cv0)), w ≠ y ∧
        IsConj (cV0 * β * y) (cV0 * β * w)) :
    ∀ y ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆,
      ∃ w ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆, w ≠ y ∧
        IsConj (cV0 * β * y) (cV0 * β * w) := by
  intro y hy
  have hy' := (hc5_mem_U_iff hvu hβ hXβ hX).1 hy
  rw [hZPeq] at hy'
  obtain ⟨w₀, hw₀, hne₀, hconj⟩ := h y hy'
  refine ⟨w₀, (hc5_mem_U_iff hvu hβ hXβ hX).2 ?_, hne₀, hconj⟩
  rw [hZPeq]
  exact hw₀

end Clauses

theorem exists_sylow_centralizer_beta
    {β : vStab cv0} (hβ : β ∈ FA) :
    ∃ X : Subgroup (vStab cv0), X ≤ Subgroup.centralizer {β} ∧ Nat.card X = 2 ^ 26 := by
  obtain ⟨u, hu, hβu⟩ := hβ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 (Subgroup.centralizer ({β} : Set (vStab cv0))) := default
  refine ⟨(S : Subgroup _).map (Subgroup.centralizer {β}).subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective (Subgroup.centralizer {β}).subtype_injective,
    Sylow.card_eq_multiplicity, natCard_centralizer_beta (mem_sphereDistThree.1 hu) hβu,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem native_HC5_sylow_beta
    {β : vStab cv0} (hβ : β ∈ FA) {X : Subgroup (vStab cv0)}
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    Nat.card (Subgroup.centralizer ({β} : Set (vStab cv0))) = 2 ^ 26 * 197358525 ∧
    ∃ a b : vStab cv0,
      X ⊓ Subgroup.centralizer X ⊓ ⁅X, X⁆ = Subgroup.closure {a, b} ∧
      X ⊓ Subgroup.centralizer X = Subgroup.closure {cV0, β} ⊔ Subgroup.closure {a, b} ∧
      Subgroup.closure {cV0, β} ⊓ Subgroup.closure {a, b} = ⊥ ∧
      Nat.card (Subgroup.closure ({a, b} : Set (vStab cv0))) = 4 ∧
      a ∈ RB ∧ cV0 * a ∈ RA ∧
      (∀ y ∈ ({b, a * b, cV0 * b, cV0 * (a * b)} : Set (vStab cv0)),
        y * y = 1 ∧ y ∈ commutator (vStab cv0) ∧ y ≠ cV0 ∧ y ∉ RA ∧ y ∉ RB) ∧
      rkH b = 2048 ∧ rkH (cV0 * b) = 2168 ∧ rkH (a * b) = 2048 ∧
      rkH (cV0 * (a * b)) = 2168 ∧ β * b ∈ FA ∧ cV0 * (β * b) ∈ FB ∧
      (∀ y ∈ Subgroup.closure ({a, b} : Set (vStab cv0)),
        ∃ w ∈ Subgroup.closure ({a, b} : Set (vStab cv0)), w ≠ y ∧ IsConj (β * y) (β * w)) ∧
      ∀ y ∈ Subgroup.closure ({a, b} : Set (vStab cv0)),
        ∃ w ∈ Subgroup.closure ({a, b} : Set (vStab cv0)), w ≠ y ∧
          IsConj (cV0 * β * y) (cV0 * β * w) := by
  obtain ⟨u, hu, hβu⟩ := hβ
  have hvu : cgraph.dist cv0 u = 3 := mem_sphereDistThree.1 hu
  have hd := hc5_data hvu hβu hXβ hX
  obtain ⟨w, w', a, b, hw, -, hdw', hcw, hww, hae, hbe, hZPeq, haa, hbb, hab, ha1, hb1, hne,
    -, -, hrb, hrcb, hrab, hrcab⟩ := hd
  have hβbFA := hc5_beta_b hβu hdw' hbe
  have hcoset := hc5_coset hvu hβu hu hw hcw hdw' hww hae hbe haa hbb hab hb1 hβbFA
  have hca := hc5_cV0_mul_a hw hae
  refine ⟨natCard_centralizer_beta hvu hβu, a, b, hc5_U_eq hvu hβu hXβ hX hZPeq,
    hc5_center_eq hvu hβu hXβ hX hZPeq, hc5_inf_eq_bot hvu hβu hZPeq,
    natCard_closure_pair haa hbb hab ha1 hb1 hne, show cV0 * a ∈ RA from hca, hca,
    hc5_four_facts hZPeq haa hbb hab hrb hrcb hrab hrcab, hrb, hrcb, hrab, hrcab, hβbFA, ?_,
    hcoset, hc5_coset_c hcoset⟩
  show cV0 * (cV0 * (β * b)) ∈ FA
  rw [cV0_mul_cV0_mul]
  exact hβbFA

theorem native_HC5_extremal_data
    {β : vStab cv0} (hβ : β ∈ FA) {X : Subgroup (vStab cv0)}
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    β ^ 2 = 1 ∧ β ∉ commutator (vStab cv0) ∧
    (∃ T : Sylow 2 (vStab cv0), X ≤ (T : Subgroup (vStab cv0))) ∧
    cV0 ∈ X ∧ β ∈ X ∧ Odd (X.relIndex (Subgroup.centralizer {β})) ∧
    (∀ z ∈ X, (∀ y ∈ X, z * y = y * z) →
      z ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ ∨
      cV0⁻¹ * z ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ ∨
      β⁻¹ * z ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ ∨
      (cV0 * β)⁻¹ * z ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆) ∧
    cV0 ∉ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ ∧
    β⁻¹ * cV0 ∉ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ ∧
    (∀ u ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆,
      ∃ u' ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆, u' ≠ u ∧
        IsConj (cV0 * β * u) (cV0 * β * u')) ∧
    ∀ u ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆, u = 1 ∨ cV0 * u ∈ RA ∨
      (u * u = 1 ∧ u ∈ commutator (vStab cv0) ∧ u ∉ RA ∧ u ∉ RB ∧ u ≠ cV0 ∧
        rkH u = 2048 ∧ rkH (cV0 * u) = 2168) := by
  obtain ⟨u, hu, hβu⟩ := hβ
  have hvu : cgraph.dist cv0 u = 3 := mem_sphereDistThree.1 hu
  have hd := hc5_data hvu hβu hXβ hX
  obtain ⟨w, w', a, b, hw, -, hdw', hcw, hww, hae, hbe, hZPeq, haa, hbb, hab, -, hb1, -,
    -, -, hrb, hrcb, hrab, hrcab⟩ := hd
  have hcoset := hc5_coset_c (hc5_coset hvu hβu hu hw hcw hdw' hww hae hbe haa hbb hab hb1
    (hc5_beta_b hβu hdw' hbe))
  have hnot := hc5_not_mem_U hvu hβu hXβ hX
  exact ⟨by rw [sq]; exact beta_mul_self hβu, beta_not_mem_commutator hvu hβu,
    IsPGroup.exists_le_sylow (IsPGroup.of_card hX), cV0_mem_X hvu hβu hXβ hX,
    beta_mem_X hvu hβu hXβ hX, odd_relIndex_centralizer hvu hβu hXβ hX,
    hc5_center_cover hvu hβu hXβ hX, hnot.1, hnot.2, hc5_coset_U hvu hβu hXβ hX hZPeq hcoset,
    hc5_U_classes' hvu hβu hXβ hX hw hae hZPeq haa hbb hab hrb hrcb hrab hrcab⟩

end CFSG.Monster.B.GSide
