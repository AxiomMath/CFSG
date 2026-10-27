module

public import CFSG.Monster.B.GSide.HClasses
public import CFSG.Monster.B.GSide.NativeCompletion
public import CFSG.Monster.B.TwoA.Amalgam.NativeChainFinal
public import CFSG.Monster.B.TwoA.Amalgam.GlobalTypeRemain
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.B.TwoA.Unitary.Stab891
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
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
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
open CFSG.Sporadic.Co2Inv (co2_involution_input)

@[expose] def triVert
    (j : Fin 2) : Fin 3 → CVert := ![cv0, cw0, cu j]

abbrev triStab
    (j : Fin 2) : Subgroup Shat := cvSetStab {cv0, cw0, cu j}

abbrev triKer
    (j : Fin 2) : Subgroup Shat := vStab cv0 ⊓ vStab cw0 ⊓ vStab (cu j)

@[expose] def IsTriA
    (j : Fin 2) (a : Shat) : Prop :=
  cvMul cv0 a = cv0 ∧ cvMul cw0 a = cu j ∧ cvMul (cu j) a = cw0

@[expose] def IsTriB
    (j : Fin 2) (b : Shat) : Prop :=
  cvMul cv0 b = cw0 ∧ cvMul cw0 b = cv0 ∧ cvMul (cu j) b = cu j

theorem isCTriangle_cu
    (j : Fin 2) : IsCTriangle cv0 cw0 (cu j) :=
  ⟨cgraph_adj_cv0_cw0, (cgraph_adj_cu j).1, (cgraph_adj_cu j).2⟩

theorem cv0_ne_cw0 :
    cv0 ≠ cw0 := cgraph_adj_cv0_cw0.ne

theorem cv0_ne_cu
    (j : Fin 2) : cv0 ≠ cu j := (cgraph_adj_cu j).1.ne

theorem cw0_ne_cu
    (j : Fin 2) : cw0 ≠ cu j := (cgraph_adj_cu j).2.ne

theorem triVert_zero
    (j : Fin 2) : triVert j 0 = cv0 := rfl

theorem triVert_one
    (j : Fin 2) : triVert j 1 = cw0 := rfl

theorem triVert_two
    (j : Fin 2) : triVert j 2 = cu j := rfl

theorem triVert_injective
    (j : Fin 2) : Function.Injective (triVert j) := by
  intro i k hik
  have h01 := cv0_ne_cw0
  have h02 := cv0_ne_cu j
  have h12 := cw0_ne_cu j
  fin_cases i <;> fin_cases k <;> first
    | rfl
    | exact absurd hik h01 | exact absurd hik h01.symm
    | exact absurd hik h02 | exact absurd hik h02.symm
    | exact absurd hik h12 | exact absurd hik h12.symm

theorem mem_triangle_iff
    {j : Fin 2} {x : CVert} :
    x ∈ ({cv0, cw0, cu j} : Set CVert) ↔ ∃ i, triVert j i = x := by
  constructor
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

theorem exists_triVert_cvMul
    {j : Fin 2} {s : Shat} (hs : s ∈ triStab j) (i : Fin 3) :
    ∃ k, cvMul (triVert j i) s = triVert j k :=
  let ⟨k, hk⟩ := mem_triangle_iff.1 ((mem_cvSetStab.1 hs (triVert j i)).2
    (mem_triangle_iff.2 ⟨i, rfl⟩))
  ⟨k, hk.symm⟩

theorem triKer_le_triStab
    (j : Fin 2) : triKer j ≤ triStab j := fun s hs =>
  mem_cvSetStab_triple ⟨by rw [mem_vStab.1 hs.1.1]; exact Set.mem_insert _ _,
    by rw [mem_vStab.1 hs.1.2]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _),
    by rw [mem_vStab.1 hs.2]; exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)⟩
    fun y hy => ⟨y, hy, by
      rcases hy with rfl | rfl | rfl
      exacts [mem_vStab.1 hs.1.1, mem_vStab.1 hs.1.2, mem_vStab.1 hs.2]⟩

theorem mem_triKer_iff
    {j : Fin 2} {s : Shat} :
    s ∈ triKer j ↔ ∀ i, cvMul (triVert j i) s = triVert j i := by
  constructor
  · intro hs i
    fin_cases i
    exacts [mem_vStab.1 hs.1.1, mem_vStab.1 hs.1.2, mem_vStab.1 hs.2]
  · intro h
    exact ⟨⟨mem_vStab.2 (h 0), mem_vStab.2 (h 1)⟩, mem_vStab.2 (h 2)⟩

@[expose] def triPermFun
    (j : Fin 2) (s : triStab j) (i : Fin 3) : Fin 3 :=
  Classical.choose (exists_triVert_cvMul ((triStab j).inv_mem s.2) i)

theorem triPermFun_spec
    (j : Fin 2) (s : triStab j) (i : Fin 3) :
    cvMul (triVert j i) (s : Shat)⁻¹ = triVert j (triPermFun j s i) :=
  Classical.choose_spec (exists_triVert_cvMul ((triStab j).inv_mem s.2) i)

theorem triPermFun_eq_iff
    {j : Fin 2} (s : triStab j) (i k : Fin 3) :
    triPermFun j s i = k ↔ cvMul (triVert j i) (s : Shat)⁻¹ = triVert j k := by
  rw [triPermFun_spec]
  exact (triVert_injective j).eq_iff.symm

theorem triPermFun_one
    (j : Fin 2) (i : Fin 3) : triPermFun j 1 i = i := by
  rw [triPermFun_eq_iff]
  show cvMul (triVert j i) (1 : Shat)⁻¹ = triVert j i
  rw [inv_one, cvMul_one]

theorem triPermFun_mul
    (j : Fin 2) (s t : triStab j) (i : Fin 3) :
    triPermFun j (s * t) i = triPermFun j s (triPermFun j t i) := by
  rw [triPermFun_eq_iff]
  show cvMul (triVert j i) ((s : Shat) * t)⁻¹ = _
  rw [mul_inv_rev, cvMul_mul, triPermFun_spec, triPermFun_spec]

@[expose] def triPerm
    (j : Fin 2) : triStab j →* Equiv.Perm (Fin 3) where
  toFun s :=
    { toFun := triPermFun j s
      invFun := triPermFun j s⁻¹
      left_inv := fun i => by
        rw [← triPermFun_mul, inv_mul_cancel, triPermFun_one]
      right_inv := fun i => by
        rw [← triPermFun_mul, mul_inv_cancel, triPermFun_one] }
  map_one' := Equiv.ext fun i => triPermFun_one j i
  map_mul' s t := Equiv.ext fun i => triPermFun_mul j s t i

theorem triPerm_apply
    (j : Fin 2) (s : triStab j) (i : Fin 3) :
    triPerm j s i = triPermFun j s i := rfl

theorem triPerm_apply_eq_iff
    {j : Fin 2} (s : triStab j) (i k : Fin 3) :
    triPerm j s i = k ↔ cvMul (triVert j i) (s : Shat)⁻¹ = triVert j k :=
  triPermFun_eq_iff s i k

theorem ker_triPerm
    (j : Fin 2) : (triPerm j).ker = (triKer j).subgroupOf (triStab j) := by
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_triKer_iff, Equiv.ext_iff]
  refine forall_congr' fun i => ?_
  rw [Equiv.Perm.coe_one, id, triPerm_apply_eq_iff]
  constructor
  · intro h
    have h' := congrArg (fun x => cvMul x (s : Shat)) h
    simp only [cvMul_inv_cancel'] at h'
    exact h'.symm
  · intro h
    have h' := congrArg (fun x => cvMul x (s : Shat)⁻¹) h
    simp only [cvMul_inv_cancel] at h'
    exact h'.symm

theorem mem_triStab_of_isTriA
    {j : Fin 2} {a : Shat} (ha : IsTriA j a) : a ∈ triStab j := by
  obtain ⟨h0, h1, h2⟩ := ha
  refine mem_cvSetStab_triple ⟨?_, ?_, ?_⟩ ?_
  · rw [h0]; exact Set.mem_insert _ _
  · rw [h1]; exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  · rw [h2]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · rintro y (rfl | rfl | rfl)
    · exact ⟨cv0, Set.mem_insert _ _, h0⟩
    · exact ⟨cu j, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), h2⟩
    · exact ⟨cw0, Set.mem_insert_of_mem _ (Set.mem_insert _ _), h1⟩

theorem mem_triStab_of_isTriB
    {j : Fin 2} {b : Shat} (hb : IsTriB j b) : b ∈ triStab j := by
  obtain ⟨h0, h1, h2⟩ := hb
  refine mem_cvSetStab_triple ⟨?_, ?_, ?_⟩ ?_
  · rw [h0]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · rw [h1]; exact Set.mem_insert _ _
  · rw [h2]; exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  · rintro y (rfl | rfl | rfl)
    · exact ⟨cw0, Set.mem_insert_of_mem _ (Set.mem_insert _ _), h1⟩
    · exact ⟨cv0, Set.mem_insert _ _, h0⟩
    · exact ⟨cu j, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), h2⟩

theorem exists_isTriA
    (j : Fin 2) : ∃ a, IsTriA j a := by
  obtain ⟨a, h1, h2, h0⟩ := exists_swap_of_isCTriangle
    ⟨(cgraph_adj_cu j).2, cgraph_adj_cv0_cw0.symm, (cgraph_adj_cu j).1.symm⟩
  exact ⟨a, h0, h1, h2⟩

theorem exists_isTriB
    (j : Fin 2) : ∃ b, IsTriB j b :=
  exists_swap_of_isCTriangle (isCTriangle_cu j)

theorem triPerm_isTriA
    {j : Fin 2} {a : Shat} (ha : IsTriA j a) :
    triPerm j ⟨a, mem_triStab_of_isTriA ha⟩ = Equiv.swap 1 2 := by
  obtain ⟨h0, h1, h2⟩ := ha
  refine Equiv.ext fun i => (triPerm_apply_eq_iff _ i _).2 ?_
  have e0 : cvMul cv0 a⁻¹ = cv0 := cvMul_inv_eq_of_cvMul_eq h0
  have e1 : cvMul (cu j) a⁻¹ = cw0 := by rw [← h1, cvMul_inv_cancel]
  have e2 : cvMul cw0 a⁻¹ = cu j := by rw [← h2, cvMul_inv_cancel]
  fin_cases i
  · exact e0
  · exact e2
  · exact e1

theorem triPerm_isTriB
    {j : Fin 2} {b : Shat} (hb : IsTriB j b) :
    triPerm j ⟨b, mem_triStab_of_isTriB hb⟩ = Equiv.swap 0 1 := by
  obtain ⟨h0, h1, h2⟩ := hb
  refine Equiv.ext fun i => (triPerm_apply_eq_iff _ i _).2 ?_
  have e0 : cvMul cw0 b⁻¹ = cv0 := by rw [← h0, cvMul_inv_cancel]
  have e1 : cvMul cv0 b⁻¹ = cw0 := by rw [← h1, cvMul_inv_cancel]
  have e2 : cvMul (cu j) b⁻¹ = cu j := cvMul_inv_eq_of_cvMul_eq h2
  fin_cases i
  · exact e1
  · exact e0
  · exact e2

theorem perm_fin_three_cases (σ : Equiv.Perm (Fin 3)) :
    σ = 1 ∨ σ = Equiv.swap 1 2 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 1 2 * Equiv.swap 0 1 ∨
      σ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨
      σ = Equiv.swap 1 2 * Equiv.swap 0 1 * Equiv.swap 1 2 := by
  revert σ
  decide

theorem triPerm_surjective
    (j : Fin 2) : Function.Surjective (triPerm j) := by
  obtain ⟨a, ha⟩ := exists_isTriA j
  obtain ⟨b, hb⟩ := exists_isTriB j
  let A : triStab j := ⟨a, mem_triStab_of_isTriA ha⟩
  let B : triStab j := ⟨b, mem_triStab_of_isTriB hb⟩
  have hA : triPerm j A = Equiv.swap 1 2 := triPerm_isTriA ha
  have hB : triPerm j B = Equiv.swap 0 1 := triPerm_isTriB hb
  intro σ
  rcases perm_fin_three_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨A, hA⟩
  · exact ⟨B, hB⟩
  · exact ⟨A * B, by rw [map_mul, hA, hB]⟩
  · exact ⟨B * A, by rw [map_mul, hA, hB]⟩
  · exact ⟨A * B * A, by rw [map_mul, map_mul, hA, hB]⟩

instance triKer_normal
    (j : Fin 2) : ((triKer j).subgroupOf (triStab j)).Normal := by
  rw [← ker_triPerm]
  exact MonoidHom.normal_ker _

@[expose] def triQuotEquiv
    (j : Fin 2) :
    triStab j ⧸ (triKer j).subgroupOf (triStab j) ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_triPerm j).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (triPerm_surjective j))

theorem mem_triKer_of_triPerm_eq_one
    {j : Fin 2} {s : triStab j} (h : triPerm j s = 1) :
    (s : Shat) ∈ triKer j := by
  have hs : s ∈ (triPerm j).ker := h
  rw [ker_triPerm, Subgroup.mem_subgroupOf] at hs
  exact hs

theorem triPerm_eq_one_of_mem_triKer
    {j : Fin 2} {s : triStab j} (h : (s : Shat) ∈ triKer j) :
    triPerm j s = 1 := by
  have hs : s ∈ (triKer j).subgroupOf (triStab j) := h
  rw [← ker_triPerm] at hs
  exact hs

theorem mem_vStab_iff_triPerm
    {j : Fin 2} (s : triStab j) :
    (s : Shat) ∈ vStab cv0 ↔ triPerm j s 0 = 0 := by
  rw [triPerm_apply_eq_iff, mem_vStab]
  constructor
  · exact cvMul_inv_eq_of_cvMul_eq
  · intro h
    have h' := cvMul_inv_eq_of_cvMul_eq h
    rwa [inv_inv] at h'

theorem triPerm_two_of_mem_cEdgeStab
    {j : Fin 2} (s : triStab j)
    (hs : (s : Shat) ∈ cvSetStab {cv0, cw0}) : triPerm j s 2 = 2 := by
  have hs' := (cvSetStab {cv0, cw0}).inv_mem hs
  obtain ⟨k, hk⟩ := exists_triVert_cvMul ((triStab j).inv_mem s.2) 2
  rw [triPerm_apply_eq_iff]
  refine hk.trans ?_
  rw [triVert_two] at hk
  fin_cases k
  · exfalso
    have h := (mem_cvSetStab.1 hs' (cu j)).1 (by rw [hk]; exact Set.mem_insert _ _)
    rcases h with h | h
    · exact cv0_ne_cu j h.symm
    · exact cw0_ne_cu j h.symm
  · exfalso
    have h := (mem_cvSetStab.1 hs' (cu j)).1 (by rw [hk]; exact Set.mem_insert_of_mem _ rfl)
    rcases h with h | h
    · exact cv0_ne_cu j h.symm
    · exact cw0_ne_cu j h.symm
  · rfl

theorem perm_fin_three_fix_zero :
    ∀ σ : Equiv.Perm (Fin 3), σ 0 = 0 → σ = 1 ∨ σ = Equiv.swap 1 2 := by
  decide

theorem perm_fin_three_fix_two :
    ∀ σ : Equiv.Perm (Fin 3), σ 2 = 2 → σ = 1 ∨ σ = Equiv.swap 0 1 := by
  decide

theorem perm_fin_three_fix_zero_two :
    ∀ σ : Equiv.Perm (Fin 3), σ 0 = 0 → σ 2 = 2 → σ = 1 := by
  decide

theorem triStab_inf_vStab
    {j : Fin 2} {a : Shat} (ha : IsTriA j a) :
    triStab j ⊓ vStab cv0 = triKer j ⊔ Subgroup.zpowers a := by
  apply le_antisymm
  · rintro s ⟨hsT, hsv⟩
    let S : triStab j := ⟨s, hsT⟩
    let A : triStab j := ⟨a, mem_triStab_of_isTriA ha⟩
    rcases perm_fin_three_fix_zero (triPerm j S) ((mem_vStab_iff_triPerm S).1 hsv) with h | h
    · exact Subgroup.mem_sup_left (mem_triKer_of_triPerm_eq_one h)
    · have h1 : triPerm j (S * A⁻¹) = 1 := by
        rw [map_mul, map_inv, h, triPerm_isTriA ha, mul_inv_cancel]
      have h2 := mem_triKer_of_triPerm_eq_one h1
      have e : s = (s * a⁻¹) * a := by group
      rw [e]
      exact Subgroup.mul_mem_sup h2 (Subgroup.mem_zpowers a)
  · refine sup_le (fun s hs => ⟨triKer_le_triStab j hs, hs.1.1⟩) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨mem_triStab_of_isTriA ha, mem_vStab.2 ha.1⟩

theorem triStab_inf_cEdgeStab
    {j : Fin 2} {b : Shat} (hb : IsTriB j b) :
    triStab j ⊓ cvSetStab {cv0, cw0} = triKer j ⊔ Subgroup.zpowers b := by
  apply le_antisymm
  · rintro s ⟨hsT, hse⟩
    let S : triStab j := ⟨s, hsT⟩
    let B : triStab j := ⟨b, mem_triStab_of_isTriB hb⟩
    rcases perm_fin_three_fix_two (triPerm j S) (triPerm_two_of_mem_cEdgeStab S hse) with h | h
    · exact Subgroup.mem_sup_left (mem_triKer_of_triPerm_eq_one h)
    · have h1 : triPerm j (S * B⁻¹) = 1 := by
        rw [map_mul, map_inv, h, triPerm_isTriB hb, mul_inv_cancel]
      have h2 := mem_triKer_of_triPerm_eq_one h1
      have e : s = (s * b⁻¹) * b := by group
      rw [e]
      exact Subgroup.mul_mem_sup h2 (Subgroup.mem_zpowers b)
  · refine sup_le (fun s hs => ⟨triKer_le_triStab j hs, cEdgeFix_le_cEdgeStab hs.1⟩) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨mem_triStab_of_isTriB hb,
      (mem_cvSetStab_pair cv0_ne_cw0).2 (Or.inr ⟨hb.1, hb.2.1⟩)⟩

theorem triStab_inf_vStab_inf_cEdgeStab
    (j : Fin 2) :
    triStab j ⊓ vStab cv0 ⊓ cvSetStab {cv0, cw0} = triKer j := by
  apply le_antisymm
  · rintro s ⟨⟨hsT, hsv⟩, hse⟩
    let S : triStab j := ⟨s, hsT⟩
    exact mem_triKer_of_triPerm_eq_one (perm_fin_three_fix_zero_two (triPerm j S)
      ((mem_vStab_iff_triPerm S).1 hsv) (triPerm_two_of_mem_cEdgeStab S hse))
  · intro s hs
    exact ⟨⟨triKer_le_triStab j hs, hs.1.1⟩, cEdgeFix_le_cEdgeStab hs.1⟩

theorem mul_self_mem_triKer_of_isTriA
    {j : Fin 2} {a : Shat} (ha : IsTriA j a) :
    a * a ∈ triKer j := by
  obtain ⟨h0, h1, h2⟩ := ha
  refine mem_triKer_iff.2 fun i => ?_
  fin_cases i
  · show cvMul cv0 (a * a) = cv0
    rw [cvMul_mul, h0, h0]
  · show cvMul cw0 (a * a) = cw0
    rw [cvMul_mul, h1, h2]
  · show cvMul (cu j) (a * a) = cu j
    rw [cvMul_mul, h2, h1]

theorem mul_self_mem_triKer_of_isTriB
    {j : Fin 2} {b : Shat} (hb : IsTriB j b) :
    b * b ∈ triKer j := by
  obtain ⟨h0, h1, h2⟩ := hb
  refine mem_triKer_iff.2 fun i => ?_
  fin_cases i
  · show cvMul cv0 (b * b) = cv0
    rw [cvMul_mul, h0, h1]
  · show cvMul cw0 (b * b) = cw0
    rw [cvMul_mul, h1, h0]
  · show cvMul (cu j) (b * b) = cu j
    rw [cvMul_mul, h2, h2]

theorem mul_pow_three_mem_triKer
    {j : Fin 2} {a b : Shat} (ha : IsTriA j a) (hb : IsTriB j b) :
    (a * b) ^ 3 ∈ triKer j := by
  obtain ⟨a0, a1, a2⟩ := ha
  obtain ⟨b0, b1, b2⟩ := hb
  have c0 : cvMul cv0 (a * b) = cw0 := by rw [cvMul_mul, a0, b0]
  have c1 : cvMul cw0 (a * b) = cu j := by rw [cvMul_mul, a1, b2]
  have c2 : cvMul (cu j) (a * b) = cv0 := by rw [cvMul_mul, a2, b1]
  refine mem_triKer_iff.2 fun i => ?_
  fin_cases i
  · show cvMul cv0 ((a * b) ^ 3) = cv0
    rw [pow_three, cvMul_mul, cvMul_mul, c0, c1, c2]
  · show cvMul cw0 ((a * b) ^ 3) = cw0
    rw [pow_three, cvMul_mul, cvMul_mul, c1, c2, c0]
  · show cvMul (cu j) ((a * b) ^ 3) = cu j
    rw [pow_three, cvMul_mul, cvMul_mul, c2, c0, c1]

theorem natCard_cEdgeFix :
    Nat.card cEdgeFix = 2 ^ 38 * 3 ^ 6 * 5 * 7 * 11 := by
  have h := natCard_subgroup_eq_mul (vStab cv0) cw0
  have horb : {x | ∃ s ∈ vStab cv0, cvMul cw0 s = x} = cgraph.neighborSet cv0 := by
    rw [← vStabOrbit_eq_neighborSet cgraph_adj_cv0_cw0]
    ext x
    exact ⟨fun ⟨s, hs, hx⟩ => ⟨s, hs, hx⟩, fun ⟨s, hs, hx⟩ => ⟨s, hs, hx⟩⟩
  rw [horb, ncard_neighborSet, natCard_vStab_eq] at h
  have e : Nat.card cEdgeFix = Nat.card ↥(vStab cv0 ⊓ vStab cw0) := rfl
  rw [e]
  omega

theorem natCard_triKer_mul
    (j : Fin 2) :
    Nat.card (triKer j) * triType cv0 cw0 (cu j) = Nat.card cEdgeFix := by
  have h := natCard_subgroup_eq_mul cEdgeFix (cu j)
  have horb : {x | ∃ s ∈ cEdgeFix, cvMul (cu j) s = x} = pairStabOrbit cv0 cw0 (cu j) := by
    ext x
    exact ⟨fun ⟨s, hs, hx⟩ => ⟨s, hs.1, hs.2, hx⟩, fun ⟨s, h1, h2, hx⟩ => ⟨s, ⟨h1, h2⟩, hx⟩⟩
  rw [horb] at h
  rw [h, mul_comm]

theorem natCard_triKer_zero :
    Nat.card (triKer 0) = 2 ^ 37 * 3 ^ 2 * 5 * 7 := by
  have h := natCard_triKer_mul 0
  rw [triType_cu.1, natCard_cEdgeFix] at h
  generalize Nat.card (triKer 0) = n at h ⊢
  omega

theorem natCard_triKer_one :
    Nat.card (triKer 1) = 2 ^ 32 * 3 ^ 4 * 5 := by
  have h := natCard_triKer_mul 1
  rw [triType_cu.2, natCard_cEdgeFix] at h
  generalize Nat.card (triKer 1) = n at h ⊢
  omega

theorem natCard_triStab
    (j : Fin 2) : Nat.card (triStab j) = 6 * Nat.card (triKer j) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((triKer j).subgroupOf (triStab j))
  have h2 : Nat.card (triStab j ⧸ (triKer j).subgroupOf (triStab j)) = 6 := by
    rw [Nat.card_congr (triQuotEquiv j).toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have h3 : Nat.card ((triKer j).subgroupOf (triStab j)) = Nat.card (triKer j) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (triKer_le_triStab j)).toEquiv
  rw [h1, h2, h3]

theorem clabelS_inv
    (v : CVert) : (clabelS v)⁻¹ = clabelS v :=
  inv_eq_of_mul_eq_one_right (clabelS_mul_self' v)

theorem commute_clabelS_iff
    (v : CVert) (s : Shat) :
    s * clabelS v = clabelS v * s ↔ cvMul v s = v := by
  rw [← commute_clabel_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem cvMul_clabelS_self
    (v : CVert) : cvMul v (clabelS v) = v :=
  (commute_clabelS_iff v _).1 rfl

theorem cvMul_clabelS_clabelS
    (w x : CVert) : cvMul (cvMul w (clabelS x)) (clabelS x) = w := by
  rw [← cvMul_mul, clabelS_mul_self', cvMul_one]

theorem clabelS_label_swap
    (w x : CVert) :
    clabelS (cvMul w (clabelS x)) = clabelS x * clabelS w * clabelS x := by
  rw [clabelS_cvMul, clabelS_inv]

theorem cvMul_label_swap_fix
    {w x : CVert} {s : Shat} (hw : cvMul w s = w)
    (hx : cvMul x s = x) : cvMul (cvMul w (clabelS x)) s = cvMul w (clabelS x) := by
  have hc : clabelS x * s = s * clabelS x := ((commute_clabelS_iff x s).2 hx).symm
  rw [← cvMul_mul, hc, cvMul_mul, hw]

theorem cvMul_clabelS_of_adj
    {v x : CVert} (h : cgraph.Adj v x) : cvMul v (clabelS x) = v :=
  (commute_clabelS_iff v _).1 (Subtype.ext (clabel_adj h).2.1.symm)

theorem cvMul_clabelS_of_dist_three
    {v y : CVert} (h : cgraph.dist v y = 3) :
    cvMul v (clabelS y) = v :=
  mem_vStab.1 (native_distance_three_labels_commute_and_fix_endpoints_final h).1

theorem mul_clabelS_mul_cancel
    (v : CVert) (t : Shat) : clabelS v * (clabelS v * t) = t := by
  rw [← mul_assoc, clabelS_mul_self', one_mul]

theorem pow_four_of_label_swap
    {w x : CVert} (hwu : cgraph.Adj w (cvMul w (clabelS x))) :
    (clabelS w * clabelS x) ^ 4 = 1 := by
  have hc : clabelS w * clabelS (cvMul w (clabelS x)) =
      clabelS (cvMul w (clabelS x)) * clabelS w := Subtype.ext (clabel_adj hwu).2.1
  rw [clabelS_label_swap] at hc
  have h2 : (clabelS w * clabelS x) ^ 2 = clabelS w * (clabelS x * clabelS w * clabelS x) := by
    rw [sq]
    group
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, sq]
  calc clabelS w * (clabelS x * clabelS w * clabelS x) *
        (clabelS w * (clabelS x * clabelS w * clabelS x))
      = clabelS w * ((clabelS x * clabelS w * clabelS x) * clabelS w) *
          (clabelS x * clabelS w * clabelS x) := by group
    _ = clabelS w * (clabelS w * (clabelS x * clabelS w * clabelS x)) *
          (clabelS x * clabelS w * clabelS x) := by rw [← hc]
    _ = 1 := by simp only [mul_assoc, mul_clabelS_mul_cancel, clabelS_mul_self']

theorem mem_sphereFour_of_label_swap
    {v w x : CVert} (hvw : cgraph.Adj v w)
    (hvx : cgraph.Adj v x) (hwu : cgraph.Adj w (cvMul w (clabelS x))) : x ∈ sphereFour w := by
  have hne : w ≠ x := by
    rintro rfl
    rw [cvMul_clabelS_self] at hwu
    exact cgraph.irrefl hwu
  have hna : ¬ cgraph.Adj w x := fun h => by
    rw [cvMul_clabelS_of_adj h] at hwu
    exact cgraph.irrefl hwu
  have hd : cgraph.dist w x = 2 := cgraph_dist_eq_two_iff.2 ⟨hne, hna, v, hvw.symm, hvx⟩
  have h4 : (clabel w * clabel x) ^ 4 = 1 := congrArg Subtype.val (pow_four_of_label_swap hwu)
  have hdvd : lblOrd w x ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  rcases labelThree_or_labelFour_of_dist exists_rootModel hd with h | h
  · exfalso
    rcases h.1 with h3 | h3 <;> rw [h3] at hdvd <;> norm_num at hdvd
  · exact ⟨hd, h.1⟩

theorem natCard_vStab_inf_of_adj
    {v w : CVert} (h : cgraph.Adj v w) :
    Nat.card ↥(vStab v ⊓ vStab w) = 2 ^ 38 * 3 ^ 6 * 5 * 7 * 11 := by
  have hc := natCard_subgroup_eq_mul (vStab v) w
  have horb : {x | ∃ s ∈ vStab v, cvMul w s = x} = cgraph.neighborSet v := by
    rw [← vStabOrbit_eq_neighborSet h]
    ext x
    exact ⟨fun ⟨s, hs, hx⟩ => ⟨s, hs, hx⟩, fun ⟨s, hs, hx⟩ => ⟨s, hs, hx⟩⟩
  rw [horb, ncard_neighborSet, natCard_vStab_eq] at hc
  generalize Nat.card ↥(vStab v ⊓ vStab w) = n at hc ⊢
  omega

theorem natCard_vStab_inf_inf_of_sphereFour
    {v w x : CVert} (hvw : cgraph.Adj v w)
    (hvx : cgraph.Adj v x) (hx : x ∈ sphereFour w) :
    Nat.card ↥(vStab v ⊓ vStab w ⊓ vStab x) = 2 ^ 27 * 3 ^ 2 * 5 * 7 := by
  obtain ⟨-, Ω, -, -, -, -, -, -, -, -, -, horb, hcard, -, hΩ0, -⟩ :=
    native_type_four_pair_eight_neighborhood_orbits w x hx
  have hv0 : v ∈ Ω 0 := by
    rw [hΩ0]
    exact ⟨hvw.symm, hvx.symm⟩
  have hc := natCard_subgroup_eq_mul (vStab w ⊓ vStab x) v
  have horb' : {y | ∃ s ∈ vStab w ⊓ vStab x, cvMul v s = y} = Ω 0 := horb 0 v hv0
  rw [horb', hcard 0, natCard_vStab_inf_of_sphereFour hx] at hc
  have e : vStab w ⊓ vStab x ⊓ vStab v = vStab v ⊓ vStab w ⊓ vStab x := by
    rw [inf_comm, inf_assoc]
  rw [e] at hc
  generalize Nat.card ↥(vStab v ⊓ vStab w ⊓ vStab x) = n at hc ⊢
  simp only [Matrix.cons_val_zero] at hc
  omega

theorem natCard_vStab_inf_inf_of_dist_three
    {v w y : CVert} (hvw : cgraph.Adj v w)
    (hy : cgraph.dist v y = 3) (hw : w ∈ sphereFour y) :
    Nat.card ↥(vStab v ⊓ vStab w ⊓ vStab y) = 3397386240 := by
  have hvy : v ∈ sphereDistThree y := by
    rw [mem_sphereDistThree, SimpleGraph.dist_comm]
    exact hy
  have h := ((distThreePaths_of_ambient ambientRootOrbitsHyp).2.2.2.1 y v hvy).2.2 w
    ⟨hvw, hw⟩
  have e : vStab y ⊓ vStab v ⊓ vStab w = vStab v ⊓ vStab w ⊓ vStab y := by
    rw [inf_comm (vStab y) (vStab v), inf_assoc, inf_comm (vStab y) (vStab w), ← inf_assoc]
  rwa [e] at h

theorem triType_mul_eq
    {v w u x : CVert} (hle : vStab v ⊓ vStab w ⊓ vStab x ≤
    vStab v ⊓ vStab w ⊓ vStab u) :
    ∃ m, Nat.card ↥(vStab v ⊓ vStab w) =
      triType v w u * (m * Nat.card ↥(vStab v ⊓ vStab w ⊓ vStab x)) := by
  have hc := natCard_subgroup_eq_mul (vStab v ⊓ vStab w) u
  have horb : {y | ∃ s ∈ vStab v ⊓ vStab w, cvMul u s = y} = pairStabOrbit v w u := by
    ext y
    exact ⟨fun ⟨s, hs, hy⟩ => ⟨s, hs.1, hs.2, hy⟩, fun ⟨s, h1, h2, hy⟩ => ⟨s, ⟨h1, h2⟩, hy⟩⟩
  rw [horb] at hc
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  exact ⟨m, by rw [hc, hm, mul_comm m]⟩

theorem le_of_label_swap
    (v w x : CVert) :
    vStab v ⊓ vStab w ⊓ vStab x ≤ vStab v ⊓ vStab w ⊓ vStab (cvMul w (clabelS x)) :=
  fun _ hs => ⟨hs.1, mem_vStab.2 (cvMul_label_swap_fix (mem_vStab.1 hs.1.2) (mem_vStab.1 hs.2))⟩

theorem triType_eq_1782_of_label_swap
    {v w x : CVert} (hvw : cgraph.Adj v w)
    (hvx : cgraph.Adj v x) (hwu : cgraph.Adj w (cvMul w (clabelS x))) :
    IsCTriangle v w (cvMul w (clabelS x)) ∧ triType v w (cvMul w (clabelS x)) = 1782 := by
  have hvu : cgraph.Adj v (cvMul w (clabelS x)) := by
    have h := (cgraph_adj_cvMul v w (clabelS x)).2 hvw
    rwa [cvMul_clabelS_of_adj hvx] at h
  have hT : IsCTriangle v w (cvMul w (clabelS x)) := ⟨hvw, hvu, hwu⟩
  refine ⟨hT, ?_⟩
  obtain ⟨M, -⟩ := exists_rootModel v
  obtain ⟨m, hm⟩ := triType_mul_eq (le_of_label_swap v w x)
  rw [natCard_vStab_inf_of_adj hvw, natCard_vStab_inf_inf_of_sphereFour hvw hvx
    (mem_sphereFour_of_label_swap hvw hvx hwu)] at hm
  rcases triType_eq_or M hT with h | h
  · exact h
  · exfalso
    rw [h] at hm
    omega

theorem triType_eq_44352_of_label_swap
    {v w y : CVert} (hvw : cgraph.Adj v w)
    (hy : cgraph.dist v y = 3) (hwu : cgraph.Adj w (cvMul w (clabelS y))) :
    IsCTriangle v w (cvMul w (clabelS y)) ∧ triType v w (cvMul w (clabelS y)) = 44352 := by
  have hvu : cgraph.Adj v (cvMul w (clabelS y)) := by
    have h := (cgraph_adj_cvMul v w (clabelS y)).2 hvw
    rwa [cvMul_clabelS_of_dist_three hy] at h
  have hT : IsCTriangle v w (cvMul w (clabelS y)) := ⟨hvw, hvu, hwu⟩
  refine ⟨hT, ?_⟩
  have hwy : w ∈ sphereFour y := by
    have hle : cgraph.dist y w ≤ 3 := native_coset_graph_diameter_three_rank_five.2.1 y w
    have hge : 2 ≤ cgraph.dist y w := by
      have h := cgraph_connected.dist_triangle (u := y) (v := w) (w := v)
      rw [SimpleGraph.dist_comm (u := y), hy, SimpleGraph.dist_comm (u := w),
        SimpleGraph.dist_eq_one_iff_adj.2 hvw] at h
      omega
    have hne3 : cgraph.dist y w ≠ 3 := fun h3 => by
      rw [cvMul_clabelS_of_dist_three (by rwa [SimpleGraph.dist_comm] at h3)] at hwu
      exact cgraph.irrefl hwu
    have hd : cgraph.dist y w = 2 := by omega
    have h4 : (clabel w * clabel y) ^ 4 = 1 := congrArg Subtype.val (pow_four_of_label_swap hwu)
    have h4' : (clabel y * clabel w) ^ 4 = 1 := by
      have e : clabel y * clabel w = (clabel y) * (clabel w * clabel y) * (clabel y)⁻¹ := by
        have hy2 : clabel y * clabel y = 1 := congrArg Subtype.val (clabelS_mul_self' y)
        rw [← mul_assoc, mul_assoc, inv_eq_of_mul_eq_one_right hy2, hy2, mul_one]
      rw [e, conj_pow, h4, mul_one, mul_inv_cancel]
    have hdvd : lblOrd y w ∣ 4 := orderOf_dvd_of_pow_eq_one h4'
    rcases labelThree_or_labelFour_of_dist exists_rootModel hd with h | h
    · exfalso
      rcases h.1 with h3 | h3 <;> rw [h3] at hdvd <;> norm_num at hdvd
    · exact ⟨hd, h.1⟩
  obtain ⟨M, -⟩ := exists_rootModel v
  obtain ⟨m, hm⟩ := triType_mul_eq (le_of_label_swap v w y)
  rw [natCard_vStab_inf_of_adj hvw, natCard_vStab_inf_inf_of_dist_three hvw hy hwy] at hm
  rcases triType_eq_or M hT with h | h
  · exfalso
    rw [h] at hm
    omega
  · exact h

theorem adj_label_swap_of_orderOf
    {v w z : CVert} (hvw : cgraph.Adj v w)
    (hz : cvMul v (clabelS z) = v) (hord : orderOf (clabel w * clabel z) = 4) :
    cgraph.Adj w (cvMul w (clabelS z)) := by
  set u := cvMul w (clabelS z) with hu
  have hvu : cgraph.Adj v u := by
    have h := (cgraph_adj_cvMul v w (clabelS z)).2 hvw
    rwa [hz] at h
  have hlu : clabel u = clabel z * clabel w * clabel z := congrArg Subtype.val
    (clabelS_label_swap w z)
  have hsq : clabel w * clabel u = (clabel w * clabel z) ^ 2 := by
    rw [hlu, sq]
    group
  have h2 : (clabel w * clabel u) ^ 2 = 1 := by
    rw [hsq, ← pow_mul, show 2 * 2 = 4 from rfl, ← hord, pow_orderOf_eq_one]
  have h1 : clabel w * clabel u ≠ 1 := by
    rw [hsq]
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num)
  have hord2 : lblOrd w u = 2 := orderOf_eq_prime h2 h1
  have hne : w ≠ u := fun e => h1 (by
    rw [← e]
    exact congrArg Subtype.val (clabelS_mul_self' w))
  by_contra hna
  have hd : cgraph.dist w u = 2 := cgraph_dist_eq_two_iff.2 ⟨hne, hna, v, hvw.symm, hvu⟩
  rcases labelThree_or_labelFour_of_dist exists_rootModel hd with h | h
  · rcases h.1 with h3 | h3 <;> rw [hord2] at h3 <;> norm_num at h3
  · rcases h.1 with h4 | h4 <;> rw [hord2] at h4 <;> norm_num at h4

theorem label_swap_cvMul
    {w x : CVert} {t : Shat} (htw : cvMul w t = w) :
    cvMul w (clabelS (cvMul x t)) = cvMul (cvMul w (clabelS x)) t := by
  rw [clabelS_cvMul, cvMul_mul, cvMul_mul, cvMul_inv_eq_of_cvMul_eq htw]

theorem exists_label_swap_of_triType_1782
    {v w u : CVert} (h : IsCTriangle v w u)
    (ht : triType v w u = 1782) :
    ∃ x, cgraph.Adj v x ∧ cvMul w (clabelS x) = u ∧ cvMul u (clabelS x) = w := by
  have hcard := natCard_adj_sphereFour exists_rootModel h.1.symm
  obtain ⟨⟨x₀, hvx₀, hx₀⟩⟩ : Nonempty {x // cgraph.Adj v x ∧ x ∈ sphereFour w} :=
    Nat.card_pos_iff.1 (by rw [hcard]; norm_num) |>.1
  have hwu₀ := adj_label_swap_of_orderOf h.1 (cvMul_clabelS_of_adj hvx₀)
    (native_coset_graph_order_four_common_neighbors.1 w x₀ hx₀).1
  obtain ⟨hT₀, ht₀⟩ := triType_eq_1782_of_label_swap h.1 hvx₀ hwu₀
  obtain ⟨t, htv, htw, htu⟩ := exists_cvMul_eq_of_triType_eq h.1 hT₀.2.1 h.2.1 (ht₀.trans ht.symm)
  refine ⟨cvMul x₀ t, ?_, ?_, ?_⟩
  · have h' := (cgraph_adj_cvMul v x₀ t).2 hvx₀
    rwa [htv] at h'
  · rw [label_swap_cvMul htw, htu]
  · rw [← (show cvMul w (clabelS (cvMul x₀ t)) = u by rw [label_swap_cvMul htw, htu]),
      cvMul_clabelS_clabelS]

theorem exists_label_swap_of_triType_44352
    {v w u : CVert} (h : IsCTriangle v w u)
    (ht : triType v w u = 44352) :
    ∃ y, cgraph.dist v y = 3 ∧ cvMul w (clabelS y) = u ∧ cvMul u (clabelS y) = w := by
  obtain ⟨y₁, hy₁⟩ := native_coset_graph_diameter_three_rank_five.2.2.1 v
  have hvy₁ : v ∈ sphereDistThree y₁ := by
    rw [mem_sphereDistThree, SimpleGraph.dist_comm]
    exact hy₁
  obtain ⟨w₁, hw₁⟩ := ((distThreePaths_of_ambient ambientRootOrbitsHyp).2.2.2.1 y₁ v hvy₁).1
  have hw : w ∈ vStabOrbit v w₁ := by
    rw [vStabOrbit_eq_neighborSet hw₁.1]
    exact h.1
  obtain ⟨s, hsv, hsw⟩ := hw
  have hy₀ : cgraph.dist v (cvMul y₁ s) = 3 := by
    rw [← hsv, dist_cvMul]
    exact hy₁
  have hwy₀ : w ∈ sphereFour (cvMul y₁ s) := by
    rw [← hsw]
    exact sphereFour_cvMul hw₁.2 s
  have hord : orderOf (clabel w * clabel (cvMul y₁ s)) = 4 := by
    rw [orderOf_mul_comm']
    exact (native_coset_graph_order_four_common_neighbors.1 _ w hwy₀).1
  have hwu₀ := adj_label_swap_of_orderOf h.1 (cvMul_clabelS_of_dist_three hy₀) hord
  obtain ⟨hT₀, ht₀⟩ := triType_eq_44352_of_label_swap h.1 hy₀ hwu₀
  obtain ⟨t, htv, htw, htu⟩ := exists_cvMul_eq_of_triType_eq h.1 hT₀.2.1 h.2.1 (ht₀.trans ht.symm)
  refine ⟨cvMul (cvMul y₁ s) t, ?_, ?_, ?_⟩
  · rw [← htv, dist_cvMul]
    exact hy₀
  · rw [label_swap_cvMul htw, htu]
  · rw [← (show cvMul w (clabelS (cvMul (cvMul y₁ s) t)) = u by rw [label_swap_cvMul htw, htu]),
      cvMul_clabelS_clabelS]

theorem exists_isTriA_adj :
    ∃ x, cgraph.Adj cv0 x ∧ IsTriA 0 (clabelS x) := by
  obtain ⟨x, hx, h1, h2⟩ := exists_label_swap_of_triType_1782 (isCTriangle_cu 0) triType_cu.1
  exact ⟨x, hx, cvMul_clabelS_of_adj hx, h1, h2⟩

theorem exists_isTriB_adj :
    ∃ x, cgraph.Adj (cu 0) x ∧ IsTriB 0 (clabelS x) := by
  have hT : IsCTriangle (cu 0) cv0 cw0 :=
    ⟨(cgraph_adj_cu 0).1.symm, (cgraph_adj_cu 0).2.symm, cgraph_adj_cv0_cw0⟩
  have ht : triType (cu 0) cv0 cw0 = 1782 :=
    (triType_perm (isCTriangle_cu 0)).2.2.2.1.trans triType_cu.1
  obtain ⟨x, hx, h1, h2⟩ := exists_label_swap_of_triType_1782 hT ht
  exact ⟨x, hx, h1, h2, cvMul_clabelS_of_adj hx⟩

theorem not_isTriA_adj
    {x : CVert} (hx : cgraph.Adj cv0 x) : ¬ IsTriA 1 (clabelS x) := by
  rintro ⟨-, h1, -⟩
  have hwu : cgraph.Adj cw0 (cvMul cw0 (clabelS x)) := by
    rw [h1]
    exact (cgraph_adj_cu 1).2
  have h := (triType_eq_1782_of_label_swap cgraph_adj_cv0_cw0 hx hwu).2
  rw [h1, triType_cu.2] at h
  norm_num at h

theorem exists_isTriA_dist_three :
    ∃ y, cgraph.dist cv0 y = 3 ∧ IsTriA 1 (clabelS y) := by
  obtain ⟨y, hy, h1, h2⟩ := exists_label_swap_of_triType_44352 (isCTriangle_cu 1) triType_cu.2
  exact ⟨y, hy, cvMul_clabelS_of_dist_three hy, h1, h2⟩

theorem exists_isTriB_dist_three :
    ∃ y, cgraph.dist (cu 1) y = 3 ∧ IsTriB 1 (clabelS y) := by
  have hT : IsCTriangle (cu 1) cv0 cw0 :=
    ⟨(cgraph_adj_cu 1).1.symm, (cgraph_adj_cu 1).2.symm, cgraph_adj_cv0_cw0⟩
  have ht : triType (cu 1) cv0 cw0 = 44352 :=
    (triType_perm (isCTriangle_cu 1)).2.2.2.1.trans triType_cu.2
  obtain ⟨y, hy, h1, h2⟩ := exists_label_swap_of_triType_44352 hT ht
  exact ⟨y, hy, h1, h2, cvMul_clabelS_of_dist_three hy⟩

theorem not_isTriA_dist_three
    {y : CVert} (hy : cgraph.dist cv0 y = 3) :
    ¬ IsTriA 0 (clabelS y) := by
  rintro ⟨-, h1, -⟩
  have hwu : cgraph.Adj cw0 (cvMul cw0 (clabelS y)) := by
    rw [h1]
    exact (cgraph_adj_cu 0).2
  have h := (triType_eq_44352_of_label_swap cgraph_adj_cv0_cw0 hy hwu).2
  rw [h1, triType_cu.1] at h
  norm_num at h

theorem clabel_mul_clabel
    (v : CVert) : clabel v * clabel v = 1 :=
  congrArg Subtype.val (clabelS_mul_self' v)

theorem sq_clabel_of_mem_cPi
    {y y' : CVert} {s : Shat} (hy : y ∈ cPi s) (hy' : y' ∈ cPi s)
    (hne : y ≠ y') (hna : ¬ cgraph.Adj y y') :
    (clabel y * clabel y') ^ 2 = (s : Dfull)⁻¹ * xhat * s := by
  have h0 := mem_cPi_iff.1 hy
  have h0' := mem_cPi_iff.1 hy'
  have hne' : (⟨_, h0⟩ : cPi0) ≠ ⟨_, h0'⟩ := fun e =>
    hne (cvMul_injective s⁻¹ (congrArg Subtype.val e))
  have hna' : ¬ cgraphPi.Adj ⟨_, h0⟩ ⟨_, h0'⟩ := fun e => hna ((cgraph_adj_cvMul y y' s⁻¹).1 e)
  have h := (native_coset_graph_order_four_common_neighbors.2.2 _ _ hne' hna').1
  have e : clabel (cvMul y s⁻¹) * clabel (cvMul y' s⁻¹) =
      (s : Dfull) * (clabel y * clabel y') * (s : Dfull)⁻¹ := by
    rw [clabel_cvMul, clabel_cvMul, InvMemClass.coe_inv, inv_inv]
    group
  rw [e, conj_pow] at h
  calc (clabel y * clabel y') ^ 2
      = (s : Dfull)⁻¹ * ((s : Dfull) * (clabel y * clabel y') ^ 2 * (s : Dfull)⁻¹) * s := by
        group
    _ = (s : Dfull)⁻¹ * xhat * s := by rw [h]

theorem adj_of_mem_cPi
    {y y' : CVert} {s : Shat} (hy : y ∈ cPi s) (hy' : y' ∈ cPi s)
    (hne : y ≠ y') (hc : clabel y * clabel y' = clabel y' * clabel y) : cgraph.Adj y y' := by
  by_contra hna
  have h := sq_clabel_of_mem_cPi hy hy' hne hna
  have h1 : (clabel y * clabel y') ^ 2 = 1 := by
    rw [sq]
    calc clabel y * clabel y' * (clabel y * clabel y')
        = clabel y * (clabel y' * clabel y) * clabel y' := by group
      _ = clabel y * (clabel y * clabel y') * clabel y' := by rw [hc]
      _ = 1 := by
          rw [← mul_assoc, clabel_mul_clabel, one_mul, clabel_mul_clabel]
  rw [h1] at h
  apply xhat_ne_one
  calc xhat = (s : Dfull) * ((s : Dfull)⁻¹ * xhat * s) * (s : Dfull)⁻¹ := by group
    _ = 1 := by rw [← h]; group

theorem exists_partner_mem_cPi
    {y : CVert} {s : Shat} (hy : y ∈ cPi s) :
    ∃ y' ∈ cPi s, clabel y' = clabel y * ((s : Dfull)⁻¹ * xhat * s) := by
  obtain ⟨k, hk⟩ := mem_cPi0.1 (mem_cPi_iff.1 hy)
  refine ⟨cvMul (cvOf (jhatS (a0J * k))) s, cvMul_mem_cPi (jhatS_mem_cPi0 _) s, ?_⟩
  have hl : clabel (cvOf (jhatS k)) = (s : Dfull) * clabel y * (s : Dfull)⁻¹ := by
    rw [← hk, clabel_cvMul, InvMemClass.coe_inv, inv_inv]
  rw [clabel_cvMul, clabel_jhatS, labE_a0J_mul, ← clabel_jhatS, hl]
  group

theorem adj_of_adj_of_commute
    {v y y' : CVert} (hy : cgraph.Adj v y) (hy' : cgraph.Adj v y')
    (hne : y ≠ y') (hc : clabel y * clabel y' = clabel y' * clabel y) : cgraph.Adj y y' := by
  by_contra hna
  have hd : cgraph.dist y y' = 2 := cgraph_dist_eq_two_iff.2 ⟨hne, hna, v, hy.symm, hy'⟩
  have h2 : (clabel y * clabel y') ^ 2 = 1 := by
    rw [sq]
    calc clabel y * clabel y' * (clabel y * clabel y')
        = clabel y * (clabel y' * clabel y) * clabel y' := by group
      _ = clabel y * (clabel y * clabel y') * clabel y' := by rw [hc]
      _ = 1 := by
          rw [← mul_assoc, clabel_mul_clabel, one_mul, clabel_mul_clabel]
  have hdvd : lblOrd y y' ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases labelThree_or_labelFour_of_dist exists_rootModel hd with h | h
  · rcases h.1 with h3 | h3 <;> rw [h3] at hdvd <;> norm_num at hdvd
  · rcases h.1 with h4 | h4 <;> rw [h4] at hdvd <;> norm_num at hdvd

theorem clabel_comm_of_adj
    {v w : CVert} (h : cgraph.Adj v w) :
    clabel v * clabel w = clabel w * clabel v :=
  (clabel_adj h).2.1

theorem exists_translate_of_isTriA
    {x : CVert} (hx : cgraph.Adj cv0 x)
    (ha : IsTriA 0 (clabelS x)) :
    ∃ s : Shat, cv0 ∈ cPi s ∧ cw0 ∈ cPi s ∧ x ∈ cPi s ∧
      clabel cw0 * clabel (cu 0) = (s : Dfull)⁻¹ * xhat * s := by
  have hwu : cgraph.Adj cw0 (cvMul cw0 (clabelS x)) := by
    rw [ha.2.1]
    exact (cgraph_adj_cu 0).2
  have hx4 := mem_sphereFour_of_label_swap cgraph_adj_cv0_cw0 hx hwu
  obtain ⟨-, -, ⟨s, hws, hxs⟩, -, hsub⟩ :=
    native_coset_graph_order_four_common_neighbors.1 cw0 x hx4
  have hvs : cv0 ∈ cPi s := hsub s hws hxs ⟨cgraph_adj_cv0_cw0.symm, hx.symm⟩
  have hne : cw0 ≠ x := fun e => by
    have h := hx4.1
    rw [e, SimpleGraph.dist_self] at h
    norm_num at h
  have hna : ¬ cgraph.Adj cw0 x := fun h' => by
    have h := hx4.1
    rw [SimpleGraph.dist_eq_one_iff_adj.2 h'] at h
    norm_num at h
  have hsq := sq_clabel_of_mem_cPi hws hxs hne hna
  have hu : clabel (cu 0) = clabel x * clabel cw0 * clabel x := by
    rw [← ha.2.1]
    exact congrArg Subtype.val (clabelS_label_swap cw0 x)
  refine ⟨s, hvs, hws, hxs, ?_⟩
  rw [hu, ← hsq, sq]
  group

theorem exists_fourth_vertex :
    ∃ g' : CVert, cgraph.Adj cv0 g' ∧ cgraph.Adj cw0 g' ∧
    cgraph.Adj (cu 0) g' ∧ clabelS g' = clabelS cv0 * clabelS cw0 * clabelS (cu 0) := by
  obtain ⟨x, hx, ha⟩ := exists_isTriA_adj
  obtain ⟨s, hvs, -, -, he⟩ := exists_translate_of_isTriA hx ha
  obtain ⟨g', hg's, hg'⟩ := exists_partner_mem_cPi hvs
  rw [← he] at hg'
  have hg : clabel g' = clabel cv0 * clabel cw0 * clabel (cu 0) := hg'.trans (mul_assoc _ _ _).symm
  have hlab : clabelS g' = clabelS cv0 * clabelS cw0 * clabelS (cu 0) := Subtype.ext hg
  have hvw : Commute (clabel cv0) (clabel cw0) := clabel_comm_of_adj cgraph_adj_cv0_cw0
  have hvu : Commute (clabel cv0) (clabel (cu 0)) := clabel_comm_of_adj (cgraph_adj_cu 0).1
  have hwu : Commute (clabel cw0) (clabel (cu 0)) := clabel_comm_of_adj (cgraph_adj_cu 0).2
  have hinj := native_global_label_bijection_and_full_vertex_centralizer.1
  have inv_self : ∀ v : CVert, (clabel v)⁻¹ = clabel v := fun v =>
    inv_eq_of_mul_eq_one_right (clabel_mul_clabel v)
  have hv : cgraph.Adj cv0 g' := by
    refine adj_of_mem_cPi hvs hg's (fun e => ?_) ?_
    · have h := (congrArg clabel e).trans hg
      have h1 : clabel cw0 * clabel (cu 0) = 1 :=
        mul_left_cancel (a := clabel cv0) (by rw [mul_one, ← mul_assoc]; exact h.symm)
      exact cw0_ne_cu 0 (hinj (((inv_eq_of_mul_eq_one_right h1).symm.trans (inv_self cw0)).symm))
    · rw [hg]
      exact (((Commute.refl _).mul_right hvw).mul_right hvu).eq
  have hw : cgraph.Adj cw0 g' := by
    refine adj_of_adj_of_commute cgraph_adj_cv0_cw0 hv (fun e => ?_) ?_
    · have h := (congrArg clabel e).trans hg
      have h1 : clabel cv0 * clabel (cu 0) = 1 :=
        mul_left_cancel (a := clabel cw0) (by rw [mul_one, ← mul_assoc, ← hvw.eq]; exact h.symm)
      exact cv0_ne_cu 0 (hinj (((inv_eq_of_mul_eq_one_right h1).symm.trans (inv_self cv0)).symm))
    · rw [hg]
      exact ((hvw.symm.mul_right (Commute.refl _)).mul_right hwu).eq
  have hu : cgraph.Adj (cu 0) g' := by
    refine adj_of_adj_of_commute (cgraph_adj_cu 0).1 hv (fun e => ?_) ?_
    · have h := (congrArg clabel e).trans hg
      have h1 : clabel cv0 * clabel cw0 = 1 :=
        mul_right_cancel (b := clabel (cu 0)) (by rw [one_mul]; exact h.symm)
      exact cv0_ne_cw0 (hinj (((inv_eq_of_mul_eq_one_right h1).symm.trans (inv_self cv0)).symm))
    · rw [hg]
      exact ((hvu.symm.mul_right hwu.symm).mul_right (Commute.refl _)).eq
  exact ⟨g', hv, hw, hu, hlab⟩

@[expose] def lamUH
    (j : Fin 2) : vStab cv0 :=
  ⟨clabelS (cu j), clabelS_mem_vStab_cv0_of_adj (cgraph_adj_cu j).1⟩

theorem lamUH_mem_RA
    (j : Fin 2) : lamUH j ∈ RA := ⟨cu j, (cgraph_adj_cu j).1, rfl⟩

theorem exists_adj_clabelS_mul_fourth
    {x : CVert} (hx : cgraph.Adj cv0 x)
    (ha : IsTriA 0 (clabelS x)) : ∃ y : CVert, cgraph.Adj cv0 y ∧
      clabelS cv0 * (clabelS x * (clabelS cv0 * clabelS cw0 * clabelS (cu 0))) = clabelS y := by
  obtain ⟨s, hvs, -, hxs, he⟩ := exists_translate_of_isTriA hx ha
  obtain ⟨y, hys, hy⟩ := exists_partner_mem_cPi hxs
  rw [← he] at hy
  have hvx : Commute (clabel cv0) (clabel x) := clabel_comm_of_adj hx
  have hvw : Commute (clabel cv0) (clabel cw0) := clabel_comm_of_adj cgraph_adj_cv0_cw0
  have hvu : Commute (clabel cv0) (clabel (cu 0)) := clabel_comm_of_adj (cgraph_adj_cu 0).1
  have hwu : Commute (clabel cw0) (clabel (cu 0)) := clabel_comm_of_adj (cgraph_adj_cu 0).2
  have inv_self : ∀ v : CVert, (clabel v)⁻¹ = clabel v := fun v =>
    inv_eq_of_mul_eq_one_right (clabel_mul_clabel v)
  have hlab : clabel cv0 * (clabel x * (clabel cv0 * clabel cw0 * clabel (cu 0))) = clabel y := by
    have hcc : ∀ t, clabel cv0 * (clabel cv0 * t) = t := fun t => by
      rw [← mul_assoc, clabel_mul_clabel, one_mul]
    rw [hy, ← mul_assoc, hvx.eq]
    simp only [mul_assoc, hcc]
  refine ⟨y, ?_, Subtype.ext hlab⟩
  refine adj_of_mem_cPi hvs hys (fun e => ?_) ?_
  ·
    have h : clabel x * (clabel cw0 * clabel (cu 0)) = clabel cv0 :=
      ((congrArg clabel e).trans hy).symm
    have hx' : clabel x = clabel cv0 * (clabel (cu 0) * clabel cw0) := by
      rw [eq_mul_inv_of_mul_eq h, mul_inv_rev, inv_self, inv_self]
    have hc : Commute (clabel x) (clabel cw0) := by
      rw [hx']
      exact hvw.mul_left (hwu.symm.mul_left (Commute.refl _))
    have hfix : cvMul cw0 (clabelS x) = cw0 :=
      (commute_clabelS_iff cw0 (clabelS x)).1 (Subtype.ext hc.eq)
    exact cw0_ne_cu 0 (hfix.symm.trans ha.2.1)
  · rw [hy]
    exact (hvx.mul_right (hvw.mul_right hvu)).eq

theorem mem_RB_mul_fourth
    {x : CVert} (hx : cgraph.Adj cv0 x) (ha : IsTriA 0 (clabelS x)) :
    (⟨clabelS x, clabelS_mem_vStab_cv0_of_adj hx⟩ * (cV0 * lamW0H * lamUH 0) : vStab cv0) ∈
      RB := by
  obtain ⟨y, hy, hlab⟩ := exists_adj_clabelS_mul_fourth hx ha
  exact ⟨y, hy, hlab⟩

abbrev triLab
    (j : Fin 2) : Subgroup Shat :=
  Subgroup.closure {clabelS cv0, clabelS cw0, clabelS (cu j)}

theorem clabelS_cv0_mem_triKer
    (j : Fin 2) : clabelS cv0 ∈ triKer j :=
  ⟨⟨mem_vStab.2 (cvMul_clabelS_self cv0),
    mem_vStab.2 (cvMul_clabelS_of_adj cgraph_adj_cv0_cw0.symm)⟩,
    mem_vStab.2 (cvMul_clabelS_of_adj (cgraph_adj_cu j).1.symm)⟩

theorem clabelS_cw0_mem_triKer
    (j : Fin 2) : clabelS cw0 ∈ triKer j :=
  ⟨⟨mem_vStab.2 (cvMul_clabelS_of_adj cgraph_adj_cv0_cw0), mem_vStab.2 (cvMul_clabelS_self cw0)⟩,
    mem_vStab.2 (cvMul_clabelS_of_adj (cgraph_adj_cu j).2.symm)⟩

theorem clabelS_cu_mem_triKer
    (j : Fin 2) : clabelS (cu j) ∈ triKer j :=
  ⟨⟨mem_vStab.2 (cvMul_clabelS_of_adj (cgraph_adj_cu j).1),
    mem_vStab.2 (cvMul_clabelS_of_adj (cgraph_adj_cu j).2)⟩,
    mem_vStab.2 (cvMul_clabelS_self (cu j))⟩

theorem triLab_le_center
    (j : Fin 2) :
    triLab j ≤ (Subgroup.center (triKer j)).map (triKer j).subtype := by
  have key : ∀ {y : CVert}, clabelS y ∈ triKer j → (∀ g ∈ triKer j, cvMul y g = y) →
      clabelS y ∈ (Subgroup.center (triKer j)).map (triKer j).subtype := fun hy hfix =>
    CFSG.Monster.mem_map_center_iff.2 ⟨hy, fun g hg => (commute_clabelS_iff _ g).2 (hfix g hg)⟩
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact key (clabelS_cv0_mem_triKer j) fun g hg => mem_vStab.1 hg.1.1
  · exact key (clabelS_cw0_mem_triKer j) fun g hg => mem_vStab.1 hg.1.2
  · exact key (clabelS_cu_mem_triKer j) fun g hg => mem_vStab.1 hg.2

theorem Ehat_commute_iff (e e' : Ehat) :
    (e : Dfull) * e' = e' * e ↔ bV (psiW e) (psiW e') = 0 := by
  rw [Ehat_comm e e']
  constructor
  · intro h
    have hx : xhat ^ (bV (psiW e) (psiW e')).val = 1 :=
      mul_left_cancel (h.trans (mul_one _).symm)
    by_contra hb
    have hb1 : bV (psiW e) (psiW e') = 1 := by
      generalize bV (psiW e) (psiW e') = b at hb ⊢
      fin_cases b
      · exact absurd rfl hb
      · rfl
    rw [hb1, ZMod.val_one, pow_one] at hx
    exact xhat_ne_one hx
  · intro h
    rw [h, ZMod.val_zero, pow_zero, mul_one]

theorem eq_one_of_wAct_eq
    {k : Short.Kstab Co2.v0} (h : ∀ w, Short.wAct Co2.v0 k w = w) :
    k = 1 := by
  have hM : (kvGL Co2.qbWBasis k : Matrix (Fin 22) (Fin 22) (ZMod 2)) = 1 := by
    rw [coe_kvGL]
    ext i j
    rw [kvMat_apply, h, Module.Basis.repr_self, Matrix.one_apply, Finsupp.single_apply]
  have hG : kvGL Co2.qbWBasis k = 1 := Units.ext hM
  apply Co2Catalog.phiHom_injective
  rw [map_one, Co2Catalog.phiHom, MonoidHom.comp_apply, MonoidHom.comp_apply, hG, map_one,
    map_one]

theorem finrank_range_wAct_of_involution
    {k : Short.Kstab Co2.v0} (hk : k * k = 1)
    (hk1 : k ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (Short.wAct Co2.v0 k - 1)) = 6 ∨
      Module.finrank (ZMod 2) (LinearMap.range (Short.wAct Co2.v0 k - 1)) = 8 ∨
      Module.finrank (ZMod 2) (LinearMap.range (Short.wAct Co2.v0 k - 1)) = 10 := by
  obtain ⟨z, t, u, -, -, -, -, -, -, rz, rt, ru, hcov⟩ := co2_involution_input
  have hP : Co2Catalog.co2CatalogEquiv k * Co2Catalog.co2CatalogEquiv k = 1 := by
    rw [← map_mul, hk, map_one]
  have hP1 : Co2Catalog.co2CatalogEquiv k ≠ 1 := by
    rw [Ne, MulEquiv.map_eq_one_iff]
    exact hk1
  rw [← CTIB.rank_kvMat_sub_one Co2.qbWBasis k]
  have e := CTIB.rank_co2 k
  rw [Co2Catalog.kvM] at e
  rw [← e]
  rcases hcov _ hP hP1 with h | h | h
  · exact .inl (by rw [CTIB.rank_co2_conj h, rz])
  · exact .inr (.inl (by rw [CTIB.rank_co2_conj h, rt]))
  · exact .inr (.inr (by rw [CTIB.rank_co2_conj h, ru]))

theorem bV_wAct (k : Short.Kstab Co2.v0) (x y : Short.Wv Co2.v0) :
    bV (Short.wAct Co2.v0 k x) (Short.wAct Co2.v0 k y) = bV x y :=
  Unitary.bW_wAct k x y

theorem bV_isRefl : bV.IsRefl := fun x y h => by rw [bV_comm]; exact h

theorem span_pair_le_orthogonal
    {α β : Short.Wv Co2.v0} (hαβ : bV α β = 0) :
    Submodule.span (ZMod 2) {α, β} ≤ bV.orthogonal (Submodule.span (ZMod 2) {α, β}) := by
  rw [Submodule.span_le]
  rintro g (rfl | rfl) <;> rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff] <;>
    intro n hn <;> obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hn
  · rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, bV_self, bV_comm β, hαβ, smul_zero, smul_zero, add_zero]
  · rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, bV_self, hαβ, smul_zero, smul_zero, add_zero]

theorem eq_one_of_fix_orthogonal
    {k : Short.Kstab Co2.v0} {α β : Short.Wv Co2.v0}
    (hαβ : bV α β = 0)
    (hfix : ∀ w ∈ bV.orthogonal (Submodule.span (ZMod 2) {α, β}), Short.wAct Co2.v0 k w = w) :
    k = 1 := by
  set N := Submodule.span (ZMod 2) {α, β} with hN
  have hNN := span_pair_le_orthogonal hαβ
  rw [← hN] at hNN
  have hmem : ∀ w, Short.wAct Co2.v0 k w - w ∈ N := by
    intro w
    rw [← LinearMap.BilinForm.orthogonal_orthogonal bV_nondegenerate bV_isRefl N,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro m hm
    rw [map_sub, ← bV_wAct k m w, hfix m hm, sub_self]
  have hfixN : ∀ n ∈ N, Short.wAct Co2.v0 k n = n := fun n hn => hfix n (hNN hn)
  have hsq : k * k = 1 := by
    apply eq_one_of_wAct_eq
    intro w
    rw [wAct_mul_rev, Module.End.mul_apply]
    have hn := hmem w
    set n := Short.wAct Co2.v0 k w - w with hn'
    have hkw : Short.wAct Co2.v0 k w = w + n := by rw [hn']; abel
    rw [hkw, map_add, hkw, hfixN n hn, add_assoc, ZModModule.add_self, add_zero]
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (Short.wAct Co2.v0 k - 1)) ≤ 2 := by
    have hle : LinearMap.range (Short.wAct Co2.v0 k - 1) ≤ N := by
      rintro _ ⟨w, rfl⟩
      exact hmem w
    classical
    have h := finrank_span_finset_le_card (R := ZMod 2) ({α, β} : Finset (Short.Wv Co2.v0))
    rw [Finset.coe_insert, Finset.coe_singleton] at h
    exact (Submodule.finrank_mono hle).trans (h.trans Finset.card_le_two)
  by_contra hk1
  rcases finrank_range_wAct_of_involution hsq hk1 with h | h | h <;> omega

theorem conj_clabel_mem_Ehat
    {y : CVert} {s : Shat} (hy : y ∈ cPi s) :
    (s : Dfull) * clabel y * (s : Dfull)⁻¹ ∈ Ehat := by
  obtain ⟨k, hk, rfl⟩ := hy
  rw [clabel_cvOf, Subgroup.coe_mul]
  have e : (s : Dfull) * (((k : Dfull) * s)⁻¹ * Sp8.cQ * ((k : Dfull) * s)) * (s : Dfull)⁻¹ =
      (k : Dfull)⁻¹ * Sp8.cQ * k := by group
  rw [e]
  exact conj_mem_Ehat hk Sp8.cQ_mem_Ehat

theorem exists_frame_zero :
    ∃ s : Shat, ∃ C E : Ehat,
    (C : Dfull) = (s : Dfull) * clabel cv0 * (s : Dfull)⁻¹ ∧
    (E : Dfull) = (s : Dfull) * clabel cw0 * (s : Dfull)⁻¹ ∧
    (s : Dfull)⁻¹ * xhat * s = clabel cw0 * clabel (cu 0) := by
  obtain ⟨x, hx, ha⟩ := exists_isTriA_adj
  obtain ⟨s, hvs, hws, -, he⟩ := exists_translate_of_isTriA hx ha
  exact ⟨s, ⟨_, conj_clabel_mem_Ehat hvs⟩, ⟨_, conj_clabel_mem_Ehat hws⟩, rfl, rfl, he.symm⟩

theorem frame_center_zero
    {s : Shat} {C E : Ehat}
    (hC : (C : Dfull) = (s : Dfull) * clabel cv0 * (s : Dfull)⁻¹)
    (hE : (E : Dfull) = (s : Dfull) * clabel cw0 * (s : Dfull)⁻¹)
    (hxs : (s : Dfull)⁻¹ * xhat * s = clabel cw0 * clabel (cu 0)) {z : Shat}
    (hz : z ∈ (Subgroup.center (triKer 0)).map (triKer 0).subtype) :
    (s : Dfull) * z * (s : Dfull)⁻¹ ∈ Jhat ∧
      ∀ q : Ehat, bV (psiW C) (psiW q) = 0 → bV (psiW E) (psiW q) = 0 →
        (q : Dfull) * ((s : Dfull) * z * (s : Dfull)⁻¹) =
          ((s : Dfull) * z * (s : Dfull)⁻¹) * q := by
  obtain ⟨hzK, hzc⟩ := CFSG.Monster.mem_map_center_iff.1 hz
  set σ : Dfull := (s : Dfull) with hσ
  have hzw : (z : Dfull) * clabel cw0 = clabel cw0 * z :=
    (commute_clabel_iff cw0 z).2 (mem_vStab.1 hzK.1.2)
  have hzu : (z : Dfull) * clabel (cu 0) = clabel (cu 0) * z :=
    (commute_clabel_iff (cu 0) z).2 (mem_vStab.1 hzK.2)
  refine ⟨?_, fun q hqC hqE => ?_⟩
  · rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff]
    have h1 : (z : Dfull) * (σ⁻¹ * xhat * σ) = (σ⁻¹ * xhat * σ) * z := by
      rw [hxs, ← mul_assoc, hzw, mul_assoc, hzu, ← mul_assoc]
    calc σ * z * σ⁻¹ * xhat = σ * ((z : Dfull) * (σ⁻¹ * xhat * σ)) * σ⁻¹ := by group
      _ = σ * ((σ⁻¹ * xhat * σ) * z) * σ⁻¹ := by rw [h1]
      _ = xhat * (σ * z * σ⁻¹) := by group
  · have hqC' := (Ehat_commute_iff C q).2 hqC
    have hqE' := (Ehat_commute_iff E q).2 hqE
    have hqx : (q : Dfull) * xhat = xhat * q := xhat_comm_of_mem_Jhat (Ehat_le_Jhat q.2)
    have hq0S : σ⁻¹ * q * σ ∈ Shat :=
      Shat.mul_mem (Shat.mul_mem (Shat.inv_mem s.2) (Jhat_le_Shat (Ehat_le_Jhat q.2))) s.2
    have conj_comm : ∀ y : Dfull, (q : Dfull) * y = y * q →
        σ⁻¹ * q * σ * (σ⁻¹ * y * σ) = σ⁻¹ * y * σ * (σ⁻¹ * q * σ) := fun y hy => by
      calc σ⁻¹ * q * σ * (σ⁻¹ * y * σ) = σ⁻¹ * (q * y) * σ := by group
        _ = σ⁻¹ * (y * q) * σ := by rw [hy]
        _ = σ⁻¹ * y * σ * (σ⁻¹ * q * σ) := by group
    have ec : clabel cv0 = σ⁻¹ * C * σ := by rw [hC]; group
    have ee : clabel cw0 = σ⁻¹ * E * σ := by rw [hE]; group
    have eu : clabel (cu 0) = σ⁻¹ * E * σ * (σ⁻¹ * xhat * σ) := by
      rw [hxs, ← ee, ← mul_assoc, clabel_mul_clabel, one_mul]
    have hc0 := conj_comm C hqC'.symm
    have he0 := conj_comm E hqE'.symm
    have hx0 := conj_comm xhat hqx
    have hu0 : σ⁻¹ * q * σ * clabel (cu 0) = clabel (cu 0) * (σ⁻¹ * q * σ) := by
      rw [eu, ← mul_assoc, he0, mul_assoc, hx0, ← mul_assoc]
    rw [← ec] at hc0
    rw [← ee] at he0
    let Q0 : Shat := ⟨_, hq0S⟩
    have hQ0K : Q0 ∈ triKer 0 :=
      ⟨⟨mem_vStab.2 ((commute_clabel_iff cv0 Q0).1 hc0),
        mem_vStab.2 ((commute_clabel_iff cw0 Q0).1 he0)⟩,
        mem_vStab.2 ((commute_clabel_iff (cu 0) Q0).1 hu0)⟩
    have h' : σ⁻¹ * q * σ * z = z * (σ⁻¹ * q * σ) := congrArg Subtype.val (hzc Q0 hQ0K)
    calc (q : Dfull) * (σ * z * σ⁻¹) = σ * ((σ⁻¹ * q * σ) * z) * σ⁻¹ := by group
      _ = σ * (z * (σ⁻¹ * q * σ)) * σ⁻¹ := by rw [h']
      _ = σ * z * σ⁻¹ * q := by group

theorem Ehat_eq_of_commute {C E Z : Ehat}
    (hZ : ∀ q : Ehat, bV (psiW C) (psiW q) = 0 → bV (psiW E) (psiW q) = 0 →
      (q : Dfull) * Z = Z * q) :
    ∃ P : Ehat, (P = 1 ∨ P = C ∨ P = E ∨ P = C * E) ∧
      ((Z : Dfull) = P ∨ (Z : Dfull) = xhat * P) := by
  have hspan : psiW Z ∈ Submodule.span (ZMod 2) {psiW C, psiW E} := by
    rw [← LinearMap.BilinForm.orthogonal_orthogonal bV_nondegenerate bV_isRefl
      (Submodule.span (ZMod 2) {psiW C, psiW E}), LinearMap.BilinForm.mem_orthogonal_iff]
    intro m hm
    obtain ⟨q, rfl⟩ := psiW_surjective m
    have hm' := LinearMap.BilinForm.mem_orthogonal_iff.1 hm
    exact (Ehat_commute_iff q Z).1 (hZ q (hm' _ (Submodule.subset_span (Set.mem_insert _ _)))
      (hm' _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))))
  have key : ∀ P : Ehat, psiW Z = psiW P → (Z : Dfull) = P ∨ (Z : Dfull) = xhat * P := by
    intro P hP
    have h0 : psiW (Z * P⁻¹) = 0 := by rw [psiW_mul, psiW_inv, hP, add_neg_cancel]
    rcases (psiW_eq_zero_iff _).1 h0 with h | h
    · left
      have := congrArg Subtype.val (mul_inv_eq_one.1 h)
      exact this
    · right
      have h' : Z = xhatE * P := (mul_inv_eq_iff_eq_mul.1 h)
      exact congrArg Subtype.val h'
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hspan
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl
  · refine ⟨1, Or.inl rfl, key 1 ?_⟩
    rw [← hab, psiW_one]
    simp
  · refine ⟨E, Or.inr (Or.inr (Or.inl rfl)), key E ?_⟩
    rw [← hab]
    simp
  · refine ⟨C, Or.inr (Or.inl rfl), key C ?_⟩
    rw [← hab]
    simp
  · refine ⟨C * E, Or.inr (Or.inr (Or.inr rfl)), key (C * E) ?_⟩
    rw [← hab, psiW_mul]
    simp

theorem center_triKer_zero :
    (Subgroup.center (triKer 0)).map (triKer 0).subtype = triLab 0 := by
  refine le_antisymm (fun z hz => ?_) (triLab_le_center 0)
  obtain ⟨s, C, E, hC, hE, hxs⟩ := exists_frame_zero
  obtain ⟨hzJ, hcomm⟩ := frame_center_zero hC hE hxs hz
  set σ : Dfull := (s : Dfull) with hσ
  have hCE : bV (psiW C) (psiW E) = 0 := by
    rw [← Ehat_commute_iff, hC, hE]
    have hvw := clabel_comm_of_adj cgraph_adj_cv0_cw0
    calc σ * clabel cv0 * σ⁻¹ * (σ * clabel cw0 * σ⁻¹)
        = σ * (clabel cv0 * clabel cw0) * σ⁻¹ := by group
      _ = σ * (clabel cw0 * clabel cv0) * σ⁻¹ := by rw [hvw]
      _ = σ * clabel cw0 * σ⁻¹ * (σ * clabel cv0 * σ⁻¹) := by group
  have hk : jhatToKv0 ⟨_, hzJ⟩ = 1 := by
    apply eq_one_of_fix_orthogonal hCE
    intro w hw
    obtain ⟨q, rfl⟩ := psiW_surjective w
    have hw' := LinearMap.BilinForm.mem_orthogonal_iff.1 hw
    have hq := hcomm q (hw' _ (Submodule.subset_span (Set.mem_insert _ _)))
      (hw' _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
    rw [← psiW_conj hzJ q.2]
    congr 1
    apply Subtype.ext
    show (σ * z * σ⁻¹)⁻¹ * q * (σ * z * σ⁻¹) = q
    rw [mul_assoc, hq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hzE : σ * z * σ⁻¹ ∈ Ehat := by
    have h : (⟨_, hzJ⟩ : Jhat) ∈ jhatToKv0.ker := hk
    rw [ker_jhatToKv0, Subgroup.mem_subgroupOf] at h
    exact h
  obtain ⟨P, hP, hZ⟩ := Ehat_eq_of_commute (C := C) (E := E) (Z := ⟨_, hzE⟩) hcomm
  have hzD : (z : Dfull) = σ⁻¹ * (σ * z * σ⁻¹) * σ := by group
  have hmem : ∀ {y : CVert}, y = cv0 ∨ y = cw0 ∨ y = cu 0 → clabelS y ∈ triLab 0 := by
    rintro y (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  obtain ⟨t, ht, htP⟩ : ∃ t ∈ triLab 0, σ⁻¹ * (P : Dfull) * σ = t := by
    rcases hP with rfl | rfl | rfl | rfl
    · exact ⟨1, (triLab 0).one_mem, by simp⟩
    · exact ⟨clabelS cv0, hmem (Or.inl rfl), by rw [hC]; simp only [coe_clabelS]; group⟩
    · exact ⟨clabelS cw0, hmem (Or.inr (Or.inl rfl)), by rw [hE]; simp only [coe_clabelS]; group⟩
    · refine ⟨clabelS cv0 * clabelS cw0,
        mul_mem (hmem (Or.inl rfl)) (hmem (Or.inr (Or.inl rfl))), ?_⟩
      rw [Subgroup.coe_mul, hC, hE, Subgroup.coe_mul, coe_clabelS, coe_clabelS]
      group
  have hxmem : clabelS cw0 * clabelS (cu 0) ∈ triLab 0 :=
    mul_mem (hmem (Or.inr (Or.inl rfl))) (hmem (Or.inr (Or.inr rfl)))
  rcases hZ with h | h
  · have hzt : z = t := Subtype.ext (by
      rw [hzD]
      exact (congrArg (fun y => σ⁻¹ * y * σ) h).trans htP)
    rw [hzt]
    exact ht
  · have hzt : z = clabelS cw0 * clabelS (cu 0) * t := Subtype.ext (by
      rw [hzD, Subgroup.coe_mul, Subgroup.coe_mul, coe_clabelS, coe_clabelS, ← hxs, ← htP]
      have h' : σ * z * σ⁻¹ = xhat * P := h
      rw [h']
      group)
    rw [hzt]
    exact mul_mem hxmem ht

@[expose] def triElt
    (t : Fin 2) (i j k : Bool) : Shat :=
  (if i then clabelS cv0 else 1) * (if j then clabelS cw0 else 1) *
    (if k then clabelS (cu t) else 1)

theorem commute_clabelS_of_adj
    {v w : CVert} (h : cgraph.Adj v w) :
    Commute (clabelS v) (clabelS w) :=
  Subtype.ext (clabel_comm_of_adj h)

theorem commute_ite {x y : Shat} (h : Commute x y) (i j : Bool) :
    Commute (if i then x else 1) (if j then y else 1) := by
  cases i <;> cases j
  · exact Commute.refl 1
  · exact Commute.one_left y
  · exact Commute.one_right x
  · exact h

theorem ite_mul_ite {x : Shat} (hx : x * x = 1) (i i' : Bool) :
    (if i then x else 1) * (if i' then x else 1) = if (i ^^ i') then x else 1 := by
  cases i <;> cases i' <;> simp [hx]

theorem mul_mul_mul_mul_mul {x y z x' y' z' : Shat} (h1 : Commute z x') (h2 : Commute y x')
    (h3 : Commute z y') : x * y * z * (x' * y' * z') = x * x' * (y * y') * (z * z') := by
  calc x * y * z * (x' * y' * z') = x * y * (z * x') * y' * z' := by group
    _ = x * (y * x') * z * y' * z' := by rw [h1.eq]; group
    _ = x * x' * y * (z * y') * z' := by rw [h2.eq]; group
    _ = x * x' * (y * y') * (z * z') := by rw [h3.eq]; group

theorem triElt_mul
    (t : Fin 2) (i j k i' j' k' : Bool) :
    triElt t i j k * triElt t i' j' k' = triElt t (i ^^ i') (j ^^ j') (k ^^ k') := by
  have hvw := commute_clabelS_of_adj cgraph_adj_cv0_cw0
  have hvu := commute_clabelS_of_adj (cgraph_adj_cu t).1
  have hwu := commute_clabelS_of_adj (cgraph_adj_cu t).2
  rw [triElt, triElt, triElt, mul_mul_mul_mul_mul (commute_ite hvu.symm k i')
    (commute_ite hvw.symm j i') (commute_ite hwu.symm k j'), ite_mul_ite (clabelS_mul_self' _),
    ite_mul_ite (clabelS_mul_self' _), ite_mul_ite (clabelS_mul_self' _)]

theorem triElt_false
    (t : Fin 2) : triElt t false false false = 1 := by
  simp [triElt]

theorem triElt_true
    (t : Fin 2) :
    triElt t true true true = clabelS cv0 * clabelS cw0 * clabelS (cu t) := by
  simp [triElt]

theorem triElt_mul_self
    (t : Fin 2) (i j k : Bool) : triElt t i j k * triElt t i j k = 1 := by
  rw [triElt_mul, Bool.xor_self, Bool.xor_self, Bool.xor_self, triElt_false]

theorem triElt_mem
    (t : Fin 2) (i j k : Bool) : triElt t i j k ∈ triLab t := by
  have h0 : clabelS cv0 ∈ triLab t := Subgroup.subset_closure (Set.mem_insert _ _)
  have h1 : clabelS cw0 ∈ triLab t :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have h2 : clabelS (cu t) ∈ triLab t :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  refine mul_mem (mul_mem ?_ ?_) ?_
  · cases i
    · exact (triLab t).one_mem
    · exact h0
  · cases j
    · exact (triLab t).one_mem
    · exact h1
  · cases k
    · exact (triLab t).one_mem
    · exact h2

theorem mem_triLab_iff
    {t : Fin 2} {z : Shat} : z ∈ triLab t ↔ ∃ i j k, z = triElt t i j k := by
  refine ⟨fun hz => ?_, fun ⟨i, j, k, h⟩ => h ▸ triElt_mem t i j k⟩
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨true, false, false, by simp [triElt]⟩
    · exact ⟨false, true, false, by simp [triElt]⟩
    · exact ⟨false, false, true, by simp [triElt]⟩
  | one => exact ⟨false, false, false, (triElt_false t).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, k, rfl⟩ := hx
    obtain ⟨i', j', k', rfl⟩ := hy
    exact ⟨_, _, _, triElt_mul t i j k i' j' k'⟩
  | inv x _ hx =>
    obtain ⟨i, j, k, rfl⟩ := hx
    exact ⟨i, j, k, inv_eq_of_mul_eq_one_right (triElt_mul_self t i j k)⟩

theorem clabelS_injective :
    Function.Injective clabelS := fun _ _ h =>
  native_global_label_bijection_and_full_vertex_centralizer.1 (congrArg Subtype.val h)

theorem clabelS_cu_ne_mul
    (t : Fin 2) : clabelS (cu t) ≠ clabelS cv0 * clabelS cw0 := by
  intro h
  have hone : pairStabOrbit cv0 cw0 (cu t) = {cu t} := by
    ext y
    constructor
    · rintro ⟨s, h0, h1, rfl⟩
      have hc0 := (commute_clabelS_iff cv0 s).2 h0
      have hc1 := (commute_clabelS_iff cw0 s).2 h1
      have hcu : s * clabelS (cu t) = clabelS (cu t) * s := by
        rw [h, ← mul_assoc, hc0, mul_assoc, hc1, ← mul_assoc]
      exact (commute_clabelS_iff (cu t) s).1 hcu
    · rintro rfl
      exact ⟨1, cvMul_one _, cvMul_one _, cvMul_one _⟩
  have ht : triType cv0 cw0 (cu t) = 1 := by rw [triType, hone, Set.ncard_singleton]
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
  · rw [triType_cu.1] at ht
    norm_num at ht
  · rw [triType_cu.2] at ht
    norm_num at ht

theorem triElt_eq_one
    {t : Fin 2} {i j k : Bool} (h : triElt t i j k = 1) :
    i = false ∧ j = false ∧ k = false := by
  have hinv : ∀ {x y : Shat}, x * y = 1 → y * y = 1 → x = y := fun hxy hy =>
    (eq_inv_of_mul_eq_one_left hxy).trans (inv_eq_of_mul_eq_one_right hy)
  cases i <;> cases j <;> cases k <;> simp only [triElt, ite_true, ite_false, mul_one, one_mul,
    Bool.false_eq_true, and_self, and_true, true_and] at h ⊢
  · exact (clabelS_ne_one _ h).elim
  · exact (clabelS_ne_one _ h).elim
  · exact (cw0_ne_cu t (clabelS_injective (hinv h (clabelS_mul_self' _)))).elim
  · exact (clabelS_ne_one _ h).elim
  · exact (cv0_ne_cu t (clabelS_injective (hinv h (clabelS_mul_self' _)))).elim
  · exact (cv0_ne_cw0 (clabelS_injective (hinv h (clabelS_mul_self' _)))).elim
  · refine (clabelS_cu_ne_mul t ?_).elim
    have hvw := commute_clabelS_of_adj cgraph_adj_cv0_cw0
    rw [← inv_eq_of_mul_eq_one_right h, mul_inv_rev, inv_eq_of_mul_eq_one_right
      (clabelS_mul_self' cv0), inv_eq_of_mul_eq_one_right (clabelS_mul_self' cw0), hvw.eq]

theorem triElt_injective
    {t : Fin 2} {i j k i' j' k' : Bool}
    (h : triElt t i j k = triElt t i' j' k') : i = i' ∧ j = j' ∧ k = k' := by
  have h1 : triElt t i j k * triElt t i' j' k' = 1 := by rw [h, triElt_mul_self]
  rw [triElt_mul] at h1
  obtain ⟨a, b, c⟩ := triElt_eq_one h1
  have key : ∀ x y : Bool, Bool.xor x y = false → x = y := by decide
  exact ⟨key _ _ a, key _ _ b, key _ _ c⟩

theorem natCard_triLab
    (t : Fin 2) : Nat.card (triLab t) = 8 := by
  let f : Bool × Bool × Bool → triLab t := fun x =>
    ⟨triElt t x.1 x.2.1 x.2.2, triElt_mem t _ _ _⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := triElt_injective (congrArg Subtype.val hxy)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · obtain ⟨i, j, k, hz⟩ := mem_triLab_iff.1 z.2
      exact ⟨(i, j, k), Subtype.ext hz.symm⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

theorem conj_triElt
    {t : Fin 2} {g : Shat} {x y w : Bool → Shat}
    (hx : ∀ i, g⁻¹ * (if i then clabelS cv0 else 1) * g = x i)
    (hy : ∀ i, g⁻¹ * (if i then clabelS cw0 else 1) * g = y i)
    (hw : ∀ i, g⁻¹ * (if i then clabelS (cu t) else 1) * g = w i) (i j k : Bool) :
    g⁻¹ * triElt t i j k * g = x i * y j * w k := by
  rw [← hx, ← hy, ← hw, triElt]
  group

theorem conj_ite {g x x' : Shat} (h : g⁻¹ * x * g = x') (i : Bool) :
    g⁻¹ * (if i then x else 1) * g = if i then x' else 1 := by
  cases i
  · simp
  · exact h

theorem fixed_triLab
    {t : Fin 2} {a b z : Shat} (ha : IsTriA t a) (hb : IsTriB t b)
    (hz : z ∈ triLab t) (hza : a⁻¹ * z * a = z) (hzb : b⁻¹ * z * b = z) :
    z = 1 ∨ z = clabelS cv0 * clabelS cw0 * clabelS (cu t) := by
  obtain ⟨i, j, k, rfl⟩ := mem_triLab_iff.1 hz
  have hvw := commute_clabelS_of_adj cgraph_adj_cv0_cw0
  have hvu := commute_clabelS_of_adj (cgraph_adj_cu t).1
  have hwu := commute_clabelS_of_adj (cgraph_adj_cu t).2
  have ha' : a⁻¹ * triElt t i j k * a = triElt t i k j := by
    rw [conj_triElt (conj_ite (by rw [← clabelS_cvMul, ha.1])) (conj_ite (by
      rw [← clabelS_cvMul, ha.2.1])) (conj_ite (by rw [← clabelS_cvMul, ha.2.2])), triElt,
      mul_assoc, (commute_ite hwu.symm j k).eq, ← mul_assoc]
  have hb' : b⁻¹ * triElt t i j k * b = triElt t j i k := by
    rw [conj_triElt (conj_ite (by rw [← clabelS_cvMul, hb.1])) (conj_ite (by
      rw [← clabelS_cvMul, hb.2.1])) (conj_ite (by rw [← clabelS_cvMul, hb.2.2])), triElt,
      (commute_ite hvw.symm i j).eq]
  rw [ha'] at hza
  rw [hb'] at hzb
  obtain ⟨-, hjk, -⟩ : i = i ∧ k = j ∧ j = k := triElt_injective hza
  obtain ⟨hij, -, -⟩ : j = i ∧ i = j ∧ k = k := triElt_injective hzb
  rw [hjk, hij]
  cases i
  · exact Or.inl (triElt_false t)
  · exact Or.inr (triElt_true t)

theorem fixed_center_triKer_zero
    {a b z : Shat} (ha : IsTriA 0 a) (hb : IsTriB 0 b)
    (hz : z ∈ (Subgroup.center (triKer 0)).map (triKer 0).subtype) (hza : a⁻¹ * z * a = z)
    (hzb : b⁻¹ * z * b = z) :
    z = 1 ∨ z = clabelS cv0 * clabelS cw0 * clabelS (cu 0) :=
  fixed_triLab ha hb (center_triKer_zero ▸ hz) hza hzb

end CFSG.Monster.B.GSide
