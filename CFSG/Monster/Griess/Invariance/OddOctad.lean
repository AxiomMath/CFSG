module

public import CFSG.Monster.Griess.Invariance.Octad.OddValues

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Matrix Module

namespace OctadInv

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem sgn_add_one (y : ZMod 2) : sgn (y + 1) = -sgn y := by
  rw [sgn_add, show sgn 1 = -1 from rfl, mul_neg_one]

theorem oddBr_same_in {i : Fin 24} {d : OctadWord} (hi : i ∈ octSupp d)
    (w : Octad.EvenQuot (octSupp d)) : oddBr i i d w = 0 := by
  rw [oddBr, uQ_mul_uQ_oct, ite_eq_left rfl, ite_eq_left hi]
  have h := sgn_mul_self (Octad.ind (octRep d w) i)
  linear_combination (-(1 : ℚ) / 8) * h

theorem oddBr_same_out {i : Fin 24} {d : OctadWord} (hi : i ∉ octSupp d)
    (w : Octad.EvenQuot (octSupp d)) : oddBr i i d w = 1 / 8 := by
  rw [oddBr, uQ_mul_uQ_oct, ite_eq_left rfl, ite_eq_right hi]
  ring

theorem oddBr_pair_in {i j : Fin 24} {d : OctadWord} (hij : i ≠ j) (hi : i ∈ octSupp d)
    (hj : j ∈ octSupp d) (w : Octad.EvenQuot (octSupp d)) :
    oddBr i j d w = -sgn (bd d w (Octad.cls (octSupp d) {i, j})) / 8 := by
  rw [oddBr, uQ_mul_uQ_oct, ite_eq_right hij, ite_eq_left hi, ite_eq_left hj,
    bd_pair d w hij hi hj, sgn_add]
  ring

theorem oddBr_pair_out {i j : Fin 24} {d : OctadWord} (hij : i ≠ j)
    (hout : ¬(i ∈ octSupp d ∧ j ∈ octSupp d)) (w : Octad.EvenQuot (octSupp d)) :
    oddBr i j d w = 0 := by
  rw [oddBr, uQ_mul_uQ_oct, ite_eq_right hij]
  by_cases hi : i ∈ octSupp d
  · rw [ite_eq_right (fun hj => hout ⟨hi, hj⟩)]
    ring
  · rw [ite_eq_right hi]
    ring

theorem sum_same_in {i : Fin 24} {d : OctadWord} (hi : i ∈ octSupp d)
    (x : Octad.EvenQuot (octSupp d)) : ∑ w, sgn (bd d x w) * oddBr i i d w = 0 := by
  simp only [oddBr_same_in hi, mul_zero, Finset.sum_const_zero]

theorem sum_same_out {i : Fin 24} {d : OctadWord} (hi : i ∉ octSupp d)
    (x : Octad.EvenQuot (octSupp d)) :
    ∑ w, sgn (bd d x w) * oddBr i i d w = if x = 0 then 8 else 0 := by
  simp only [oddBr_same_out hi]
  rw [← Finset.sum_mul, sum_sgn_bd]
  split_ifs <;> norm_num

theorem sum_pair_in {i j : Fin 24} {d : OctadWord} (hij : i ≠ j) (hi : i ∈ octSupp d)
    (hj : j ∈ octSupp d) (x : Octad.EvenQuot (octSupp d)) :
    ∑ w, sgn (bd d x w) * oddBr i j d w =
      if x + Octad.cls (octSupp d) {i, j} = 0 then -8 else 0 := by
  have e : ∀ w, sgn (bd d x w) * oddBr i j d w =
      -(8 : ℚ)⁻¹ * sgn (bd d (x + Octad.cls (octSupp d) {i, j}) w) := by
    intro w
    rw [oddBr_pair_in hij hi hj, map_add (bd d) x, LinearMap.add_apply,
      bd_comm d (Octad.cls (octSupp d) {i, j}) w, sgn_add]
    ring
  rw [Finset.sum_congr rfl fun w _ => e w, ← Finset.mul_sum, sum_sgn_bd]
  split_ifs <;> norm_num

theorem sum_pair_out {i j : Fin 24} {d : OctadWord} (hij : i ≠ j)
    (hout : ¬(i ∈ octSupp d ∧ j ∈ octSupp d)) (x : Octad.EvenQuot (octSupp d)) :
    ∑ w, sgn (bd d x w) * oddBr i j d w = 0 := by
  simp only [oddBr_pair_out hij hout, mul_zero, Finset.sum_const_zero]

theorem tauB_sect0 (a : C₀) (i : Fin 24) : tauB (sectVec a i 0) = sectVec a i 1 :=
  tauB_sectVec a i 0

theorem tauB_symm_sect0 (a : C₀) (i : Fin 24) : tauB.symm (sectVec a i 0) = sectVec a i 2 :=
  tauB_symm_sectVec a i 2

theorem T_tauB_sect0_eq (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (v : Octad.EvenQuot (octSupp d)) :
    T (tauB (sectVec a i 0)) (tauB (sectVec b j 0)) (tauB (octVec ⟨d, v⟩)) =
      if (a : C) + b = d + μ₀ d • ΩC then
        (8 : ℚ)⁻¹ * sgn (((a : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j +
          μ₀ (d : C) + θ (d : C) (b : C)) *
          ∑ w, sgn (bd d (v + etaOf b d) w) * oddBr i j d w
      else 0 := by
  rw [tauB_sect0, tauB_sect0, tauB_octVec, map_sum (T (sectVec a i 1) (sectVec b j 1))]
  simp only [map_smul, smul_eq_mul, T_sect1_sect1_oct]
  by_cases hc : (a : C) + b = d + μ₀ d • ΩC
  · rw [ite_eq_left hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ite_eq_left hc, octHD_apply, map_add (bd d) v (etaOf b d), LinearMap.add_apply]
    have e : bd d v w + qd d w + (((a : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j +
        μ₀ (d : C) + qd d w + θ (d : C) (b : C) + bd d (etaOf b d) w) =
        (((a : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j + μ₀ (d : C) +
          θ (d : C) (b : C)) + (bd d v w + bd d (etaOf b d) w) := by
      linear_combination (qd d w) * two_eq_zero'
    have e2 := congrArg sgn e
    simp only [sgn_add] at e2 ⊢
    linear_combination (8 : ℚ)⁻¹ * oddBr i j d w * e2
  · rw [ite_eq_right hc]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [ite_eq_right hc, zero_mul, mul_zero]

theorem T_tauB_symm_sect0_eq (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (v : Octad.EvenQuot (octSupp d)) :
    T (tauB.symm (sectVec a i 0)) (tauB.symm (sectVec b j 0)) (tauB.symm (octVec ⟨d, v⟩)) =
      if (a : C) + b = d + μ₀ d • ΩC then
        (8 : ℚ)⁻¹ * sgn (qd d v + P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) +
          θ (d : C) (b : C)) * ∑ w, sgn (bd d (v + etaOf b d) w) * oddBr i j d w
      else 0 := by
  rw [tauB_symm_sect0, tauB_symm_sect0, tauB_symm_octVec,
    map_sum (T (sectVec a i 2) (sectVec b j 2))]
  simp only [map_smul, smul_eq_mul, T_sect2_sect2_oct]
  by_cases hc : (a : C) + b = d + μ₀ d • ΩC
  · rw [ite_eq_left hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ite_eq_left hc, octHD_apply, map_add (bd d) v (etaOf b d), LinearMap.add_apply,
      bd_comm d w v]
    simp only [sgn_add]
    ring
  · rw [ite_eq_right hc]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [ite_eq_right hc, zero_mul, mul_zero]

theorem T_tauB_sect0 (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (v : Octad.EvenQuot (octSupp d)) :
    T (tauB (sectVec a i 0)) (tauB (sectVec b j 0)) (tauB (octVec ⟨d, v⟩)) =
      T (sectVec a i 0) (sectVec b j 0) (octVec ⟨d, v⟩) := by
  rw [T_tauB_sect0_eq, T_sect0_sect0_oct, oddOctVal]
  by_cases hc : (a : C) + b = d + μ₀ d • ΩC
  · rw [ite_eq_left hc, ite_eq_left hc, θ_oct_odd' hc]
    have hd := coord_of_cond hc
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_right (show ¬(i ≠ i ∧ i ∈ octSupp d ∧ i ∈ octSupp d ∧
        v = etaOf b d + Octad.cls (octSupp d) {i, i}) from fun h => h.1 rfl)]
      by_cases hi : i ∈ octSupp d
      · rw [sum_same_in hi, mul_zero, ite_eq_right (show ¬(i = i ∧ i ∉ octSupp d ∧
          v = etaOf b d) from fun h => h.2.1 hi)]
      · rw [sum_same_out hi]
        by_cases hv : v = etaOf b d
        · rw [ite_eq_left (show v + etaOf b d = 0 from by rw [hv, add_self_F2]),
            ite_eq_left (show i = i ∧ i ∉ octSupp d ∧ v = etaOf b d from ⟨rfl, hi, hv⟩)]
          have e : ((a : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) i + μ₀ (d : C) +
              θ (d : C) (a : C) = θ (d : C) (a : C) := by
            have hdi := hd i
            rw [coe_apply_eq_zero hi] at hdi
            linear_combination -hdi
          rw [e]
          ring
        · rw [ite_eq_right (show ¬(v + etaOf b d = 0) from fun h =>
            hv ((eq_iff_add_eq_zero_F2 v (etaOf b d)).2 h)),
            ite_eq_right (show ¬(i = i ∧ i ∉ octSupp d ∧ v = etaOf b d) from fun h => hv h.2.2)]
          ring
    · rw [ite_eq_right (show ¬(i = j ∧ i ∉ octSupp d ∧ v = etaOf b d) from fun h => hij h.1)]
      by_cases hin : i ∈ octSupp d ∧ j ∈ octSupp d
      · rw [sum_pair_in hij hin.1 hin.2]
        by_cases hv : v = etaOf b d + Octad.cls (octSupp d) {i, j}
        · rw [ite_eq_left (show v + etaOf b d + Octad.cls (octSupp d) {i, j} = 0 from by
            rw [hv, add_assoc, add_self_F2]),
            ite_eq_left (show i ≠ j ∧ i ∈ octSupp d ∧ j ∈ octSupp d ∧
              v = etaOf b d + Octad.cls (octSupp d) {i, j} from ⟨hij, hin.1, hin.2, hv⟩)]
          have e : θ (d : C) (a : C) + ((b : C) : Fin 24 → ZMod 2) i +
              ((b : C) : Fin 24 → ZMod 2) j =
              ((a : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j + μ₀ (d : C) +
                θ (d : C) (a : C) + 1 := by
            have hdi := hd i
            rw [coe_apply_eq_one hin.1] at hdi
            linear_combination -hdi - (((a : C) : Fin 24 → ZMod 2) i + μ₀ (d : C)) * two_eq_zero'
          rw [e, sgn_add_one]
          ring
        · rw [ite_eq_right (show ¬(v + etaOf b d + Octad.cls (octSupp d) {i, j} = 0) from
            fun h => hv (add_add_eq_zero_iff_F2.1 (by rwa [add_comm v] at h))),
            ite_eq_right (show ¬(i ≠ j ∧ i ∈ octSupp d ∧ j ∈ octSupp d ∧
              v = etaOf b d + Octad.cls (octSupp d) {i, j}) from fun h => hv h.2.2.2)]
          ring
      · rw [sum_pair_out hij hin, mul_zero, ite_eq_right (show ¬(i ≠ j ∧ i ∈ octSupp d ∧
          j ∈ octSupp d ∧ v = etaOf b d + Octad.cls (octSupp d) {i, j}) from
            fun h => hin ⟨h.2.1, h.2.2.1⟩)]
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem T_tauB_symm_sect0 (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (v : Octad.EvenQuot (octSupp d)) :
    T (tauB.symm (sectVec a i 0)) (tauB.symm (sectVec b j 0)) (tauB.symm (octVec ⟨d, v⟩)) =
      T (sectVec a i 0) (sectVec b j 0) (octVec ⟨d, v⟩) := by
  rw [T_tauB_symm_sect0_eq, T_sect0_sect0_oct, oddOctVal]
  by_cases hc : (a : C) + b = d + μ₀ d • ΩC
  · rw [ite_eq_left hc, ite_eq_left hc, θ_oct_odd' hc]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_right (show ¬(i ≠ i ∧ i ∈ octSupp d ∧ i ∈ octSupp d ∧
        v = etaOf b d + Octad.cls (octSupp d) {i, i}) from fun h => h.1 rfl)]
      by_cases hi : i ∈ octSupp d
      · rw [sum_same_in hi, mul_zero, ite_eq_right (show ¬(i = i ∧ i ∉ octSupp d ∧
          v = etaOf b d) from fun h => h.2.1 hi)]
      · rw [sum_same_out hi]
        by_cases hv : v = etaOf b d
        · rw [ite_eq_left (show v + etaOf b d = 0 from by rw [hv, add_self_F2]),
            ite_eq_left (show i = i ∧ i ∉ octSupp d ∧ v = etaOf b d from ⟨rfl, hi, hv⟩)]
          have e : qd d v + P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) +
              θ (d : C) (a : C) = θ (d : C) (a : C) := by
            rw [hv, qd_etaOf hc]
            linear_combination (P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2)) *
              two_eq_zero'
          rw [e]
          ring
        · rw [ite_eq_right (show ¬(v + etaOf b d = 0) from fun h =>
            hv ((eq_iff_add_eq_zero_F2 v (etaOf b d)).2 h)),
            ite_eq_right (show ¬(i = i ∧ i ∉ octSupp d ∧ v = etaOf b d) from fun h => hv h.2.2)]
          ring
    · rw [ite_eq_right (show ¬(i = j ∧ i ∉ octSupp d ∧ v = etaOf b d) from fun h => hij h.1)]
      by_cases hin : i ∈ octSupp d ∧ j ∈ octSupp d
      · rw [sum_pair_in hij hin.1 hin.2]
        by_cases hv : v = etaOf b d + Octad.cls (octSupp d) {i, j}
        · rw [ite_eq_left (show v + etaOf b d + Octad.cls (octSupp d) {i, j} = 0 from by
            rw [hv, add_assoc, add_self_F2]),
            ite_eq_left (show i ≠ j ∧ i ∈ octSupp d ∧ j ∈ octSupp d ∧
              v = etaOf b d + Octad.cls (octSupp d) {i, j} from ⟨hij, hin.1, hin.2, hv⟩)]
          have e : θ (d : C) (a : C) + ((b : C) : Fin 24 → ZMod 2) i +
              ((b : C) : Fin 24 → ZMod 2) j =
              qd d v + P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) +
                θ (d : C) (a : C) + 1 := by
            rw [hv, qd_add, qd_etaOf hc, qd_pair hij hin.1 hin.2,
              bd_etaOf_pair b d hij hin.1 hin.2]
            linear_combination (-(P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) +
              1)) * two_eq_zero'
          rw [e, sgn_add_one]
          ring
        · rw [ite_eq_right (show ¬(v + etaOf b d + Octad.cls (octSupp d) {i, j} = 0) from
            fun h => hv (add_add_eq_zero_iff_F2.1 (by rwa [add_comm v] at h))),
            ite_eq_right (show ¬(i ≠ j ∧ i ∈ octSupp d ∧ j ∈ octSupp d ∧
              v = etaOf b d + Octad.cls (octSupp d) {i, j}) from fun h => hv h.2.2.2)]
          ring
      · rw [sum_pair_out hij hin, mul_zero, ite_eq_right (show ¬(i ≠ j ∧ i ∈ octSupp d ∧
          j ∈ octSupp d ∧ v = etaOf b d + Octad.cls (octSupp d) {i, j}) from
            fun h => hin ⟨h.2.1, h.2.2.1⟩)]
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem tauB_symm_tauB_symm (x : SpaceB) : tauB.symm (tauB.symm x) = tauB x := by
  conv_lhs => rw [← tauB_tauB_tauB x]
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

theorem T_tauB_sector0 {u v w : SpaceB} (hu : u ∈ sectSpan 0) (hv : v ∈ sectSpan 0)
    (hw : w ∈ octSpan) : T (tauB u) (tauB v) (tauB w) = T u v w := by
  refine T_comp_eq_of_span (tauB : SpaceB →ₗ[ℚ] SpaceB) ?_ hu hv hw
  rintro _ ⟨⟨a, i⟩, rfl⟩ _ ⟨⟨b, j⟩, rfl⟩ _ ⟨⟨d, x⟩, rfl⟩
  exact T_tauB_sect0 a b i j d x

theorem T_tauB_symm_sector0 {u v w : SpaceB} (hu : u ∈ sectSpan 0) (hv : v ∈ sectSpan 0)
    (hw : w ∈ octSpan) : T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w := by
  refine T_comp_eq_of_span (tauB.symm : SpaceB →ₗ[ℚ] SpaceB) ?_ hu hv hw
  rintro _ ⟨⟨a, i⟩, rfl⟩ _ ⟨⟨b, j⟩, rfl⟩ _ ⟨⟨d, x⟩, rfl⟩
  exact T_tauB_symm_sect0 a b i j d x

theorem T_tauB_sector1 {u v w : SpaceB} (hu : u ∈ sectSpan 1) (hv : v ∈ sectSpan 1)
    (hw : w ∈ octSpan) :
    T (tauB u) (tauB v) (tauB w) = T u v w ∧
      T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w := by
  have hu0 : tauB.symm u ∈ sectSpan 0 := tauB_symm_mem_sectSpan (k := 0) hu
  have hv0 : tauB.symm v ∈ sectSpan 0 := tauB_symm_mem_sectSpan (k := 0) hv
  have hw0 : tauB.symm w ∈ octSpan := tauB_symm_mem_octSpan hw
  have hP := T_tauB_sector0 hu0 hv0 hw0
  have hQ := T_tauB_symm_sector0 hu0 hv0 hw0
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] at hP
  refine ⟨?_, hP.symm⟩
  rw [← tauB_symm_tauB_symm u, ← tauB_symm_tauB_symm v, ← tauB_symm_tauB_symm w, hQ]
  exact hP.symm

theorem T_tauB_sector2 {u v w : SpaceB} (hu : u ∈ sectSpan 2) (hv : v ∈ sectSpan 2)
    (hw : w ∈ octSpan) :
    T (tauB u) (tauB v) (tauB w) = T u v w ∧
      T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w := by
  have hu0 : tauB u ∈ sectSpan 0 := tauB_mem_sectSpan (k := 2) hu
  have hv0 : tauB v ∈ sectSpan 0 := tauB_mem_sectSpan (k := 2) hv
  have hw0 : tauB w ∈ octSpan := tauB_mem_octSpan hw
  have hP := T_tauB_sector0 hu0 hv0 hw0
  have hQ := T_tauB_symm_sector0 hu0 hv0 hw0
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply] at hQ
  refine ⟨hQ.symm, ?_⟩
  rw [← tauB_tauB u, ← tauB_tauB v, ← tauB_tauB w, hP]
  exact hQ.symm

end OctadInv

open OctadInv

theorem triality_Griess_odd_octad_invariance :
    (∀ (k : Fin 3), ∀ u ∈ sectSpan k, ∀ v ∈ sectSpan k, ∀ w ∈ octSpan,
      (T (tauB u) (tauB v) (tauB w) = T u v w ∧
        T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w) ∧
      (T (tauB u) (tauB w) (tauB v) = T u w v ∧
        T (tauB.symm u) (tauB.symm w) (tauB.symm v) = T u w v) ∧
      (T (tauB w) (tauB u) (tauB v) = T w u v ∧
        T (tauB.symm w) (tauB.symm u) (tauB.symm v) = T w u v)) ∧
    (∀ (a b : C₀) (i j : Fin 24) (d : OctadWord) (v : Octad.EvenQuot (octSupp d)),
      T (sectVec a i 0) (sectVec b j 0) (octVec ⟨d, v⟩) = oddOctVal a b i j d v) := by
  have main : ∀ (k : Fin 3), ∀ u ∈ sectSpan k, ∀ v ∈ sectSpan k, ∀ w ∈ octSpan,
      T (tauB u) (tauB v) (tauB w) = T u v w ∧
        T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w := by
    intro k u hu v hv w hw
    fin_cases k
    · exact ⟨T_tauB_sector0 hu hv hw, T_tauB_symm_sector0 hu hv hw⟩
    · exact T_tauB_sector1 hu hv hw
    · exact T_tauB_sector2 hu hv hw
  refine ⟨fun k u hu v hv w hw => ?_, T_sect0_sect0_oct⟩
  obtain ⟨h1, h2⟩ := main k u hu v hv w hw
  refine ⟨⟨h1, h2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [← T_swap23 (tauB u) (tauB v) (tauB w), h1, T_swap23 u v w]
  · rw [← T_swap23 (tauB.symm u) (tauB.symm v) (tauB.symm w), h2, T_swap23 u v w]
  · rw [T_cycle (tauB w) (tauB u) (tauB v), h1, T_cycle w u v]
  · rw [T_cycle (tauB.symm w) (tauB.symm u) (tauB.symm v), h2, T_cycle w u v]

end CFSG.Monster.Griess
