module

public import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog

variable {K : Type} [Field K]

theorem rootChar_g2 (a : Fin Tag.G2.rank → Kˣ) (v : Fin Tag.G2.rank → ℤ) :
    rootChar a v = a g2ia ^ v g2ia * a g2ir ^ v g2ir := by
  change ∏ i : Fin 2, a i ^ v i = _
  rw [Fin.prod_univ_two]
  rfl

theorem cube_root_cases {ζ x : Kˣ} (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) (hx : x ^ 3 = 1) :
    x = 1 ∨ x = ζ ∨ x = ζ ^ 2 := by
  have hζ3' : (ζ : K) ^ 3 = 1 := by
    have := congrArg Units.val hζ3
    simpa using this
  have hx' : (x : K) ^ 3 = 1 := by
    have := congrArg Units.val hx
    simpa using this
  have h1 : (ζ : K) ^ 2 + ζ + 1 = 0 := by
    have h : ((ζ : K) - 1) * ((ζ : K) ^ 2 + ζ + 1) = 0 := by linear_combination hζ3'
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (Units.ext (by simpa using sub_eq_zero.1 h)) hζ1
    · exact h
  have hprod : ((x : K) - 1) * ((x : K) - ζ) * ((x : K) - ζ ^ 2) = 0 := by
    linear_combination hx' + (-(x : K) ^ 2 + (x : K) * ζ) * h1 - hζ3'
  rcases mul_eq_zero.1 hprod with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (Units.ext (by simpa using sub_eq_zero.1 h))
    · exact Or.inr (Or.inl (Units.ext (sub_eq_zero.1 h)))
  · exact Or.inr (Or.inr (Units.ext (by simpa using sub_eq_zero.1 h)))

theorem orderOf_eq_three {ζ : Kˣ} (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) : orderOf ζ = 3 :=
  orderOf_eq_prime hζ3 hζ1

theorem rootChar_smul_eq_of_single {τ : Tag} {a b : Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (h : ∀ i, rootChar a (w • (Pi.single i 1 : Fin τ.rank → ℤ)) = rootChar b (Pi.single i 1))
    (v : Fin τ.rank → ℤ) : rootChar a (w • v) = rootChar b v := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _
  rw [hw, rootChar_sum]
  conv_rhs => rw [hv, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul, rootChar_zsmul, h i]

theorem exists_weyl_threeB {b : Fin Tag.G2.rank → Kˣ} (hb3 : b ^ 3 = 1) (hb0 : b g2ia ≠ 1) :
    ∃ (w : WeylGroup .G2) (ζ : Kˣ), orderOf ζ = 3 ∧
      ∀ v, rootChar b (w • v) = rootChar (Pi.mulSingle g2ia ζ) v := by
  have h0 : b g2ia ^ 3 = 1 := by simpa using congrFun hb3 g2ia
  have h1 : b g2ir ^ 3 = 1 := by simpa using congrFun hb3 g2ir
  obtain ⟨w, hw⟩ : ∃ w : WeylGroup .G2, rootChar b (w • g2r) = 1 := by
    rcases cube_root_cases h0 hb0 h1 with h | h | h
    · refine ⟨1, ?_⟩
      rw [one_smul, rootChar_g2, h]
      have e1 : g2r g2ia = 0 := rfl
      rw [e1, zpow_zero, one_zpow, one_mul]
    · refine ⟨simple .G2 g2ir * simple .G2 g2ia, ?_⟩
      have e : (simple .G2 g2ir * simple .G2 g2ia) • g2r = g2v := by
        rw [mul_smul, simple_smul, simple_smul]
        exact List.ofFn_injective (by decide +kernel)
      rw [e, rootChar_g2, h]
      have e1 : g2v g2ia = 1 := rfl
      have e2 : g2v g2ir = 2 := rfl
      rw [e1, e2, zpow_one, zpow_two, ← pow_three, h0]
    · refine ⟨simple .G2 g2ia, ?_⟩
      have e : simple .G2 g2ia • g2r = g2u := by
        rw [simple_smul]
        exact List.ofFn_injective (by decide +kernel)
      rw [e, rootChar_g2, h]
      have e1 : g2u g2ia = 1 := rfl
      have e2 : g2u g2ir = 1 := rfl
      rw [e1, e2, zpow_one, zpow_one, ← pow_succ', h0]
  set ζ := rootChar b (w • g2a) with hζ
  have hchar : ∀ v, rootChar b (w • v) = rootChar (Pi.mulSingle g2ia ζ) v := by
    refine rootChar_smul_eq_of_single fun i => ?_
    rw [rootChar_mulSingle_eq_zpow]
    rcases fin_G2_cases i with rfl | rfl
    · rw [← g2a_eq_single, show g2a g2ia = 1 from rfl, zpow_one]
    · rw [← g2r_eq_single, hw, show g2r g2ia = 0 from rfl, zpow_zero]
  refine ⟨w, ζ, orderOf_eq_three (rootChar_pow_of_pow_eq_one hb3 _) fun hζ1 => hb0 ?_, hchar⟩
  have := hchar (w⁻¹ • g2a)
  rw [smul_inv_smul, hζ1, Pi.mulSingle_one, rootChar_g2 b g2a] at this
  have e1 : g2a g2ia = 1 := rfl
  have e2 : g2a g2ir = 0 := rfl
  rw [e1, e2, zpow_one, zpow_zero, mul_one] at this
  rw [this]
  simp [rootChar]

section ThreeB

variable {ζ : Kˣ} (hζ : orderOf ζ = 3)
include hζ

theorem modEq_of_mem_stabilizer_threeB {w : WeylGroup .G2}
    (hw : w ∈ rootCharStabilizerSubgroup (Pi.mulSingle g2ia ζ)) (v : Fin Tag.G2.rank → ℤ) :
    (w • v) g2ia ≡ v g2ia [ZMOD 3] := by
  have h0 : rootChar (Pi.mulSingle g2ia ζ) (w • v) = rootChar (Pi.mulSingle g2ia ζ) v := hw v
  rw [rootChar_mulSingle_eq_zpow, rootChar_mulSingle_eq_zpow, zpow_eq_zpow_iff_modEq, hζ] at h0
  exact_mod_cast h0

theorem rootCharKernel_threeB : rootCharKernel (Pi.mulSingle g2ia ζ) = {g2r, -g2r} := by
  ext α
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hα, hχ⟩
    rw [rootChar_mulSingle_eq_zpow, ← orderOf_dvd_iff_zpow_eq_one, hζ] at hχ
    rcases g2_root_cases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr rfl | (revert hχ; decide)
  · rintro (rfl | rfl)
    · refine ⟨isRoot_g2r, ?_⟩
      rw [rootChar_mulSingle_eq_zpow]
      exact zpow_zero ζ
    · refine ⟨IsRoot.neg isRoot_g2r, ?_⟩
      rw [rootChar_mulSingle_eq_zpow]
      exact zpow_zero ζ

theorem stabilizer_le_threeB :
    rootCharStabilizerSubgroup (Pi.mulSingle g2ia ζ) ≤
      kernelReflectionGroup (Pi.mulSingle g2ia ζ) := by
  intro w hw
  have ka := modEq_of_mem_stabilizer_threeB hζ hw g2a
  have kr := modEq_of_mem_stabilizer_threeB hζ hw g2r
  rcases g2_weyl_cases w with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [weyl_G2_ext (w := w) (w' := 1) (by rw [h1, one_smul]) (by rw [h2, one_smul])]
    exact one_mem _
  rotate_left
  ·
    refine Subgroup.subset_closure ⟨1, g2ir, ?_, weyl_G2_ext ?_ ?_⟩
    · rw [one_smul, ← g2r_eq_single, rootCharKernel_threeB hζ]
      exact Or.inl rfl
    · rw [h1, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  all_goals
    exfalso
    rw [h1] at ka
    rw [h2] at kr
    revert ka kr
    decide

end ThreeB

section ThreeA

variable {ζ : Kˣ} (hζ : orderOf ζ = 3)
include hζ

theorem modEq_of_mem_stabilizer_threeA {w : WeylGroup .G2}
    (hw : w ∈ rootCharStabilizerSubgroup (Pi.mulSingle g2ir ζ)) (v : Fin Tag.G2.rank → ℤ) :
    (w • v) g2ir ≡ v g2ir [ZMOD 3] := by
  have h0 : rootChar (Pi.mulSingle g2ir ζ) (w • v) = rootChar (Pi.mulSingle g2ir ζ) v := hw v
  rw [rootChar_mulSingle_eq_zpow, rootChar_mulSingle_eq_zpow, zpow_eq_zpow_iff_modEq, hζ] at h0
  exact_mod_cast h0

theorem rootCharKernel_threeA :
    rootCharKernel (Pi.mulSingle g2ir ζ) = {g2a, -g2a, g2b, -g2b, g2c, -g2c} := by
  ext α
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hα, hχ⟩
    rw [rootChar_mulSingle_eq_zpow, ← orderOf_dvd_iff_zpow_eq_one, hζ] at hχ
    rcases g2_root_cases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> (revert hχ; decide)
  · have key : ∀ v : Fin Tag.G2.rank → ℤ, IsRoot .G2 v → (3 : ℤ) ∣ v g2ir →
        v ∈ rootCharKernel (Pi.mulSingle g2ir ζ) := fun v hv h3 => by
      refine ⟨hv, ?_⟩
      rw [rootChar_mulSingle_eq_zpow, ← orderOf_dvd_iff_zpow_eq_one, hζ]
      exact_mod_cast h3
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact key _ isRoot_g2a (by decide)
    · exact key _ (IsRoot.neg isRoot_g2a) (by decide)
    · exact key _ isRoot_g2b (by decide)
    · exact key _ (IsRoot.neg isRoot_g2b) (by decide)
    · exact key _ isRoot_g2c (by decide)
    · exact key _ (IsRoot.neg isRoot_g2c) (by decide)

theorem stabilizer_le_threeA :
    rootCharStabilizerSubgroup (Pi.mulSingle g2ir ζ) ≤
      kernelReflectionGroup (Pi.mulSingle g2ir ζ) := by
  intro w hw
  have ka := modEq_of_mem_stabilizer_threeA hζ hw g2a
  have kr := modEq_of_mem_stabilizer_threeA hζ hw g2r
  have hinv : ∀ i : Fin Tag.G2.rank, (simple .G2 i)⁻¹ = simple .G2 i :=
    (coxeterSystem .G2).inv_simple
  have hSig := rootCharKernel_threeA hζ
  have hsa : simple .G2 g2ia ∈ kernelReflectionGroup (Pi.mulSingle g2ir ζ) := by
    refine Subgroup.subset_closure ⟨1, g2ia, ?_, by rw [one_mul, inv_one, mul_one]⟩
    rw [one_smul, ← g2a_eq_single, hSig]
    simp
  have hsb : simple .G2 g2ir * simple .G2 g2ia * (simple .G2 g2ir)⁻¹ ∈
      kernelReflectionGroup (Pi.mulSingle g2ir ζ) := by
    refine Subgroup.subset_closure ⟨simple .G2 g2ir, g2ia, ?_, rfl⟩
    have e : simple .G2 g2ir • (Pi.single g2ia 1 : Fin Tag.G2.rank → ℤ) = g2b := by
      rw [simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    rw [e, hSig]
    simp
  have hsc : (simple .G2 g2ia * simple .G2 g2ir) * simple .G2 g2ia *
      (simple .G2 g2ia * simple .G2 g2ir)⁻¹ ∈ kernelReflectionGroup (Pi.mulSingle g2ir ζ) := by
    refine Subgroup.subset_closure ⟨simple .G2 g2ia * simple .G2 g2ir, g2ia, ?_, rfl⟩
    have e : (simple .G2 g2ia * simple .G2 g2ir) • (Pi.single g2ia 1 : Fin Tag.G2.rank → ℤ) =
        g2c := by
      rw [mul_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    rw [e, hSig]
    simp
  rcases g2_weyl_cases w with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [weyl_G2_ext (w := w) (w' := 1) (by rw [h1, one_smul]) (by rw [h2, one_smul])]
    exact one_mem _
  ·
    rw [weyl_G2_ext (w := w) (w' := simple .G2 g2ia) (by
      rw [h1, simple_smul]
      exact List.ofFn_injective (by decide +kernel)) (by
      rw [h2, simple_smul]
      exact List.ofFn_injective (by decide +kernel))]
    exact hsa
  rotate_left 4
  ·
    rw [weyl_G2_ext (w := w) (w' := simple .G2 g2ir * simple .G2 g2ia * (simple .G2 g2ir)⁻¹) (by
      rw [h1, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)) (by
      rw [h2, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel))]
    exact hsb
  ·
    rw [weyl_G2_ext (w := w) (w' := (simple .G2 g2ir * simple .G2 g2ia * (simple .G2 g2ir)⁻¹) *
      simple .G2 g2ia) (by
      rw [h1, hinv, mul_smul, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul,
        simple_smul]
      exact List.ofFn_injective (by decide +kernel)) (by
      rw [h2, hinv, mul_smul, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul,
        simple_smul]
      exact List.ofFn_injective (by decide +kernel))]
    exact mul_mem hsb hsa
  ·
    rw [weyl_G2_ext (w := w) (w' := simple .G2 g2ia *
      (simple .G2 g2ir * simple .G2 g2ia * (simple .G2 g2ir)⁻¹)) (by
      rw [h1, hinv, mul_smul, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul,
        simple_smul]
      exact List.ofFn_injective (by decide +kernel)) (by
      rw [h2, hinv, mul_smul, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul,
        simple_smul]
      exact List.ofFn_injective (by decide +kernel))]
    exact mul_mem hsa hsb
  ·
    rw [weyl_G2_ext (w := w) (w' := (simple .G2 g2ia * simple .G2 g2ir) * simple .G2 g2ia *
      (simple .G2 g2ia * simple .G2 g2ir)⁻¹) (by
      rw [h1]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)) (by
      rw [h2]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel))]
    exact hsc
  all_goals
    exfalso
    rw [h1] at ka
    rw [h2] at kr
    revert ka kr
    decide

end ThreeA

section LongTorus

variable {ζ : Kˣ} (hζ : orderOf ζ = 3)
include hζ

omit hζ in
theorem rootChar_torusA (v : Fin Tag.G2.rank → ℤ) :
    rootChar (fun j => ζ ^ Tag.G2.cartan g2ia j) v = ζ ^ (2 * v g2ia + -1 * v g2ir) := by
  rw [rootChar_g2, ← zpow_mul, ← zpow_mul, ← zpow_add]
  congr 1

theorem rootCharKernel_torusA :
    rootCharKernel (fun j => ζ ^ Tag.G2.cartan g2ia j) = {g2v, -g2v} := by
  ext α
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hα, hχ⟩
    rw [rootChar_torusA, ← orderOf_dvd_iff_zpow_eq_one, hζ] at hχ
    rcases g2_root_cases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr rfl | (revert hχ; decide)
  · rintro (rfl | rfl)
    · refine ⟨isRoot_g2v, ?_⟩
      rw [rootChar_torusA]
      exact zpow_zero ζ
    · refine ⟨IsRoot.neg isRoot_g2v, ?_⟩
      rw [rootChar_torusA]
      exact zpow_zero ζ

theorem stabilizer_le_torusA :
    rootCharStabilizerSubgroup (fun j => ζ ^ Tag.G2.cartan g2ia j) ≤
      kernelReflectionGroup (fun j => ζ ^ Tag.G2.cartan g2ia j) := by
  intro w hw
  have key : ∀ v : Fin Tag.G2.rank → ℤ, (3 : ℤ) ∣
      (2 * (w • v) g2ia + -1 * (w • v) g2ir) - (2 * v g2ia + -1 * v g2ir) := fun v => by
    have h0 : rootChar (fun j => ζ ^ Tag.G2.cartan g2ia j) (w • v) =
        rootChar (fun j => ζ ^ Tag.G2.cartan g2ia j) v := hw v
    rw [rootChar_torusA, rootChar_torusA, zpow_eq_zpow_iff_modEq, hζ] at h0
    exact Int.ModEq.dvd (by exact_mod_cast h0.symm)
  have ka := key g2a
  have kr := key g2r
  have hinv : ∀ i : Fin Tag.G2.rank, (simple .G2 i)⁻¹ = simple .G2 i :=
    (coxeterSystem .G2).inv_simple
  rcases g2_weyl_cases w with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [weyl_G2_ext (w := w) (w' := 1) (by rw [h1, one_smul]) (by rw [h2, one_smul])]
    exact one_mem _
  rotate_left 9
  ·
    refine Subgroup.subset_closure ⟨simple .G2 g2ir * simple .G2 g2ia, g2ir, ?_,
      weyl_G2_ext ?_ ?_⟩
    · have e : (simple .G2 g2ir * simple .G2 g2ia) • (Pi.single g2ir 1 : Fin Tag.G2.rank → ℤ) =
          g2v := by
        rw [mul_smul, simple_smul, simple_smul]
        exact List.ofFn_injective (by decide +kernel)
      rw [e, rootCharKernel_torusA hζ]
      exact Or.inl rfl
    · rw [h1]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  all_goals
    exfalso
    rw [h1] at ka
    rw [h2] at kr
    revert ka kr
    decide

end LongTorus

section ShortTorus

variable {μ : Kˣ} (hμ : 4 ≤ orderOf μ)
include hμ

theorem eq_zero_of_zpow_eq_one_of_small {d : ℤ} (hd : -3 ≤ d ∧ d ≤ 3) (h : μ ^ d = 1) :
    d = 0 := by
  rw [← orderOf_dvd_iff_zpow_eq_one] at h
  by_contra hd0
  have h1 := Int.le_of_dvd (abs_pos.mpr hd0) ((dvd_abs _ _).mpr h)
  have h2 : (4 : ℤ) ≤ orderOf μ := by exact_mod_cast hμ
  have h3 : |d| ≤ 3 := abs_le.mpr ⟨by omega, by omega⟩
  omega

theorem rootCharKernel_shortNine :
    rootCharKernel (Pi.mulSingle g2ir μ) = {g2a, -g2a} := by
  ext α
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hα, hχ⟩
    rw [rootChar_mulSingle_eq_zpow] at hχ
    have hb : -3 ≤ α g2ir ∧ α g2ir ≤ 3 := by
      rcases g2_root_cases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> decide
    have h0 := eq_zero_of_zpow_eq_one_of_small hμ hb hχ
    rcases g2_root_cases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr rfl | (revert h0; decide)
  · rintro (rfl | rfl)
    · refine ⟨isRoot_g2a, ?_⟩
      rw [rootChar_mulSingle_eq_zpow]
      exact zpow_zero μ
    · refine ⟨IsRoot.neg isRoot_g2a, ?_⟩
      rw [rootChar_mulSingle_eq_zpow]
      exact zpow_zero μ

theorem stabilizer_le_shortNine :
    rootCharStabilizerSubgroup (Pi.mulSingle g2ir μ) ≤
      kernelReflectionGroup (Pi.mulSingle g2ir μ) := by
  intro w hw
  have key : ∀ v : Fin Tag.G2.rank → ℤ, μ ^ ((w • v) g2ir - v g2ir) = 1 := fun v => by
    have h0 : rootChar (Pi.mulSingle g2ir μ) (w • v) = rootChar (Pi.mulSingle g2ir μ) v := hw v
    rw [rootChar_mulSingle_eq_zpow, rootChar_mulSingle_eq_zpow] at h0
    rw [zpow_sub, h0, mul_inv_cancel]
  have ka := key g2a
  have kr := key g2r
  rcases g2_weyl_cases w with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [weyl_G2_ext (w := w) (w' := 1) (by rw [h1, one_smul]) (by rw [h2, one_smul])]
    exact one_mem _
  ·
    refine Subgroup.subset_closure ⟨1, g2ia, ?_, weyl_G2_ext ?_ ?_⟩
    · rw [one_smul, ← g2a_eq_single, rootCharKernel_shortNine hμ]
      exact Or.inl rfl
    · rw [h1, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  all_goals
    exfalso
    rw [h1] at ka
    rw [h2] at kr
    have hka := eq_zero_of_zpow_eq_one_of_small hμ (by decide) ka
    have hkr := eq_zero_of_zpow_eq_one_of_small hμ (by decide) kr
    revert hka hkr
    decide

end ShortTorus

end CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
