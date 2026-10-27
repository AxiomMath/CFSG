module

public import CFSG.RankThree.Chevalley.SteinbergBID4NativeA2
public import CFSG.RankThree.Chevalley.SteinbergBID4RootSL2Shape

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

variable (K : Type) [Field K]

@[expose] def sl2Block (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem det_sl2Block (A : Matrix (Fin 2) (Fin 2) K) : (sl2Block K A).det = A.det := by
  rw [sl2Block, Matrix.det_fin_three, Matrix.det_fin_two]
  simp

theorem sl2Block_one : sl2Block K 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Block]

theorem sl2Block_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    sl2Block K (A * B) = sl2Block K A * sl2Block K B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Block, Matrix.mul_apply, Fin.sum_univ_succ]

@[expose] def sl2BlockSL3 : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K where
  toFun A := ⟨sl2Block K A, by rw [det_sl2Block, A.2]⟩
  map_one' := Subtype.ext (sl2Block_one K)
  map_mul' A B := Subtype.ext (sl2Block_mul K A B)

theorem coe_sl2BlockSL3 (A : SpecialLinearGroup (Fin 2) K) :
    ((sl2BlockSL3 K A : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      sl2Block K A :=
  rfl

@[expose] def d4A2Iota : SpecialLinearGroup (Fin 2) K →* subsystemGroup Tag.D4 K d4SuppA2 :=
  ((MulEquiv.ofBijective (d4A2Rep K) ⟨d4A2Rep_injective, d4A2Rep_surjective⟩).symm :
    SpecialLinearGroup (Fin 3) K →* subsystemGroup Tag.D4 K d4SuppA2).comp (sl2BlockSL3 K)

theorem d4A2Rep_d4A2Iota (A : SpecialLinearGroup (Fin 2) K) :
    d4A2Rep K (d4A2Iota K A) = sl2BlockSL3 K A :=
  (MulEquiv.ofBijective (d4A2Rep K) ⟨d4A2Rep_injective, d4A2Rep_surjective⟩).apply_symm_apply _

theorem d4A2Mat_d4A2Iota (A : SpecialLinearGroup (Fin 2) K) :
    d4A2Mat ((d4A2Iota K A : subsystemGroup Tag.D4 K d4SuppA2) : ModGL Tag.D4 K) =
      sl2Block K A :=
  congrArg Subtype.val (d4A2Rep_d4A2Iota K A)

theorem sl2Block_one_add_single_zero_one (c : K) :
    sl2Block K (1 + single 0 1 c) = 1 + single 0 1 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Block]

theorem sl2Block_one_add_single_one_zero (c : K) :
    sl2Block K (1 + single 1 0 c) = 1 + single 1 0 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Block]

theorem d4A2Iota_mem (A : SpecialLinearGroup (Fin 2) K) :
    ((d4A2Iota K A : subsystemGroup Tag.D4 K d4SuppA2) : ModGL Tag.D4 K) ∈
      subsystemGroup Tag.D4 K ({0} : Set (Fin Tag.D4.rank)) := by
  have hA : A ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 2 K) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]
    exact Subgroup.mem_top A
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, j, hij, c, rfl⟩ := hx
    match i, j, hij with
    | 0, 0, h => exact absurd rfl h
    | 0, 1, h =>
      have e : d4A2Iota K (SpecialLinearGroup.transvection h c) =
          ⟨xUnit Tag.D4 K 0 c, xUnit_mem_subsystemGroup zero_mem_d4SuppA2 c⟩ := by
        refine d4A2Rep_injective (Subtype.ext ?_)
        rw [d4A2Rep_d4A2Iota, coe_sl2BlockSL3, coe_d4A2Rep, d4A2Mat_x0,
          CFSG.LinearGroups.coe_transvection, sl2Block_one_add_single_zero_one]
      rw [e]
      exact xUnit_mem_subsystemGroup (Set.mem_singleton 0) c
    | 1, 0, h =>
      have e : d4A2Iota K (SpecialLinearGroup.transvection h c) =
          ⟨yUnit Tag.D4 K 0 c, yUnit_mem_subsystemGroup zero_mem_d4SuppA2 c⟩ := by
        refine d4A2Rep_injective (Subtype.ext ?_)
        rw [d4A2Rep_d4A2Iota, coe_sl2BlockSL3, coe_d4A2Rep, d4A2Mat_y0,
          CFSG.LinearGroups.coe_transvection, sl2Block_one_add_single_one_zero]
      rw [e]
      exact yUnit_mem_subsystemGroup (Set.mem_singleton 0) c
    | 1, 1, h => exact absurd rfl h
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul, Subgroup.coe_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv, Subgroup.coe_inv]; exact inv_mem hx

theorem d4A2Weight_zero_eq : d4A2Weight 0 = d4A2Weight 1 + d4E0 := by
  decide

theorem d4E0Shape_d4A2Iota (A : SpecialLinearGroup (Fin 2) K) :
    D4E0Shape (((d4A2Iota K A : subsystemGroup Tag.D4 K d4SuppA2) : ModGL Tag.D4 K) :
      Module.End K (RootModule Tag.D4 K)) (A : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨B, hB⟩ := exists_d4E0Shape (d4A2Iota_mem K A)
  obtain ⟨m0, hm0⟩ := exists_d4RootVec_d4A2Weight 0
  obtain ⟨m1, hm1⟩ := exists_d4RootVec_d4A2Weight 1
  have hs : d4RootVec m0 = d4RootVec m1 + d4E0 := by rw [hm0, hm1, d4A2Weight_zero_eq]
  have ht := hB.top m1 m0 hs
  have hb := hB.bot m1 m0 hs
  rw [hm0, hm1, rootVec_d4A2Weight, rootVec_d4A2Weight] at ht hb
  have hM := d4A2Mat_d4A2Iota K A
  have entry : ∀ i j : Fin 3, (((d4A2Iota K A : subsystemGroup Tag.D4 K d4SuppA2) :
      ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) (d4A2Vec K j) (d4A2Label i) =
        sl2Block K A i j :=
    fun i j => by rw [← hM]; rfl
  have e00 := entry 0 0
  have e10 := entry 1 0
  have e01 := entry 0 1
  have e11 := entry 1 1
  rw [ht] at e00 e10
  rw [hb] at e01 e11
  simp [d4A2Vec_apply, sl2Block] at e00 e10 e01 e11
  have hBA : B = A := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact e00
    · exact e01
    · exact e10
    · exact e11
  rw [← hBA]
  exact hB

theorem trace_d4A2Iota (A : SpecialLinearGroup (Fin 2) K) :
    LinearMap.trace K (RootModule Tag.D4 K)
        (((d4A2Iota K A : subsystemGroup Tag.D4 K d4SuppA2) : ModGL Tag.D4 K) :
          Module.End K (RootModule Tag.D4 K)) =
      (A : Matrix (Fin 2) (Fin 2) K).trace ^ 2 + 8 * (A : Matrix (Fin 2) (Fin 2) K).trace + 8 := by
  rw [trace_eq_of_d4E0Shape (d4E0Shape_d4A2Iota K A), Matrix.trace_fin_two]
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  linear_combination (-1 : K) * hdet

section Finite

variable {Ω : Type} [Field Ω]

theorem trace_conj_d4A2Iota (z : ModGL Tag.D4 Ω) (A : SpecialLinearGroup (Fin 2) Ω) :
    LinearMap.trace Ω (RootModule Tag.D4 Ω)
        ((z * ((d4A2Iota Ω A : subsystemGroup Tag.D4 Ω d4SuppA2) : ModGL Tag.D4 Ω) * z⁻¹ :
          ModGL Tag.D4 Ω) : Module.End Ω (RootModule Tag.D4 Ω)) =
      (A : Matrix (Fin 2) (Fin 2) Ω).trace ^ 2 + 8 * (A : Matrix (Fin 2) (Fin 2) Ω).trace + 8 := by
  rw [Units.val_mul, Units.val_mul, LinearMap.trace_conj, trace_d4A2Iota]

@[expose] def sl2Companion {k : Type} [Field k] (t : k) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![0, -1; 1, t], by simp [Matrix.det_fin_two]⟩

theorem trace_sl2Companion {k : Type} [Field k] (t : k) :
    (sl2Companion t : Matrix (Fin 2) (Fin 2) k).trace = t := by
  simp [sl2Companion, Matrix.trace_fin_two]

theorem subfield_coe_ofNat (k : Subfield Ω) (n : ℕ) [n.AtLeastTwo] :
    ((OfNat.ofNat n : k) : Ω) = OfNat.ofNat n :=
  map_ofNat k.subtype n

theorem exists_sq_of_two_eq_zero (k : Subfield Ω) [Finite k] (h2 : (2 : Ω) = 0) (x : k) :
    ∃ y : k, y * y = x := by
  have hinj : Function.Injective fun y : k => y * y := by
    intro y w hyw
    have h : ((y : Ω) - w) * ((y : Ω) - w) = 0 := by
      have e : ((y * y : k) : Ω) = ((w * w : k) : Ω) := congrArg Subtype.val hyw
      push_cast at e
      linear_combination e + (w : Ω) * (w - y) * h2
    exact Subtype.ext (sub_eq_zero.1 (mul_self_eq_zero.1 h))
  exact Finite.surjective_of_injective hinj x

theorem closure_traces_eq (k : Subfield Ω) [Finite k] (z : ModGL Tag.D4 Ω) :
    Subfield.closure {x : Ω | ∃ A : SpecialLinearGroup (Fin 2) k,
      x = LinearMap.trace Ω (RootModule Tag.D4 Ω)
        ((z * ((d4A2Iota Ω (SpecialLinearGroup.map k.subtype A) :
          subsystemGroup Tag.D4 Ω d4SuppA2) : ModGL Tag.D4 Ω) * z⁻¹ : ModGL Tag.D4 Ω) :
            Module.End Ω (RootModule Tag.D4 Ω))} = k := by
  set S := Subfield.closure {x : Ω | ∃ A : SpecialLinearGroup (Fin 2) k,
      x = LinearMap.trace Ω (RootModule Tag.D4 Ω)
        ((z * ((d4A2Iota Ω (SpecialLinearGroup.map k.subtype A) :
          subsystemGroup Tag.D4 Ω d4SuppA2) : ModGL Tag.D4 Ω) * z⁻¹ : ModGL Tag.D4 Ω) :
            Module.End Ω (RootModule Tag.D4 Ω))} with hS
  have htr : ∀ A : SpecialLinearGroup (Fin 2) k,
      ((SpecialLinearGroup.map k.subtype A : SpecialLinearGroup (Fin 2) Ω) :
        Matrix (Fin 2) (Fin 2) Ω).trace = ((A : Matrix (Fin 2) (Fin 2) k).trace : Ω) := by
    intro A
    rw [SpecialLinearGroup.map_apply_coe, Matrix.trace_fin_two, Matrix.trace_fin_two]
    simp
  have hval : ∀ t : k, (t : Ω) ^ 2 + 8 * t + 8 ∈ S := by
    intro t
    refine Subfield.subset_closure ⟨sl2Companion t, ?_⟩
    rw [trace_conj_d4A2Iota, htr, trace_sl2Companion]
  refine le_antisymm ((Subfield.closure_le).2 ?_) fun x hx => ?_
  · rintro x ⟨A, rfl⟩
    rw [trace_conj_d4A2Iota, htr]
    exact add_mem (add_mem (pow_mem (SetLike.coe_mem _) 2)
      (mul_mem (ofNat_mem k 8) (SetLike.coe_mem _))) (ofNat_mem k 8)
  · have h8 : (8 : Ω) ∈ S := ofNat_mem S 8
    have hsq : ∀ s : k, (s : Ω) ^ 2 ∈ S := by
      intro s
      have h := hval (s - 4)
      have e : ((s - 4 : k) : Ω) ^ 2 + 8 * ((s - 4 : k) : Ω) + 8 = (s : Ω) ^ 2 - 8 := by
        rw [Subfield.coe_sub, subfield_coe_ofNat]
        ring
      rw [e] at h
      simpa using add_mem h h8
    by_cases h2 : (2 : Ω) = 0
    · obtain ⟨y, hy⟩ := exists_sq_of_two_eq_zero k h2 ⟨x, hx⟩
      have e : x = ((y : Ω)) ^ 2 := by
        rw [sq]
        exact (congrArg Subtype.val hy).symm
      rw [e]
      exact hsq y
    · have e : x = (((⟨x, hx⟩ + 1) / 2 : k) : Ω) ^ 2 - (((⟨x, hx⟩ - 1) / 2 : k) : Ω) ^ 2 := by
        rw [Subfield.coe_div, Subfield.coe_div, Subfield.coe_add, Subfield.coe_sub,
          Subfield.coe_one, subfield_coe_ofNat]
        field_simp
        ring
      rw [e]
      exact sub_mem (hsq _) (hsq _)

end Finite

end CFSG.RankThree.Chevalley
