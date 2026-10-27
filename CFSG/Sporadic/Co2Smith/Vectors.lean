module

public import CFSG.Sporadic.Co2Smith.Check
public import CFSG.Sporadic.Co2Smith.Elements

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

abbrev V : Type := Fin 22 → ZMod 2

@[expose] def vec (v : ℕ) : V := toVecD 22 v

theorem vec_injective {v w : ℕ} (hv : v < 2 ^ 22) (hw : w < 2 ^ 22) (h : vec v = vec w) :
    v = w :=
  toVecD_injective hv hw h

theorem mulVec_vec {u : K} {R : Array ℕ} (hu : u.val.val = rowsMatrix 22 R) (v : ℕ) :
    u.val.val *ᵥ vec v = vec (Native.colAct R v) :=
  val_mulVec hu v

theorem rowsMatrix_mulVec_vec (R : Array ℕ) (v : ℕ) :
    rowsMatrix 22 R *ᵥ vec v = vec (Native.colAct R v) := by
  rw [vec, rowsMatrix_mulVec, Native.colAct, vec]

theorem rowsMatrix_subId (M : Array ℕ) :
    rowsMatrix 22 (Native.subId M) = rowsMatrix 22 M - 1 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.one_apply, rowsMatrix_apply, rowsMatrix_apply, Native.subId]
  have hi : (i : ℕ) < ((List.range 22).toArray.map fun k => M[k]! ^^^ 1 <<< k).size := by
    simp
  rw [Array.getElem?_eq_getElem hi, Option.getD_some, Array.getElem_map]
  simp only [List.getElem_toArray, List.getElem_range]
  rw [toVecD_xor, Pi.add_apply]
  have hM : M[(i : ℕ)]! = M[(i : ℕ)]?.getD 0 := by
    rw [getElem!_def]
    cases M[(i : ℕ)]? <;> rfl
  rw [hM]
  have h1 : toVecD 22 (1 <<< (i : ℕ)) j = if i = j then 1 else 0 := by
    rw [toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : i = j
    · subst h; simp
    · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
      simp [h, h']
  rw [h1]
  split_ifs <;> simp [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

@[expose] noncomputable def zEnd :
    V →ₗ[ZMod 2] V := (z0.val.val - 1).mulVecLin

@[expose] noncomputable def Zsub :
    Submodule (ZMod 2) V := LinearMap.range zEnd

theorem zEnd_vec
    (v : ℕ) : zEnd (vec v) = vec (Native.colAct (Native.subId co2RowsA) v) := by
  rw [zEnd, Matrix.mulVecLin_apply, z0_val, ← rowsMatrix_subId, rowsMatrix_mulVec_vec]

theorem mem_Zsub_of_comm
    {g : K} (hg : g * z0 = z0 * g) {v : V} (hv : v ∈ Zsub) :
    g.val.val *ᵥ v ∈ Zsub := by
  obtain ⟨u, rfl⟩ := hv
  refine ⟨g.val.val *ᵥ u, ?_⟩
  have hm : g.val.val * z0.val.val = z0.val.val * g.val.val := by
    rw [← val_val_mul, ← val_val_mul, hg]
  simp only [zEnd, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, hm]

@[expose] noncomputable def zetaV (i : Fin 6) : V := vec Native.zetaVecs[(i : ℕ)]!

theorem zeta_spec :
    (∀ i < 6, Native.colAct (Native.subId co2RowsA) Native.zetaPre[i]! = Native.zetaVecs[i]! ∧
      Native.zetaVecs[i]! < 4194304 ∧ Native.zetaPre[i]! < 4194304) ∧
    (∀ c < 63, Native.zetaComb (c + 1) ≠ 0) ∧
    (∀ k < 22, ∃ c < 64, Native.zetaComb c = Native.colAct (Native.subId co2RowsA) (1 <<< k)) := by
  have h := zeta_check
  simp only [Native.zetaOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range, decide_eq_true_eq, and_assoc, bne_iff_ne, ne_eq] at h
  obtain ⟨-, -, h1, h2, h3, -⟩ := h
  exact ⟨fun i hi => h1 i hi, fun c hc => h2 c hc, fun k hk => h3 k hk⟩

theorem vec_zetaComb (c : ℕ) :
    vec (Native.zetaComb c) = ∑ i : Fin 6, if c.testBit i = true then zetaV i else 0 := by
  rw [vec, Native.zetaComb, foldl_xor_toVecD, toVecD_zero, zero_add,
    ← Fin.sum_univ_eq_sum_range (fun i => if c.testBit i = true then
      toVecD 22 Native.zetaVecs[i]! else 0)]
  rfl

theorem zetaV_mem
    (i : Fin 6) : zetaV i ∈ Zsub := by
  refine ⟨vec Native.zetaPre[(i : ℕ)]!, ?_⟩
  rw [zEnd_vec, (zeta_spec.1 i i.2).1]
  rfl

theorem zetaV_linearIndependent : LinearIndependent (ZMod 2) zetaV := by
  have h : ∀ g : Fin 6 → ZMod 2, ∑ i, g i • zetaV i = 0 → g = 0 := by decide +kernel
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  refine (injective_iff_map_eq_zero (Fintype.linearCombination (ZMod 2) zetaV)).2 fun g hg => ?_
  rw [Fintype.linearCombination_apply] at hg
  exact h g hg

theorem vec_one_shiftLeft (k : Fin 22) : vec (1 <<< (k : ℕ)) = Pi.single k 1 := by
  funext j
  rw [vec, toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : k = j
  · subst h; simp
  · have h' : (k : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h', Ne.symm h]

theorem span_zetaV :
    Submodule.span (ZMod 2) (Set.range zetaV) = Zsub := by
  refine Submodule.span_eq_of_le (p := Zsub) ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact zetaV_mem i
  · rintro _ ⟨u, rfl⟩
    have hu : u = ∑ k : Fin 22, u k • Pi.single k 1 := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hu, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul, ← vec_one_shiftLeft, zEnd_vec]
    obtain ⟨c, -, hc⟩ := zeta_spec.2.2 k k.2
    rw [← hc, vec_zetaComb]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
    split_ifs
    · exact Submodule.subset_span ⟨i, rfl⟩
    · exact Submodule.zero_mem _

@[expose] noncomputable def zetaB6 :
    Module.Basis (Fin 6) (ZMod 2) Zsub :=
  Module.Basis.mk (v := fun i => ⟨zetaV i, zetaV_mem i⟩)
    (LinearIndependent.of_comp Zsub.subtype zetaV_linearIndependent)
    ((Submodule.span_range_subtype_eq_top_iff Zsub zetaV_mem).mpr span_zetaV).ge

theorem zetaB6_apply
    (i : Fin 6) : (zetaB6 i : V) = zetaV i := by
  rw [zetaB6, Module.Basis.mk_apply]

end CFSG.Sporadic.Co2Smith
