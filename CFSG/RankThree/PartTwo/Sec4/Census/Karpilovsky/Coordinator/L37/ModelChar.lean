module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelPoints
public import CFSG.RankThree.Native.ONTripleSylow
public import CFSG.Certificates.Kernel.Misc.F7Echelon

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

open CFSG.KC.Misc.F7 CFSG.KC.Loop CFSG.RankThree.Native.ONTriple

attribute [local irreducible] dotProduct

noncomputable instance instMulActionGMSub7 : MulAction GM Sub7 :=
  MulAction.compHom Sub7 (ptAct.comp M.subtype)

theorem smul_sub7 (g : GM) (U : Sub7) : g • U = ptAct (g : Mat45ˣ) U := rfl

@[expose] noncomputable def gMG (k : ℕ) : GM :=
  if h : k < 8 then ⟨gM ⟨k, h⟩, gM_mem _⟩ else 1

theorem coe_gMG {k : ℕ} (hk : k < 8) : ((gMG k : GM) : Mat45ˣ) = gM ⟨k, hk⟩ := by
  rw [gMG, dif_pos hk]

noncomputable abbrev W : Sub7 := ptS 0

noncomputable abbrev mH : Subgroup GM := Subgroup.closure (Set.range fun l : Fin 6 => gMG l)

theorem gMG_mem_mH {l : ℕ} (hl : l < 6) : gMG l ∈ mH :=
  Subgroup.subset_closure ⟨⟨l, hl⟩, rfl⟩

theorem zG_smul (U : Sub7) : zG • U = U := by
  have h2 : U.map ((gM 7 : Mat45ˣ) : Mat45).vecMulLinear = U := by
    have hv : ((2 : ZMod 7) • (1 : Mat45)).vecMulLinear = (2 : ZMod 7) • LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      rw [Matrix.vecMulLinear_apply, Matrix.vecMul_smul, Matrix.vecMul_one]
      rfl
    rw [gM_seven_eq, hv, Submodule.map_smul _ _ _ (by decide), Submodule.map_id]
  rw [smul_sub7]
  change ptAct (gM 7) U = U
  rw [ptAct_apply]
  conv_lhs => rw [← h2]
  rw [← map_vml_mul, Units.mul_inv, vml_one, Submodule.map_id]

theorem ptMat_mul_eq {g : Mat45}
    (hg : rowSpan (ptMat 0 * g) ≤ rowSpan (ptMat 0)) : ptMat 0 * g = resW g * ptMat 0 := by
  ext i j
  have hu : rows (ptMat 0 * g) i ∈ rowSpan (ptMat 0) :=
    hg (Submodule.subset_span (Set.mem_range_self i))
  have h := congrFun ((mem_rowSpan_iff pivots_ptMat_zero _).1 hu) j
  rw [Finset.sum_apply] at h
  rw [Matrix.mul_apply (M := resW g)]
  exact h

theorem resW_one : resW 1 = 1 := by
  ext i c
  rw [resW, Matrix.mul_one, Matrix.one_apply]
  exact pivots_ptMat_zero.apply c i

theorem resW_mul {g h : Mat45}
    (hg : rowSpan (ptMat 0 * g) ≤ rowSpan (ptMat 0)) : resW (g * h) = resW g * resW h := by
  ext i c
  rw [resW, ← Matrix.mul_assoc, ptMat_mul_eq hg, Matrix.mul_assoc, Matrix.mul_apply,
    Matrix.mul_apply]
  rfl

theorem rowSpan_le_of_mem {g : GM}
    (hg : g ∈ MulAction.stabilizer GM W) :
    rowSpan (ptMat 0 * ((g : Mat45ˣ) : Mat45)) ≤ rowSpan (ptMat 0) := by
  have h1 : g⁻¹ • W = W := MulAction.mem_stabilizer_iff.1 (Subgroup.inv_mem _ hg)
  rw [smul_sub7, ptAct_apply] at h1
  rw [rowSpan_mul]
  have e : (((g⁻¹ : GM) : Mat45ˣ)⁻¹ : Mat45ˣ) = (g : Mat45ˣ) := by
    rw [Subgroup.coe_inv, inv_inv]
  rw [e] at h1
  exact h1.le

@[expose] noncomputable def chiW0 :
    MulAction.stabilizer GM W →* ZMod 7 where
  toFun g := (resW ((g : GM) : Mat45ˣ)).det
  map_one' := by
    change (resW ((1 : Mat45ˣ) : Mat45)).det = 1
    rw [Units.val_one, resW_one, Matrix.det_one]
  map_mul' g h := by
    change (resW (((g : GM) : Mat45ˣ) * ((h : GM) : Mat45ˣ) : Mat45ˣ)).det = _
    rw [Units.val_mul, resW_mul (rowSpan_le_of_mem g.2), Matrix.det_mul]

@[expose] noncomputable def chiW :
    MulAction.stabilizer GM W →* (ZMod 7)ˣ := chiW0.toHomUnits

theorem coe_chiW (g : MulAction.stabilizer GM W) :
    ((chiW g : (ZMod 7)ˣ) : ZMod 7) = (resW ((g : GM) : Mat45ˣ)).det := by
  rw [chiW, MonoidHom.coe_toHomUnits]
  rfl

theorem zG_mem_stab : zG ∈ MulAction.stabilizer GM W :=
  MulAction.mem_stabilizer_iff.2 (zG_smul W)

theorem gMG_mem_stab {l : ℕ} (hl : l < 6) :
    gMG l ∈ MulAction.stabilizer GM W := by
  rw [MulAction.mem_stabilizer_iff, smul_sub7, coe_gMG (by omega)]
  exact fixes_W hl

theorem mH_le_stab : mH ≤ MulAction.stabilizer GM W := by
  rw [Subgroup.closure_le]
  rintro _ ⟨l, rfl⟩
  exact gMG_mem_stab l.isLt

theorem chiW_zG :
    ((chiW ⟨zG, zG_mem_stab⟩ : (ZMod 7)ˣ) : ZMod 7) = 4 := by
  rw [coe_chiW]
  have e : resW ((zG : GM) : Mat45ˣ) = (2 : ZMod 7) • (1 : Matrix (Fin 8) (Fin 8) (ZMod 7)) := by
    change resW ((gM 7 : Mat45ˣ) : Mat45) = _
    rw [gM_seven_eq]
    ext i c
    rw [resW, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.one_apply]
    exact congrArg (fun x => (2 : ZMod 7) • x) (pivots_ptMat_zero.apply c i)
  rw [e, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  decide

theorem chiW_gMG {l : ℕ} (hl : l < 6) :
    ((chiW ⟨gMG l, gMG_mem_stab hl⟩ : (ZMod 7)ˣ) : ZMod 7) = -1 := by
  rw [coe_chiW]
  change (resW ((gMG l : GM) : Mat45ˣ)).det = -1
  rw [coe_gMG (by omega)]
  exact det_resW_gM hl

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
