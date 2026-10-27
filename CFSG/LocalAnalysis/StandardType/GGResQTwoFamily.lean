module

public import CFSG.LocalAnalysis.StandardType.GGResQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGResILin
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA3
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA4
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA5
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataB3
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataB4
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataB5
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataB6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataB7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC3
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC4
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC5
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD4
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD5
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataF4
public import CFSG.LocalAnalysis.StandardType.GGForkCells

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResQTwoFinite_A3 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 3 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.A 3 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨3, CartanMatrix.A 3, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.A3.pt_A3_b0, GGResIDisp.A3.hcyc_A3_b0,
      GGResIDisp.A3.shapes_A3_b0, GGResIDisp.A3.vecs_A3_b0,
      GGResIDisp.A3.hcand_A3_b0,
      GGResQTwoCellDataA3.wits_A3_b0, GGResQTwoCellDataA3.cell_A3_b0,
      GGResQTwoCellDataA3.hsideOK_A3_b0, GGResQTwoCellDataA3.hshapeNZ_A3_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨3, CartanMatrix.A 3, e, hCe, 2, hk, 0, by decide,
      GGResIDisp.A3.pt_A3_b2, GGResIDisp.A3.hcyc_A3_b2,
      GGResIDisp.A3.shapes_A3_b2, GGResIDisp.A3.vecs_A3_b2,
      GGResIDisp.A3.hcand_A3_b2,
      GGResQTwoCellDataA3.wits_A3_b2, GGResQTwoCellDataA3.cell_A3_b2,
      GGResQTwoCellDataA3.hsideOK_A3_b2, GGResQTwoCellDataA3.hshapeNZ_A3_b2⟩⟩

theorem ggResQTwoFinite_A4 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 4 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.A 4 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨4, CartanMatrix.A 4, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.A4.pt_A4_b0, GGResIDisp.A4.hcyc_A4_b0,
      GGResIDisp.A4.shapes_A4_b0, GGResIDisp.A4.vecs_A4_b0,
      GGResIDisp.A4.hcand_A4_b0,
      GGResQTwoCellDataA4.wits_A4_b0, GGResQTwoCellDataA4.cell_A4_b0,
      GGResQTwoCellDataA4.hsideOK_A4_b0, GGResQTwoCellDataA4.hshapeNZ_A4_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨4, CartanMatrix.A 4, e, hCe, 3, hk, 0, by decide,
      GGResIDisp.A4.pt_A4_b3, GGResIDisp.A4.hcyc_A4_b3,
      GGResIDisp.A4.shapes_A4_b3, GGResIDisp.A4.vecs_A4_b3,
      GGResIDisp.A4.hcand_A4_b3,
      GGResQTwoCellDataA4.wits_A4_b3, GGResQTwoCellDataA4.cell_A4_b3,
      GGResQTwoCellDataA4.hsideOK_A4_b3, GGResQTwoCellDataA4.hshapeNZ_A4_b3⟩⟩

theorem ggResQTwoFinite_A5 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 5 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.A 5 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨5, CartanMatrix.A 5, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.A5.pt_A5_b0, GGResIDisp.A5.hcyc_A5_b0,
      GGResIDisp.A5.shapes_A5_b0, GGResIDisp.A5.vecs_A5_b0,
      GGResIDisp.A5.hcand_A5_b0,
      GGResQTwoCellDataA5.wits_A5_b0, GGResQTwoCellDataA5.cell_A5_b0,
      GGResQTwoCellDataA5.hsideOK_A5_b0, GGResQTwoCellDataA5.hshapeNZ_A5_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2} 2 4
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨5, CartanMatrix.A 5, e, hCe, 4, hk, 0, by decide,
      GGResIDisp.A5.pt_A5_b4, GGResIDisp.A5.hcyc_A5_b4,
      GGResIDisp.A5.shapes_A5_b4, GGResIDisp.A5.vecs_A5_b4,
      GGResIDisp.A5.hcand_A5_b4,
      GGResQTwoCellDataA5.wits_A5_b4, GGResQTwoCellDataA5.cell_A5_b4,
      GGResQTwoCellDataA5.hsideOK_A5_b4, GGResQTwoCellDataA5.hshapeNZ_A5_b4⟩⟩

theorem ggResQTwoFinite_A6 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 6 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.A 6 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨6, CartanMatrix.A 6, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.A6.pt_A6_b0, GGResIDisp.A6.hcyc_A6_b0,
      GGResIDisp.A6.shapes_A6_b0, GGResIDisp.A6.vecs_A6_b0,
      GGResIDisp.A6.hcand_A6_b0,
      GGResQTwoCellDataA6.wits_A6_b0, GGResQTwoCellDataA6.cell_A6_b0,
      GGResQTwoCellDataA6.hsideOK_A6_b0, GGResQTwoCellDataA6.hshapeNZ_A6_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2} 2 4
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3} 3 5
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨6, CartanMatrix.A 6, e, hCe, 5, hk, 0, by decide,
      GGResIDisp.A6.pt_A6_b5, GGResIDisp.A6.hcyc_A6_b5,
      GGResIDisp.A6.shapes_A6_b5, GGResIDisp.A6.vecs_A6_b5,
      GGResIDisp.A6.hcand_A6_b5,
      GGResQTwoCellDataA6.wits_A6_b5, GGResQTwoCellDataA6.cell_A6_b5,
      GGResQTwoCellDataA6.hsideOK_A6_b5, GGResQTwoCellDataA6.hshapeNZ_A6_b5⟩⟩

theorem ggResQTwoFinite_A7 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.A 7 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨7, CartanMatrix.A 7, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.A7.pt_A7_b0, GGResIDisp.A7.hcyc_A7_b0,
      GGResIDisp.A7.shapes_A7_b0, GGResIDisp.A7.vecs_A7_b0,
      GGResIDisp.A7.hcand_A7_b0,
      GGResQTwoCellDataA7.wits_A7_b0, GGResQTwoCellDataA7.cell_A7_b0,
      GGResQTwoCellDataA7.hsideOK_A7_b0, GGResQTwoCellDataA7.hshapeNZ_A7_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2} 2 4
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3} 3 5
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3, 4} 4 6
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨7, CartanMatrix.A 7, e, hCe, 6, hk, 0, by decide,
      GGResIDisp.A7.pt_A7_b6, GGResIDisp.A7.hcyc_A7_b6,
      GGResIDisp.A7.shapes_A7_b6, GGResIDisp.A7.vecs_A7_b6,
      GGResIDisp.A7.hcand_A7_b6,
      GGResQTwoCellDataA7.wits_A7_b6, GGResQTwoCellDataA7.cell_A7_b6,
      GGResQTwoCellDataA7.hsideOK_A7_b6, GGResQTwoCellDataA7.hshapeNZ_A7_b6⟩⟩

theorem ggResQTwoFinite_B3 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 3 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.B 3 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨3, CartanMatrix.B 3, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.B3.pt_B3_b0, GGResIDisp.B3.hcyc_B3_b0,
      GGResIDisp.B3.shapes_B3_b0, GGResIDisp.B3.vecs_B3_b0,
      GGResIDisp.B3.hcand_B3_b0,
      GGResQTwoCellDataB3.wits_B3_b0, GGResQTwoCellDataB3.cell_B3_b0,
      GGResQTwoCellDataB3.hsideOK_B3_b0, GGResQTwoCellDataB3.hshapeNZ_B3_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨3, CartanMatrix.B 3, e, hCe, 2, hk, 0, by decide,
      GGResIDisp.B3.pt_B3_b2, GGResIDisp.B3.hcyc_B3_b2,
      GGResIDisp.B3.shapes_B3_b2, GGResIDisp.B3.vecs_B3_b2,
      GGResIDisp.B3.hcand_B3_b2,
      GGResQTwoCellDataB3.wits_B3_b2, GGResQTwoCellDataB3.cell_B3_b2,
      GGResQTwoCellDataB3.hsideOK_B3_b2, GGResQTwoCellDataB3.hshapeNZ_B3_b2⟩⟩

theorem ggResQTwoFinite_B4 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 4 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.B 4 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨4, CartanMatrix.B 4, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.B4.pt_B4_b0, GGResIDisp.B4.hcyc_B4_b0,
      GGResIDisp.B4.shapes_B4_b0, GGResIDisp.B4.vecs_B4_b0,
      GGResIDisp.B4.hcand_B4_b0,
      GGResQTwoCellDataB4.wits_B4_b0, GGResQTwoCellDataB4.cell_B4_b0,
      GGResQTwoCellDataB4.hsideOK_B4_b0, GGResQTwoCellDataB4.hshapeNZ_B4_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨4, CartanMatrix.B 4, e, hCe, 3, hk, 0, by decide,
      GGResIDisp.B4.pt_B4_b3, GGResIDisp.B4.hcyc_B4_b3,
      GGResIDisp.B4.shapes_B4_b3, GGResIDisp.B4.vecs_B4_b3,
      GGResIDisp.B4.hcand_B4_b3,
      GGResQTwoCellDataB4.wits_B4_b3, GGResQTwoCellDataB4.cell_B4_b3,
      GGResQTwoCellDataB4.hsideOK_B4_b3, GGResQTwoCellDataB4.hshapeNZ_B4_b3⟩⟩

theorem ggResQTwoFinite_B5 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 5 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.B 5 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨5, CartanMatrix.B 5, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.B5.pt_B5_b0, GGResIDisp.B5.hcyc_B5_b0,
      GGResIDisp.B5.shapes_B5_b0, GGResIDisp.B5.vecs_B5_b0,
      GGResIDisp.B5.hcand_B5_b0,
      GGResQTwoCellDataB5.wits_B5_b0, GGResQTwoCellDataB5.cell_B5_b0,
      GGResQTwoCellDataB5.hsideOK_B5_b0, GGResQTwoCellDataB5.hshapeNZ_B5_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2} 2 4
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨5, CartanMatrix.B 5, e, hCe, 4, hk, 0, by decide,
      GGResIDisp.B5.pt_B5_b4, GGResIDisp.B5.hcyc_B5_b4,
      GGResIDisp.B5.shapes_B5_b4, GGResIDisp.B5.vecs_B5_b4,
      GGResIDisp.B5.hcand_B5_b4,
      GGResQTwoCellDataB5.wits_B5_b4, GGResQTwoCellDataB5.cell_B5_b4,
      GGResQTwoCellDataB5.hsideOK_B5_b4, GGResQTwoCellDataB5.hshapeNZ_B5_b4⟩⟩

theorem ggResQTwoFinite_B6 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 6 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.B 6 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨6, CartanMatrix.B 6, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.B6.pt_B6_b0, GGResIDisp.B6.hcyc_B6_b0,
      GGResIDisp.B6.shapes_B6_b0, GGResIDisp.B6.vecs_B6_b0,
      GGResIDisp.B6.hcand_B6_b0,
      GGResQTwoCellDataB6.wits_B6_b0, GGResQTwoCellDataB6.cell_B6_b0,
      GGResQTwoCellDataB6.hsideOK_B6_b0, GGResQTwoCellDataB6.hshapeNZ_B6_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2} 2 4
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3} 3 5
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨6, CartanMatrix.B 6, e, hCe, 5, hk, 0, by decide,
      GGResIDisp.B6.pt_B6_b5, GGResIDisp.B6.hcyc_B6_b5,
      GGResIDisp.B6.shapes_B6_b5, GGResIDisp.B6.vecs_B6_b5,
      GGResIDisp.B6.hcand_B6_b5,
      GGResQTwoCellDataB6.wits_B6_b5, GGResQTwoCellDataB6.cell_B6_b5,
      GGResQTwoCellDataB6.hsideOK_B6_b5, GGResQTwoCellDataB6.hshapeNZ_B6_b5⟩⟩

theorem ggResQTwoFinite_B7 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.B 7 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨7, CartanMatrix.B 7, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.B7.pt_B7_b0, GGResIDisp.B7.hcyc_B7_b0,
      GGResIDisp.B7.shapes_B7_b0, GGResIDisp.B7.vecs_B7_b0,
      GGResIDisp.B7.hcand_B7_b0,
      GGResQTwoCellDataB7.wits_B7_b0, GGResQTwoCellDataB7.cell_B7_b0,
      GGResQTwoCellDataB7.hsideOK_B7_b0, GGResQTwoCellDataB7.hshapeNZ_B7_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2} 2 4
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3} 3 5
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3, 4} 4 6
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨7, CartanMatrix.B 7, e, hCe, 6, hk, 0, by decide,
      GGResIDisp.B7.pt_B7_b6, GGResIDisp.B7.hcyc_B7_b6,
      GGResIDisp.B7.shapes_B7_b6, GGResIDisp.B7.vecs_B7_b6,
      GGResIDisp.B7.hcand_B7_b6,
      GGResQTwoCellDataB7.wits_B7_b6, GGResQTwoCellDataB7.cell_B7_b6,
      GGResQTwoCellDataB7.hsideOK_B7_b6, GGResQTwoCellDataB7.hshapeNZ_B7_b6⟩⟩

theorem ggResQTwoFinite_C3 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 3 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.C 3 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨3, CartanMatrix.C 3, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.C3.pt_C3_b0, GGResIDisp.C3.hcyc_C3_b0,
      GGResIDisp.C3.shapes_C3_b0, GGResIDisp.C3.vecs_C3_b0,
      GGResIDisp.C3.hcand_C3_b0,
      GGResQTwoCellDataC3.wits_C3_b0, GGResQTwoCellDataC3.cell_C3_b0,
      GGResQTwoCellDataC3.hsideOK_C3_b0, GGResQTwoCellDataC3.hshapeNZ_C3_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨3, CartanMatrix.C 3, e, hCe, 2, hk, 0, by decide,
      GGResIDisp.C3.pt_C3_b2, GGResIDisp.C3.hcyc_C3_b2,
      GGResIDisp.C3.shapes_C3_b2, GGResIDisp.C3.vecs_C3_b2,
      GGResIDisp.C3.hcand_C3_b2,
      GGResQTwoCellDataC3.wits_C3_b2, GGResQTwoCellDataC3.cell_C3_b2,
      GGResQTwoCellDataC3.hsideOK_C3_b2, GGResQTwoCellDataC3.hshapeNZ_C3_b2⟩⟩

theorem ggResQTwoFinite_C4 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 4 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.C 4 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨4, CartanMatrix.C 4, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.C4.pt_C4_b0, GGResIDisp.C4.hcyc_C4_b0,
      GGResIDisp.C4.shapes_C4_b0, GGResIDisp.C4.vecs_C4_b0,
      GGResIDisp.C4.hcand_C4_b0,
      GGResQTwoCellDataC4.wits_C4_b0, GGResQTwoCellDataC4.cell_C4_b0,
      GGResQTwoCellDataC4.hsideOK_C4_b0, GGResQTwoCellDataC4.hshapeNZ_C4_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨4, CartanMatrix.C 4, e, hCe, 3, hk, 0, by decide,
      GGResIDisp.C4.pt_C4_b3, GGResIDisp.C4.hcyc_C4_b3,
      GGResIDisp.C4.shapes_C4_b3, GGResIDisp.C4.vecs_C4_b3,
      GGResIDisp.C4.hcand_C4_b3,
      GGResQTwoCellDataC4.wits_C4_b3, GGResQTwoCellDataC4.cell_C4_b3,
      GGResQTwoCellDataC4.hsideOK_C4_b3, GGResQTwoCellDataC4.hshapeNZ_C4_b3⟩⟩

theorem ggResQTwoFinite_C5 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 5 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.C 5 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨5, CartanMatrix.C 5, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.C5.pt_C5_b0, GGResIDisp.C5.hcyc_C5_b0,
      GGResIDisp.C5.shapes_C5_b0, GGResIDisp.C5.vecs_C5_b0,
      GGResIDisp.C5.hcand_C5_b0,
      GGResQTwoCellDataC5.wits_C5_b0, GGResQTwoCellDataC5.cell_C5_b0,
      GGResQTwoCellDataC5.hsideOK_C5_b0, GGResQTwoCellDataC5.hshapeNZ_C5_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2} 2 4
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨5, CartanMatrix.C 5, e, hCe, 4, hk, 0, by decide,
      GGResIDisp.C5.pt_C5_b4, GGResIDisp.C5.hcyc_C5_b4,
      GGResIDisp.C5.shapes_C5_b4, GGResIDisp.C5.vecs_C5_b4,
      GGResIDisp.C5.hcand_C5_b4,
      GGResQTwoCellDataC5.wits_C5_b4, GGResQTwoCellDataC5.cell_C5_b4,
      GGResQTwoCellDataC5.hsideOK_C5_b4, GGResQTwoCellDataC5.hshapeNZ_C5_b4⟩⟩

theorem ggResQTwoFinite_C6 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 6 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.C 6 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨6, CartanMatrix.C 6, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.C6.pt_C6_b0, GGResIDisp.C6.hcyc_C6_b0,
      GGResIDisp.C6.shapes_C6_b0, GGResIDisp.C6.vecs_C6_b0,
      GGResIDisp.C6.hcand_C6_b0,
      GGResQTwoCellDataC6.wits_C6_b0, GGResQTwoCellDataC6.cell_C6_b0,
      GGResQTwoCellDataC6.hsideOK_C6_b0, GGResQTwoCellDataC6.hshapeNZ_C6_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2} 2 4
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3} 3 5
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨6, CartanMatrix.C 6, e, hCe, 5, hk, 0, by decide,
      GGResIDisp.C6.pt_C6_b5, GGResIDisp.C6.hcyc_C6_b5,
      GGResIDisp.C6.shapes_C6_b5, GGResIDisp.C6.vecs_C6_b5,
      GGResIDisp.C6.hcand_C6_b5,
      GGResQTwoCellDataC6.wits_C6_b5, GGResQTwoCellDataC6.cell_C6_b5,
      GGResQTwoCellDataC6.hsideOK_C6_b5, GGResQTwoCellDataC6.hshapeNZ_C6_b5⟩⟩

theorem ggResQTwoFinite_C7 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.C 7 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨7, CartanMatrix.C 7, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.C7.pt_C7_b0, GGResIDisp.C7.hcyc_C7_b0,
      GGResIDisp.C7.shapes_C7_b0, GGResIDisp.C7.vecs_C7_b0,
      GGResIDisp.C7.hcand_C7_b0,
      GGResQTwoCellDataC7.wits_C7_b0, GGResQTwoCellDataC7.cell_C7_b0,
      GGResQTwoCellDataC7.hsideOK_C7_b0, GGResQTwoCellDataC7.hshapeNZ_C7_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2} 2 4
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3} 3 5
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3, 4} 4 6
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨7, CartanMatrix.C 7, e, hCe, 6, hk, 0, by decide,
      GGResIDisp.C7.pt_C7_b6, GGResIDisp.C7.hcyc_C7_b6,
      GGResIDisp.C7.shapes_C7_b6, GGResIDisp.C7.vecs_C7_b6,
      GGResIDisp.C7.hcand_C7_b6,
      GGResQTwoCellDataC7.wits_C7_b6, GGResQTwoCellDataC7.cell_C7_b6,
      GGResQTwoCellDataC7.hsideOK_C7_b6, GGResQTwoCellDataC7.hshapeNZ_C7_b6⟩⟩

theorem ggResQTwoFinite_D4 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 4 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.D 4 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨4, CartanMatrix.D 4, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.D4.pt_D4_b0, GGResIDisp.D4.hcyc_D4_b0,
      GGResIDisp.D4.shapes_D4_b0, GGResIDisp.D4.vecs_D4_b0,
      GGResIDisp.D4.hcand_D4_b0,
      GGResQTwoCellDataD4.wits_D4_b0, GGResQTwoCellDataD4.cell_D4_b0,
      GGResQTwoCellDataD4.hsideOK_D4_b0, GGResQTwoCellDataD4.hshapeNZ_D4_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨4, CartanMatrix.D 4, e, hCe, 2, hk, 0, by decide,
      GGResIDisp.D4.pt_D4_b2, GGResIDisp.D4.hcyc_D4_b2,
      GGResIDisp.D4.shapes_D4_b2, GGResIDisp.D4.vecs_D4_b2,
      GGResIDisp.D4.hcand_D4_b2,
      GGResQTwoCellDataD4.wits_D4_b2, GGResQTwoCellDataD4.cell_D4_b2,
      GGResQTwoCellDataD4.hsideOK_D4_b2, GGResQTwoCellDataD4.hshapeNZ_D4_b2⟩⟩
  · exact ⟨⟨4, CartanMatrix.D 4, e, hCe, 3, hk, 0, by decide,
      GGResIDisp.D4.pt_D4_b3, GGResIDisp.D4.hcyc_D4_b3,
      GGResIDisp.D4.shapes_D4_b3, GGResIDisp.D4.vecs_D4_b3,
      GGResIDisp.D4.hcand_D4_b3,
      GGResQTwoCellDataD4.wits_D4_b3, GGResQTwoCellDataD4.cell_D4_b3,
      GGResQTwoCellDataD4.hsideOK_D4_b3, GGResQTwoCellDataD4.hshapeNZ_D4_b3⟩⟩

theorem ggResQTwoFinite_D5 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 5 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.D 5 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨5, CartanMatrix.D 5, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.D5.pt_D5_b0, GGResIDisp.D5.hcyc_D5_b0,
      GGResIDisp.D5.shapes_D5_b0, GGResIDisp.D5.vecs_D5_b0,
      GGResIDisp.D5.hcand_D5_b0,
      GGResQTwoCellDataD5.wits_D5_b0, GGResQTwoCellDataD5.cell_D5_b0,
      GGResQTwoCellDataD5.hsideOK_D5_b0, GGResQTwoCellDataD5.hshapeNZ_D5_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨5, CartanMatrix.D 5, e, hCe, 3, hk, 0, by decide,
      GGResIDisp.D5.pt_D5_b3, GGResIDisp.D5.hcyc_D5_b3,
      GGResIDisp.D5.shapes_D5_b3, GGResIDisp.D5.vecs_D5_b3,
      GGResIDisp.D5.hcand_D5_b3,
      GGResQTwoCellDataD5.wits_D5_b3, GGResQTwoCellDataD5.cell_D5_b3,
      GGResQTwoCellDataD5.hsideOK_D5_b3, GGResQTwoCellDataD5.hshapeNZ_D5_b3⟩⟩
  · exact ⟨⟨5, CartanMatrix.D 5, e, hCe, 4, hk, 0, by decide,
      GGResIDisp.D5.pt_D5_b4, GGResIDisp.D5.hcyc_D5_b4,
      GGResIDisp.D5.shapes_D5_b4, GGResIDisp.D5.vecs_D5_b4,
      GGResIDisp.D5.hcand_D5_b4,
      GGResQTwoCellDataD5.wits_D5_b4, GGResQTwoCellDataD5.cell_D5_b4,
      GGResQTwoCellDataD5.hsideOK_D5_b4, GGResQTwoCellDataD5.hshapeNZ_D5_b4⟩⟩

theorem ggResQTwoFinite_D6 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 6 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.D 6 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨6, CartanMatrix.D 6, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.D6.pt_D6_b0, GGResIDisp.D6.hcyc_D6_b0,
      GGResIDisp.D6.shapes_D6_b0, GGResIDisp.D6.vecs_D6_b0,
      GGResIDisp.D6.hcand_D6_b0,
      GGResQTwoCellDataD6.wits_D6_b0, GGResQTwoCellDataD6.cell_D6_b0,
      GGResQTwoCellDataD6.hsideOK_D6_b0, GGResQTwoCellDataD6.hshapeNZ_D6_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2} 2 4
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨6, CartanMatrix.D 6, e, hCe, 4, hk, 0, by decide,
      GGResIDisp.D6.pt_D6_b4, GGResIDisp.D6.hcyc_D6_b4,
      GGResIDisp.D6.shapes_D6_b4, GGResIDisp.D6.vecs_D6_b4,
      GGResIDisp.D6.hcand_D6_b4,
      GGResQTwoCellDataD6.wits_D6_b4, GGResQTwoCellDataD6.cell_D6_b4,
      GGResQTwoCellDataD6.hsideOK_D6_b4, GGResQTwoCellDataD6.hshapeNZ_D6_b4⟩⟩
  · exact ⟨⟨6, CartanMatrix.D 6, e, hCe, 5, hk, 0, by decide,
      GGResIDisp.D6.pt_D6_b5, GGResIDisp.D6.hcyc_D6_b5,
      GGResIDisp.D6.shapes_D6_b5, GGResIDisp.D6.vecs_D6_b5,
      GGResIDisp.D6.hcand_D6_b5,
      GGResQTwoCellDataD6.wits_D6_b5, GGResQTwoCellDataD6.cell_D6_b5,
      GGResQTwoCellDataD6.hsideOK_D6_b5, GGResQTwoCellDataD6.hshapeNZ_D6_b5⟩⟩

theorem ggResQTwoFinite_D7 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.D 7 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨7, CartanMatrix.D 7, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.D7.pt_D7_b0, GGResIDisp.D7.hcyc_D7_b0,
      GGResIDisp.D7.shapes_D7_b0, GGResIDisp.D7.vecs_D7_b0,
      GGResIDisp.D7.hcand_D7_b0,
      GGResQTwoCellDataD7.wits_D7_b0, GGResQTwoCellDataD7.cell_D7_b0,
      GGResQTwoCellDataD7.hsideOK_D7_b0, GGResQTwoCellDataD7.hshapeNZ_D7_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2} 2 4
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3} 3 5
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨7, CartanMatrix.D 7, e, hCe, 5, hk, 0, by decide,
      GGResIDisp.D7.pt_D7_b5, GGResIDisp.D7.hcyc_D7_b5,
      GGResIDisp.D7.shapes_D7_b5, GGResIDisp.D7.vecs_D7_b5,
      GGResIDisp.D7.hcand_D7_b5,
      GGResQTwoCellDataD7.wits_D7_b5, GGResQTwoCellDataD7.cell_D7_b5,
      GGResQTwoCellDataD7.hsideOK_D7_b5, GGResQTwoCellDataD7.hshapeNZ_D7_b5⟩⟩
  · exact ⟨⟨7, CartanMatrix.D 7, e, hCe, 6, hk, 0, by decide,
      GGResIDisp.D7.pt_D7_b6, GGResIDisp.D7.hcyc_D7_b6,
      GGResIDisp.D7.shapes_D7_b6, GGResIDisp.D7.vecs_D7_b6,
      GGResIDisp.D7.hcand_D7_b6,
      GGResQTwoCellDataD7.wits_D7_b6, GGResQTwoCellDataD7.cell_D7_b6,
      GGResQTwoCellDataD7.hsideOK_D7_b6, GGResQTwoCellDataD7.hshapeNZ_D7_b6⟩⟩

theorem ggResQTwoFinite_E6 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 6 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.E 6 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨6, CartanMatrix.E 6, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.E6.pt_E6_b0, GGResIDisp.E6.hcyc_E6_b0,
      GGResIDisp.E6.shapes_E6_b0, GGResIDisp.E6.vecs_E6_b0,
      GGResIDisp.E6.hcand_E6_b0,
      GGResQTwoCellDataE6.wits_E6_b0, GGResQTwoCellDataE6.cell_E6_b0,
      GGResQTwoCellDataE6.hsideOK_E6_b0, GGResQTwoCellDataE6.hshapeNZ_E6_b0⟩⟩
  · exact ⟨⟨6, CartanMatrix.E 6, e, hCe, 1, hk, 0, by decide,
      GGResIDisp.E6.pt_E6_b1, GGResIDisp.E6.hcyc_E6_b1,
      GGResIDisp.E6.shapes_E6_b1, GGResIDisp.E6.vecs_E6_b1,
      GGResIDisp.E6.hcand_E6_b1,
      GGResQTwoCellDataE6.wits_E6_b1, GGResQTwoCellDataE6.cell_E6_b1,
      GGResQTwoCellDataE6.hsideOK_E6_b1, GGResQTwoCellDataE6.hshapeNZ_E6_b1⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {1} 1 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3} 3 5
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨6, CartanMatrix.E 6, e, hCe, 5, hk, 0, by decide,
      GGResIDisp.E6.pt_E6_b5, GGResIDisp.E6.hcyc_E6_b5,
      GGResIDisp.E6.shapes_E6_b5, GGResIDisp.E6.vecs_E6_b5,
      GGResIDisp.E6.hcand_E6_b5,
      GGResQTwoCellDataE6.wits_E6_b5, GGResQTwoCellDataE6.cell_E6_b5,
      GGResQTwoCellDataE6.hsideOK_E6_b5, GGResQTwoCellDataE6.hshapeNZ_E6_b5⟩⟩

theorem ggResQTwoFinite_E7 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 7 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.E 7 i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨7, CartanMatrix.E 7, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.E7.pt_E7_b0, GGResIDisp.E7.hcyc_E7_b0,
      GGResIDisp.E7.shapes_E7_b0, GGResIDisp.E7.vecs_E7_b0,
      GGResIDisp.E7.hcand_E7_b0,
      GGResQTwoCellDataE7.wits_E7_b0, GGResQTwoCellDataE7.cell_E7_b0,
      GGResQTwoCellDataE7.hsideOK_E7_b0, GGResQTwoCellDataE7.hshapeNZ_E7_b0⟩⟩
  · exact ⟨⟨7, CartanMatrix.E 7, e, hCe, 1, hk, 0, by decide,
      GGResIDisp.E7.pt_E7_b1, GGResIDisp.E7.hcyc_E7_b1,
      GGResIDisp.E7.shapes_E7_b1, GGResIDisp.E7.vecs_E7_b1,
      GGResIDisp.E7.hcand_E7_b1,
      GGResQTwoCellDataE7.wits_E7_b1, GGResQTwoCellDataE7.cell_E7_b1,
      GGResQTwoCellDataE7.hsideOK_E7_b1, GGResQTwoCellDataE7.hshapeNZ_E7_b1⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {1} 1 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3} 3 5
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1, 2, 3, 4} 4 6
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨7, CartanMatrix.E 7, e, hCe, 6, hk, 0, by decide,
      GGResIDisp.E7.pt_E7_b6, GGResIDisp.E7.hcyc_E7_b6,
      GGResIDisp.E7.shapes_E7_b6, GGResIDisp.E7.vecs_E7_b6,
      GGResIDisp.E7.hcand_E7_b6,
      GGResQTwoCellDataE7.wits_E7_b6, GGResQTwoCellDataE7.cell_E7_b6,
      GGResQTwoCellDataE7.hsideOK_E7_b6, GGResQTwoCellDataE7.hshapeNZ_E7_b6⟩⟩

theorem ggResQTwoFinite_F4 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (e : Fin 4 ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = CartanMatrix.F₄ i j)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  obtain ⟨k, hk⟩ : ∃ k, e k = b := ⟨e.symm b, e.apply_symm_apply b⟩
  fin_cases k
  · exact ⟨⟨4, CartanMatrix.F₄, e, hCe, 0, hk, 1, by decide,
      GGResIDisp.F4.pt_F4_b0, GGResIDisp.F4.hcyc_F4_b0,
      GGResIDisp.F4.shapes_F4_b0, GGResIDisp.F4.vecs_F4_b0,
      GGResIDisp.F4.hcand_F4_b0,
      GGResQTwoCellDataF4.wits_F4_b0, GGResQTwoCellDataF4.cell_F4_b0,
      GGResQTwoCellDataF4.hsideOK_F4_b0, GGResQTwoCellDataF4.hshapeNZ_F4_b0⟩⟩
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0} 0 2
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exfalso
    exact ggResII_leaf_cut hCL hdel e hCe hk {0, 1} 1 3
      (by decide) (by decide) (by decide) (by decide)
      (by intro a ha c hc hcb; fin_cases a <;> fin_cases c <;> simp_all <;> decide)
  · exact ⟨⟨4, CartanMatrix.F₄, e, hCe, 3, hk, 0, by decide,
      GGResIDisp.F4.pt_F4_b3, GGResIDisp.F4.hcyc_F4_b3,
      GGResIDisp.F4.shapes_F4_b3, GGResIDisp.F4.vecs_F4_b3,
      GGResIDisp.F4.hcand_F4_b3,
      GGResQTwoCellDataF4.wits_F4_b3, GGResQTwoCellDataF4.cell_F4_b3,
      GGResQTwoCellDataF4.hsideOK_F4_b3, GGResQTwoCellDataF4.hshapeNZ_F4_b3⟩⟩

theorem ggResQTwoFinite_of_weyl
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hWL : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (h3 : 3 ≤ Nat.card Λ) (h8 : Nat.card Λ < 8)
    (hdel : GGDeletedConnected ML b) : Nonempty (GGResQTwoFinite b CL) := by
  classical
  have h3' : 3 ≤ Fintype.card Λ := by simpa [Nat.card_eq_fintype_card] using h3
  have h8' : Fintype.card Λ < 8 := by simpa [Nat.card_eq_fintype_card] using h8
  rcases ggIntCartan_models hWL hCL with
    ⟨n, e, _hn, hA | ⟨_hn2, hB | hC⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
      ⟨e, hF | hFt⟩ | ⟨e, _hG | _hGt⟩
  · have hcard : n = Fintype.card Λ := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    have hn3 : 3 ≤ n := by omega
    have hn8 : n < 8 := by omega
    interval_cases n
    · exact ggResQTwoFinite_A3 hCL e hA hdel
    · exact ggResQTwoFinite_A4 hCL e hA hdel
    · exact ggResQTwoFinite_A5 hCL e hA hdel
    · exact ggResQTwoFinite_A6 hCL e hA hdel
    · exact ggResQTwoFinite_A7 hCL e hA hdel
  · have hcard : n = Fintype.card Λ := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    have hn3 : 3 ≤ n := by omega
    have hn8 : n < 8 := by omega
    interval_cases n
    · exact ggResQTwoFinite_B3 hCL e hB hdel
    · exact ggResQTwoFinite_B4 hCL e hB hdel
    · exact ggResQTwoFinite_B5 hCL e hB hdel
    · exact ggResQTwoFinite_B6 hCL e hB hdel
    · exact ggResQTwoFinite_B7 hCL e hB hdel
  · have hcard : n = Fintype.card Λ := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    have hn3 : 3 ≤ n := by omega
    have hn8 : n < 8 := by omega
    interval_cases n
    · exact ggResQTwoFinite_C3 hCL e hC hdel
    · exact ggResQTwoFinite_C4 hCL e hC hdel
    · exact ggResQTwoFinite_C5 hCL e hC hdel
    · exact ggResQTwoFinite_C6 hCL e hC hdel
    · exact ggResQTwoFinite_C7 hCL e hC hdel
  · have hcard : n = Fintype.card Λ := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    have hnD : 4 ≤ n := hn4
    have hn8 : n < 8 := by omega
    interval_cases n
    · exact ggResQTwoFinite_D4 hCL e hD hdel
    · exact ggResQTwoFinite_D5 hCL e hD hdel
    · exact ggResQTwoFinite_D6 hCL e hD hdel
    · exact ggResQTwoFinite_D7 hCL e hD hdel
  · exact ggResQTwoFinite_E6 hCL e hE6 hdel
  · exact ggResQTwoFinite_E7 hCL e hE7 hdel
  · exfalso
    have hcard : Nat.card Λ = 8 := by
      rw [Nat.card_eq_fintype_card]
      simpa using (Fintype.card_congr e).symm
    omega
  · exact ggResQTwoFinite_F4 hCL e hF hdel
  · refine ggResQTwoFinite_F4 hCL (Fin.revPerm.trans e) ?_ hdel
    intro i j
    simp only [Equiv.trans_apply, Fin.revPerm_apply]
    rw [hFt, ggResI_F₄_rev]
  · exfalso
    have hcard : Nat.card Λ = 2 := by
      rw [Nat.card_eq_fintype_card]
      simpa using (Fintype.card_congr e).symm
    omega
  · exfalso
    have hcard : Nat.card Λ = 2 := by
      rw [Nat.card_eq_fintype_card]
      simpa using (Fintype.card_congr e).symm
    omega

theorem ggResQTwo_actual_family
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLD : GGResLeviDatum 3 Bs L J K ggSelI (ggTypRankLt 8))
    (hFork : ¬ GGCoxeterForkDatum 3 Bs L K)
    (hStd : ¬ GGCoxeterStdDatum 3 Bs L K)
    (hE6 : ¬ GGE6DepPerpCfg 3 Bs L K)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hFix : GGTBFixInput) (ha₀ : GGLNoncyclicInput) :
    GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8) GGResQTwoResidualCell ∨
      GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
  ggResQTwo_actual hH hLD hFork hStd hE6 hq hFix ha₀
    (fun b ML CL hWL hCL h3 h8 hdel => ggResQTwoFinite_of_weyl hWL hCL h3 h8 hdel)

section QTwoFamilyHolds


theorem ggResQTwo_actual_family_of_holds
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLD : GGResLeviDatum 3 Bs L J K ggSelI (ggTypRankLt 8))
    (hFork : ¬ GGCoxeterForkDatum 3 Bs L K)
    (hStd : ¬ GGCoxeterStdDatum 3 Bs L K)
    (hE6 : ¬ GGE6DepPerpCfg 3 Bs L K)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hFix : GGTBFixInput) :
    GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8) GGResQTwoResidualCell ∨
      GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
  ggResQTwo_actual_family hH hLD hFork hStd hE6 hq hFix ggLNoncyclicInput_holds

end QTwoFamilyHolds

end CFSG.StandardType
