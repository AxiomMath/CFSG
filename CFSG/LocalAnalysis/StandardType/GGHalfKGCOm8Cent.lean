module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCDefs
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFOm8
public import CFSG.GH74.GLS.Balance.SolvAPIDefs
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec19.Step1914E
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.Walter.J1Props
public import Certificates.Certificate8166

public section

namespace CFSG.StandardType

open CFSG.RankThree.PartTwo.Sec4.RonanK429F
open CFSG.RankThree.PartTwo.Sec4.RonanK429E
open Matrix

private abbrev ggHalfKGCOm8Cent_C : Subgroup Om8 :=
  Subgroup.centralizer ({Om8.y7} : Set Om8)

private abbrev ggHalfKGCOm8Cent_S : Subalgebra (ZMod 2) (Matrix Om8.ι6 Om8.ι6 (ZMod 2)) :=
  Algebra.adjoin (ZMod 2) ({Sp6.y0M} : Set (Matrix Om8.ι6 Om8.ι6 (ZMod 2)))

private lemma ggHalfKGCOm8Cent_hX {x : Om8} (hx : x ∈ ggHalfKGCOm8Cent_C) :
    Om8.matO x * Om8.emb Sp6.y0M = Om8.emb Sp6.y0M * Om8.matO x := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp hx
  rw [← Om8.matO_y7, ← map_mul, ← map_mul, h]

private lemma ggHalfKGCOm8Cent_bd {x : Om8} (hx : x ∈ ggHalfKGCOm8Cent_C) :
    IsBlockDiag (bl Om8.eO (Om8.matO x)) := by
  have hX := ggHalfKGCOm8Cent_hX hx
  have hE : Om8.matO x * (∑ i ∈ Finset.range 7, Om8.emb Sp6.y0M ^ i) =
      (∑ i ∈ Finset.range 7, Om8.emb Sp6.y0M ^ i) * Om8.matO x := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Commute.pow_right (show Commute (Om8.matO x) (Om8.emb Sp6.y0M) from hX) i).eq
  have hsum : bl Om8.eO (∑ i ∈ Finset.range 7, Om8.emb Sp6.y0M ^ i) = fromBlocks 0 0 0 1 := by
    decide +kernel
  exact isBlockDiag_of_commute (by rw [← hsum, ← bl_mul, ← bl_mul, hE])

private lemma ggHalfKGCOm8Cent_eq_fromBlocks {x : Om8} (hx : x ∈ ggHalfKGCOm8Cent_C) :
    bl Om8.eO (Om8.matO x) = fromBlocks (Om8.B6 x) 0 0 (Om8.B2 x) :=
  eq_fromBlocks_of_isBlockDiag (ggHalfKGCOm8Cent_bd hx)

private lemma ggHalfKGCOm8Cent_B6_commute {x : Om8} (hx : x ∈ ggHalfKGCOm8Cent_C) :
    Om8.B6 x * Sp6.y0M = Sp6.y0M * Om8.B6 x := by
  have h := bl_commute Om8.eO (ggHalfKGCOm8Cent_hX hx)
  rw [eq_fromBlocks_of_isBlockDiag (ggHalfKGCOm8Cent_bd hx), Om8.bl_emb,
      fromBlocks_diag_mul, fromBlocks_diag_mul] at h
  exact (fromBlocks_inj.mp h).1

private lemma ggHalfKGCOm8Cent_krylovPoly_mem_adjoin (w : Om8.ι6 → ZMod 2) :
    krylovPoly Sp6.y0M Sp6.kr6i Sp6.ex6 w ∈ ggHalfKGCOm8Cent_S := by
  rw [krylovPoly]
  refine Subalgebra.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
  exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton (R := ZMod 2) Sp6.y0M) _

private lemma ggHalfKGCOm8Cent_B6_mem {x : Om8} (hx : x ∈ ggHalfKGCOm8Cent_C) :
    Om8.B6 x ∈ ggHalfKGCOm8Cent_S := by
  have h6 := ggHalfKGCOm8Cent_B6_commute hx
  have heq := eq_krylovPoly_of_commute (kr := Sp6.kr6) (kr' := Sp6.kr6i) (v := Sp6.v6)
      (e := Sp6.ex6) (fun _ _ => rfl) Sp6.kr6i_mul_kr6 h6
  rw [heq]
  exact ggHalfKGCOm8Cent_krylovPoly_mem_adjoin _

private lemma ggHalfKGCOm8Cent_B6_mul_comm {x y : Om8}
    (hx : x ∈ ggHalfKGCOm8Cent_C) (hy : y ∈ ggHalfKGCOm8Cent_C) :
    Om8.B6 x * Om8.B6 y = Om8.B6 y * Om8.B6 x := by
  have hcomm := isMulCommutative_iff.mp
    (Algebra.isMulCommutative_adjoin_singleton (R := ZMod 2) Sp6.y0M)
  exact congrArg Subtype.val (hcomm ⟨Om8.B6 x, ggHalfKGCOm8Cent_B6_mem hx⟩
    ⟨Om8.B6 y, ggHalfKGCOm8Cent_B6_mem hy⟩)

private lemma ggHalfKGCOm8Cent_B2_mul {x y : Om8}
    (hx : x ∈ ggHalfKGCOm8Cent_C) (hy : y ∈ ggHalfKGCOm8Cent_C) :
    Om8.B2 (x * y) = Om8.B2 x * Om8.B2 y := by
  unfold Om8.B2
  rw [map_mul, bl_mul]
  exact IsBlockDiag.toBlocks₂₂_mul (ggHalfKGCOm8Cent_bd hx) (ggHalfKGCOm8Cent_bd hy)

private lemma ggHalfKGCOm8Cent_B2_mul_inv {x : Om8} (hx : x ∈ ggHalfKGCOm8Cent_C) :
    Om8.B2 x * Om8.B2 x⁻¹ = 1 := by
  rw [← ggHalfKGCOm8Cent_B2_mul hx (inv_mem hx), mul_inv_cancel, Om8.B2_one]

private lemma ggHalfKGCOm8Cent_B2_inv_mul {x : Om8} (hx : x ∈ ggHalfKGCOm8Cent_C) :
    Om8.B2 x⁻¹ * Om8.B2 x = 1 := by
  rw [← ggHalfKGCOm8Cent_B2_mul (inv_mem hx) hx, inv_mul_cancel, Om8.B2_one]

private noncomputable def ggHalfKGCOm8Cent_planeFun (x : ggHalfKGCOm8Cent_C) :
    GL (Fin 2) (ZMod 2) :=
  Units.mk (Om8.B2 (x : Om8)) (Om8.B2 ((x⁻¹ : ggHalfKGCOm8Cent_C) : Om8))
    (ggHalfKGCOm8Cent_B2_mul_inv x.2) (ggHalfKGCOm8Cent_B2_inv_mul x.2)

private noncomputable def ggHalfKGCOm8Cent_plane :
    ggHalfKGCOm8Cent_C →* GL (Fin 2) (ZMod 2) where
  toFun := ggHalfKGCOm8Cent_planeFun
  map_one' := by
    apply Units.ext
    change Om8.B2 (1 : Om8) = 1
    rw [Om8.B2_one]
  map_mul' := by
    intro x y
    apply Units.ext
    change Om8.B2 ((x : Om8) * (y : Om8)) = Om8.B2 (x : Om8) * Om8.B2 (y : Om8)
    rw [ggHalfKGCOm8Cent_B2_mul x.2 y.2]

private lemma ggHalfKGCOm8Cent_plane_ker_comm :
    ∀ a b : ggHalfKGCOm8Cent_plane.ker, a * b = b * a := by
  intro a b
  have ha2 : Om8.B2 (a : Om8) = 1 := by
    have h := congrArg Units.val (MonoidHom.mem_ker.mp a.2)
    simpa [ggHalfKGCOm8Cent_plane, ggHalfKGCOm8Cent_planeFun] using h
  have hb2 : Om8.B2 (b : Om8) = 1 := by
    have h := congrArg Units.val (MonoidHom.mem_ker.mp b.2)
    simpa [ggHalfKGCOm8Cent_plane, ggHalfKGCOm8Cent_planeFun] using h
  have hbda := ggHalfKGCOm8Cent_bd (x := (a : Om8)) a.1.2
  have hbdb := ggHalfKGCOm8Cent_bd (x := (b : Om8)) b.1.2
  apply Subtype.ext
  apply Subtype.ext
  change (a : Om8) * (b : Om8) = (b : Om8) * (a : Om8)
  apply Om8.matO_injective
  apply bl_injective Om8.eO
  rw [map_mul, map_mul, bl_mul, bl_mul,
      ggHalfKGCOm8Cent_eq_fromBlocks (x := (a : Om8)) a.1.2,
      ggHalfKGCOm8Cent_eq_fromBlocks (x := (b : Om8)) b.1.2,
      fromBlocks_diag_mul, fromBlocks_diag_mul, ha2, hb2]
  rw [ggHalfKGCOm8Cent_B6_mul_comm a.1.2 b.1.2]

private noncomputable def ggHalfKGCOm8Cent_glPerm :
    GL (Fin 2) (ZMod 2) →* Equiv.Perm (Fin 2 → ZMod 2) where
  toFun A := Equiv.ofBijective (fun v => (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ v)
    ⟨fun v w hvw => by
        have h := congrArg (fun u => ((A⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ u) hvw
        simp only [] at h
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h
        simpa using h,
     fun w => ⟨((A⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ w, by
        change (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
          (((A⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ w) = w
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩⟩
  map_one' := by
    ext v
    simp [Matrix.one_mulVec]
  map_mul' := by
    intro A B
    ext v i
    change ((↑(A * B) : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ v) i =
      ((↑A : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
        ((↑B : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ v)) i
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]

private lemma ggHalfKGCOm8Cent_glPerm_injective :
    Function.Injective ggHalfKGCOm8Cent_glPerm := by
  intro A B h
  apply Units.ext
  ext i j
  have h' := congrFun (congrArg (fun e : Equiv.Perm (Fin 2 → ZMod 2) => e (Pi.single j 1)) h) i
  change ((↑A : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ Pi.single j 1) i =
    ((↑B : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ Pi.single j 1) i at h'
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h'
  exact h'

private lemma ggHalfKGCOm8Cent_gl2_solvable : Group.IsSolvable (GL (Fin 2) (ZMod 2)) := by
  haveI : Group.IsSolvable (Equiv.Perm (Fin 2 → ZMod 2)) :=
    Equiv.Perm.isSolvable (by simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card])
  exact Group.isSolvable_of_isSolvable_injective
    (f := ggHalfKGCOm8Cent_glPerm) ggHalfKGCOm8Cent_glPerm_injective

theorem ggKGCOm8_cent_y7_solvable :
    Group.IsSolvable ↥(Subgroup.centralizer ({Om8.y7} : Set Om8)) := by
  show Group.IsSolvable ↥ggHalfKGCOm8Cent_C
  haveI : Group.IsSolvable ggHalfKGCOm8Cent_plane.ker :=
    isSolvable_of_comm ggHalfKGCOm8Cent_plane_ker_comm
  haveI : Group.IsSolvable (GL (Fin 2) (ZMod 2)) := ggHalfKGCOm8Cent_gl2_solvable
  haveI : Group.IsSolvable (ggHalfKGCOm8Cent_C ⧸ ggHalfKGCOm8Cent_plane.ker) :=
    Group.isSolvable_of_isSolvable_injective
      (f := QuotientGroup.kerLift ggHalfKGCOm8Cent_plane)
      (QuotientGroup.kerLift_injective ggHalfKGCOm8Cent_plane)
  exact Group.isSolvable_of_subgroup_quotient ggHalfKGCOm8Cent_plane.ker

end CFSG.StandardType

end
