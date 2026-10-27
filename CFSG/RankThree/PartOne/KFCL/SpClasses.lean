module

public import CFSG.RankThree.PartOne.KFCL.BlockSL
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KFCL.SpBlocks

public section

namespace CFSG.RankThree.PartOne.KFCL.Sp

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KFCL.BlockSL
open scoped MatrixGroups commutatorElement Classical

variable {K : Type} [Field K] {p : ℕ}

section Classes

variable (S : Subgroup (StatedSp 3 K))

@[expose] noncomputable def cls (a : Fin 3 ⊕ Fin 3) : ↥S → K := fun s => mat 3 K s.1 a a

variable {S}

theorem cls_par (hST : S ≤ spTorus p 3 K) (a : Fin 3 ⊕ Fin 3) : cls S (par a) = (cls S a)⁻¹ := by
  funext s
  exact spTorus_par (hST s.2) a

theorem cls_par_ne (hodd : Odd p) (hST : S ≤ spTorus p 3 K) {a : Fin 3 ⊕ Fin 3} (h : cls S a ≠ 1) :
    cls S (par a) ≠ cls S a := by
  intro hcontra
  apply h
  rw [cls_par hST] at hcontra
  funext s
  have h1 : (cls S a s)⁻¹ = cls S a s := congrFun hcontra s
  have h0 : cls S a s ≠ 0 := by
    intro h0
    have := spTorus_pow (hST s.2) a
    show False
    simp only [cls] at h0
    rw [h0, zero_pow (by intro hp0; subst hp0; simp at hodd)] at this
    exact zero_ne_one this
  have h2 : (cls S a s) ^ 2 = 1 := by
    field_simp at h1
    linear_combination -h1
  exact eq_one_of_sq_eq_one hodd (spTorus_pow (hST s.2) a) h2

theorem bd_of_mem_centralizer (hST : S ≤ spTorus p 3 K) {c : StatedSp 3 K}
    (hc : c ∈ Subgroup.centralizer (S : Set (StatedSp 3 K))) {a b : Fin 3 ⊕ Fin 3}
    (hab : cls S a ≠ cls S b) : mat 3 K c a b = 0 := by
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hab
  have hcomm : t.1 * c = c * t.1 := Subgroup.mem_centralizer_iff.1 hc t.1 t.2
  have hdiag : ∀ a b, a ≠ b → mat 3 K t.1 a b = 0 := fun a b h => spTorus_apply_ne (hST t.2) h
  have h1 := (commute_iff_entries hdiag).1 hcomm a b
  by_contra hne
  apply ht
  exact mul_right_cancel₀ hne (h1.trans (mul_comm _ _))

end Classes

section Blocks

variable (S : Subgroup (StatedSp 3 K))

@[expose] noncomputable def blkS (κ : ↥S → K) (g : StatedSp 3 K) : Matrix {a // cls S a = κ} {a // cls S a = κ} K :=
  blk1 (fun a => cls S a = κ) (mat 3 K g)

variable {S}

theorem blkS_apply (κ : ↥S → K) (g : StatedSp 3 K) (a b : {a // cls S a = κ}) :
    blkS S κ g a b = mat 3 K g a.1 b.1 := rfl

theorem blkS_mul (hST : S ≤ spTorus p 3 K) (κ : ↥S → K) {g : StatedSp 3 K}
    (hg : g ∈ Subgroup.centralizer (S : Set (StatedSp 3 K))) (h : StatedSp 3 K) :
    blkS S κ (g * h) = blkS S κ g * blkS S κ h := by
  unfold blkS
  rw [map_mul]
  exact blk1_mul (fun a => cls S a = κ) (mat 3 K g) (mat 3 K h) (fun a b ha hb =>
    bd_of_mem_centralizer hST hg (fun hab => hb (hab.symm.trans ha)))

theorem blkS_one (κ : ↥S → K) : blkS S κ (1 : StatedSp 3 K) = 1 := by
  classical
  unfold blkS
  rw [map_one]
  ext a b
  simp [blk1, Matrix.submatrix_apply, Matrix.one_apply, Subtype.ext_iff]

theorem blkS_inv (hST : S ≤ spTorus p 3 K) (κ : ↥S → K) {g : StatedSp 3 K}
    (hg : g ∈ Subgroup.centralizer (S : Set (StatedSp 3 K))) :
    blkS S κ g⁻¹ = (blkS S κ g)⁻¹ := by
  have h1 : blkS S κ g * blkS S κ g⁻¹ = 1 := by
    rw [← blkS_mul hST κ hg, mul_inv_cancel, blkS_one]
  exact (Matrix.inv_eq_right_inv h1).symm

theorem blkS_inv_eq_one (hST : S ≤ spTorus p 3 K) (κ : ↥S → K) {g : StatedSp 3 K}
    (hg : g ∈ Subgroup.centralizer (S : Set (StatedSp 3 K))) (h1 : blkS S κ g = 1) :
    blkS S κ⁻¹ g = 1 := by
  classical
  have h2 : blkS S κ g⁻¹ = 1 := by rw [blkS_inv hST κ hg, h1, inv_one]
  ext a b
  have hpa : cls S (par a.1) = κ := by
    rw [cls_par hST, a.2, inv_inv]
  have hpb : cls S (par b.1) = κ := by
    rw [cls_par hST, b.2, inv_inv]
  have e1 : mat 3 K g⁻¹ (par b.1) (par a.1) = (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (par b.1) (par a.1) := by
    have := congrFun (congrFun h2 ⟨par b.1, hpb⟩) ⟨par a.1, hpa⟩
    simpa [blkS_apply, Matrix.one_apply] using this
  have e2 : mat 3 K g a.1 b.1 = sgn K a.1 * sgn K b.1 * mat 3 K g⁻¹ (par b.1) (par a.1) := by
    have := mat_inv_apply (K := K) g⁻¹ a.1 b.1
    rwa [inv_inv] at this
  rw [blkS_apply, e2, e1]
  by_cases hab : a.1 = b.1
  · have : a = b := Subtype.ext hab
    subst this
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one]
    rcases a with ⟨x, hx⟩
    rcases x with i | i <;> simp [sgn]
  · have h3 : (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (par b.1) (par a.1) = 0 :=
      Matrix.one_apply_ne (fun h => hab (par_injective h).symm)
    have h4 : (1 : Matrix {x // cls S x = κ⁻¹} {x // cls S x = κ⁻¹} K) a b = 0 :=
      Matrix.one_apply_ne (fun h => hab (congrArg Subtype.val h))
    rw [h3, h4, mul_zero]

@[expose] noncomputable def detBlk (κ : ↥S → K) (g : StatedSp 3 K) : K := (blkS S κ g).det

theorem detBlk_mul_inv (hST : S ≤ spTorus p 3 K) (κ : ↥S → K) {g : StatedSp 3 K}
    (hg : g ∈ Subgroup.centralizer (S : Set (StatedSp 3 K))) :
    detBlk κ g * detBlk κ g⁻¹ = 1 := by
  unfold detBlk
  rw [← Matrix.det_mul, ← blkS_mul hST κ hg, mul_inv_cancel, blkS_one, Matrix.det_one]

theorem detBlk_commutator (hST : S ≤ spTorus p 3 K) (κ : ↥S → K) {x y : StatedSp 3 K}
    (hx : x ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)))
    (hy : y ∈ Subgroup.centralizer (S : Set (StatedSp 3 K))) : detBlk κ ⁅x, y⁆ = 1 := by
  have hxy : x * y ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)) := Subgroup.mul_mem _ hx hy
  have hxyx : x * y * x⁻¹ ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)) :=
    Subgroup.mul_mem _ hxy (Subgroup.inv_mem _ hx)
  have e : detBlk κ ⁅x, y⁆ = detBlk κ x * detBlk κ y * detBlk κ x⁻¹ * detBlk κ y⁻¹ := by
    unfold detBlk
    rw [commutatorElement_def, blkS_mul hST κ hxyx, blkS_mul hST κ hxy, blkS_mul hST κ hx]
    simp only [Matrix.det_mul]
  rw [e]
  have h1 := detBlk_mul_inv hST κ hx
  have h2 := detBlk_mul_inv hST κ hy
  calc detBlk κ x * detBlk κ y * detBlk κ x⁻¹ * detBlk κ y⁻¹ =
      (detBlk κ x * detBlk κ x⁻¹) * (detBlk κ y * detBlk κ y⁻¹) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

end Blocks

end CFSG.RankThree.PartOne.KFCL.Sp
