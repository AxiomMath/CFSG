module

public import Certificates.Certificate899110

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen

open CFSG.Quasithin.H13.MatNCert Matrix

@[ext] structure Form4 where
  mat : M4

instance : Finite Form4 := Finite.of_injective Form4.mat fun _ _ h => Form4.ext h

instance : MulAction GL4 Form4 where
  smul g w := ⟨(((g⁻¹ : GL4) : M4))ᵀ * w.mat * ((g⁻¹ : GL4) : M4)⟩
  one_smul w := by
    ext1
    show (((1⁻¹ : GL4) : M4))ᵀ * w.mat * ((1⁻¹ : GL4) : M4) = w.mat
    simp
  mul_smul g h w := by
    ext1
    show (((g * h)⁻¹ : GL4) : M4)ᵀ * w.mat * (((g * h)⁻¹ : GL4) : M4) =
      (((g⁻¹ : GL4) : M4))ᵀ * ((((h⁻¹ : GL4) : M4))ᵀ * w.mat * ((h⁻¹ : GL4) : M4)) *
        ((g⁻¹ : GL4) : M4)
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

theorem smul_mat4 (g : GL4) (w : Form4) :
    (g • w).mat = (((g⁻¹ : GL4) : M4))ᵀ * w.mat * ((g⁻¹ : GL4) : M4) := rfl

theorem inv_smul_mat4 (g : GL4) (w : Form4) :
    (g⁻¹ • w).mat = ((g : M4))ᵀ * w.mat * (g : M4) := by
  rw [smul_mat4, inv_inv]

@[expose] noncomputable def W0 : Form4 := ⟨decN 4 w0c4⟩

@[expose] noncomputable def Sbar : Subgroup GL4 := genSubN 4 sbGens4

theorem card_GL4 : Nat.card GL4 = 20160 := by
  rw [Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_succ]

theorem card_stab_mul4 : Nat.card (MulAction.stabilizer GL4 W0) *
    (MulAction.orbit GL4 W0).ncard = 20160 := by
  rw [← MulAction.index_stabilizer, Subgroup.card_mul_index, card_GL4]

section Max


theorem card_Sbar : Nat.card Sbar = 720 := Certificates.certificate899110.1

theorem stabilizer_eq4 :
    Sbar = MulAction.stabilizer GL4 W0 ∧ (MulAction.orbit GL4 W0).ncard = 28 := by
  have hst : Sbar = MulAction.stabilizer GL4 W0 := by
    ext g
    rw [← inv_mem_iff (H := MulAction.stabilizer GL4 W0), MulAction.mem_stabilizer_iff,
      Form4.ext_iff, inv_smul_mat4]
    exact Certificates.certificate899110.2.1 g
  refine ⟨hst, ?_⟩
  have h := card_stab_mul4
  rw [← hst, card_Sbar] at h
  omega

theorem sbar_le_stabilizer4 : Sbar ≤ MulAction.stabilizer GL4 W0 := stabilizer_eq4.1.le

theorem sbar_max4 {Z : Subgroup GL4} (hZ : Sbar ≤ Z) : Z = Sbar ∨ Z = ⊤ :=
  Certificates.certificate899110.2.2.1 Z hZ

end Max

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen
