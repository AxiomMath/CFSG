module

public import CFSG.Quasithin.Background.JonesParshallCurtisGroupInputs
public import CFSG.Quasithin.Background.JonesParshallBasic

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

namespace CertificateChecks.Batch17000

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

private theorem xE_mul_self_0 :  ∀ s, xE s * xE s = 1  := by
  decide +kernel

private theorem yE_mul_self_1 :  ∀ s, yE s * yE s = 1  := by
  decide +kernel

private theorem sE_mul_self_2 :  ∀ s, sE s * sE s = 1  := by
  decide +kernel

private theorem sE_eq_yxy_3 :  ∀ s, sE s = yE s * xE s * yE s  := by
  decide +kernel

private theorem xE_mul_yE_4 :  ∀ s, xE s * yE s = yE s * sE s  := by
  decide +kernel

private theorem xE_eq_ysy_5 :  ∀ s, xE s = yE s * sE s * yE s  := by
  decide +kernel

private theorem xE_upU_6 :  ∀ s, IsUpU (xE s : Matrix (Fin 5) (Fin 5) (ZMod 2))  := by
  decide +kernel

private theorem yE_loU_7 :  ∀ s, IsLoU (yE s : Matrix (Fin 5) (Fin 5) (ZMod 2))  := by
  decide +kernel

private theorem root_comm_8 :  ∀ s t : Fin 4, (s.val + 2 ≤ t.val ∨ t.val + 2 ≤ s.val) →
    xE s * xE t = xE t * xE s ∧ xE s * yE t = yE t * xE s ∧ yE s * xE t = xE t * yE s ∧
      yE s * yE t = yE t * yE s  := by
  decide +kernel

private theorem xM_transpose_9 :  ∀ s, (xM s)ᵀ = yM s  := by
  decide +kernel

private theorem yM_transpose_10 :  ∀ s, (yM s)ᵀ = xM s  := by
  decide +kernel

private theorem Qs_conj_x0_11 :  ∀ c1 c2 c3 c4 c5 c6 c7 c8 c9 : ZMod 2,
    IsQs 0 (xM 0 * upMat 0 c1 c2 c3 c4 c5 c6 c7 c8 c9 * xM 0)  := by
  decide +kernel

private theorem Qs_conj_y0_12 :  ∀ c1 c2 c3 c4 c5 c6 c7 c8 c9 : ZMod 2,
    IsQs 0 (yM 0 * upMat 0 c1 c2 c3 c4 c5 c6 c7 c8 c9 * yM 0)  := by
  decide +kernel

private theorem Qs_conj_x1_13 :  ∀ c0 c1 c2 c3 c5 c6 c7 c8 c9 : ZMod 2,
    IsQs 1 (xM 1 * upMat c0 c1 c2 c3 0 c5 c6 c7 c8 c9 * xM 1)  := by
  decide +kernel

private theorem Qs_conj_y1_14 :  ∀ c0 c1 c2 c3 c5 c6 c7 c8 c9 : ZMod 2,
    IsQs 1 (yM 1 * upMat c0 c1 c2 c3 0 c5 c6 c7 c8 c9 * yM 1)  := by
  decide +kernel

private theorem Qs_conj_x2_15 :  ∀ c0 c1 c2 c3 c4 c5 c6 c8 c9 : ZMod 2,
    IsQs 2 (xM 2 * upMat c0 c1 c2 c3 c4 c5 c6 0 c8 c9 * xM 2)  := by
  decide +kernel

private theorem Qs_conj_y2_16 :  ∀ c0 c1 c2 c3 c4 c5 c6 c8 c9 : ZMod 2,
    IsQs 2 (yM 2 * upMat c0 c1 c2 c3 c4 c5 c6 0 c8 c9 * yM 2)  := by
  decide +kernel

private theorem Qs_conj_x3_17 :  ∀ c0 c1 c2 c3 c4 c5 c6 c7 c8 : ZMod 2,
    IsQs 3 (xM 3 * upMat c0 c1 c2 c3 c4 c5 c6 c7 c8 0 * xM 3)  := by
  decide +kernel

private theorem Qs_conj_y3_18 :  ∀ c0 c1 c2 c3 c4 c5 c6 c7 c8 : ZMod 2,
    IsQs 3 (yM 3 * upMat c0 c1 c2 c3 c4 c5 c6 c7 c8 0 * yM 3)  := by
  decide +kernel

end CertificateChecks.Batch17000

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix in
theorem certificate17000 : (
 ∀ s, xE s * xE s = 1 
)
    ∧ (
 ∀ s, yE s * yE s = 1 
)
    ∧ (
 ∀ s, sE s * sE s = 1 
)
    ∧ (
 ∀ s, sE s = yE s * xE s * yE s 
)
    ∧ (
 ∀ s, xE s * yE s = yE s * sE s 
)
    ∧ (
 ∀ s, xE s = yE s * sE s * yE s 
)
    ∧ (
 ∀ s, IsUpU (xE s : Matrix (Fin 5) (Fin 5) (ZMod 2)) 
)
    ∧ (
 ∀ s, IsLoU (yE s : Matrix (Fin 5) (Fin 5) (ZMod 2)) 
)
    ∧ (
 ∀ s t : Fin 4, (s.val + 2 ≤ t.val ∨ t.val + 2 ≤ s.val) →
    xE s * xE t = xE t * xE s ∧ xE s * yE t = yE t * xE s ∧ yE s * xE t = xE t * yE s ∧
      yE s * yE t = yE t * yE s 
)
    ∧ (
 ∀ s, (xM s)ᵀ = yM s 
)
    ∧ (
 ∀ s, (yM s)ᵀ = xM s 
)
    ∧ (
 ∀ c1 c2 c3 c4 c5 c6 c7 c8 c9 : ZMod 2,
    IsQs 0 (xM 0 * upMat 0 c1 c2 c3 c4 c5 c6 c7 c8 c9 * xM 0) 
)
    ∧ (
 ∀ c1 c2 c3 c4 c5 c6 c7 c8 c9 : ZMod 2,
    IsQs 0 (yM 0 * upMat 0 c1 c2 c3 c4 c5 c6 c7 c8 c9 * yM 0) 
)
    ∧ (
 ∀ c0 c1 c2 c3 c5 c6 c7 c8 c9 : ZMod 2,
    IsQs 1 (xM 1 * upMat c0 c1 c2 c3 0 c5 c6 c7 c8 c9 * xM 1) 
)
    ∧ (
 ∀ c0 c1 c2 c3 c5 c6 c7 c8 c9 : ZMod 2,
    IsQs 1 (yM 1 * upMat c0 c1 c2 c3 0 c5 c6 c7 c8 c9 * yM 1) 
)
    ∧ (
 ∀ c0 c1 c2 c3 c4 c5 c6 c8 c9 : ZMod 2,
    IsQs 2 (xM 2 * upMat c0 c1 c2 c3 c4 c5 c6 0 c8 c9 * xM 2) 
)
    ∧ (
 ∀ c0 c1 c2 c3 c4 c5 c6 c8 c9 : ZMod 2,
    IsQs 2 (yM 2 * upMat c0 c1 c2 c3 c4 c5 c6 0 c8 c9 * yM 2) 
)
    ∧ (
 ∀ c0 c1 c2 c3 c4 c5 c6 c7 c8 : ZMod 2,
    IsQs 3 (xM 3 * upMat c0 c1 c2 c3 c4 c5 c6 c7 c8 0 * xM 3) 
)
    ∧ (
 ∀ c0 c1 c2 c3 c4 c5 c6 c7 c8 : ZMod 2,
    IsQs 3 (yM 3 * upMat c0 c1 c2 c3 c4 c5 c6 c7 c8 0 * yM 3) 
) := by
  exact ⟨@CertificateChecks.Batch17000.xE_mul_self_0, @CertificateChecks.Batch17000.yE_mul_self_1, @CertificateChecks.Batch17000.sE_mul_self_2, @CertificateChecks.Batch17000.sE_eq_yxy_3, @CertificateChecks.Batch17000.xE_mul_yE_4, @CertificateChecks.Batch17000.xE_eq_ysy_5, @CertificateChecks.Batch17000.xE_upU_6, @CertificateChecks.Batch17000.yE_loU_7, @CertificateChecks.Batch17000.root_comm_8, @CertificateChecks.Batch17000.xM_transpose_9, @CertificateChecks.Batch17000.yM_transpose_10, @CertificateChecks.Batch17000.Qs_conj_x0_11, @CertificateChecks.Batch17000.Qs_conj_y0_12, @CertificateChecks.Batch17000.Qs_conj_x1_13, @CertificateChecks.Batch17000.Qs_conj_y1_14, @CertificateChecks.Batch17000.Qs_conj_x2_15, @CertificateChecks.Batch17000.Qs_conj_y2_16, @CertificateChecks.Batch17000.Qs_conj_x3_17, @CertificateChecks.Batch17000.Qs_conj_y3_18⟩

end Certificates
