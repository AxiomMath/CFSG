module

public import CFSG.Quasithin.Background.JonesParshallCurtisWeylInputs
public import CFSG.Quasithin.Background.JonesParshallCurtisGroup

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

namespace CertificateChecks.Batch17026

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

private theorem sM_eq_toMat_0 :  ∀ s, sM s = toMat (sB s)  := by
  decide +kernel

private theorem xM_eq_toMat_1 :  ∀ s, xM s = toMat (xB s)  := by
  decide +kernel

private theorem yM_eq_toMat_2 :  ∀ s, yM s = toMat (yB s)  := by
  decide +kernel

private theorem canW_cons_3 :  ∀ k : Fin 120, k ≠ 0 → canW k = headS k :: canW (tailIdx k)  := by
  decide +kernel

private theorem sE_mul_wE_bits_4 :  ∀ (s : Fin 4) (k : Fin 120),
    bmul (sB s) (bword (canW k)) = bword (canW (mulTab s k))  := by
  decide +kernel

private theorem wE_conj_bits_5 :  ∀ (k : Fin 120) (s : Fin 4),
    IsUpU (toMat (bmul (bmul (bword (canW k).reverse) (xB s)) (bword (canW k)))) ∨
      IsUpU (toMat (bmul (bmul (bword (canW k).reverse) (yB s)) (bword (canW k))))  := by
  decide +kernel

private theorem wE_tail_conj_bits_6 :  ∀ k : Fin 120, k ≠ 0 →
    IsUpU (toMat (bmul (bmul (bword (canW (tailIdx k)).reverse) (xB (headS k)))
      (bword (canW (tailIdx k)))))  := by
  decide +kernel

end CertificateChecks.Batch17026

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix in
theorem certificate17026 : (
 ∀ s, sM s = toMat (sB s) 
)
    ∧ (
 ∀ s, xM s = toMat (xB s) 
)
    ∧ (
 ∀ s, yM s = toMat (yB s) 
)
    ∧ (
 ∀ k : Fin 120, k ≠ 0 → canW k = headS k :: canW (tailIdx k) 
)
    ∧ (
 ∀ (s : Fin 4) (k : Fin 120),
    bmul (sB s) (bword (canW k)) = bword (canW (mulTab s k)) 
)
    ∧ (
 ∀ (k : Fin 120) (s : Fin 4),
    IsUpU (toMat (bmul (bmul (bword (canW k).reverse) (xB s)) (bword (canW k)))) ∨
      IsUpU (toMat (bmul (bmul (bword (canW k).reverse) (yB s)) (bword (canW k)))) 
)
    ∧ (
 ∀ k : Fin 120, k ≠ 0 →
    IsUpU (toMat (bmul (bmul (bword (canW (tailIdx k)).reverse) (xB (headS k)))
      (bword (canW (tailIdx k))))) 
) := by
  exact ⟨@CertificateChecks.Batch17026.sM_eq_toMat_0, @CertificateChecks.Batch17026.xM_eq_toMat_1, @CertificateChecks.Batch17026.yM_eq_toMat_2, @CertificateChecks.Batch17026.canW_cons_3, @CertificateChecks.Batch17026.sE_mul_wE_bits_4, @CertificateChecks.Batch17026.wE_conj_bits_5, @CertificateChecks.Batch17026.wE_tail_conj_bits_6⟩

end Certificates
