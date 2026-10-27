module

public import CFSG.Sporadic.Co1.Cover.Fox
public import CFSG.Certificates.Kernel.F2RowsSound

public section

namespace CertificateChecks.KernelCo1Cover

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.SmallF2 Matrix CFSG.KC.F2Rows

abbrev e66 : Fin 6 × Fin 11 ≃ Fin (6 * 11) := finProdFinEquiv

abbrev e121 : I2 ≃ Fin (11 * 11) := finProdFinEquiv

theorem fox_rows :
    addR (11 + 11) (addR (11 + 11)
        (mulR 11 (rowsOf (Equiv.refl _) (Equiv.refl _) (deltaMat Amat Bmat))
          (rowsOf (Equiv.refl _) (Equiv.refl _) (listMat foxXrows 11 (11 + 11))))
        (mulR (6 * 11) (rowsOf (Equiv.refl _) e66 yMat) (rowsOf e66 (Equiv.refl _) foxMatC)))
      (mulR 1 (rowsOf (Equiv.refl _) (Equiv.refl _) zMat)
        (rowsOf (Equiv.refl _) (Equiv.refl _) (lamMat (toVecD 11 x0mask)))) = idR (11 + 11) := by
  decide +kernel

theorem fox_cert :
    deltaMat Amat Bmat * listMat foxXrows 11 (11 + 11) +
      yMat * foxMatC + zMat * lamMat (toVecD 11 x0mask) = 1 := by
  rw [← bitMat_rowsOf (Equiv.refl _) (Equiv.refl _) (deltaMat Amat Bmat),
    ← bitMat_rowsOf (Equiv.refl _) (Equiv.refl _) (listMat foxXrows 11 (11 + 11)),
    ← bitMat_rowsOf (Equiv.refl _) e66 yMat, ← bitMat_rowsOf e66 (Equiv.refl _) foxMatC,
    ← bitMat_rowsOf (Equiv.refl _) (Equiv.refl _) zMat,
    ← bitMat_rowsOf (Equiv.refl _) (Equiv.refl _) (lamMat (toVecD 11 x0mask)),
    bitMat_mul, bitMat_mul, bitMat_mul, bitMat_add, bitMat_add, fox_rows, bitMat_idR]

theorem hl_cert :
    listMat clX1 11 11 * (Amatᵀ - 1) + listMat clX2 11 11 * (Bmatᵀ - 1) = 1 := by
  decide +kernel

theorem hC_rows :
    addR (11 * 11) (addR (11 * 11) (addR (11 * 11)
        (mulR (11 * 11) (rowsOf e121 e121 (bigMat cSsym)) (rowsOf e121 e121 Rsym))
        (mulR (11 * 11) (rowsOf e121 e121 (bigMat cSdiag)) (rowsOf e121 e121 Rdiag)))
        (mulR (11 * 11) (rowsOf e121 e121 (bigMat cSA)) (rowsOf e121 e121 (Rinv Amat))))
      (mulR (11 * 11) (rowsOf e121 e121 (bigMat cSB)) (rowsOf e121 e121 (Rinv Bmat))) =
      idR (11 * 11) := by
  decide +kernel

theorem hC_cert :
    bigMat cSsym * Rsym + bigMat cSdiag * Rdiag + bigMat cSA * Rinv Amat +
      bigMat cSB * Rinv Bmat = 1 := by
  rw [← bitMat_rowsOf e121 e121 (bigMat cSsym), ← bitMat_rowsOf e121 e121 Rsym,
    ← bitMat_rowsOf e121 e121 (bigMat cSdiag), ← bitMat_rowsOf e121 e121 Rdiag,
    ← bitMat_rowsOf e121 e121 (bigMat cSA), ← bitMat_rowsOf e121 e121 (Rinv Amat),
    ← bitMat_rowsOf e121 e121 (bigMat cSB), ← bitMat_rowsOf e121 e121 (Rinv Bmat),
    bitMat_mul, bitMat_mul, bitMat_mul, bitMat_mul, bitMat_add, bitMat_add, bitMat_add, hC_rows,
    bitMat_idR]

theorem neg10060 :
    (addR (11 + 11) (addR (11 + 11)
        (mulR 11 (rowsOf (Equiv.refl _) (Equiv.refl _) (deltaMat Bmat Amat))
          (rowsOf (Equiv.refl _) (Equiv.refl _) (listMat foxXrows 11 (11 + 11))))
        (mulR (6 * 11) (rowsOf (Equiv.refl _) e66 yMat) (rowsOf e66 (Equiv.refl _) foxMatC)))
      (mulR 1 (rowsOf (Equiv.refl _) (Equiv.refl _) zMat)
        (rowsOf (Equiv.refl _) (Equiv.refl _) (lamMat (toVecD 11 x0mask)))) ≠ idR (11 + 11)) ∧
    (addR (11 + 11) (addR (11 + 11)
        (mulR 11 (rowsOf (Equiv.refl _) (Equiv.refl _) (deltaMat Amat Bmat))
          (rowsOf (Equiv.refl _) (Equiv.refl _) (listMat foxXrows 11 (11 + 11))))
        (mulR (6 * 11) (rowsOf (Equiv.refl _) e66 yMat) (rowsOf e66 (Equiv.refl _) foxMatC)))
      (mulR 1 (rowsOf (Equiv.refl _) (Equiv.refl _) zMat)
        (rowsOf (Equiv.refl _) (Equiv.refl _) (lamMat (toVecD 11 (x0mask ^^^ 1))))) ≠
        idR (11 + 11)) ∧
    (addR (11 * 11) (addR (11 * 11) (addR (11 * 11)
        (mulR (11 * 11) (rowsOf e121 e121 (bigMat cSsym)) (rowsOf e121 e121 Rsym))
        (mulR (11 * 11) (rowsOf e121 e121 (bigMat cSdiag)) (rowsOf e121 e121 Rdiag)))
        (mulR (11 * 11) (rowsOf e121 e121 (bigMat cSB)) (rowsOf e121 e121 (Rinv Amat))))
      (mulR (11 * 11) (rowsOf e121 e121 (bigMat cSA)) (rowsOf e121 e121 (Rinv Bmat))) ≠
      idR (11 * 11)) := by
  decide +kernel

theorem Amat_x0 : Amat *ᵥ toVecD 11 x0mask = toVecD 11 x0mask := by
  decide +kernel

open Certificates in
open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.SmallF2 Matrix in
theorem facts10060 :
    (deltaMat Amat Bmat * listMat foxXrows 11 (11 + 11) +
      yMat * foxMatC + zMat * lamMat (toVecD 11 x0mask) = 1)
    ∧ (listMat clX1 11 11 * (Amatᵀ - 1) + listMat clX2 11 11 * (Bmatᵀ - 1) = 1)
    ∧ (bigMat cSsym * Rsym + bigMat cSdiag * Rdiag + bigMat cSA * Rinv Amat +
      bigMat cSB * Rinv Bmat = 1)
    ∧ (Amat *ᵥ toVecD 11 x0mask = toVecD 11 x0mask) :=
  ⟨fox_cert, hl_cert, hC_cert, Amat_x0⟩

end CertificateChecks.KernelCo1Cover

end
