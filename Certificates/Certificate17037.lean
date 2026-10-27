module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7FinInputs

public section

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.A5.Delta5 Equiv

namespace CertificateChecks.Batch17037

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.A5.Delta5 Equiv

private theorem dmul_0 :  ∀ x y : DihedralGroup 4, rmul (dtab x) (dtab y) = dtab (x * y)  := by
  decide +kernel

private theorem dtab_one_1 :  dtab 1 = rone  := by
  decide +kernel

private theorem dihedral4_pow_2 :  ∀ d : DihedralGroup 4, d ^ 4 = 1  := by
  decide +kernel

private theorem pmul_3 :  ∀ x y : Perm (Fin 4), rmul (ptab x) (ptab y) = ptab (x * y)  := by
  decide +kernel

private theorem ptab_one_4 :  ptab 1 = rone  := by
  decide +kernel

private theorem dpcomm_5 :  ∀ (d : DihedralGroup 4) (s : Perm (Fin 4)),
    rmul (dtab d) (ptab s) = rmul (ptab s) (dtab d)  := by
  decide +kernel

private theorem dtab_fix_6 :  ∀ d : DihedralGroup 4, pact (dtab d).2 g1 = g1 ∧ isEven (dtab d).1  := by
  decide +kernel

private theorem ptab_fix_7 :  ∀ s : Perm (Fin 4), pact (ptab s).2 g1 = g1 ∧ isEven (ptab s).1  := by
  decide +kernel

private theorem dp_kernel_8 :  ∀ (d : DihedralGroup 4) (s : Perm (Fin 4)),
    rmul (dtab d) (ptab s) = rone → d = 1 ∧ s = 1  := by
  decide +kernel

private theorem dp_cover_9 :  ∀ v : Fin 5 → ZMod 2, isEven v → ∀ σ : Perm (Fin 5), pact σ g1 = g1 →
    ∃ (d : DihedralGroup 4) (s : Perm (Fin 4)), rmul (dtab d) (ptab s) = (v, σ)  := by
  decide +kernel

private theorem fix_A4_10 :  ∀ v : Fin 5 → ZMod 2, isEven v →
    (∀ s : Perm (Fin 4), Perm.sign s = 1 → pact (ptab s).2 v = v) →
    v = 0 ∨ v = g1 ∨ v = gW1 ∨ v = gW1'  := by
  decide +kernel

private theorem fix_A4_mem_11 :  ∀ s : Perm (Fin 4), Perm.sign s = 1 →
    pact (ptab s).2 0 = 0 ∧ pact (ptab s).2 g1 = g1 ∧ pact (ptab s).2 gW1 = gW1 ∧
      pact (ptab s).2 gW1' = gW1'  := by
  decide +kernel

private theorem gW1_even_12 :  isEven gW1  := by
  decide +kernel

private theorem gW1'_even_13 :  isEven gW1'  := by
  decide +kernel

private theorem g1_ne_gW1_14 :  g1 ≠ gW1  := by
  decide +kernel

private theorem g1_ne_gW1'_15 :  g1 ≠ gW1'  := by
  decide +kernel

private theorem gW1_ne_gW1'_16 :  gW1 ≠ gW1'  := by
  decide +kernel

private theorem gW1_ne_zero_17 :  gW1 ≠ 0  := by
  decide +kernel

private theorem gW1'_ne_zero_18 :  gW1' ≠ 0  := by
  decide +kernel

private theorem g1_ne_zero'_19 :  g1 ≠ 0  := by
  decide +kernel

private theorem vecF_even_20 :  ∀ i, isEven (vecF i)  := by
  decide +kernel

private theorem vecF_mem_21 :  ∀ i, vecF i = 0 ∨ vecF i = g1 ∨ vecF i = gW1 ∨ vecF i = gW1'  := by
  decide +kernel

private theorem vecF_cover_22 :  ∀ v : Fin 5 → ZMod 2, (v = 0 ∨ v = g1 ∨ v = gW1 ∨ v = gW1') →
    ∃ i, vecF i = v  := by
  decide +kernel

private theorem vecF_inj_23 :  ∀ i j, vecF i = vecF j → i = j  := by
  decide +kernel

private theorem gW1_conj_z0_24 :  ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ pact σ z0 = gW1  := by
  decide +kernel

private theorem gW1'_conj_z0_25 :  ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ pact σ z0 = gW1'  := by
  decide +kernel

end CertificateChecks.Batch17037

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split Equiv in
theorem certificate17037 : (
 ∀ x y : DihedralGroup 4, rmul (dtab x) (dtab y) = dtab (x * y) 
)
    ∧ (
 dtab 1 = rone 
)
    ∧ (
 ∀ d : DihedralGroup 4, d ^ 4 = 1 
)
    ∧ (
 ∀ x y : Perm (Fin 4), rmul (ptab x) (ptab y) = ptab (x * y) 
)
    ∧ (
 ptab 1 = rone 
)
    ∧ (
 ∀ (d : DihedralGroup 4) (s : Perm (Fin 4)),
    rmul (dtab d) (ptab s) = rmul (ptab s) (dtab d) 
)
    ∧ (
 ∀ d : DihedralGroup 4, pact (dtab d).2 g1 = g1 ∧ isEven (dtab d).1 
)
    ∧ (
 ∀ s : Perm (Fin 4), pact (ptab s).2 g1 = g1 ∧ isEven (ptab s).1 
)
    ∧ (
 ∀ (d : DihedralGroup 4) (s : Perm (Fin 4)),
    rmul (dtab d) (ptab s) = rone → d = 1 ∧ s = 1 
)
    ∧ (
 ∀ v : Fin 5 → ZMod 2, isEven v → ∀ σ : Perm (Fin 5), pact σ g1 = g1 →
    ∃ (d : DihedralGroup 4) (s : Perm (Fin 4)), rmul (dtab d) (ptab s) = (v, σ) 
)
    ∧ (
 ∀ v : Fin 5 → ZMod 2, isEven v →
    (∀ s : Perm (Fin 4), Perm.sign s = 1 → pact (ptab s).2 v = v) →
    v = 0 ∨ v = g1 ∨ v = gW1 ∨ v = gW1' 
)
    ∧ (
 ∀ s : Perm (Fin 4), Perm.sign s = 1 →
    pact (ptab s).2 0 = 0 ∧ pact (ptab s).2 g1 = g1 ∧ pact (ptab s).2 gW1 = gW1 ∧
      pact (ptab s).2 gW1' = gW1' 
)
    ∧ (
 isEven gW1 
)
    ∧ (
 isEven gW1' 
)
    ∧ (
 g1 ≠ gW1 
)
    ∧ (
 g1 ≠ gW1' 
)
    ∧ (
 gW1 ≠ gW1' 
)
    ∧ (
 gW1 ≠ 0 
)
    ∧ (
 gW1' ≠ 0 
)
    ∧ (
 g1 ≠ 0 
)
    ∧ (
 ∀ i, isEven (vecF i) 
)
    ∧ (
 ∀ i, vecF i = 0 ∨ vecF i = g1 ∨ vecF i = gW1 ∨ vecF i = gW1' 
)
    ∧ (
 ∀ v : Fin 5 → ZMod 2, (v = 0 ∨ v = g1 ∨ v = gW1 ∨ v = gW1') →
    ∃ i, vecF i = v 
)
    ∧ (
 ∀ i j, vecF i = vecF j → i = j 
)
    ∧ (
 ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ pact σ z0 = gW1 
)
    ∧ (
 ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ pact σ z0 = gW1' 
) := by
  exact ⟨@CertificateChecks.Batch17037.dmul_0, @CertificateChecks.Batch17037.dtab_one_1, @CertificateChecks.Batch17037.dihedral4_pow_2, @CertificateChecks.Batch17037.pmul_3, @CertificateChecks.Batch17037.ptab_one_4, @CertificateChecks.Batch17037.dpcomm_5, @CertificateChecks.Batch17037.dtab_fix_6, @CertificateChecks.Batch17037.ptab_fix_7, @CertificateChecks.Batch17037.dp_kernel_8, @CertificateChecks.Batch17037.dp_cover_9, @CertificateChecks.Batch17037.fix_A4_10, @CertificateChecks.Batch17037.fix_A4_mem_11, @CertificateChecks.Batch17037.gW1_even_12, @CertificateChecks.Batch17037.gW1'_even_13, @CertificateChecks.Batch17037.g1_ne_gW1_14, @CertificateChecks.Batch17037.g1_ne_gW1'_15, @CertificateChecks.Batch17037.gW1_ne_gW1'_16, @CertificateChecks.Batch17037.gW1_ne_zero_17, @CertificateChecks.Batch17037.gW1'_ne_zero_18, @CertificateChecks.Batch17037.g1_ne_zero'_19, @CertificateChecks.Batch17037.vecF_even_20, @CertificateChecks.Batch17037.vecF_mem_21, @CertificateChecks.Batch17037.vecF_cover_22, @CertificateChecks.Batch17037.vecF_inj_23, @CertificateChecks.Batch17037.gW1_conj_z0_24, @CertificateChecks.Batch17037.gW1'_conj_z0_25⟩

end Certificates
