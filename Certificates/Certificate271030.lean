module

public import CFSG.CGT.T75JM.L2FInputs
import Certificates.Kernel.T75JM.N0KGlue
import Certificates.Kernel.T75JM.L2KChecks
import Certificates.Kernel.T75JM.L2KDChecks
import Certificates.Kernel.T75JM.L2KFChecks
import CFSG.Certificates.Kernel.T75JM.L2KDSound
import CFSG.Certificates.Kernel.T75JM.L2KFSound
public import CFSG.CGT.T75JM.PData

public section

open CFSG.CGT.T75JM CFSG.KC.N0K

namespace Certificates

open CFSG.CosetTable CFSG.CGT.T75JM in
theorem certificate271030 : (tCheck = true) ∧ (bCheck = true) ∧
    (∀ n : PG 6 rels6, ∀ k < 16, ∃ l < 16, n * val6 (CFSG.CGT.T75JM.tw k) * n⁻¹ = val6 (CFSG.CGT.T75JM.tw l)) ∧
    (∀ x : PG 6 rels6, x * x = 1 → (∀ k < 16, x ≠ val6 (CFSG.CGT.T75JM.tw k)) →
      ∃ n : PG 6 rels6, n * val6 (bGen 0) * n⁻¹ = x) ∧
    (alphaRelCheck = true) ∧
    (∀ w w' : List (Fin 6 × Bool), val6 (substWord w) = val6 (substWord w') → val6 w = val6 w') ∧
    (alphaTCheck = true) ∧
    (∀ c : PG 6 rels6, c * c = 1 → c * val6 (bGen 0) = val6 (bGen 0) * c →
      (∀ k < 16, c ≠ val6 (CFSG.CGT.T75JM.tw k)) → (∀ k < 16, val6 (bGen 0) * c ≠ val6 (CFSG.CGT.T75JM.tw k)) →
      c ≠ val6 (bGen 0) →
      (∀ y : PG 6 rels6, (y * val6 (bGen 0) = val6 (bGen 0) * y ∨ y * c = c * y ∨
          y * (val6 (bGen 0) * c) = val6 (bGen 0) * c * y) →
        y * val6 (bGen 0) * y⁻¹ ∈ ({1, val6 (bGen 0), c, val6 (bGen 0) * c} : Set _) ∧
        y * c * y⁻¹ ∈ ({1, val6 (bGen 0), c, val6 (bGen 0) * c} : Set _) ∧
        y⁻¹ * val6 (bGen 0) * y ∈ ({1, val6 (bGen 0), c, val6 (bGen 0) * c} : Set _) ∧
        y⁻¹ * c * y ∈ ({1, val6 (bGen 0), c, val6 (bGen 0) * c} : Set _)) →
      ∃ n : PG 6 rels6,
        (n * val6 (bGen 0) * n⁻¹ ∈ ({1, val6 (bGen 0), c, val6 (bGen 0) * c} : Set _) ∧
          n * val6 (bGen 1) * n⁻¹ ∈ ({1, val6 (bGen 0), c, val6 (bGen 0) * c} : Set _)) ∨
        (n * val6 (substWord (bGen 0)) * n⁻¹ ∈
            ({1, val6 (bGen 0), c, val6 (bGen 0) * c} : Set _) ∧
          n * val6 (substWord (bGen 1)) * n⁻¹ ∈
            ({1, val6 (bGen 0), c, val6 (bGen 0) * c} : Set _))) := by
  refine ⟨tCheck_of letterRd_LP tK_ok, bCheck_of letterRd_LP bK_ok,
    normal_of letterRd_LP n0Inv_ok n0k_ok normalK_ok,
    inv_class_of letterRd_LP n0Inv_ok n0k_ok icK_ok, aRelCheck_of letterRd_LP aRelK_ok,
    alphaInj_of letterRd_LP n0Inv_ok n0k_ok alphaK_ok, aTCheck_of letterRd_LP aTK_ok,
    fun c hcc hcb hcT hbcT hcb0 hcent => ?_⟩
  have h := klein_of letterRd_LP n0Inv_ok n0k_ok klK_ok c hcc hcb hcT hbcT hcb0 fun y hy => by
    have e := hcent y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at e
    exact e
  simp only [S4, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact h

end Certificates
