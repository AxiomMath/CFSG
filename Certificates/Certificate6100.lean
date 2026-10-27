module

public import CFSG.Sporadic.Recognition.HSGraphModelInputs
import Certificates.Kernel.HSGraph6100.Check
import CFSG.Certificates.Kernel.HSGraph6100Sound
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAutInputs
public import CFSG.Sporadic.Recognition.HSGraphStab

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.Recognition CFSG.Sporadic.Recognition.HSGraph
  CFSG.ComponentClassification.WittDesign CFSG.KC.HSGraph6100 CFSG.KC.HSIdent
  CertificateChecks.KernelHSGraph6100

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.Recognition CFSG.Sporadic.Recognition.HSGraph
  CFSG.ComponentClassification.WittDesign in
open scoped Pointwise in
theorem certificate6100 : (∀ v : Vert hexads, (hsGraph hexads).degree v = 22)
    ∧ (∀ v w : Vert hexads, (hsGraph hexads).Adj v w →
      Fintype.card ((hsGraph hexads).commonNeighbors v w) = 0)
    ∧ (∀ v w : Vert hexads, v ≠ w → ¬ (hsGraph hexads).Adj v w →
      Fintype.card ((hsGraph hexads).commonNeighbors v w) = 6)
    ∧ (∀ i j : Fin 100, modelVertAtF i = modelVertAtF j → i = j)
    ∧ (∀ i, psiInvFun (HSGraph.psiFun i) = i)
    ∧ (∀ i, HSGraph.psiFun (psiInvFun i) = i)
    ∧ (∀ i j : Fin 100,
      (hsGraph hexads).Adj (modelVertAtF (HSGraph.psiFun i)) (modelVertAtF (HSGraph.psiFun j)) ↔
        (hsGraph hexads).Adj (modelVertAtF i) (modelVertAtF j))
    ∧ (modelVertAtF (HSGraph.psiFun 0) = vPt 0)
    ∧ (modelVertAtF (HSGraph.psiFun 1) = vBlk (modelBlkAt 0))
    ∧ (∀ (σ : Equiv.Perm (Fin 22)) (hσ : σ ∈ blockAut hexads), ⇑σ = sigmaFun →
      Equiv.Perm.sign (extPerm (𝓑 := hexads) σ hσ) = -1) := by
  have hinj := modelVertAtF_injective_of distinct_ok
  obtain ⟨h1, h2, h3⟩ := srg_of hinj srg_ok
  have h8 : modelVertAtF (HSGraph.psiFun 0) = vPt 0 := modelVertAt_pt (k := 0) (by decide)
  have h9 : modelVertAtF (HSGraph.psiFun 1) = vBlk (modelBlkAt 0) := modelVertAt_blk 0
  exact ⟨h1, h2, h3, hinj, psiInv_left_ok, psiInv_right_ok, psi_check_of psi_ok, h8, h9,
    fun σ hσ hf => sign_extPerm_of σ hσ hf hinj sig_ok sigInv_ok sign_ok⟩

end Certificates
