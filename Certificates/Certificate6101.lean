module

public import Certificates.Data.CFSGNative.Recognition.HSPinnedData
import Certificates.Kernel.HSPinned6101.Glue
import Certificates.Kernel.HSPinned6101.Srg
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic

public section

open CertificateChecks.KernelHSPinned6101

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.Recognition CFSG.Sporadic.Recognition.HSPinned in
open CFSG.Sporadic.Recognition.HSPinned.Native CFSG.Sporadic.HS.Native CFSG.Sporadic.SmallF2.Native in
theorem certificate6101 : (starsClosedOK (hsData.orbit ()).alpha (hsData.orbit ()).beta = true)
    ∧ (∀ i < 100, ∀ t ∈ stars[i]!, t < 1100)
    ∧ (∀ i < 100, ∀ j < 100, i = j ∨ ∃ x ∈ stars[i]!, x ∉ stars[j]!)
    ∧ (∀ i < 100, 0 < i →
      vtxPar[i]! < i ∧ ((vtxLab[i]! = 1 ∧ vtxA[vtxPar[i]!]! = i) ∨
        (vtxLab[i]! = 2 ∧ vtxB[vtxPar[i]!]! = i)))
    ∧ (∀ k < 20, wit[k]!.1 < 100 ∧ wit[k]!.2 < 100 ∧
      ∀ x < 1100, (x ∈ stars[wit[k]!.1]! ∧ x ∈ stars[wit[k]!.2]!) ↔ x = hsData.basis[k]!)
    ∧ (∀ x < 100, ∀ y < 100,
      adjB x y = true ↔ (x ≠ y ∧ ∃ t ∈ stars[x]!, t ∈ stars[y]!))
    ∧ (∀ x < 100, ∃ y < 100, adjB x y = true)
    ∧ (∀ v : Fin 100, (Finset.univ.filter fun w : Fin 100 => adjB v w = true).card =
      22)
    ∧ (∀ v w : Fin 100, adjB v w = true →
      (Finset.univ.filter fun z : Fin 100 => adjB v z = true ∧ adjB w z = true).card = 0)
    ∧ (∀ v w : Fin 100, v ≠ w → adjB v w = false →
      (Finset.univ.filter fun z : Fin 100 => adjB v z = true ∧ adjB w z = true).card = 6)
    ∧ (adjB 0 4 = true)
    ∧ (adjB 0 1 = false)
    ∧ ((Finset.univ.filter fun w : Fin 100 => w ≠ 0 ∧ adjB 0 w = false).card = 77)
    ∧ (pairOrbOK vtxA vtxB (pairCode 0 4) covAdj = true)
    ∧ (pairOrbOK vtxA vtxB (pairCode 0 1) covNon = true) :=
  ⟨starsClosed_check, stars_lt, stars_inj, tree_ok, wit_check, adj_spec, nbr_exists, srg_deg,
    srg_lam, srg_mu, adjB_zero_four, adjB_zero_one, card_non_nbrs, flagAdj_check,
    flagNon_check⟩

end Certificates
