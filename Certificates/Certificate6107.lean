module

public import CFSG.Sporadic.Recognition.McLMultiplierMats
import Certificates.Kernel.McLMult.Ident

public section

namespace Certificates

open CertificateChecks.KernelMcLMult

open CFSG.LieType.Multipliers CFSG.Sporadic.McL CFSG.Sporadic.Recognition.McLMultiplier in
theorem certificate6107 :
    ((∀ r ∈ mclRels, mclEvalY r = 1) ∧ (∀ i : Fin 6, mclEvalY (mclCommWord i) = mclY i) ∧
      mclEvalY mclSurjA = mA ∧ mclEvalY mclSurjB = mB) ∧
    (∀ i : Fin 6, PresentedGroup.mk (wordSet mclRels) (mclCommW i) = PresentedGroup.of i) ∧
    (Finite MclCover ∧ Nat.card MclCover ≤ 2694384000) ∧
    3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover) :=
  ⟨⟨mclEvalY_rels, mclEvalY_comm, mclEvalY_surjA, mclEvalY_surjB⟩, mk_mclCommW,
    card_mclCover_le, three_dvd_orderOf_mclR0⟩

end Certificates
