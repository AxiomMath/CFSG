module

public import CFSG.RankThree.PartTwo.Notation
public import Certificates.Data.Kernel.M12Sig
import Certificates.Kernel.M12Sig.Checks
import Certificates.Kernel.M12Cent.Check
import CFSG.Certificates.Kernel.M12SigSound

public section

namespace Certificates

open CFSG CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo
  CFSG.KC.M12Sig CertificateChecks.KernelM12Sig CertificateChecks.KernelM12Cent
open scoped commutatorElement

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec4.Sporadic CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig CFSG.GH74.M12.Hyp
  CFSG.RankThree.PartTwo.Toolkit.M12 Subgroup in
open scoped commutatorElement in
theorem certificate8170 : invariantPiSubgroups ⊤ basisE.sub (CFSG.RankThree.PartTwo.piOf 2) = {⊥} ∧
    invariantPiSubgroups ⊤ basisF.sub (CFSG.RankThree.PartTwo.piOf 2) = {⊥} ∧
    (∀ i < 3, ∀ g : CFSG.GH74.M12.Hyp.G12, g * (⁅CFSG.RankThree.PartTwo.Toolkit.M12.x, y⁆ ^ i * (CFSG.RankThree.PartTwo.Toolkit.M12.x * y)) = ⁅CFSG.RankThree.PartTwo.Toolkit.M12.x, y⁆ ^ i * (CFSG.RankThree.PartTwo.Toolkit.M12.x * y) * g →
      ∃ k ∈ idxC i, tbl g.1 = CFSG.RankThree.PartTwo.Toolkit.M12.prodT k) ∧
    (∀ Y : Subgroup CFSG.GH74.M12.Hyp.G12, Y ∈ invariantPiSubgroups ⊤ basisA.sub (CFSG.RankThree.PartTwo.piOf 2) → Y ≠ ⊥ →
      ∃ i < 3, ∀ y ∈ Y, tbl y.1 ∈ CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig.VT i) ∧
    (∀ α : MulAut CFSG.GH74.M12.Hyp.G12, (∀ f ∈ basisA.sub, α f = f) →
      α ∈ (MulAut.conj : CFSG.GH74.M12.Hyp.G12 →* MulAut CFSG.GH74.M12.Hyp.G12).range) ∧
    chkNormal = true ∧ chkVStruct = true ∧ chkGamma = true ∧ CFSG.KC.M12Sig.centL = true := by
  have hz : Nat.card (Subgroup.centralizer ({⁅x, y⁆} : Set G12)) = 54 :=
    Sec4.Item434SporGen.card_centralizer_E (Subgroup.subset_closure (Set.mem_insert _ _)) z_ne_one
  have hcent : CFSG.KC.M12Cent.centCheck (tbl (⁅x, y⁆ : G12).1) D.S D.W D.C D.R = true := by
    rw [tbl_z, ← t_eq]
    exact cent_ok
  have hC := mem_C_of_facts card_normalizer_xy inv_ok xconj_ok centL_ok
  refine ⟨?_, ?_, hC, le_V_of_facts hz card_centralizer_basisA hC vstruct_ok vv_ok twoC_ok,
    inner_of_outerB outer_ok (cz_words (g := ⁅x, y⁆) (S := D.S) (W := D.W) (R := D.R) hcent),
    normal_ok, vstruct_ok, gamma_ok, centL_ok⟩
  · exact invariant_eq_bot_of_cent basisE
      (fun e he he1 => Sec4.Item434SporGen.card_centralizer_E he he1) card_centralizer_basisE
  · exact invariant_eq_bot_of_cent basisF
      (fun e he he1 => Sec4.Item434SporGen.card_centralizer_F he he1) card_centralizer_basisF

end Certificates
