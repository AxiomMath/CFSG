module

public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
import Certificates.Kernel.Sporadic.M22Alt.Bridge
import CFSG.Sporadic.Schreier.ClassSum
public meta import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.ImagePairs

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu in
open CFSG.Sporadic.Schreier.Native in
theorem certificate2195 : (m22Certificate.check = true)
    ∧ (ordTest 22 2 (toTable m22gA) = true ∧ ordTest 22 4 (toTable m22gB) = true ∧
      pairTest 22 11 6 2 4 (toTable m22gA) (toTable m22gB) = true
    )
    ∧ ((orderTables m22Certificate 2).length = 1155 ∧
      (orderTables m22Certificate 4).length = 41580
    )
    ∧ (pairCount (orderTables m22Certificate 2) (orderTables m22Certificate 4)
      (pairTest 22 11 6 2 4) = 1774080
    ) := by
  obtain ⟨h1, h2, h3, hok, htot⟩ := KernelSpor.M22Alt.counts
  have hQ : ValidSchreier m22Certificate := h1
  have hH : m22Certificate.originalSubgroup = Subgroup.closure {g | g ∈ [m22gA, m22gB]} :=
    certificate_originalSubgroup _ _ _ _ _
  have hA : m22gA ∈ m22Certificate.originalSubgroup := by
    rw [hH]; exact Subgroup.subset_closure (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := by
    rw [hH]; exact Subgroup.subset_closure (by simp)
  refine ⟨h1, h2, h3, ?_⟩
  rw [← card_image_pairs_eq (by norm_num) m22Certificate hQ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num), card_image_pairs_eq_classTotal₂ (by norm_num) m22Certificate hQ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA hB 2000 hok, htot]

end Certificates
