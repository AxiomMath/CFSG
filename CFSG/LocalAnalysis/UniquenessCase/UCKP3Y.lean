module

public import CFSG.LocalAnalysis.UniquenessCase.UCKP3Tor
public import CFSG.LocalAnalysis.UniquenessCase.UCKP3Fix
public import Certificates.Certificate419001

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.RankThree.PartTwo.Sec4.Item434U38

section Transport

theorem YCoverPlus.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (φ : Y ≃* Y')
    (h : YCoverPlus Y') : YCoverPlus Y := by
  intro t ht
  have ht' : orderOf (φ t) = 3 := by rw [MulEquiv.orderOf_eq]; exact ht
  obtain ⟨e, f, g, he, hf, hef, hfe, htm, hge, hgf⟩ := h (φ t) ht'
  refine ⟨φ.symm e, φ.symm f, φ.symm g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact he
  · rw [MulEquiv.orderOf_eq]; exact hf
  · rw [← map_mul, ← map_mul, hef]
  · intro hmem
    apply hfe
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    apply φ.symm.injective
    rw [map_zpow]
    exact hk
  · have h1 : φ t ∈ Subgroup.closure ({e, f} : Set Y') := htm
    have h2 : t ∈ (Subgroup.closure ({e, f} : Set Y')).map φ.symm.toMonoidHom :=
      ⟨φ t, h1, by simp⟩
    rw [MonoidHom.map_closure] at h2
    simpa [Set.image_pair] using h2
  · rw [← map_mul, ← map_mul, hge]
  · rw [← map_mul, ← map_inv, ← map_mul, hgf]

theorem YFix3Wit.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (φ : Y ≃* Y')
    (h : YFix3Wit Y') : YFix3Wit Y := by
  intro s hs
  have hs' : orderOf (φ s) = 7 := by rw [MulEquiv.orderOf_eq]; exact hs
  obtain ⟨z, hz, hzs⟩ := h (φ s) hs'
  refine ⟨φ.symm z, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact hz
  · have : φ.symm z * φ.symm (φ s) = φ.symm (φ s) * φ.symm z := by
      rw [← map_mul, ← map_mul, hzs]
    simpa using this

theorem YFixClaim.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (φ : Y ≃* Y')
    (h : YFixClaim Y') : YFixClaim Y := by
  intro β hβ x hx hβx
  have hx' : orderOf (φ x) = 7 := by rw [MulEquiv.orderOf_eq]; exact hx
  have hβ' : (MulAut.congr φ β) ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hfix : (MulAut.congr φ β) (φ x) = φ x := by
    rw [MulAut.congr_apply]
    simp [hβx]
  obtain ⟨t, ht3, ht⟩ := h _ hβ' _ hx' hfix
  refine ⟨φ.symm t, ?_, fun y => ?_⟩
  · rw [← map_pow, ht3, map_one]
  · apply φ.injective
    have h1 := ht (φ y)
    rw [MulAut.congr_apply] at h1
    simpa using h1

end Transport

section Certificate


theorem checks_of_certificate419001 :
    U38Fix.fixCheck () = true ∧ U38Fix.toralCheck () = true := by
  have h := Certificates.certificate419001
  simpa only [U38Fix.u38FixAllCheck, Bool.and_eq_true] using h

theorem yCoverPlus_psu38 : YCoverPlus ↥X' :=
  yCoverPlus_of_toralCheck checks_of_certificate419001.2

theorem exists_orderOf_three_psu38 : ∃ t : ↥X', orderOf t = 3 :=
  exists_orderOf_three_of_toralCheck checks_of_certificate419001.2

theorem yFix3Wit_psu38 : YFix3Wit ↥X' :=
  yFix3Wit_of_fixCheck checks_of_certificate419001.1

theorem yFixClaim_psu38 : YFixClaim ↥X' :=
  yFixClaim_of_fixCheck checks_of_certificate419001.1

end Certificate

end CFSG.LocalAnalysis.UniquenessCase.UCK
