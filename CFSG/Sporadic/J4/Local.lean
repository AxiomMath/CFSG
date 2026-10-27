module

public import CFSG.Sporadic.J4.FaithSpec
public import CFSG.Sporadic.J4.CertParts
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.J4.QT2LocPath
import Certificates.Data.CFSGNative.J4.Tables
import Certificates.Data.CFSGNative.J4.Chain
import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.J4

open Native Matrix CFSG.Sporadic.Th CFSG.Perm CFSG.Perm.Native

@[expose] noncomputable def xJ (k : ℕ) : J := ⟨locGL k, locGL_mem k⟩

noncomputable abbrev Hj : Subgroup J := Subgroup.closure {xJ 0, xJ 1, xJ 2}

theorem xJ_mem {k : ℕ} (hk : k < 3) : xJ k ∈ Hj := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem xJ_inv_smul (hM : MatFacts) (k : ℕ) (w : Row) :
    ofRow ((xJ k)⁻¹ • w) = ofRow w ᵥ* rowsMatrix ((locMats ())[k]?.getD idRows) := by
  rw [inv_smul_row, locMats_spec hM]; rfl

theorem xJ_smul (hM : MatFacts) (k : ℕ) (w : Row) :
    ofRow (xJ k • w) = ofRow w ᵥ* rowsMatrix ((locInvs ())[k]?.getD idRows) := by
  rw [smul_row, locInvs_spec hM]
  rfl

theorem xJ_inv_smul_root (hM : MatFacts) {k : ℕ} (hk : k < 3) :
    (xJ k)⁻¹ • toRow rootV.toVec = toRow rootV.toVec := by
  have h := hM.locFix
  rw [Array.all_eq_true] at h
  have hsz := hM.locSize
  have := V2.beq_iff.1 (h k (by omega))
  rw [← ofRow_inj, xJ_inv_smul hM, Array.getElem?_eq_getElem (by omega), Option.getD_some]
  show rootV.toVec ᵥ* rowsMatrix (locMats ())[k] = rootV.toVec
  rw [← frApply_toVec_eq_vecMul, this]

theorem Hj_fix_root (hM : MatFacts) : ∀ g ∈ Hj, g • toRow rootV.toVec = toRow rootV.toVec := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    have : ∃ k < 3, x = xJ k := by
      rcases hx with h | h | h
      · exact ⟨0, by norm_num, h⟩
      · exact ⟨1, by norm_num, h⟩
      · exact ⟨2, by norm_num, h⟩
    obtain ⟨k, hk, rfl⟩ := this
    have := xJ_inv_smul_root hM hk
    calc xJ k • toRow rootV.toVec = xJ k • ((xJ k)⁻¹ • toRow rootV.toVec) := by rw [this]
      _ = toRow rootV.toVec := smul_inv_smul _ _
  | one => exact one_smul _ _
  | mul x y _ _ hx hy => rw [mul_smul, hy, hx]
  | inv x _ hx => rw [inv_smul_eq_iff, hx]

structure J4Facts : Prop where
  mat : MatFacts
  cardHj : Nat.card Hj = 501397585920
  cardJ : Nat.card J = 86775571046077562880
  stab : ∀ x : J, x • toRow rootV.toVec = toRow rootV.toVec → x ∈ Hj
  coatom : IsCoatom Hj
  simple : IsSimpleGroup J
  cosets : ∀ g : J, ∃ ℓ < 7, ∃ h ∈ Hj, ∃ h' ∈ Hj,
    g = h * (QT2.pathElt (QT2.repPaths.getD ℓ []))⁻¹ * h'
  sizes : ∀ ℓ < 7,
    (MulAction.orbit Hj ((QT2.pathElt (QT2.repPaths.getD ℓ []))⁻¹ • toRow rootV.toVec)).ncard =
      [1, 32643072, 82575360, 54405120, 3400320, 15180, 28336].getD ℓ 0

end CFSG.Sporadic.J4
