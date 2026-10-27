module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotRel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanE6TwoBits
import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotMatK

public section

namespace CFSG.StandardType.FF81.CentE6

open CFSG.Blueprint.Chevalley CFSG.StandardType.GGSixE6Two CFSG.StandardType.E6TwoMat
  CFSG.StandardType.GGHalf
open CFSG.Monster.B.Classical.E6Adjoint (toVec)
open CFSG.SeitzReduction (highRoot highNode)

@[expose] def rWordE6 : List ℕ := [66, 47, 57, 56, 52, 76, 52, 56, 57, 47, 66]

@[expose] def zWordE6 : List ℕ := [76, 77]

@[expose] def uWordE6 : List ℕ := [6, 12, 9, 18, 11, 22]

theorem rz_wordsAgree :
    wordsAgree (rWordE6 ++ zWordE6) (zWordE6 ++ zWordE6 ++ uWordE6 ++ rWordE6) = true :=
  E6TwoMatK.wordsAgree_of_K (by decide +kernel)

theorem uCube_wordsAgree : wordsAgree (uWordE6 ++ uWordE6 ++ uWordE6) [] = true :=
  E6TwoMatK.wordsAgree_of_K (by decide +kernel)

theorem zCube_wordsAgree : wordsAgree (zWordE6 ++ zWordE6 ++ zWordE6) [] = true :=
  E6TwoMatK.wordsAgree_of_K (by decide +kernel)

theorem rootOf_76 : rootOf 76 = highRoot .E6 := by
  decide +kernel

theorem rootOf_77 : rootOf 77 = -highRoot .E6 := by
  decide +kernel

theorem rootOf_uWordE6_mem :
    ∀ a ∈ uWordE6, rootOf a ∈ SeitzReduction.E6Pilot.a5LeviRoots := by
  intro a ha
  have h : (6 ≤ a ∧ a < 78) ∧ rootOf a (highNode .E6) = 0 := by
    simp only [uWordE6, List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  exact ⟨isRoot_rootOf ⟨a, h.1.2⟩ h.1.1, h.2⟩

section Words


private noncomputable def cElt (w : List ℕ) : EC :=
  ⟨wordElt F2 w, E6TwoPilot.wordElt_mem_adjointGroup w⟩

private theorem cElt_append (w₁ w₂ : List ℕ) : cElt (w₁ ++ w₂) = cElt w₁ * cElt w₂ :=
  Subtype.ext (wordElt_append F2 w₁ w₂)

private theorem cElt_cons (a : ℕ) (w : List ℕ) : cElt (a :: w) = xr (rootOf a) * cElt w :=
  Subtype.ext (wordElt_cons F2 a w)

private theorem cElt_nil : cElt [] = 1 :=
  rfl

private theorem zE_eq_cElt : zE = cElt zWordE6 := by
  rw [zWordE6, cElt_cons, cElt_cons, cElt_nil, mul_one, rootOf_76, rootOf_77]
  rfl

private theorem cElt_mem_lE {w : List ℕ}
    (hw : ∀ a ∈ w, rootOf a ∈ SeitzReduction.E6Pilot.a5LeviRoots) : cElt w ∈ lE := by
  induction w with
  | nil => exact lE.one_mem
  | cons a w ih =>
    rw [cElt_cons]
    exact lE.mul_mem (SeitzReduction.E6Pilot.pinnedX_mem_a5Levi (hw a (by simp)) 1)
      (ih fun b hb => hw b (by simp [hb]))

end Words

section Model


private theorem cElt_eq_of_wordsAgree {w₁ w₂ : List ℕ} (h : wordsAgree w₁ w₂ = true) :
    cElt w₁ = cElt w₂ :=
  Subtype.ext (wordElt_eq_of_wordsAgree h)

private theorem cElt_uWordE6_ne_one : cElt uWordE6 ≠ 1 := by
  intro h
  have h1 : ((wordElt F2 uWordE6 : ModGL .E6 F2) : Module.End F2 (RootModule .E6 F2)) = 1 :=
    congrArg Units.val (congrArg Subtype.val h)
  have hv := LinearMap.congr_fun h1 (toVec F2 (1 <<< 6))
  rw [Module.End.one_apply, wordElt_toVec (w := uWordE6) (by decide +kernel)] at hv
  have := CFSG.AGLEmbedding.E6Two.toVec_inj (by decide +kernel) (by decide +kernel) hv
  revert this
  decide +kernel

theorem exists_conj_zE_eq_inv_mul :
    ∃ g : EC, ∃ u ∈ lE, u ≠ 1 ∧ u ^ 3 = 1 ∧ g * zE * g⁻¹ = zE⁻¹ * u := by
  refine ⟨cElt rWordE6, cElt uWordE6, cElt_mem_lE rootOf_uWordE6_mem, cElt_uWordE6_ne_one, ?_, ?_⟩
  · have h := cElt_eq_of_wordsAgree uCube_wordsAgree
    rw [cElt_append, cElt_append, cElt_nil] at h
    rw [pow_three, ← mul_assoc, h]
  · have hz : zE ^ 3 = 1 := by
      have h := cElt_eq_of_wordsAgree zCube_wordsAgree
      rw [cElt_append, cElt_append, cElt_nil, ← zE_eq_cElt] at h
      rw [pow_three, ← mul_assoc, h]
    have hzinv : zE⁻¹ = zE * zE := by
      rw [inv_eq_iff_mul_eq_one, ← pow_three, hz]
    have h := cElt_eq_of_wordsAgree rz_wordsAgree
    rw [cElt_append, cElt_append, cElt_append, cElt_append, ← zE_eq_cElt] at h
    rw [mul_inv_eq_iff_eq_mul, hzinv, h]

end Model

end CFSG.StandardType.FF81.CentE6

end
