module

public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4SecIrred
public import CFSG.LocalAnalysis.SectionRank.LargeRee.RankOneBlock
public import CFSG.Blueprint.ChevalleySimpleRootOperators

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SectionRank.LargeRee

@[expose] def dv (a b c d : ℤ) : Fin TwistTag.D4.tag.rank → ℤ := ![a, b, c, d]

macro "d4root" : tactic =>
  `(tactic| (simp only [isRoot_iff_mem_artifactRoots]; decide +kernel))

section Strings

variable {i : Fin TwistTag.D4.tag.rank} {α : Fin TwistTag.D4.tag.rank → ℤ}

theorem stringUp_eq_one (hα : IsRoot TwistTag.D4.tag α) (h₁ : α ≠ Pi.single i 1)
    (h₂ : α ≠ -Pi.single i 1) (ha : IsRoot TwistTag.D4.tag (α + Pi.single i 1))
    (hb : ¬ IsRoot TwistTag.D4.tag (α + (2 : ℤ) • Pi.single i 1)) :
    stringUp TwistTag.D4.tag i α = 1 := by
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  have e1 := (h 1).1 (by rwa [one_smul])
  have e2 := mt (h 2).2 hb
  omega

theorem stringUp_eq_zero (hα : IsRoot TwistTag.D4.tag α) (h₁ : α ≠ Pi.single i 1)
    (h₂ : α ≠ -Pi.single i 1) (ha : ¬ IsRoot TwistTag.D4.tag (α + Pi.single i 1)) :
    stringUp TwistTag.D4.tag i α = 0 := by
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  have e1 := mt (h 1).2 (by rwa [one_smul])
  omega

theorem stringDown_eq_one (hα : IsRoot TwistTag.D4.tag α) (h₁ : α ≠ Pi.single i 1)
    (h₂ : α ≠ -Pi.single i 1) (ha : IsRoot TwistTag.D4.tag (α - Pi.single i 1))
    (hb : ¬ IsRoot TwistTag.D4.tag (α - (2 : ℤ) • Pi.single i 1)) :
    stringDown TwistTag.D4.tag i α = 1 := by
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  have e1 := (h (-1)).1 (by rwa [neg_smul, one_smul, ← sub_eq_add_neg])
  have e2 := mt (h (-2)).2 (by rwa [neg_smul, ← sub_eq_add_neg])
  omega

theorem stringDown_eq_zero (hα : IsRoot TwistTag.D4.tag α) (h₁ : α ≠ Pi.single i 1)
    (h₂ : α ≠ -Pi.single i 1) (ha : ¬ IsRoot TwistTag.D4.tag (α - Pi.single i 1)) :
    stringDown TwistTag.D4.tag i α = 0 := by
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  have e1 := mt (h (-1)).2 (by rwa [neg_smul, one_smul, ← sub_eq_add_neg])
  omega

end Strings

variable {L : Type} [Field L]

section Ops

variable {i : Fin TwistTag.D4.tag.rank} {α γ : Fin TwistTag.D4.tag.rank → ℤ}

theorem xOp_rv_up (t : L) (hα : IsRoot TwistTag.D4.tag α) (h₁ : α ≠ Pi.single i 1)
    (h₂ : α ≠ -Pi.single i 1) (ha : IsRoot TwistTag.D4.tag (α + Pi.single i 1))
    (hb : ¬ IsRoot TwistTag.D4.tag (α + (2 : ℤ) • Pi.single i 1))
    (hc : ¬ IsRoot TwistTag.D4.tag (α - Pi.single i 1)) (hγ : α + Pi.single i 1 = γ) :
    xOp TwistTag.D4.tag L i t (rootVec TwistTag.D4.tag L α) =
      rootVec TwistTag.D4.tag L α + t • rootVec TwistTag.D4.tag L γ := by
  rw [xOp_rootVec_of_stringUp_eq_one t hα h₁ h₂ (stringUp_eq_one hα h₁ h₂ ha hb)
    (stringDown_eq_zero hα h₁ h₂ hc), hγ]

theorem xOp_rv_fix (t : L) (hα : IsRoot TwistTag.D4.tag α) (h₁ : α ≠ Pi.single i 1)
    (h₂ : α ≠ -Pi.single i 1) (ha : ¬ IsRoot TwistTag.D4.tag (α + Pi.single i 1)) :
    xOp TwistTag.D4.tag L i t (rootVec TwistTag.D4.tag L α) = rootVec TwistTag.D4.tag L α :=
  xOp_rootVec_of_stringUp_eq_zero t hα h₁ h₂ (stringUp_eq_zero hα h₁ h₂ ha)

theorem xOp_rv_self (t : L) (hα : α = Pi.single i 1) :
    xOp TwistTag.D4.tag L i t (rootVec TwistTag.D4.tag L α) = rootVec TwistTag.D4.tag L α := by
  subst hα; exact Blueprint.Chevalley.xOp_apply_rootVec_single i t

theorem xOp_rv_neg (t : L) (hα : α = -Pi.single i 1) (hγ : Pi.single i 1 = γ) :
    xOp TwistTag.D4.tag L i t (rootVec TwistTag.D4.tag L α) =
      rootVec TwistTag.D4.tag L α + t • hVec TwistTag.D4.tag L i +
        t ^ 2 • rootVec TwistTag.D4.tag L γ := by
  subst hα hγ; exact Blueprint.Chevalley.xOp_apply_rootVec_neg_single i t

theorem yOp_rv_down (t : L) (hα : IsRoot TwistTag.D4.tag α) (h₁ : α ≠ Pi.single i 1)
    (h₂ : α ≠ -Pi.single i 1) (ha : IsRoot TwistTag.D4.tag (α - Pi.single i 1))
    (hb : ¬ IsRoot TwistTag.D4.tag (α - (2 : ℤ) • Pi.single i 1))
    (hc : ¬ IsRoot TwistTag.D4.tag (α + Pi.single i 1)) (hγ : α - Pi.single i 1 = γ) :
    yOp TwistTag.D4.tag L i t (rootVec TwistTag.D4.tag L α) =
      rootVec TwistTag.D4.tag L α + t • rootVec TwistTag.D4.tag L γ := by
  rw [yOp_rootVec_of_stringDown_eq_one t hα h₁ h₂ (stringDown_eq_one hα h₁ h₂ ha hb)
    (stringUp_eq_zero hα h₁ h₂ hc), hγ]

theorem yOp_rv_fix (t : L) (hα : IsRoot TwistTag.D4.tag α) (h₁ : α ≠ Pi.single i 1)
    (h₂ : α ≠ -Pi.single i 1) (ha : ¬ IsRoot TwistTag.D4.tag (α - Pi.single i 1)) :
    yOp TwistTag.D4.tag L i t (rootVec TwistTag.D4.tag L α) = rootVec TwistTag.D4.tag L α :=
  yOp_rootVec_of_stringDown_eq_zero t hα h₁ h₂ (stringDown_eq_zero hα h₁ h₂ ha)

theorem yOp_rv_self (t : L) (hα : α = -Pi.single i 1) :
    yOp TwistTag.D4.tag L i t (rootVec TwistTag.D4.tag L α) = rootVec TwistTag.D4.tag L α := by
  subst hα; exact Blueprint.Chevalley.yOp_apply_rootVec_neg_single i t

theorem yOp_rv_pos (t : L) (hα : α = Pi.single i 1) (hγ : -Pi.single i 1 = γ) :
    yOp TwistTag.D4.tag L i t (rootVec TwistTag.D4.tag L α) =
      rootVec TwistTag.D4.tag L α + t • hVec TwistTag.D4.tag L i +
        t ^ 2 • rootVec TwistTag.D4.tag L γ := by
  subst hα hγ; exact Blueprint.Chevalley.yOp_apply_rootVec_single i t

theorem xOp_hv_adj (t : L) {j : Fin TwistTag.D4.tag.rank}
    (hij : (TwistTag.D4.tag.cartan j i).natAbs = 1) (hγ : Pi.single i 1 = γ) :
    xOp TwistTag.D4.tag L i t (hVec TwistTag.D4.tag L j) =
      hVec TwistTag.D4.tag L j + t • rootVec TwistTag.D4.tag L γ := by
  rw [xOp_apply_hVec, hij, hγ, Nat.cast_one, one_mul]

theorem xOp_hv_fix (h2 : (2 : L) = 0) (t : L) {j : Fin TwistTag.D4.tag.rank}
    (hij : (TwistTag.D4.tag.cartan j i).natAbs = 0 ∨ (TwistTag.D4.tag.cartan j i).natAbs = 2) :
    xOp TwistTag.D4.tag L i t (hVec TwistTag.D4.tag L j) = hVec TwistTag.D4.tag L j := by
  rw [xOp_apply_hVec]
  rcases hij with h | h <;> rw [h] <;> simp [h2]

theorem yOp_hv_adj (t : L) {j : Fin TwistTag.D4.tag.rank}
    (hij : (TwistTag.D4.tag.cartan j i).natAbs = 1) (hγ : -Pi.single i 1 = γ) :
    yOp TwistTag.D4.tag L i t (hVec TwistTag.D4.tag L j) =
      hVec TwistTag.D4.tag L j + t • rootVec TwistTag.D4.tag L γ := by
  rw [yOp_apply_hVec, hij, hγ, Nat.cast_one, one_mul]

theorem yOp_hv_fix (h2 : (2 : L) = 0) (t : L) {j : Fin TwistTag.D4.tag.rank}
    (hij : (TwistTag.D4.tag.cartan j i).natAbs = 0 ∨ (TwistTag.D4.tag.cartan j i).natAbs = 2) :
    yOp TwistTag.D4.tag L i t (hVec TwistTag.D4.tag L j) = hVec TwistTag.D4.tag L j := by
  rw [yOp_apply_hVec]
  rcases hij with h | h <;> rw [h] <;> simp [h2]

theorem weylElt_rv (h2 : (2 : L) = 0) (hα : IsRoot TwistTag.D4.tag α)
    (hγ : reflect TwistTag.D4.tag i α = γ) :
    (weylElt TwistTag.D4.tag L i 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L α) = rootVec TwistTag.D4.tag L γ := by
  rw [weylElt_rootVec i 1 hα, one_zpow, Units.val_one, mul_one, hγ]
  have hneg : (-1 : L) = 1 := by linear_combination -h2
  rw [hneg, one_pow, one_smul]

theorem weylElt_hv_adj (h2 : (2 : L) = 0) {j : Fin TwistTag.D4.tag.rank}
    (hij : (TwistTag.D4.tag.cartan j i).natAbs = 1) :
    (weylElt TwistTag.D4.tag L i 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L j) = hVec TwistTag.D4.tag L j + hVec TwistTag.D4.tag L i := by
  rw [weylElt_hVec, hij, Nat.cast_one, one_smul, sub_eq_add_neg]
  congr 1
  have : (-1 : L) = 1 := by linear_combination -h2
  rw [← neg_one_smul L (hVec TwistTag.D4.tag L i), this, one_smul]

theorem weylElt_hv_fix {j : Fin TwistTag.D4.tag.rank}
    (hij : (TwistTag.D4.tag.cartan j i).natAbs = 0) :
    (weylElt TwistTag.D4.tag L i 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L j) = hVec TwistTag.D4.tag L j := by
  rw [weylElt_hVec, hij, Nat.cast_zero, zero_smul, sub_zero]

theorem weylElt_hv_self (h2 : (2 : L) = 0) :
    (weylElt TwistTag.D4.tag L i 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L i) = hVec TwistTag.D4.tag L i := by
  rw [weylElt_hVec_self]
  have : (-1 : L) = 1 := by linear_combination -h2
  rw [← neg_one_smul L (hVec TwistTag.D4.tag L i), this, one_smul]

end Ops

section Tables

variable [CharP L 2]

theorem x0_1111 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 1 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 1) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x0_1110 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 1 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y0_1110 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 1 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 0) +
        t • rootVec TwistTag.D4.tag L (dv 0 1 1 0) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x0_1011 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 1 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 1) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y0_1011 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 1 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 1) +
        t • rootVec TwistTag.D4.tag L (dv 0 0 1 1) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x0_0111 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 1) +
        t • rootVec TwistTag.D4.tag L (dv 1 1 1 1) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y0_0111 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 1) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x0_1010 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 1 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y0_1010 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 1 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 0) +
        t • rootVec TwistTag.D4.tag L (dv 0 0 1 0) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x0_0110 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 0) +
        t • rootVec TwistTag.D4.tag L (dv 1 1 1 0) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y0_0110 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x0_0011 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 1) +
        t • rootVec TwistTag.D4.tag L (dv 1 0 1 1) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y0_0011 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 1) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x0_1000 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 1 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) :=
  xOp_rv_self t (by decide +kernel)

theorem y0_1000 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 1 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) +
        t • hVec TwistTag.D4.tag L 0 +
        t ^ 2 • rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) :=
  yOp_rv_pos t (by decide +kernel) (by decide +kernel)

theorem x0_0100 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 1 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 0 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y0_0100 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 1 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 0 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y0_0010 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x0_0001 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 0 0 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 1) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y0_0001 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 0 0 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 1) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x0_000m (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 0 0 (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y0_000m (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 0 0 (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x0_00m0 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x0_0m00 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y0_0m00 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x0_m000 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv (-1) 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) +
        t • hVec TwistTag.D4.tag L 0 +
        t ^ 2 • rootVec TwistTag.D4.tag L (dv 1 0 0 0) :=
  xOp_rv_neg t (by decide +kernel) (by decide +kernel)

theorem y0_m000 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv (-1) 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) :=
  yOp_rv_self t (by decide +kernel)

theorem x0_00mm (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y0_00mm (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)) +
        t • rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x0_0mm0 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y0_0mm0 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) +
        t • rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x0_m0m0 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) +
        t • rootVec TwistTag.D4.tag L (dv 0 0 (-1) 0) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y0_m0m0 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x0_0mmm (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y0_0mmm (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) +
        t • rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) (-1)) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x0_m0mm (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) +
        t • rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y0_m0mm (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x0_mmm0 (t : L) :
    xOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0) +
        t • rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y0_mmm0 (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y0_mmmm (t : L) :
    yOp TwistTag.D4.tag L 0 t (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) (-1)) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x0_h0 (t : L) :
    xOp TwistTag.D4.tag L 0 t (hVec TwistTag.D4.tag L 0) =
      hVec TwistTag.D4.tag L 0 :=
  xOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem y0_h0 (t : L) :
    yOp TwistTag.D4.tag L 0 t (hVec TwistTag.D4.tag L 0) =
      hVec TwistTag.D4.tag L 0 :=
  yOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem x0_h1 (t : L) :
    xOp TwistTag.D4.tag L 0 t (hVec TwistTag.D4.tag L 1) =
      hVec TwistTag.D4.tag L 1 :=
  xOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem y0_h1 (t : L) :
    yOp TwistTag.D4.tag L 0 t (hVec TwistTag.D4.tag L 1) =
      hVec TwistTag.D4.tag L 1 :=
  yOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem x0_h2 (t : L) :
    xOp TwistTag.D4.tag L 0 t (hVec TwistTag.D4.tag L 2) =
      hVec TwistTag.D4.tag L 2 +
        t • rootVec TwistTag.D4.tag L (dv 1 0 0 0) :=
  xOp_hv_adj t (by decide +kernel) (by decide +kernel)

theorem y0_h2 (t : L) :
    yOp TwistTag.D4.tag L 0 t (hVec TwistTag.D4.tag L 2) =
      hVec TwistTag.D4.tag L 2 +
        t • rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) :=
  yOp_hv_adj t (by decide +kernel) (by decide +kernel)

theorem x0_h3 (t : L) :
    xOp TwistTag.D4.tag L 0 t (hVec TwistTag.D4.tag L 3) =
      hVec TwistTag.D4.tag L 3 :=
  xOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem y0_h3 (t : L) :
    yOp TwistTag.D4.tag L 0 t (hVec TwistTag.D4.tag L 3) =
      hVec TwistTag.D4.tag L 3 :=
  yOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem x1_1111 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 1 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 1) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_1110 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 1 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y1_1110 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 1 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 0) +
        t • rootVec TwistTag.D4.tag L (dv 1 0 1 0) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x1_1011 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 1 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 1) +
        t • rootVec TwistTag.D4.tag L (dv 1 1 1 1) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y1_1011 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 1 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 1) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_0111 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 1) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y1_0111 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 1) +
        t • rootVec TwistTag.D4.tag L (dv 0 0 1 1) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x1_1010 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 1 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 0) +
        t • rootVec TwistTag.D4.tag L (dv 1 1 1 0) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y1_1010 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 1 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_0110 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y1_0110 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 0) +
        t • rootVec TwistTag.D4.tag L (dv 0 0 1 0) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x1_0011 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 1) +
        t • rootVec TwistTag.D4.tag L (dv 0 1 1 1) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y1_0011 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 1) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_1000 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 1 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y1_1000 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 1 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_0100 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 1 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 0 0) :=
  xOp_rv_self t (by decide +kernel)

theorem y1_0100 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 1 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 0 0) +
        t • hVec TwistTag.D4.tag L 1 +
        t ^ 2 • rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) :=
  yOp_rv_pos t (by decide +kernel) (by decide +kernel)

theorem y1_0010 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_0001 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 0 0 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 1) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y1_0001 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 0 0 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 1) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_000m (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 0 0 (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y1_000m (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 0 0 (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_00m0 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_0m00 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) +
        t • hVec TwistTag.D4.tag L 1 +
        t ^ 2 • rootVec TwistTag.D4.tag L (dv 0 1 0 0) :=
  xOp_rv_neg t (by decide +kernel) (by decide +kernel)

theorem y1_0m00 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) :=
  yOp_rv_self t (by decide +kernel)

theorem x1_m000 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv (-1) 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y1_m000 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv (-1) 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_00mm (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y1_00mm (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)) +
        t • rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x1_0mm0 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) +
        t • rootVec TwistTag.D4.tag L (dv 0 0 (-1) 0) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y1_0mm0 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_m0m0 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y1_m0m0 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) +
        t • rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x1_0mmm (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) +
        t • rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y1_0mmm (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_m0mm (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y1_m0mm (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) +
        t • rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) (-1)) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x1_mmm0 (t : L) :
    xOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0) +
        t • rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y1_mmm0 (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y1_mmmm (t : L) :
    yOp TwistTag.D4.tag L 1 t (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) (-1)) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x1_h0 (t : L) :
    xOp TwistTag.D4.tag L 1 t (hVec TwistTag.D4.tag L 0) =
      hVec TwistTag.D4.tag L 0 :=
  xOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem y1_h0 (t : L) :
    yOp TwistTag.D4.tag L 1 t (hVec TwistTag.D4.tag L 0) =
      hVec TwistTag.D4.tag L 0 :=
  yOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem x1_h1 (t : L) :
    xOp TwistTag.D4.tag L 1 t (hVec TwistTag.D4.tag L 1) =
      hVec TwistTag.D4.tag L 1 :=
  xOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem y1_h1 (t : L) :
    yOp TwistTag.D4.tag L 1 t (hVec TwistTag.D4.tag L 1) =
      hVec TwistTag.D4.tag L 1 :=
  yOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem x1_h2 (t : L) :
    xOp TwistTag.D4.tag L 1 t (hVec TwistTag.D4.tag L 2) =
      hVec TwistTag.D4.tag L 2 +
        t • rootVec TwistTag.D4.tag L (dv 0 1 0 0) :=
  xOp_hv_adj t (by decide +kernel) (by decide +kernel)

theorem y1_h2 (t : L) :
    yOp TwistTag.D4.tag L 1 t (hVec TwistTag.D4.tag L 2) =
      hVec TwistTag.D4.tag L 2 +
        t • rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) :=
  yOp_hv_adj t (by decide +kernel) (by decide +kernel)

theorem x1_h3 (t : L) :
    xOp TwistTag.D4.tag L 1 t (hVec TwistTag.D4.tag L 3) =
      hVec TwistTag.D4.tag L 3 :=
  xOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem y1_h3 (t : L) :
    yOp TwistTag.D4.tag L 1 t (hVec TwistTag.D4.tag L 3) =
      hVec TwistTag.D4.tag L 3 :=
  yOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem x3_1110 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 1 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 0) +
        t • rootVec TwistTag.D4.tag L (dv 1 1 1 1) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y3_1110 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 1 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x3_1011 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 1 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 1) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y3_1011 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 1 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 1) +
        t • rootVec TwistTag.D4.tag L (dv 1 0 1 0) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x3_0111 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 1) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y3_0111 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 1) +
        t • rootVec TwistTag.D4.tag L (dv 0 1 1 0) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x3_1010 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 1 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 0) +
        t • rootVec TwistTag.D4.tag L (dv 1 0 1 1) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y3_1010 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 1 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x3_0110 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 0) +
        t • rootVec TwistTag.D4.tag L (dv 0 1 1 1) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y3_0110 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x3_0011 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 1) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y3_0011 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 1) +
        t • rootVec TwistTag.D4.tag L (dv 0 0 1 0) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x3_1000 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 1 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y3_1000 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 1 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x3_0100 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 1 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 0 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y3_0100 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 1 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 0 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x3_0001 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 0 0 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 1) :=
  xOp_rv_self t (by decide +kernel)

theorem y3_0001 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 0 0 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 1) +
        t • hVec TwistTag.D4.tag L 3 +
        t ^ 2 • rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)) :=
  yOp_rv_pos t (by decide +kernel) (by decide +kernel)

theorem x3_000m (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 0 0 (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)) +
        t • hVec TwistTag.D4.tag L 3 +
        t ^ 2 • rootVec TwistTag.D4.tag L (dv 0 0 0 1) :=
  xOp_rv_neg t (by decide +kernel) (by decide +kernel)

theorem y3_000m (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 0 0 (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)) :=
  yOp_rv_self t (by decide +kernel)

theorem x3_0m00 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y3_0m00 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x3_m000 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv (-1) 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y3_m000 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv (-1) 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x3_00mm (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)) +
        t • rootVec TwistTag.D4.tag L (dv 0 0 (-1) 0) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y3_00mm (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x3_0mm0 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y3_0mm0 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) +
        t • rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x3_m0m0 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y3_m0m0 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) +
        t • rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x3_0mmm (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) +
        t • rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y3_0mmm (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x3_m0mm (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) +
        t • rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) :=
  xOp_rv_up t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem y3_m0mm (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) :=
  yOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem x3_mmm0 (t : L) :
    xOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0) :=
  xOp_rv_fix t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root)

theorem y3_mmm0 (t : L) :
    yOp TwistTag.D4.tag L 3 t (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0) +
        t • rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) (-1)) :=
  yOp_rv_down t (by d4root) (by decide +kernel) (by decide +kernel) (by d4root) (by d4root)
    (by d4root) (by decide +kernel)

theorem x3_h0 (t : L) :
    xOp TwistTag.D4.tag L 3 t (hVec TwistTag.D4.tag L 0) =
      hVec TwistTag.D4.tag L 0 :=
  xOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem y3_h0 (t : L) :
    yOp TwistTag.D4.tag L 3 t (hVec TwistTag.D4.tag L 0) =
      hVec TwistTag.D4.tag L 0 :=
  yOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem x3_h1 (t : L) :
    xOp TwistTag.D4.tag L 3 t (hVec TwistTag.D4.tag L 1) =
      hVec TwistTag.D4.tag L 1 :=
  xOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem y3_h1 (t : L) :
    yOp TwistTag.D4.tag L 3 t (hVec TwistTag.D4.tag L 1) =
      hVec TwistTag.D4.tag L 1 :=
  yOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem x3_h2 (t : L) :
    xOp TwistTag.D4.tag L 3 t (hVec TwistTag.D4.tag L 2) =
      hVec TwistTag.D4.tag L 2 +
        t • rootVec TwistTag.D4.tag L (dv 0 0 0 1) :=
  xOp_hv_adj t (by decide +kernel) (by decide +kernel)

theorem y3_h2 (t : L) :
    yOp TwistTag.D4.tag L 3 t (hVec TwistTag.D4.tag L 2) =
      hVec TwistTag.D4.tag L 2 +
        t • rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)) :=
  yOp_hv_adj t (by decide +kernel) (by decide +kernel)

theorem x3_h3 (t : L) :
    xOp TwistTag.D4.tag L 3 t (hVec TwistTag.D4.tag L 3) =
      hVec TwistTag.D4.tag L 3 :=
  xOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem y3_h3 (t : L) :
    yOp TwistTag.D4.tag L 3 t (hVec TwistTag.D4.tag L 3) =
      hVec TwistTag.D4.tag L 3 :=
  yOp_hv_fix (CharP.cast_eq_zero L 2) t (by decide +kernel)

theorem n0_1111 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_1110 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_1011 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_0110 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_0011 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_1000 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_0100 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 1 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_0010 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_0001 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 0 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_000m :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 0 (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_00m0 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_0m00 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_m000 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_00mm :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_0mm0 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_m0mm :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_mmm0 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_mmmm :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n0_h0 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 0) =
      hVec TwistTag.D4.tag L 0 :=
  weylElt_hv_self (CharP.cast_eq_zero L 2)

theorem n0_h1 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 1) =
      hVec TwistTag.D4.tag L 1 :=
  weylElt_hv_fix (by decide +kernel)

theorem n0_h2 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 2) =
      hVec TwistTag.D4.tag L 2 +
        hVec TwistTag.D4.tag L 0 :=
  weylElt_hv_adj (CharP.cast_eq_zero L 2) (by decide +kernel)

theorem n0_h3 :
    (weylElt TwistTag.D4.tag L 0 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 3) =
      hVec TwistTag.D4.tag L 3 :=
  weylElt_hv_fix (by decide +kernel)

theorem n1_1111 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_1011 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_0111 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_1010 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_0110 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_1000 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_0100 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 1 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_0010 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_0001 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 0 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_000m :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 0 (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_00m0 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_0m00 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_m000 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_0mm0 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_m0m0 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_0mmm :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_m0mm :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_mmmm :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n1_h0 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 0) =
      hVec TwistTag.D4.tag L 0 :=
  weylElt_hv_fix (by decide +kernel)

theorem n1_h1 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 1) =
      hVec TwistTag.D4.tag L 1 :=
  weylElt_hv_self (CharP.cast_eq_zero L 2)

theorem n1_h2 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 2) =
      hVec TwistTag.D4.tag L 2 +
        hVec TwistTag.D4.tag L 1 :=
  weylElt_hv_adj (CharP.cast_eq_zero L 2) (by decide +kernel)

theorem n1_h3 :
    (weylElt TwistTag.D4.tag L 1 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 3) =
      hVec TwistTag.D4.tag L 3 :=
  weylElt_hv_fix (by decide +kernel)

theorem n2_1110 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_1011 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_0111 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_1010 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_0110 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_0011 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_1000 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_0100 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 1 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_0001 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 0 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_000m :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 0 (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_0m00 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_m000 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_00mm :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_0mm0 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_m0m0 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_0mmm :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_m0mm :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_mmm0 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n2_h0 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 0) =
      hVec TwistTag.D4.tag L 0 +
        hVec TwistTag.D4.tag L 2 :=
  weylElt_hv_adj (CharP.cast_eq_zero L 2) (by decide +kernel)

theorem n2_h1 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 1) =
      hVec TwistTag.D4.tag L 1 +
        hVec TwistTag.D4.tag L 2 :=
  weylElt_hv_adj (CharP.cast_eq_zero L 2) (by decide +kernel)

theorem n2_h2 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 2) =
      hVec TwistTag.D4.tag L 2 :=
  weylElt_hv_self (CharP.cast_eq_zero L 2)

theorem n2_h3 :
    (weylElt TwistTag.D4.tag L 2 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 3) =
      hVec TwistTag.D4.tag L 3 +
        hVec TwistTag.D4.tag L 2 :=
  weylElt_hv_adj (CharP.cast_eq_zero L 2) (by decide +kernel)

theorem n3_1110 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 1 1 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_1011 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_0111 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 1 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_1010 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 0 1 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 1 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_0110 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 1 1 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 1 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_0011 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 1 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 1 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_1000 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 1 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_0100 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 1 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 1 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_0001 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 0 1)) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_000m :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 0 (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 0 1) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_0m00 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_m000 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) 0 0 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_00mm :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 0 (-1) 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_0mm0 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_m0m0 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_0mmm :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_m0mm :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1))) =
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_mmm0 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0)) =
      rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) (-1)) :=
  weylElt_rv (CharP.cast_eq_zero L 2) (by d4root) (by decide +kernel)

theorem n3_h0 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 0) =
      hVec TwistTag.D4.tag L 0 :=
  weylElt_hv_fix (by decide +kernel)

theorem n3_h1 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 1) =
      hVec TwistTag.D4.tag L 1 :=
  weylElt_hv_fix (by decide +kernel)

theorem n3_h2 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 2) =
      hVec TwistTag.D4.tag L 2 +
        hVec TwistTag.D4.tag L 3 :=
  weylElt_hv_adj (CharP.cast_eq_zero L 2) (by decide +kernel)

theorem n3_h3 :
    (weylElt TwistTag.D4.tag L 3 1 : Module.End L (RootModule TwistTag.D4.tag L))
      (hVec TwistTag.D4.tag L 3) =
      hVec TwistTag.D4.tag L 3 :=
  weylElt_hv_self (CharP.cast_eq_zero L 2)

end Tables

end CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof
