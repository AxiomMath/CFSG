module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmVec
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmNoAlt
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmNonsing

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
open CFSG.ClassicalGroups.Orthogonal
open scoped Matrix

@[expose] noncomputable def P2pair : Subgroup OmG :=
  MulAction.stabilizer OmG sig0 ⊓ MulAction.stabilizer OmG tau0

@[expose] def Kperp : Set (Fin 6 → ZMod 2) :=
  {v | polarMinus v sig0 = 0 ∧ polarMinus v tau0 = 0}

@[expose] def trv (a x : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 := x + polarMinus x a • a

private theorem reflect_apply_trv {a : Fin 6 → ZMod 2} (ha : qMinus a = 1) (x : Fin 6 → ZMod 2) :
    reflect qMinusForm a x = trv a x := by
  rw [reflect_apply_of_map_eq_one (by rwa [qMinusForm_apply]), polar_qMinusForm]
  rfl

@[expose] def cK (y : Fin 4 → ZMod 2) : Fin 6 → ZMod 2 :=
  ![0, 0, y 2, y 3, y 1 + y 2 + y 3, y 0 + y 1]

@[expose] def dK (w : Fin 6 → ZMod 2) : Fin 4 → ZMod 2 :=
  ![w 5 + w 4 + w 2 + w 3, w 4 + w 2 + w 3, w 2, w 3]

private abbrev a1 : Fin 6 → ZMod 2 := ![0, 0, 0, 0, 0, 1]
private abbrev b1 : Fin 6 → ZMod 2 := ![0, 0, 0, 0, 1, 0]
private abbrev a2 : Fin 6 → ZMod 2 := ![0, 0, 0, 1, 0, 1]
private abbrev b2 : Fin 6 → ZMod 2 := ![0, 0, 1, 0, 0, 1]

private theorem qa1 : qMinus a1 = 1 := by decide
private theorem qb1 : qMinus b1 = 1 := by decide
private theorem qa2 : qMinus a2 = 1 := by decide
private theorem qb2 : qMinus b2 = 1 := by decide

private noncomputable def g3 : OmG :=
  ⟨reflect qMinusForm b1 * reflect qMinusForm b2, reflect_mul_reflect_mem_timmesfeldOmega qb1 qb2⟩

private noncomputable def g5 : OmG :=
  ⟨(reflect qMinusForm a1 * reflect qMinusForm b1) * (reflect qMinusForm a2 * reflect qMinusForm b2),
    Subgroup.mul_mem _ (reflect_mul_reflect_mem_timmesfeldOmega qa1 qb1)
      (reflect_mul_reflect_mem_timmesfeldOmega qa2 qb2)⟩

private theorem g3_apply (x : Fin 6 → ZMod 2) : g3 • x = trv b1 (trv b2 x) := by
  change (reflect qMinusForm b1 * reflect qMinusForm b2) x = _
  rw [LinearEquiv.mul_apply, reflect_apply_trv qb2, reflect_apply_trv qb1]

private theorem g5_apply (x : Fin 6 → ZMod 2) :
    g5 • x = trv a1 (trv b1 (trv a2 (trv b2 x))) := by
  change ((reflect qMinusForm a1 * reflect qMinusForm b1) *
    (reflect qMinusForm a2 * reflect qMinusForm b2)) x = _
  simp only [LinearEquiv.mul_apply, reflect_apply_trv qa1, reflect_apply_trv qb1,
    reflect_apply_trv qa2, reflect_apply_trv qb2]

private theorem g3_mem : g3 ∈ P2pair := by
  rw [P2pair, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    g3_apply, g3_apply]
  unfold trv sig0 tau0
  decide +kernel

private theorem g5_mem : g5 ∈ P2pair := by
  rw [P2pair, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    g5_apply, g5_apply]
  unfold trv sig0 tau0
  decide +kernel

private theorem cK_mem (y : Fin 4 → ZMod 2) : cK y ∈ Kperp := by
  revert y
  unfold Kperp cK sig0 tau0 polarMinus
  decide +kernel

private theorem cK_add (y z : Fin 4 → ZMod 2) : cK (y + z) = cK y + cK z := by
  revert y z
  unfold cK
  decide +kernel

private theorem dK_add (u v : Fin 6 → ZMod 2) : dK (u + v) = dK u + dK v := by
  revert u v
  unfold dK
  decide +kernel

private theorem cK_smul (a : ZMod 2) (y : Fin 4 → ZMod 2) : cK (a • y) = a • cK y := by
  revert a y
  unfold cK
  decide +kernel

private theorem dK_smul (a : ZMod 2) (w : Fin 6 → ZMod 2) : dK (a • w) = a • dK w := by
  revert a w
  unfold dK
  decide +kernel

private theorem cK_dK {w : Fin 6 → ZMod 2} (hw : w ∈ Kperp) : cK (dK w) = w := by
  revert w
  unfold Kperp dK cK sig0 tau0 polarMinus
  decide +kernel

private theorem dK_trv5 {w : Fin 6 → ZMod 2} (hw : w ∈ Kperp) :
    dK (trv a1 (trv b1 (trv a2 (trv b2 w)))) = natFive *ᵥ dK w := by
  revert w
  unfold Kperp trv dK sig0 tau0 polarMinus natFive Matrix.mulVec dotProduct
  simp only [Fin.sum_univ_four]
  decide +kernel

private theorem dK_trv3 {w : Fin 6 → ZMod 2} (hw : w ∈ Kperp) :
    dK (trv b1 (trv b2 w)) = natThree *ᵥ dK w := by
  revert w
  unfold Kperp trv dK sig0 tau0 polarMinus natThree Matrix.mulVec dotProduct
  simp only [Fin.sum_univ_four]
  decide +kernel

private theorem cK_mulVec5 (y : Fin 4 → ZMod 2) :
    trv a1 (trv b1 (trv a2 (trv b2 (cK y)))) = cK (natFive *ᵥ y) := by
  revert y
  unfold trv cK polarMinus natFive Matrix.mulVec dotProduct
  simp only [Fin.sum_univ_four]
  decide +kernel

private theorem cK_mulVec3 (y : Fin 4 → ZMod 2) :
    trv b1 (trv b2 (cK y)) = cK (natThree *ᵥ y) := by
  revert y
  unfold trv cK polarMinus natThree Matrix.mulVec dotProduct
  simp only [Fin.sum_univ_four]
  decide +kernel

theorem om_alt_zero (f : (Fin 6 → ZMod 2) → (Fin 6 → ZMod 2) → (Fin 6 → ZMod 2))
    (hadd1 : ∀ v₁ ∈ Kperp, ∀ v₂ ∈ Kperp, ∀ w ∈ Kperp, f (v₁ + v₂) w = f v₁ w + f v₂ w)
    (hadd2 : ∀ v ∈ Kperp, ∀ w₁ ∈ Kperp, ∀ w₂ ∈ Kperp, f v (w₁ + w₂) = f v w₁ + f v w₂)
    (halt : ∀ v ∈ Kperp, f v v = 0)
    (hmem : ∀ v ∈ Kperp, ∀ w ∈ Kperp, f v w ∈ Kperp)
    (heq : ∀ g : OmG, g ∈ P2pair → ∀ v ∈ Kperp, ∀ w ∈ Kperp, f (g • v) (g • w) = g • f v w) :
    ∀ v ∈ Kperp, ∀ w ∈ Kperp, f v w = 0 := by
  have hz0 : (0 : Fin 6 → ZMod 2) ∈ Kperp := by
    unfold Kperp sig0 tau0 polarMinus; decide +kernel
  have hz1 : ∀ w ∈ Kperp, f 0 w = 0 := fun w hw => by
    have h := hadd1 0 hz0 0 hz0 w hw
    rw [add_zero] at h
    exact left_eq_add.mp h
  have hz2 : ∀ v ∈ Kperp, f v 0 = 0 := fun v hv => by
    have h := hadd2 v hv 0 hz0 0 hz0
    rw [add_zero] at h
    exact left_eq_add.mp h
  have hs1 : ∀ (a : ZMod 2), ∀ v ∈ Kperp, ∀ w ∈ Kperp, f (a • v) w = a • f v w := by
    intro a
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · intro v hv w hw
      rw [zero_smul, zero_smul]
      exact hz1 w hw
    · intro v hv w hw
      rw [one_smul, one_smul]
  have hs2 : ∀ (a : ZMod 2), ∀ v ∈ Kperp, ∀ w ∈ Kperp, f v (a • w) = a • f v w := by
    intro a
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · intro v hv w hw
      rw [zero_smul, zero_smul]
      exact hz2 v hv
    · intro v hv w hw
      rw [one_smul, one_smul]
  let F : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    LinearMap.mk₂ (ZMod 2) (fun y z => dK (f (cK y) (cK z)))
      (fun y y' z => by
        simp only [cK_add, hadd1 _ (cK_mem y) _ (cK_mem y') _ (cK_mem z), dK_add])
      (fun a y z => by
        simp only [cK_smul, hs1 a _ (cK_mem y) _ (cK_mem z), dK_smul, smul_eq_mul])
      (fun y z z' => by
        simp only [cK_add, hadd2 _ (cK_mem y) _ (cK_mem z) _ (cK_mem z'), dK_add])
      (fun a y z => by
        simp only [cK_smul, hs2 a _ (cK_mem y) _ (cK_mem z), dK_smul, smul_eq_mul])
  have hF : ∀ y z, F y z = dK (f (cK y) (cK z)) := fun y z => rfl
  have hF0 : F = 0 := by
    refine Om_no_alt_map_concrete F (fun y => ?_) (fun y z => ?_) (fun y z => ?_)
    · rw [hF, halt _ (cK_mem y)]
      decide +revert
    · rw [hF, hF, ← cK_mulVec5, ← cK_mulVec5, ← g5_apply, ← g5_apply,
        heq g5 g5_mem _ (cK_mem y) _ (cK_mem z), g5_apply]
      exact (dK_trv5 (hmem _ (cK_mem y) _ (cK_mem z)))
    · rw [hF, hF, ← cK_mulVec3, ← cK_mulVec3, ← g3_apply, ← g3_apply,
        heq g3 g3_mem _ (cK_mem y) _ (cK_mem z), g3_apply]
      exact (dK_trv3 (hmem _ (cK_mem y) _ (cK_mem z)))
  intro v hv w hw
  have h := hF (dK v) (dK w)
  rw [hF0, cK_dK hv, cK_dK hw] at h
  have h2 := cK_dK (hmem v hv w hw)
  rw [← h2]
  have : dK (f v w) = 0 := h.symm
  rw [this]
  decide +revert

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
