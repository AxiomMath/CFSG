module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmNonsing
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmIso
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmVec
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2OmegaPts

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
  CFSG.ClassicalGroups.Orthogonal MulAction

@[expose] noncomputable def P2 : Subgroup OmG := stabilizer OmG sig0 ⊓ stabilizer OmG tau0

@[expose] def transv (a x : F6) : F6 := x + polarMinus x a • a

theorem polarMinus_comm (u v : F6) : polarMinus u v = polarMinus v u := by
  unfold polarMinus
  ring

theorem qMinus_sig0 : qMinus sig0 = 1 := by decide

theorem qMinus_tau0 : qMinus tau0 = 0 := by decide

theorem qMinus_sig0_add_tau0 : qMinus (sig0 + tau0) = 0 := by decide

theorem polarMinus_sig0_tau0 : polarMinus sig0 tau0 = 1 := by decide

theorem sig0_ne_zero : sig0 ≠ 0 := by decide

theorem tau0_ne_zero : tau0 ≠ 0 := by decide

theorem qMinus_add (x y : F6) : qMinus (x + y) = qMinus x + qMinus y + polarMinus x y := by
  revert x y
  decide +kernel

theorem polarMinus_self (x : F6) : polarMinus x x = 0 := by
  revert x
  decide

@[expose] noncomputable def rrOm {a b : F6} (ha : qMinus a = 1) (hb : qMinus b = 1) : OmG :=
  ⟨reflect qMinusForm a * reflect qMinusForm b, reflect_mul_reflect_mem_timmesfeldOmega ha hb⟩

theorem rrOm_smul {a b : F6} (ha : qMinus a = 1) (hb : qMinus b = 1) (x : F6) :
    rrOm ha hb • x = transv a (transv b x) := by
  show (reflect qMinusForm a * reflect qMinusForm b) x = _
  rw [LinearEquiv.mul_apply,
    reflect_apply_of_map_eq_one (Q := qMinusForm) (v := b) (by rwa [qMinusForm_apply]),
    reflect_apply_of_map_eq_one (Q := qMinusForm) (v := a) (by rwa [qMinusForm_apply]),
    polar_qMinusForm, polar_qMinusForm]
  rfl

@[expose] def nlSig : List F6 :=
  [![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1], ![0, 0, 1, 0, 0, 1], ![0, 0, 1, 0, 1, 0],
    ![0, 0, 1, 0, 1, 1], ![0, 0, 1, 1, 0, 0], ![1, 1, 0, 0, 0, 0], ![1, 1, 0, 1, 0, 0],
    ![1, 1, 1, 0, 0, 0], ![1, 1, 1, 1, 0, 1], ![1, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1]]

theorem nlSig_spec : ∀ a ∈ nlSig, qMinus a = 1 ∧ polarMinus sig0 a = 0 := by decide

theorem nlSig_fix : ∀ a ∈ nlSig, ∀ b ∈ nlSig, transv a (transv b sig0) = sig0 := by decide +kernel

theorem nlSig_reach : ∀ t : F6, qMinus t = 0 → polarMinus sig0 t = 1 →
    ∃ a ∈ nlSig, ∃ b ∈ nlSig, transv a (transv b tau0) = t := by
  decide +kernel

theorem om_pair_trans {s t : F6} (hs : qMinus s = 1) (ht : qMinus t = 0)
    (hst : qMinus (s + t) = 0) (h0 : t ≠ 0) :
    ∃ g : OmG, g • sig0 = s ∧ g • tau0 = t := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact absurd hs (by decide)
  obtain ⟨g₁, hg₁, hg₁s⟩ := exists_mem_timmesfeldOmega_apply_eq sig0_ne_zero hs0
    (by rw [qMinus_sig0, hs])
  let G : OmG := ⟨g₁, hg₁⟩
  have hGs : G • sig0 = s := hg₁s
  have hB : polarMinus s t = 1 := by
    have h := qMinus_add s t
    rw [hst, hs, ht] at h
    revert h
    generalize polarMinus s t = c
    revert c
    decide
  have hinv : ∀ x : F6, G • (G⁻¹ • x) = x := fun x => smul_inv_smul G x
  have hGs' : G⁻¹ • s = sig0 := by rw [← hGs, inv_smul_smul]
  have hq' : qMinus (G⁻¹ • t) = 0 := by
    have := qMinus_apply_of_mem (g := ((G⁻¹ : OmG) : F6 ≃ₗ[ZMod 2] F6)) (G⁻¹).2 t
    exact this.trans ht
  have hB' : polarMinus sig0 (G⁻¹ • t) = 1 := by
    have := polarMinus_apply_of_mem (g := ((G⁻¹ : OmG) : F6 ≃ₗ[ZMod 2] F6)) (G⁻¹).2 s t
    have h2 : polarMinus (G⁻¹ • s) (G⁻¹ • t) = 1 := this.trans hB
    rwa [hGs'] at h2
  obtain ⟨a, ha, b, hb, hab⟩ := nlSig_reach _ hq' hB'
  have ha' := nlSig_spec a ha
  have hb' := nlSig_spec b hb
  refine ⟨G * rrOm ha'.1 hb'.1, ?_, ?_⟩
  · rw [mul_smul, rrOm_smul, nlSig_fix a ha b hb, hGs]
  · rw [mul_smul, rrOm_smul, hab, hinv]

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
