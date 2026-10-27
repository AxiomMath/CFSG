module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuHeisHom

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

private theorem eichlerSU_congr (h : UnitaryFieldData p f K)
    {v v' w w' : HypIndex r ε → K} {γ γ' : K}
    (hv : v = v') (hw : w = w') (hγ : γ = γ')
    (p1 : hypForm h r ε v v = 0) (p2 : hypForm h r ε v w = 0)
    (p3 : γ + h.bar γ + hypForm h r ε w w = 0)
    (q1 : hypForm h r ε v' v' = 0) (q2 : hypForm h r ε v' w' = 0)
    (q3 : γ' + h.bar γ' + hypForm h r ε w' w' = 0) :
    eichlerSU h p1 p2 p3 = eichlerSU h q1 q2 q3 := by
  subst hv hw hγ
  exact Subtype.ext (Units.ext rfl)

private theorem heisScalar_zero_zero (h : UnitaryFieldData p f K)
    (w₁ w₂ : HypIndex r ε → K) (c : h.fixedField) :
    heisScalar h w₁ w₂ ⟨0, 0, c⟩ =
      -2 * (c : K) * ((hypForm h r ε w₁ w₂ - h.bar (hypForm h r ε w₁ w₂)) / 2) := by
  simp only [heisScalar, heisVec, zero_smul, add_zero, map_zero, zero_div, neg_zero,
    zero_add, zero_sub, mul_zero, Subfield.coe_zero]
  ring

private theorem bar_hypForm_heisVec_heisVec (h : UnitaryFieldData p f K)
    (w₁ w₂ w₃ w₄ : HypIndex r ε → K)
    (h13 : h.bar (hypForm h r ε w₁ w₃) = hypForm h r ε w₁ w₃)
    (h14 : h.bar (hypForm h r ε w₁ w₄) = hypForm h r ε w₁ w₄)
    (h23 : h.bar (hypForm h r ε w₂ w₃) = hypForm h r ε w₂ w₃)
    (h24 : h.bar (hypForm h r ε w₂ w₄) = hypForm h r ε w₂ w₄)
    (x y : Heis h.fixedField) :
    h.bar (hypForm h r ε (heisVec h w₁ w₂ x) (heisVec h w₃ w₄ y)) =
      hypForm h r ε (heisVec h w₁ w₂ x) (heisVec h w₃ w₄ y) := by
  have ha : h.bar (x.a : K) = (x.a : K) := h.mem_fixedField.mp x.a.2
  have hb : h.bar (x.b : K) = (x.b : K) := h.mem_fixedField.mp x.b.2
  have hc : h.bar (y.a : K) = (y.a : K) := h.mem_fixedField.mp y.a.2
  have hd : h.bar (y.b : K) = (y.b : K) := h.mem_fixedField.mp y.b.2
  simp only [heisVec, map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply]
  simp only [map_add, map_mul, ha, hb, hc, hd, h13, h14, h23, h24]

private theorem eichlerSU_mul_comm (h : UnitaryFieldData p f K)
    {v A B : HypIndex r ε → K} {α β : K}
    (hv : hypForm h r ε v v = 0) (hA : hypForm h r ε v A = 0)
    (hB : hypForm h r ε v B = 0) (hα : α + h.bar α + hypForm h r ε A A = 0)
    (hβ : β + h.bar β + hypForm h r ε B B = 0)
    (hAB : hypForm h r ε B A = hypForm h r ε A B) :
    eichlerSU h hv hA hα * eichlerSU h hv hB hβ =
      eichlerSU h hv hB hβ * eichlerSU h hv hA hα := by
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_eichlerSU,
    hypEichler_mul h α β hv hA hB, hypEichler_mul h β α hv hB hA]
  rw [add_comm A B, hAB, add_comm α β]

theorem exists_heis_pair_hypPSU (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {v w₁ w₂ w₃ w₄ : HypIndex r ε → K} (hv0 : v ≠ 0) (hv : hypForm h r ε v v = 0)
    (h₁ : hypForm h r ε v w₁ = 0) (h₂ : hypForm h r ε v w₂ = 0)
    (h₃ : hypForm h r ε v w₃ = 0) (h₄ : hypForm h r ε v w₄ = 0)
    (hω : h.bar (hypForm h r ε w₁ w₂) ≠ hypForm h r ε w₁ w₂)
    (hω' : hypForm h r ε w₃ w₄ = hypForm h r ε w₁ w₂)
    (h13 : h.bar (hypForm h r ε w₁ w₃) = hypForm h r ε w₁ w₃)
    (h14 : h.bar (hypForm h r ε w₁ w₄) = hypForm h r ε w₁ w₄)
    (h23 : h.bar (hypForm h r ε w₂ w₃) = hypForm h r ε w₂ w₃)
    (h24 : h.bar (hypForm h r ε w₂ w₄) = hypForm h r ε w₂ w₄) :
    ∃ ι₁ ι₂ : Heis h.fixedField →* hypPSU h r ε, Function.Injective ι₁ ∧
      Function.Injective ι₂ ∧ (∀ a b, Commute (ι₁ a) (ι₂ b)) ∧
      (∀ c, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩) ∧
      ∀ x, ι₁ x = hypProj h r ε (eichlerSU h hv (hypForm_heisVec h h₁ h₂ x)
        (heisScalar_trace h hp2 w₁ w₂ x)) := by
  have hω₂ : h.bar (hypForm h r ε w₃ w₄) ≠ hypForm h r ε w₃ w₄ := by
    intro hc
    exact hω (by rw [← hω']; exact hc)
  obtain ⟨ι₁, hι₁, hι₁x⟩ := exists_heis_hypPSU h hp2 hv0 hv h₁ h₂ hω
  obtain ⟨ι₂, hι₂, hι₂x⟩ := exists_heis_hypPSU h hp2 hv0 hv h₃ h₄ hω₂
  refine ⟨ι₁, ι₂, hι₁, hι₂, ?_, ?_, hι₁x⟩
  · intro a b
    show ι₁ a * ι₂ b = ι₂ b * ι₁ a
    have hAB : hypForm h r ε (heisVec h w₃ w₄ b) (heisVec h w₁ w₂ a) =
        hypForm h r ε (heisVec h w₁ w₂ a) (heisVec h w₃ w₄ b) := by
      have hbar := bar_hypForm_heisVec_heisVec h w₁ w₂ w₃ w₄ h13 h14 h23 h24 a b
      have hsymm := (LinearMap.isSymm_def.mp (hypForm_isSymm h))
        (heisVec h w₁ w₂ a) (heisVec h w₃ w₄ b)
      exact hsymm.symm.trans hbar
    rw [hι₁x a, hι₂x b, ← map_mul, ← map_mul]
    congr 1
    exact eichlerSU_mul_comm h hv (hypForm_heisVec h h₁ h₂ a) (hypForm_heisVec h h₃ h₄ b)
      (heisScalar_trace h hp2 w₁ w₂ a) (heisScalar_trace h hp2 w₃ w₄ b) hAB
  · intro c
    have hvec1 : heisVec h w₁ w₂ (⟨0, 0, c⟩ : Heis h.fixedField) = 0 := by
      simp [heisVec]
    have hvec3 : heisVec h w₃ w₄ (⟨0, 0, c⟩ : Heis h.fixedField) = 0 := by
      simp [heisVec]
    have hsc1 := heisScalar_zero_zero h w₁ w₂ c
    have hsc3 := heisScalar_zero_zero h w₃ w₄ c
    have hvec : heisVec h w₁ w₂ ⟨0, 0, c⟩ = heisVec h w₃ w₄ ⟨0, 0, c⟩ := by
      rw [hvec1, hvec3]
    have hsc : heisScalar h w₁ w₂ ⟨0, 0, c⟩ = heisScalar h w₃ w₄ ⟨0, 0, c⟩ := by
      rw [hsc1, hsc3, hω']
    have hEU : eichlerSU h hv (hypForm_heisVec h h₁ h₂ (⟨0, 0, c⟩ : Heis h.fixedField))
        (heisScalar_trace h hp2 w₁ w₂ (⟨0, 0, c⟩ : Heis h.fixedField)) =
        eichlerSU h hv (hypForm_heisVec h h₃ h₄ (⟨0, 0, c⟩ : Heis h.fixedField))
          (heisScalar_trace h hp2 w₃ w₄ (⟨0, 0, c⟩ : Heis h.fixedField)) :=
      eichlerSU_congr h rfl hvec hsc hv (hypForm_heisVec h h₁ h₂ _)
        (heisScalar_trace h hp2 w₁ w₂ _) hv (hypForm_heisVec h h₃ h₄ _)
        (heisScalar_trace h hp2 w₃ w₄ _)
    rw [hι₁x ⟨0, 0, c⟩, hι₂x ⟨0, 0, c⟩, hEU]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
