module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherHermitian

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem rckFlagSUGeom_eq_top_of_ne_bot {f : ℕ} {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] (h : UnitaryFieldData 2 f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : 2 ≤ Module.finrank K V) {P : Submodule K V} (hPne : P ≠ ⊥)
    (hP : ∀ x ∈ P, ∀ u : V, B u u = 0 → B u x ≠ 0 → u ∈ P) :
    P = ⊤ := by
  have : CharP K 2 := h.charP
  obtain ⟨x, hxP, hx0⟩ := (Submodule.ne_bot_iff P).mp hPne
  have hsymm : ∀ y z : V, B y z = h.bar (B z y) := fun y z => (hB.eq z y).symm
  have hne : ∀ u : V, u ≠ 0 → ∃ z : V, B u z ≠ 0 := by
    intro u hu
    by_contra hcon
    push Not at hcon
    exact hu (hBl u hcon)
  have key : ∀ u : V, B u u = 0 → u ∈ P := by
    intro u hu
    by_cases hu0 : u = 0
    · rw [hu0]; exact P.zero_mem
    by_cases hux : B u x = 0
    ·
      obtain ⟨z, huz, hxz⟩ : ∃ z : V, B u z ≠ 0 ∧ B x z ≠ 0 := by
        obtain ⟨a, ha⟩ := hne u hu0
        obtain ⟨b, hb⟩ := hne x hx0
        by_cases hxa : B x a = 0
        · by_cases hub : B u b = 0
          · refine ⟨a + b, ?_, ?_⟩
            · rw [map_add, hub, add_zero]; exact ha
            · rw [map_add, hxa, zero_add]; exact hb
          · exact ⟨b, hub, hb⟩
        · exact ⟨a, ha, hxa⟩
      have hzu : B z u ≠ 0 := by
        rw [hsymm z u]; exact (map_ne_zero h.bar).mpr huz
      have hzx : B z x ≠ 0 := by
        rw [hsymm z x]; exact (map_ne_zero h.bar).mpr hxz
      obtain ⟨c, hc⟩ := h.traceLin_surjective ⟨B z z, hB.eq z z⟩
      have hc' : h.trace c = B z z := by simpa using congrArg Subtype.val hc
      set a : K := c / B z u with ha
      have hatr : h.trace (a * B z u) = B z z := by
        rw [ha, div_mul_cancel₀ _ hzu]; exact hc'
      set w : V := z + a • u with hw
      have hww : B w w = 0 := by
        have htrace : B w w = B z z + h.trace (a * B z u) := by
          rw [hw]
          rw [LinearMap.map_add B z (a • u), LinearMap.add_apply,
            LinearMap.map_smulₛₗ B a u, LinearMap.smul_apply,
            LinearMap.map_add (B z) z (a • u), LinearMap.map_smul (B z) a u,
            smul_eq_mul,
            LinearMap.map_add (B u) z (a • u), LinearMap.map_smul (B u) a u,
            smul_eq_mul, hu, smul_zero, add_zero, hsymm u z, ← map_mul]
          simp only [UnitaryFieldData.trace]
          ring
        rw [htrace, hatr, CharTwo.add_self_eq_zero]
      have hwx : B w x ≠ 0 := by
        have hwx' : B w x = B z x + h.bar a * B u x := by
          rw [hw, LinearMap.map_add B z (a • u), LinearMap.add_apply,
            LinearMap.map_smulₛₗ B a u, LinearMap.smul_apply, smul_eq_mul]
        rw [hwx', hux, mul_zero, add_zero]; exact hzx
      have hwP : w ∈ P := hP x hxP w hww hwx
      exact hP w hwP u hu (by
        have huw : B u w = B u z := by
          rw [hw, LinearMap.map_add (B u) z (a • u), LinearMap.map_smul (B u) a u,
            smul_eq_mul, hu, mul_zero, add_zero]
        rw [huw]; exact huz)
    · exact hP x hxP u hu hux
  rw [eq_top_iff, ← span_isotropic_eq_top h hB hBl hn]
  exact Submodule.span_le.mpr (fun v hv => key v hv.2)

end CFSG.StandardType.RCKFlag
