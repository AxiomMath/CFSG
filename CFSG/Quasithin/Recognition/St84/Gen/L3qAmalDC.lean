module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCTransport
import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalRoots
import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalExtend
import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open
open CFSG.GH74.QTGen4.DSGen4.L34
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
open CFSG.QuasithinUnique.Fin257.L3
open CFSG.Quasithin.H13.F431.L3.P3

theorem dcStd_of_eight_le {F : Type} [Field F] [Finite F] [CharP F 2]
    (hq : 8 ≤ Nat.card F) : DCStd F := by
  unfold DCStd
  refine dcProp_of_forall_exists_extend (A := Ln F) (B := Pt F) ?_
  intro σ hσ
  obtain ⟨u, hu, l, m, n, hnmul, hxroot, hyroot, -, hHroot⟩ :=
    exists_rootData_of_mulAut hq σ hσ
  obtain ⟨ρ, -, hl_eq, hm_eq⟩ :=
    exists_ringEquiv_of_map_mul n.toAddMonoidHom l.toAddMonoidHom m.toAddMonoidHom
      n.bijective hnmul
  have hl1 : l 1 ≠ 0 := by
    intro h
    exact one_ne_zero (l.injective (by rw [h, map_zero]))
  have hm1 : m 1 ≠ 0 := by
    intro h
    exact one_ne_zero (m.injective (by rw [h, map_zero]))
  have hl_eq' : ∀ a : F, l a = l 1 * ρ a := fun a => hl_eq a
  have hm_eq' : ∀ b : F, m b = m 1 * ρ b := fun b => hm_eq b
  let s : Fˣ := Units.mk0 (l 1) hl1
  let t : Fˣ := Units.mk0 (m 1) hm1
  have hx : ∀ (x : ↥(Ln F ⊓ Pt F)) (a : F), (x : projectiveSL 3 F) = xP a →
      ((σ x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) =
        u * xP ((s : F) * ρ a) * u⁻¹ := by
    intro x a hxa
    rw [hxroot x a hxa, hl_eq' a]
    rfl
  have hy : ∀ (x : ↥(Ln F ⊓ Pt F)) (b : F), (x : projectiveSL 3 F) = yP b →
      ((σ x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) =
        u * yP ((t : F) * ρ b) * u⁻¹ := by
    intro x b hxb
    rw [hyroot x b hxb, hm_eq' b]
    rfl
  have hH : ∀ x : ↥(Ln F ⊓ Pt F), (x : projectiveSL 3 F) ∈ torus3 F →
      u⁻¹ * ((σ x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) * u ∈ torus3 F := hHroot
  have heq := eq_on_inf_of_roots σ hu s t ρ hx hy hH
  let Φ : MulAut (projectiveSL 3 F) :=
    LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ
  let Ψ : MulAut (projectiveSL 3 F) := MulAut.conj u * Φ
  have hΨ : ∀ g : projectiveSL 3 F, Ψ g = u * Φ g * u⁻¹ := fun g => by
    simp [Ψ, MulAut.mul_apply, MulAut.conj_apply]
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · intro g
    have huLn : u ∈ Ln F := U_le_normalizer_V2 hu
    have hN := Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer (H := Ln F) huLn)
    rw [hΨ g]
    exact (mem_Ln_iff_conjAut_fieldAut s t ρ g).trans (hN (Φ g))
  · intro g
    have huPt : u ∈ Pt F := U_le_normalizer_V1 hu
    have hN := Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer (H := Pt F) huPt)
    rw [hΨ g]
    exact (mem_Pt_iff_conjAut_fieldAut s t ρ g).trans (hN (Φ g))
  · intro b
    rw [heq b, hΨ (b : projectiveSL 3 F)]
    rfl

end CFSG.Quasithin.F112R.St84
