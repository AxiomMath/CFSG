module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatB.A8Model
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

@[expose] def xa : Perm (Fin 8) := swap 4 5 * swap 6 7
@[expose] def xb : Perm (Fin 8) := swap 5 6 * swap 6 7
@[expose] def xc : Perm (Fin 8) := swap 3 6 * swap 4 5
@[expose] def xd : Perm (Fin 8) := swap 3 4 * swap 5 6

@[expose] def a5s : List (Perm (Fin 8)) := [xa, xb, xc, xd]

theorem conj_swap2_kb (u : Perm (Fin 8)) (p q r s : Fin 8) :
    u * (swap p q * swap r s) * u⁻¹ = swap (u p) (u q) * swap (u r) (u s) := by
  rw [swap_apply_apply u p q, swap_apply_apply u r s]
  group

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
theorem kb_tab : ∀ a0 a1 a2 : Fin 8, a1 ∉ [a0] → a2 ∉ [a0, a1] →
    ((swap a0 a1 * swap a1 a2) * (swap 0 1 * swap 1 2)⁻¹) ^ 8 = 1 →
    ∀ a3 : Fin 8, a3 ∉ [a0, a1, a2] → ∀ a4 : Fin 8, a4 ∉ [a0, a1, a2, a3] →
    ∀ a5 : Fin 8, a5 ∉ [a0, a1, a2, a3, a4] → ∀ a6 : Fin 8, a6 ∉ [a0, a1, a2, a3, a4, a5] →
    ((swap a3 a6 * swap a4 a5) * (swap 3 6 * swap 4 5)⁻¹) ^ 8 = 1 →
    ((swap a3 a4 * swap a5 a6) * (swap 3 4 * swap 5 6)⁻¹) ^ 8 = 1 →
    ∀ a7 : Fin 8, a7 ∉ [a0, a1, a2, a3, a4, a5, a6] →
    ((swap a4 a5 * swap a6 a7) * (swap 4 5 * swap 6 7)⁻¹) ^ 8 = 1 →
    ((swap a5 a6 * swap a6 a7) * (swap 5 6 * swap 6 7)⁻¹) ^ 8 = 1 →
    (∀ y : Fin 8, (![a0, a1, a2, a3, a4, a5, a6, a7] : Fin 8 → Fin 8)^[8] y = y) →
    a0 = 0 ∧ a1 = 1 ∧ a2 = 2 ∧ a3 = 3 ∧ a4 = 4 ∧ a5 = 5 ∧ a6 = 6 ∧ a7 = 7 := by
  decide +kernel

theorem kb_check : ∀ u : Perm (Fin 8), u ^ 8 = 1 → (u * a8c * u⁻¹ * a8c⁻¹) ^ 8 = 1 →
    (∀ x ∈ a5s, (u * x * u⁻¹ * x⁻¹) ^ 8 = 1) → u = 1 := by
  intro u hu8 hc hx
  have h1 := hx xa (by simp [a5s])
  have h2 := hx xb (by simp [a5s])
  have h3 := hx xc (by simp [a5s])
  have h4 := hx xd (by simp [a5s])
  unfold a8c at hc
  unfold xa at h1
  unfold xb at h2
  unfold xc at h3
  unfold xd at h4
  rw [conj_swap2_kb] at hc h1 h2 h3 h4
  have htab : (⇑u : Fin 8 → Fin 8) = ![u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 7] := by
    funext y
    fin_cases y <;> rfl
  have hit : ∀ y, (⇑u)^[8] y = y := fun y => by
    rw [← Equiv.Perm.coe_pow, hu8]
    rfl
  rw [htab] at hit
  have key := kb_tab (u 0) (u 1) (u 2) (by simp) (by simp) hc (u 3) (by simp) (u 4) (by simp)
    (u 5) (by simp) (u 6) (by simp) h3 h4 (u 7) (by simp) h1 h2 hit
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7⟩ := key
  refine Equiv.ext fun y => ?_
  fin_cases y
  · exact k0
  · exact k1
  · exact k2
  · exact k3
  · exact k4
  · exact k5
  · exact k6
  · exact k7

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
