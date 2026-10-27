module

public import CFSG.Quasithin.EmptyFaithful.S143A6Nat

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm

@[expose] def cls (g : Perm (Fin 6)) : Fin 6 :=
  if g = 1 then 0 else if g * g = 1 then 1 else if g * g * g = 1 then (if ∃ i, g i = i then 2 else 3)
  else if g * g * g * g = 1 then 4 else 5

set_option maxRecDepth 100000 in
theorem cls_count : (Finset.univ.filter fun g : alternatingGroup (Fin 6) => cls g.1 = 0).card = 1 ∧
    (Finset.univ.filter fun g : alternatingGroup (Fin 6) => cls g.1 = 1).card = 45 ∧
    (Finset.univ.filter fun g : alternatingGroup (Fin 6) => cls g.1 = 2).card = 40 ∧
    (Finset.univ.filter fun g : alternatingGroup (Fin 6) => cls g.1 = 3).card = 40 ∧
    (Finset.univ.filter fun g : alternatingGroup (Fin 6) => cls g.1 = 4).card = 90 ∧
    (Finset.univ.filter fun g : alternatingGroup (Fin 6) => cls g.1 = 5).card = 144 := by
  unfold cls
  decide +kernel

@[expose] def bx : Perm (Fin 6) := swap 0 1 * swap 2 3

@[expose] def u1 : Perm (Fin 6) := swap 0 1 * swap 4 5

@[expose] def u2 : Perm (Fin 6) := swap 2 3 * swap 4 5

@[expose] def u3 : Perm (Fin 6) := swap 0 2 * swap 1 3

@[expose] def u4 : Perm (Fin 6) := swap 0 3 * swap 1 2

set_option maxRecDepth 100000 in
theorem comm_bx : ∀ y : Perm (Fin 6), sign y = 1 → y * y = 1 → y ≠ 1 → y ≠ bx → y * bx = bx * y →
    y = u1 ∨ y = u2 ∨ y = u3 ∨ y = u4 := by
  unfold bx u1 u2 u3 u4
  decide +kernel

theorem sign_bx : sign bx = 1 := by unfold bx; decide

theorem bx_sq : bx * bx = 1 := by unfold bx; decide

theorem bx_ne : bx ≠ 1 := by unfold bx; decide

theorem klein_conj (c d : Perm (Fin 6)) (hc : sign c = 1) (hd : sign d = 1) (hc1 : c ≠ 1) (hd1 : d ≠ 1)
    (hcd : c ≠ d) (hc2 : c * c = 1) (hd2 : d * d = 1) (hcomm : c * d = d * c) :
    ∃ r : Perm (Fin 6), sign r = 1 ∧ r * c * r⁻¹ = bx ∧
      (r * d * r⁻¹ = u1 ∨ r * d * r⁻¹ = u2 ∨ r * d * r⁻¹ = u3 ∨ r * d * r⁻¹ = u4) := by
  have hcA : c ∈ alternatingGroup (Fin 6) := mem_alternatingGroup.mpr hc
  have hbxA : bx ∈ alternatingGroup (Fin 6) := mem_alternatingGroup.mpr sign_bx
  obtain ⟨r, hrA, hr⟩ := CFSG.Quasithin.S143.alt6_invol_conj c bx hcA hbxA hc1 bx_ne hc2 bx_sq
  refine ⟨r, mem_alternatingGroup.mp hrA, hr, ?_⟩
  have h1 : sign (r * d * r⁻¹) = 1 := by
    have := mem_alternatingGroup.mp hrA
    simp [sign_mul, sign_inv, hd, this]
  have h2 : (r * d * r⁻¹) * (r * d * r⁻¹) = 1 := by
    calc (r * d * r⁻¹) * (r * d * r⁻¹) = r * (d * d) * r⁻¹ := by group
      _ = 1 := by rw [hd2]; group
  have h3 : r * d * r⁻¹ ≠ 1 := by
    intro h
    apply hd1
    have := congrArg (fun t => r⁻¹ * t * r) h
    simpa [mul_assoc] using this
  have h4 : r * d * r⁻¹ ≠ bx := by
    intro h
    apply hcd
    rw [← hr] at h
    have := congrArg (fun t => r⁻¹ * t * r) h
    simpa [mul_assoc] using this.symm
  have h5 : (r * d * r⁻¹) * bx = bx * (r * d * r⁻¹) := by
    rw [← hr]
    calc (r * d * r⁻¹) * (r * c * r⁻¹) = r * (d * c) * r⁻¹ := by group
      _ = r * (c * d) * r⁻¹ := by rw [hcomm]
      _ = (r * c * r⁻¹) * (r * d * r⁻¹) := by group
  exact comm_bx _ h1 h2 h3 h4 h5

@[expose] def NormV (g a b : Perm (Fin 6)) : Prop :=
  (g * a * g⁻¹ = a ∨ g * a * g⁻¹ = b ∨ g * a * g⁻¹ = a * b) ∧
    (g * b * g⁻¹ = a ∨ g * b * g⁻¹ = b ∨ g * b * g⁻¹ = a * b)

set_option maxRecDepth 100000 in
theorem normV_B : ∀ u : Perm (Fin 6), (u = u1 ∨ u = u2) → ∀ g : Perm (Fin 6), sign g = 1 →
    g * g * g = 1 → g ≠ 1 → NormV g bx u → ∀ i, g i ≠ i := by
  unfold bx u1 u2 NormV
  decide +kernel

set_option maxRecDepth 100000 in
theorem normV_A : ∀ u : Perm (Fin 6), (u = u3 ∨ u = u4) → ∀ g : Perm (Fin 6), sign g = 1 →
    g * g * g = 1 → g ≠ 1 → NormV g bx u → ∃ i, g i = i := by
  unfold bx u3 u4 NormV
  decide +kernel

set_option maxRecDepth 100000 in
theorem exists_B : ∀ u : Perm (Fin 6), (u = u1 ∨ u = u2) → ∃ g : Perm (Fin 6), sign g = 1 ∧
    g * g * g = 1 ∧ g ≠ 1 ∧ NormV g bx u ∧ ∀ i, g i ≠ i := by
  unfold bx u1 u2 NormV
  decide +kernel

set_option maxRecDepth 100000 in
theorem exists_A : ∀ u : Perm (Fin 6), (u = u3 ∨ u = u4) → ∃ g : Perm (Fin 6), sign g = 1 ∧
    g * g * g = 1 ∧ g ≠ 1 ∧ NormV g bx u ∧ ∃ i, g i = i := by
  unfold bx u3 u4 NormV
  decide +kernel

end CFSG.Quasithin.A6Fin
