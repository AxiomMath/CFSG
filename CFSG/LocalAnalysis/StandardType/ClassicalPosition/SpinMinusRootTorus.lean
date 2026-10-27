module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Spin.Twisted.Datum

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted

private theorem conj_mem_minusRootGroup_of_frame
    {n : ℕ} {F : Type*} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (g : spinGroup (quadMinus n F b c)) (a : Fin (n - 1) → Bool → F)
    (hvec : ∀ i s, spinAction (quadMinus n F b c) g (minusVec n i s) =
      a i s • minusVec n i s)
    (hplane : ∀ p : Fin 2 → F, ∃ q : Fin 2 → F,
      spinAction (quadMinus n F b c) g (planeVec n p) = planeVec n q)
    (γ : Fin (n - 1) → ℤ) (hγ : γ ∈ (minusDatum n hirr).roots)
    (z : spinGroup (quadMinus n F b c)) (hz : z ∈ (minusDatum n hirr).rootGroup γ) :
    g * z * g⁻¹ ∈ (minusDatum n hirr).rootGroup γ := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with
    ⟨i, j, hij, s, t, hγ⟩ | ⟨i, s, hγ⟩
  · obtain ⟨x, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hγ).mp hz
    rw [(minusFrame n b c).conj_longRoot g hij s t hij s t (hvec i s) (hvec j t)]
    exact longRoot_mem_minusRootGroup n hirr hij s t hγ _
  · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hγ).mp hz
    obtain ⟨q, hq⟩ := hplane p
    rw [conj_twShortRoot n hirr g i s (hvec i s) hq]
    exact twShortRoot_mem_minusRootGroup n hirr i s hγ _

theorem mem_ggTorus_minusDatum_of_frame_lines
    {n : ℕ} {F : Type*} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (g : spinGroup (quadMinus n F b c))
    (hvec : ∀ i s, ∃ a : Fˣ,
      spinAction (quadMinus n F b c) g (minusVec n i s) = (a : F) • minusVec n i s)
    (hplane : ∀ p : Fin 2 → F, ∃ q : Fin 2 → F,
      spinAction (quadMinus n F b c) g (planeVec n p) = planeVec n q)
    (hplaneInv : ∀ p : Fin 2 → F, ∃ q : Fin 2 → F,
      spinAction (quadMinus n F b c) g⁻¹ (planeVec n p) = planeVec n q) :
    g ∈ ggTorus (minusDatum n hirr) := by
  classical
  choose a ha using hvec
  have hvecInv : ∀ i s, spinAction (quadMinus n F b c) g⁻¹ (minusVec n i s) =
      (((a i s)⁻¹ : Fˣ) : F) • minusVec n i s := by
    intro i s
    refine spinAction_inv_apply_of_apply _ _ ?_
    rw [map_smul, ha, smul_smul]
    simp
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ hγ
  refine Subgroup.mem_normalizer_iff.mpr fun z => ⟨?_, ?_⟩
  · exact conj_mem_minusRootGroup_of_frame hirr g (fun i s => (a i s : F))
      ha hplane γ hγ z
  · intro hz
    have h := conj_mem_minusRootGroup_of_frame hirr g⁻¹ (fun i s => (((a i s)⁻¹ : Fˣ) : F))
      hvecInv hplaneInv γ hγ (g * z * g⁻¹) hz
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
      mul_inv_cancel_right, mul_one] using h

theorem mem_ggTorus_minusDatum_of_frame_scalars
    {n : ℕ} {F : Type*} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (g : spinGroup (quadMinus n F b c)) (a : Fin (n - 1) → Bool → Fˣ)
    (hvec : ∀ i s, spinAction (quadMinus n F b c) g (minusVec n i s) =
      (a i s : F) • minusVec n i s)
    (hplane : ∀ p : Fin 2 → F,
      spinAction (quadMinus n F b c) g (planeVec n p) = planeVec n p) :
    g ∈ ggTorus (minusDatum n hirr) := by
  refine mem_ggTorus_minusDatum_of_frame_lines hirr g
    (fun i s => ⟨a i s, hvec i s⟩) (fun p => ⟨p, hplane p⟩) ?_
  exact fun p => ⟨p, spinAction_inv_apply_of_apply _ _ (hplane p)⟩

end CFSG.StandardType.ClassicalPosition
