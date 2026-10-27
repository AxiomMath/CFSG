module

public import CFSG.Quasithin.Background.FLcModel

public section

namespace CFSG.Quasithin.FLc

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def Yk (n k : ℕ) : Subgroup (Multiplicative (Vt n)) :=
  subgroupOfSpace (flagSpace n (ZMod 2) k)

theorem mem_Yk {n k : ℕ} {x : Multiplicative (Vt n)} :
    x ∈ Yk n k ↔ ∀ j : Fin n, k ≤ (j : ℕ) → Multiplicative.toAdd x j = 0 := by
  rw [Yk, mem_subgroupOfSpace, mem_flagSpace]

theorem card_Yk {n k : ℕ} (hk : k ≤ n) : Nat.card (Yk n k) = 2 ^ k := by
  rw [Yk, card_subgroupOfSpace, finrank_flagSpace hk]

theorem sInvG_Ut_Yk (n k : ℕ) : SInvG (Ut n) (Yk n k) := by
  intro q hq x hx
  have h := flagSpace_invariant k (unitriangular_le_upperTriangular n (ZMod 2) hq) hx
  exact h

theorem eq_Yk_of_Ut_invariant {n k : ℕ} {X : Subgroup (Multiplicative (Vt n))}
    (hX : SInvG (Ut n) X) (hc : Nat.card X = 2 ^ k) : X = Yk n k := by
  have h1 : SInv (Ut n) (spaceOfSubgroup X) := fun q hq v hv => hX q hq (Multiplicative.ofAdd v) hv
  obtain ⟨m, hm, hXm⟩ := eq_flagSpace_of_invariant (K := ZMod 2) (n := n) h1
  have h2 : finrank (ZMod 2) (spaceOfSubgroup X) = k := by
    have h3 := card_subgroupOfSpace (spaceOfSubgroup X)
    rw [subgroupOfSpace_spaceOfSubgroup, hc] at h3
    exact (Nat.pow_right_injective le_rfl h3).symm
  rw [hXm, finrank_flagSpace hm] at h2
  rw [← subgroupOfSpace_spaceOfSubgroup X, hXm, h2]
  rfl

theorem mem_stabilizer_iff {n : ℕ} {g : SLt n} {F : Submodule (ZMod 2) (Vt n)} :
    g ∈ stabilizer F ↔ ∀ v, v ∈ F ↔ mat g *ᵥ v ∈ F := by
  constructor
  · intro h v
    have hmap : F.map (mulVecLin (mat g)) = F := mem_stabilizer.1 h
    constructor
    · intro hv
      rw [← hmap]
      exact ⟨v, hv, rfl⟩
    · intro hv
      rw [← hmap] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have : w = v := by
        have h2 := congrArg (fun x => mat g⁻¹ *ᵥ x) hwv
        simp only [mulVecLin_apply, mulVec_mulVec] at h2
        have e : mat g⁻¹ * mat g = 1 := by
          rw [← mat_mul, inv_mul_cancel, mat_one]
        rw [e, one_mulVec, one_mulVec] at h2
        exact h2
      rw [← this]
      exact hw
  · intro h
    rw [mem_stabilizer]
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).1 hw
    · intro hv
      refine ⟨mat g⁻¹ *ᵥ v, ?_, ?_⟩
      · have e : mat g * mat g⁻¹ = 1 := mat_mul_inv g
        have := (h (mat g⁻¹ *ᵥ v)).2
        rw [mulVec_mulVec, e, one_mulVec] at this
        exact this hv
      · simp only [mulVecLin_apply, mulVec_mulVec, mat_mul_inv, one_mulVec]

@[expose] def actM {n : ℕ} (h : SLt n) : Multiplicative (Vt n) ≃* Multiplicative (Vt n) where
  toFun x := Multiplicative.ofAdd (mat h *ᵥ Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (mat h⁻¹ *ᵥ Multiplicative.toAdd x)
  left_inv x := by
    simp only [toAdd_ofAdd, mulVec_mulVec]
    rw [← mat_mul, inv_mul_cancel, mat_one, one_mulVec]
    rfl
  right_inv x := by
    simp only [toAdd_ofAdd, mulVec_mulVec]
    rw [← mat_mul, mul_inv_cancel, mat_one, one_mulVec]
    rfl
  map_mul' x y := by simp only [toAdd_mul, mulVec_add, ofAdd_add]

theorem toAdd_actM {n : ℕ} (h : SLt n) (x : Multiplicative (Vt n)) :
    Multiplicative.toAdd (actM h x) = mat h *ᵥ Multiplicative.toAdd x := rfl

end CFSG.Quasithin.FLc
