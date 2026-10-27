module

public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.StabilizerTransitive

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

theorem normal_two_subgroup_fixes_subspace {n : ℕ} (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (K : Subgroup (GL (Fin n) (ZMod 2))) (hK2 : IsPGroup 2 K) (hKD : K ≤ stabMat n D)
    (hKn : ∀ s ∈ stabMat n D, ∀ k ∈ K, s * k * s⁻¹ ∈ K) :
    ∀ k ∈ K, ∀ u ∈ D, (k : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u = u := by
  by_cases hD : D = ⊥
  · intro k _ u hu
    rw [hD] at hu
    rw [(Submodule.mem_bot _).mp hu, Matrix.mulVec_zero]
  · letI : MulAction K D :=
      { smul := fun k u =>
          ⟨(k : GL (Fin n) (ZMod 2)).1 *ᵥ (u : Fin n → ZMod 2), (hKD k.2 u).mpr u.2⟩
        one_smul := fun u => Subtype.ext (by
          show ((1 : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
            (u : Fin n → ZMod 2) = u
          rw [Units.val_one, Matrix.one_mulVec])
        mul_smul := fun k l u => Subtype.ext (by
          show ((k * l : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
            (u : Fin n → ZMod 2) = (k : GL (Fin n) (ZMod 2)).1 *ᵥ
              ((l : GL (Fin n) (ZMod 2)).1 *ᵥ (u : Fin n → ZMod 2))
          rw [Units.val_mul, Matrix.mulVec_mulVec]) }
    have h0 : (0 : D) ∈ MulAction.fixedPoints K D := by
      rw [MulAction.mem_fixedPoints]
      intro k
      exact Subtype.ext (Matrix.mulVec_zero (k : GL (Fin n) (ZMod 2)).1)
    obtain ⟨b, hb, hne⟩ := hK2.exists_fixed_point_of_prime_dvd_card_of_fixed_point D
      (two_dvd_natCard_of_ne_bot D hD) h0
    have hw : (b : Fin n → ZMod 2) ∈ D := b.2
    have hw0 : (b : Fin n → ZMod 2) ≠ 0 := fun h => hne (Subtype.ext h.symm)
    have hwfix : ∀ k ∈ K, (k : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ (b : Fin n → ZMod 2) =
        (b : Fin n → ZMod 2) := fun k hk =>
      congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hb) ⟨k, hk⟩)
    intro k hk u hu
    by_cases hu0 : u = 0
    · rw [hu0, Matrix.mulVec_zero]
    · obtain ⟨T, hT, hTw⟩ := exists_mem_stabMat_mulVec_eq D hw hu hw0 hu0
      have hmem : T⁻¹ * k * T ∈ K := by
        have h := hKn T⁻¹ ((stabMat n D).inv_mem hT) k hk
        rwa [inv_inv] at h
      have e : k * T = T * (T⁻¹ * k * T) := by group
      have h1 : ((k * T : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
          (b : Fin n → ZMod 2) = (T : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ (b : Fin n → ZMod 2) := by
        rw [e, Units.val_mul, ← Matrix.mulVec_mulVec, hwfix _ hmem]
      rw [← hTw, Matrix.mulVec_mulVec, ← Units.val_mul]
      exact h1

end CFSG.ASVolI.ChH
