module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3Frame
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PSplitDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def L3FrameExists (t : CFSG.Open.StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → 5 ≤ p → LieModel X t 3 p 1 →
    Subgroup.center X = ⊥ ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k p) (F : L3Frame (MulAut X) p k),
        F.I = (MulAut.conj : X →* MulAut X).range ∧
          ∃ K₀ : Subgroup X, ⁅K₀, K₀⁆ = K₀ ∧ Nat.card K₀ = p * (p ^ 2 - 1) ∧
            F.Kb = K₀.map (MulAut.conj : X →* MulAut X)

@[expose] def L3ThreeNoFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X], (LieModel X .PSL 3 3 1 ∨ LieModel X .PSU 3 3 1) →
    ¬ 5 ∣ Nat.card (MulAut X)

private theorem mul_conj_mul_inv {X : Type} [Group X] (d : MulAut X) (y : X) :
    d * MulAut.conj y * d⁻¹ = MulAut.conj (d y) := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

private theorem conj_injective {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro a b hab
  have hc : b⁻¹ * a ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h : a * z * a⁻¹ = b * z * b⁻¹ := by
      simpa only [MulAut.conj_apply] using congrArg (fun φ : MulAut X => φ z) hab
    calc z * (b⁻¹ * a) = b⁻¹ * (b * z * b⁻¹) * a := by group
      _ = b⁻¹ * (a * z * a⁻¹) * a := by rw [h]
      _ = b⁻¹ * a * z := by group
  rw [hZ, Subgroup.mem_bot] at hc
  calc a = b * (b⁻¹ * a) := by group
    _ = b := by rw [hc, mul_one]

theorem l3InvertSplit_of_frames (hlin : L3FrameExists .PSL)
    (huni : L3FrameExists .PSU) (h3 : L3ThreeNoFive) : L3InvertSplit := by
  intro X _ _ p hp hp2 hX A S B hIA hS hBA hBab hBodd h3B h5B hperm hinv
  have : Finite (MulAut X) :=
    Finite.of_injective (fun α : MulAut X => (α : X → X)) DFunLike.coe_injective
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp3 : p = 3
  · subst hp3
    exact absurd (dvd_trans h5B (Subgroup.card_subgroup_dvd_card B)) (h3 X hX)
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra h
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  obtain ⟨hZ, k, _, _, _, F, hFI, K₀, hK₀, hK₀c, hFK⟩ :=
    hX.elim (hlin X p hp hp5) (huni X p hp hp5)
  refine F.exists_inv hp5 (hFI.le.trans hIA) hS hBab hBodd h3B h5B hperm ?_
  rintro g hg d hdB hdp hdK
  rw [hFI] at hg
  obtain ⟨x₀, rfl⟩ := hg
  let f : X →* X := (MulAut.conj x₀).toMonoidHom
  have hfinj : Function.Injective f := fun _ _ h => (MulAut.conj x₀).injective h
  refine hinv (K₀.map f) ?_ ?_ d hdB hdp ?_
  · rw [← Subgroup.map_commutator, hK₀]
  · rw [Subgroup.card_map_of_injective hfinj, hK₀c]
  · rintro _ ⟨y, hy, rfl⟩
    have hyK : MulAut.conj y ∈ F.Kb := by
      rw [hFK]
      exact ⟨y, hy, rfl⟩
    have h := hdK _ hyK
    have hconj : MulAut.conj x₀ * MulAut.conj y * (MulAut.conj x₀)⁻¹ = MulAut.conj (f y) := by
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [hconj] at h
    apply conj_injective hZ
    rw [← mul_conj_mul_inv, h, mul_inv_cancel_right]

end CFSG.LocalAnalysis.UniquenessCase.UC22
