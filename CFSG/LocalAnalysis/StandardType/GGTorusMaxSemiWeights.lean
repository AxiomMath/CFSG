module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CFSG.RankThree.SubgroupLists2.SpectralBounds

public section

namespace CFSG.StandardType.FrameRoute

open Matrix
open CFSG.RankThree.SubgroupLists

private lemma natCast_ne_zero_of_odd {L : Type*} [Field L] [CharP L 2] {n : ℕ} (hn : Odd n) :
    (n : L) ≠ 0 := by
  intro h0
  have h2 : 2 ∣ n := (CharP.cast_eq_zero_iff L 2 n).mp h0
  rw [Nat.dvd_iff_mod_eq_zero] at h2
  have h1 : n % 2 = 1 := Nat.odd_iff.mp hn
  omega

theorem tmWt_weights {F : Type} [Field F] [Finite F] [CharP F 2] (d : ℕ)
    (C : Subgroup (GL (Fin d) F)) (hab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (hodd : Odd (Nat.card C)) :
    ∃ Λ : Finset (↥C →* (AlgebraicClosure F)ˣ),
      Λ.card ≤ d ∧
      (∀ χ ∈ Λ, ∃ v : Fin d → AlgebraicClosure F, v ≠ 0 ∧ ∀ a : C,
        (((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
          (algebraMap F (AlgebraicClosure F))).mulVec v =
            ((χ a : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) • v) ∧
      (∀ a : C, (∀ χ ∈ Λ, χ a = 1) → a = 1) ∧
      (∀ (g : GL (Fin d) F) (τ : MulAut ↥C),
        (∀ a : C, ((τ a : C) : GL (Fin d) F) = g * (a : GL (Fin d) F) * g⁻¹) →
          ∀ χ ∈ Λ, χ.comp τ.toMonoidHom ∈ Λ) := by
  classical
  set L := AlgebraicClosure F
  set f := algebraMap F L
  let Φ : GL (Fin d) F →* Matrix (Fin d) (Fin d) L :=
    { toFun := fun u => (((u : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)).map (algebraMap F L)
      map_one' := by
        change (1 : Matrix (Fin d) (Fin d) F).map (algebraMap F L) = 1
        exact Matrix.map_one (algebraMap F L) (map_zero _) (map_one _)
      map_mul' := by
        intro u v
        show ((((u * v : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F)).map (algebraMap F L) =
          (((u : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F).map (algebraMap F L) *
            (((v : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F).map (algebraMap F L)
        rw [Units.val_mul, Matrix.map_mul] }
  let A : ↥C → Matrix (Fin d) (Fin d) L := fun a => Φ (a : GL (Fin d) F)
  have hcomm : ∀ a b : ↥C, A a * A b = A b * A a := by
    intro a b
    have hab' : a * b = b * a := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hab a a.2 b b.2
    have h : (a : GL (Fin d) F) * (b : GL (Fin d) F) =
        (b : GL (Fin d) F) * (a : GL (Fin d) F) := by
      simpa only [Subgroup.coe_mul] using
        congrArg (fun x : ↥C => (x : GL (Fin d) F)) hab'
    calc A a * A b = Φ ((a : GL (Fin d) F) * (b : GL (Fin d) F)) := (map_mul Φ _ _).symm
      _ = Φ ((b : GL (Fin d) F) * (a : GL (Fin d) F)) := by rw [h]
      _ = A b * A a := map_mul Φ _ _
  have hpow : ∀ a : ↥C, A a ^ Nat.card ↥C = 1 := by
    intro a
    have ha : (a : GL (Fin d) F) ^ Nat.card ↥C = 1 := by
      have h : ((a ^ Nat.card ↥C : ↥C) : GL (Fin d) F) =
          (a : GL (Fin d) F) ^ Nat.card ↥C :=
        map_pow (Subgroup.subtype C) a (Nat.card ↥C)
      rw [pow_card_eq_one'] at h
      simpa using h.symm
    calc A a ^ Nat.card ↥C = Φ ((a : GL (Fin d) F) ^ Nat.card ↥C) := (map_pow Φ _ _).symm
      _ = Φ (1 : GL (Fin d) F) := by rw [ha]
      _ = 1 := map_one Φ
  have hchar : (Nat.card ↥C : L) ≠ 0 := natCast_ne_zero_of_odd hodd
  obtain ⟨P, hP, D, hD⟩ :=
    exists_simultaneous_diagonal A hcomm (fun a => ⟨Nat.card ↥C, hchar, hpow a⟩)
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hdiag : ∀ a : ↥C, diagonal (D a) = P⁻¹ * A a * P := by
    intro a
    rw [Matrix.mul_assoc, hD a, ← Matrix.mul_assoc, nonsing_inv_mul _ hPdet, Matrix.one_mul]
  have hD_mul : ∀ a b : ↥C, ∀ j, D (a * b) j = D a j * D b j := by
    intro a b j
    have hAB : A (a * b) = A a * A b := by
      show Φ ((a * b : ↥C) : GL (Fin d) F) =
        Φ (a : GL (Fin d) F) * Φ (b : GL (Fin d) F)
      rw [Subgroup.coe_mul, map_mul Φ]
    have h : diagonal (D (a * b)) = diagonal (D a) * diagonal (D b) := by
      rw [hdiag, hdiag, hdiag, hAB]
      calc P⁻¹ * (A a * A b) * P = P⁻¹ * A a * (P * P⁻¹) * A b * P := by
            rw [mul_nonsing_inv _ hPdet, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = P⁻¹ * A a * P * (P⁻¹ * A b * P) := by simp only [Matrix.mul_assoc]
    rw [diagonal_mul_diagonal] at h
    exact congrFun (diagonal_injective h) j
  have hm : Nat.card ↥C ≠ 0 := fun h => hchar (by rw [h, Nat.cast_zero])
  have hd0 : ∀ a j, D a j ≠ 0 := by
    intro a j h0
    have := pow_eq_one_of_mul_eq_mul_diagonal hP (hD a) (hpow a) j
    rw [h0, zero_pow hm] at this
    exact zero_ne_one this
  have hD_one : ∀ j, D 1 j = 1 := by
    intro j
    have h := hD_mul 1 1 j
    rw [one_mul] at h
    exact (mul_left_cancel₀ (hd0 1 j) ((mul_one _).trans h)).symm
  let χw : Fin d → (↥C →* Lˣ) := fun j =>
    { toFun := fun a => Units.mk0 (D a j) (hd0 a j)
      map_one' := by
        apply Units.ext
        simp [hD_one j]
      map_mul' := by
        intro a b
        apply Units.ext
        simp [hD_mul a b j] }
  set v : Fin d → (Fin d → L) := fun j => P *ᵥ Pi.single j 1 with hv
  have hv0 : ∀ j, v j ≠ 0 := by
    intro j h0
    have h0' : P *ᵥ Pi.single j 1 = 0 := h0
    have h : P⁻¹ *ᵥ (P *ᵥ Pi.single j 1) = P⁻¹ *ᵥ 0 := by rw [h0']
    rw [mulVec_mulVec, nonsing_inv_mul _ hPdet, one_mulVec, mulVec_zero] at h
    have := congrFun h j
    simp at this
  have hAv : ∀ a j, A a *ᵥ v j = D a j • v j := by
    intro a j
    have hs : Pi.single j (D a j * 1) = D a j • (Pi.single j 1 : Fin d → L) := by
      ext i
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    rw [hv, mulVec_mulVec, hD a, ← mulVec_mulVec, diagonal_mulVec_single, hs, mulVec_smul]
  have heig : ∀ (w : Fin d → L), w ≠ 0 → ∀ ψ : ↥C → L,
      (∀ a, A a *ᵥ w = ψ a • w) → ∃ k, ∀ a, D a k = ψ a := by
    intro w hw ψ hψ
    set z := P⁻¹ *ᵥ w with hz
    have hPz : P *ᵥ z = w := by rw [hz, mulVec_mulVec, mul_nonsing_inv _ hPdet, one_mulVec]
    have hz0 : z ≠ 0 := by
      intro h0
      apply hw
      rw [← hPz, h0, mulVec_zero]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hz0
    refine ⟨j, fun a => ?_⟩
    have hdz : diagonal (D a) *ᵥ z = ψ a • z := by
      rw [hdiag, ← mulVec_mulVec, hPz, ← mulVec_mulVec, hψ a, mulVec_smul]
    have := congrFun hdz j
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hj this
  set Λ : Finset (↥C →* Lˣ) := Finset.univ.image χw with hΛ
  have hΛcard : Λ.card ≤ d := by
    rw [hΛ]
    calc (Finset.univ.image χw).card ≤ (Finset.univ : Finset (Fin d)).card :=
          Finset.card_image_le
      _ = d := Finset.card_fin d
  refine ⟨Λ, hΛcard, ?_, ?_, ?_⟩
  · intro χ hχ
    obtain ⟨j, -, hχj⟩ := Finset.mem_image.mp hχ
    subst hχj
    exact ⟨v j, hv0 j, fun a => hAv a j⟩
  · intro a ha
    have hDa : D a = fun _ => 1 := by
      funext j
      have h1 : χw j a = 1 :=
        ha (χw j) (by rw [hΛ]; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      have h2 : ((χw j a : Lˣ) : L) = 1 := by rw [h1, Units.val_one]
      simpa [χw] using h2
    have hd1 : diagonal (D a) = 1 := by rw [hDa, Matrix.diagonal_one]
    have hA1 : A a = 1 := by
      calc A a = A a * P * P⁻¹ := by
            rw [Matrix.mul_assoc, mul_nonsing_inv _ hPdet, Matrix.mul_one]
        _ = 1 := by rw [hD a, hd1, Matrix.mul_one, mul_nonsing_inv _ hPdet]
    have hΦinj : Function.Injective Φ := by
      intro u v huv
      apply Units.ext
      apply Matrix.map_injective (algebraMap F L).injective
      exact huv
    apply Subtype.ext
    exact hΦinj (by simpa [A] using hA1)
  · intro g τ hτ χ hχ
    obtain ⟨j, -, hχj⟩ := Finset.mem_image.mp hχ
    subst hχj
    let Ag : Matrix (Fin d) (Fin d) L := Φ g
    let Ag' : Matrix (Fin d) (Fin d) L := Φ (g⁻¹)
    have hAg : Ag * Ag' = 1 := by
      show Φ g * Φ g⁻¹ = 1
      rw [← map_mul Φ, mul_inv_cancel, map_one]
    have hAg' : Ag' * Ag = 1 := by
      show Φ g⁻¹ * Φ g = 1
      rw [← map_mul Φ, inv_mul_cancel, map_one]
    have hτA : ∀ a : ↥C, A (τ a) = Ag * A a * Ag' := by
      intro a
      have h := congrArg Φ (hτ a)
      rw [map_mul, map_mul] at h
      simpa only [A, Ag, Ag'] using h
    have hw : Ag' *ᵥ v j ≠ 0 := by
      intro h0
      apply hv0 j
      have h := congrArg (fun z => Ag *ᵥ z) h0
      rw [mulVec_zero, mulVec_mulVec, hAg, one_mulVec] at h
      exact h
    have hψ : ∀ a : ↥C, A a *ᵥ (Ag' *ᵥ v j) = D (τ a) j • (Ag' *ᵥ v j) := by
      intro a
      have hA' : A a = Ag' * A (τ a) * Ag := by
        rw [hτA a]
        calc A a = (Ag' * Ag) * A a * (Ag' * Ag) := by
              rw [hAg', Matrix.one_mul, Matrix.mul_one]
          _ = Ag' * (Ag * A a * Ag') * Ag := by simp only [Matrix.mul_assoc]
      calc A a *ᵥ (Ag' *ᵥ v j)
          = ((Ag' * A (τ a) * Ag) * Ag') *ᵥ v j := by rw [hA', mulVec_mulVec]
        _ = (Ag' * A (τ a) * (Ag * Ag')) *ᵥ v j := by simp only [Matrix.mul_assoc]
        _ = (Ag' * A (τ a)) *ᵥ v j := by rw [hAg, Matrix.mul_one]
        _ = Ag' *ᵥ (A (τ a) *ᵥ v j) := by rw [← mulVec_mulVec]
        _ = Ag' *ᵥ (D (τ a) j • v j) := by rw [hAv]
        _ = D (τ a) j • (Ag' *ᵥ v j) := by rw [mulVec_smul]
    obtain ⟨k, hk⟩ := heig (Ag' *ᵥ v j) hw (fun a => D (τ a) j) hψ
    refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
    have hcomp : (χw j).comp τ.toMonoidHom = χw k := by
      refine MonoidHom.ext fun a => ?_
      apply Units.ext
      exact (hk a).symm
    exact hcomp.symm

end CFSG.StandardType.FrameRoute

end
