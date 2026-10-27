module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubflag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

namespace SP207Lin

variable {m : ℕ} {K : Type*} [Field K]

theorem reflectionMatrix_mul_diagonal {i : ℕ} (hi : 1 ≤ i) (hin : i < m) (d : Fin m → K) :
    LinearFlag.reflectionMatrix m K i *
        diagonal (fun b => d (Equiv.swap (⟨i - 1, by omega⟩ : Fin m) ⟨i, hin⟩ b)) =
      diagonal d * LinearFlag.reflectionMatrix m K i := by
  rw [LinearFlag.reflectionMatrix_eq i hi hin]
  ext a b
  rw [mul_diagonal, mul_diagonal, diagonal_mul, mul_diagonal, LinearFlag.permMatrix_apply]
  by_cases h : a = Equiv.swap (⟨i - 1, by omega⟩ : Fin m) ⟨i, hin⟩ b
  · subst h
    simp only [if_true]
    ring
  · simp [h]

end SP207Lin

theorem uc22sp207_not_dvd_card_sub_one {m : ℕ} (hm : 3 ≤ m) {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] [Finite X] (α : SpecialLinearGroup (Fin m) K →* X)
    (hαc : α.ker ≤ center (SpecialLinearGroup (Fin m) K)) {I : Set ℕ} {i : ℕ} (hi : i ∈ I)
    (hi1 : 1 ≤ i) (him : i < m) {Y : Subgroup X} (hY : Y.comap α = LinearFlag.flagStabilizer m K I)
    {p : ℕ} (hp : p.Prime) (hYp : IsStronglyPEmbedded p Y) : ¬ p ∣ Nat.card K - 1 := by
  intro hpq
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  have hζp : (ζ : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hζ, pow_orderOf_eq_one, Units.val_one]
  have hζ1 : (ζ : K) ≠ 1 := fun h => by
    have := hζ
    rw [Units.ext (h.trans Units.val_one.symm), orderOf_one] at this
    exact hp.one_lt.ne this
  have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨1, by omega⟩
  let c : Fin m := ⟨2, by omega⟩
  let d : Fin m → K := fun j =>
    if (j : ℕ) = 0 then (ζ : K) else if (j : ℕ) = 1 then (ζ : K)⁻¹ else 1
  have hprod : ∏ j, d j = 1 := by
    rw [Fintype.prod_eq_mul a b (fun h => by simpa [a, b] using congrArg Fin.val h) fun j hj => ?_]
    · simp [d, a, b, hζ0]
    · have h0 : (j : ℕ) ≠ 0 := fun h => hj.1 (Fin.ext h)
      have h1 : (j : ℕ) ≠ 1 := fun h => hj.2 (Fin.ext h)
      simp [d, h0, h1]
  set τ : Equiv.Perm (Fin m) := Equiv.swap (⟨i - 1, by omega⟩ : Fin m) ⟨i, him⟩ with hτ
  have hprod' : ∏ j, d (τ j) = 1 := by rw [Equiv.prod_comp τ d, hprod]
  let x : SpecialLinearGroup (Fin m) K := ⟨diagonal d, by rw [det_diagonal]; exact hprod⟩
  let y : SpecialLinearGroup (Fin m) K := ⟨diagonal fun j => d (τ j), by
    rw [det_diagonal]; exact hprod'⟩
  let g := LinearFlag.reflection m K i hi1 him
  have hdiag : ∀ z : SpecialLinearGroup (Fin m) K, (∃ e : Fin m → K,
      (z : Matrix (Fin m) (Fin m) K) = diagonal e) → z ∈ LinearFlag.flagStabilizer m K I := by
    rintro z ⟨e, he⟩
    refine LinearFlag.upperTriangular_le_flagStabilizer I fun r s hrs => ?_
    rw [he, diagonal_apply_ne _ (ne_of_gt hrs)]
  have hgy : g * y = x * g :=
    Subtype.ext (by
      change LinearFlag.reflectionMatrix m K i * diagonal (fun j => d (τ j)) =
        diagonal d * LinearFlag.reflectionMatrix m K i
      exact SP207Lin.reflectionMatrix_mul_diagonal hi1 him d)
  have hg : g ∉ Y.comap α := by
    rw [hY]
    exact fun h => (((LinearFlag.subflag_stabilizer_generation (K := K) (n := m) I).2.2 i hi1
      him).1 h) hi
  have hx : x ∈ Y.comap α ⊓ (Y.comap α).map (MulAut.conj g).toMonoidHom := by
    rw [hY]
    refine ⟨hdiag x ⟨d, rfl⟩, y, hdiag y ⟨_, rfl⟩, ?_⟩
    change g * y * g⁻¹ = x
    rw [hgy, mul_assoc, mul_inv_cancel, mul_one]
  have hxp : x ^ p = 1 := by
    have hdp : d ^ p = 1 := by
      funext j
      by_cases h0 : (j : ℕ) = 0
      · simp [d, h0, hζp]
      · by_cases h1 : (j : ℕ) = 1
        · simp [d, h1, inv_pow, hζp]
        · simp [d, h0, h1]
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    change (diagonal d) ^ p = 1
    rw [diagonal_pow, hdp]
    exact diagonal_one
  have hxz : x ∉ center (SpecialLinearGroup (Fin m) K) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    rintro ⟨r, -, hr⟩
    have h0 := congr_fun (congr_fun hr a) a
    have h2 := congr_fun (congr_fun hr c) c
    simp [x, d, a, c, scalar_apply] at h0 h2
    exact hζ1 (h0.symm.trans h2)
  exact uc22sp207_not_isStronglyPEmbedded_of_witness α hαc hp hg hx hxp hxz hYp

end CFSG.LocalAnalysis.UniquenessCase.UC22
