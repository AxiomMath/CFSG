module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16e_d5_tetra_dot : ∀ u v : Fin 4 → ZMod 3,
    (∀ i j : Fin 4, i ≠ j → u i * v j ≠ u j * v i) →
    ∀ p : Fin 4 → ZMod 3, (∀ i, p i ≠ 0) →
      ∑ i, p i * u i = 0 → ∑ i, p i * v i = 0 → False := by
  decide +kernel

theorem s16e_d5_cols_prop : ∀ ui vi uj vj : ZMod 3, ui * vj = uj * vi →
    ∃ a b : ZMod 3, (a ≠ 0 ∨ b ≠ 0) ∧ a * ui + b * vi = 0 ∧ a * uj + b * vj = 0 := by
  decide

private lemma s16e_d5_apply_eq_sum (f : (Fin 4 → ZMod 3) →ₗ[ZMod 3] ZMod 3)
    (x : Fin 4 → ZMod 3) : f x = ∑ i, x i * f (Pi.single i 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  congr 1
  apply congrArg f
  funext j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem s16e_d5_tetra {u v : Multiplicative (Fin 4 → ZMod 3)}
    (huv : ∀ i j : Fin 4, i ≠ j →
      (Multiplicative.toAdd u) i * (Multiplicative.toAdd v) j ≠
        (Multiplicative.toAdd u) j * (Multiplicative.toAdd v) i)
    {S : Subgroup (Multiplicative (Fin 4 → ZMod 3))} (hu : u ∈ S) (hv : v ∈ S)
    (hS : 27 ≤ Nat.card ↥S) :
    ∃ i : Fin 4, Multiplicative.ofAdd (Pi.single i (1 : ZMod 3)) ∈ S := by
  classical
  let S' : Submodule (ZMod 3) (Fin 4 → ZMod 3) :=
    AddSubgroup.toZModSubmodule 3 (Subgroup.toAddSubgroup' S)
  have hmemS' : ∀ x : Fin 4 → ZMod 3, x ∈ S' ↔ Multiplicative.ofAdd x ∈ S :=
    fun _ => Iff.rfl
  have hcardS' : 27 ≤ Nat.card ↥S' := by
    have e : ↥S' ≃ ↥S :=
      { toFun := fun x => ⟨Multiplicative.ofAdd x.1, (hmemS' x.1).mp x.2⟩
        invFun := fun y =>
          ⟨Multiplicative.toAdd y.1, (hmemS' _).mpr (by simpa using y.2)⟩
        left_inv := fun x => by ext; simp
        right_inv := fun y => by ext; simp }
    rw [Nat.card_congr e]
    exact hS
  have hpow : (3 : ℕ) ^ 3 ≤ 3 ^ Module.finrank (ZMod 3) S' := by
    have hcard3 : Nat.card ↥S' = 3 ^ Module.finrank (ZMod 3) S' := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3), ZMod.card 3]
    rw [hcard3] at hcardS'
    norm_num at hcardS' ⊢
    exact hcardS'
  have hfr : 3 ≤ Module.finrank (ZMod 3) S' :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow
  by_cases htop : S' = ⊤
  · refine ⟨0, ?_⟩
    have hmem : (Pi.single 0 (1 : ZMod 3) : Fin 4 → ZMod 3) ∈ S' := by
      rw [htop]; exact Submodule.mem_top
    exact hmem
  · have hSlt : S' < ⊤ := lt_of_le_of_ne le_top htop
    obtain ⟨f, hf, hSle⟩ := Submodule.exists_le_ker_of_lt_top S' hSlt
    have hu' : Multiplicative.toAdd u ∈ S' :=
      (hmemS' (Multiplicative.toAdd u)).mpr (by simpa using hu)
    have hv' : Multiplicative.toAdd v ∈ S' :=
      (hmemS' (Multiplicative.toAdd v)).mpr (by simpa using hv)
    have hfu : f (Multiplicative.toAdd u) = 0 := (LinearMap.mem_ker (f := f)).mp (hSle hu')
    have hfv : f (Multiplicative.toAdd v) = 0 := (LinearMap.mem_ker (f := f)).mp (hSle hv')
    have hsumu : ∑ i, f (Pi.single i 1) * (Multiplicative.toAdd u) i = 0 := by
      calc ∑ i, f (Pi.single i 1) * (Multiplicative.toAdd u) i
          = ∑ i, (Multiplicative.toAdd u) i * f (Pi.single i 1) :=
            Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = f (Multiplicative.toAdd u) := (s16e_d5_apply_eq_sum f _).symm
        _ = 0 := hfu
    have hsumv : ∑ i, f (Pi.single i 1) * (Multiplicative.toAdd v) i = 0 := by
      calc ∑ i, f (Pi.single i 1) * (Multiplicative.toAdd v) i
          = ∑ i, (Multiplicative.toAdd v) i * f (Pi.single i 1) :=
            Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = f (Multiplicative.toAdd v) := (s16e_d5_apply_eq_sum f _).symm
        _ = 0 := hfv
    have hzero : ∃ i : Fin 4, f (Pi.single i 1) = 0 := by
      by_contra h
      rw [not_exists] at h
      exact s16e_d5_tetra_dot (Multiplicative.toAdd u) (Multiplicative.toAdd v) huv
        (fun i => f (Pi.single i 1)) h hsumu hsumv
    obtain ⟨i, hi⟩ := hzero
    have hfinV : Module.finrank (ZMod 3) (Fin 4 → ZMod 3) = 4 := by
      simp
    have hkerfin : Module.finrank (ZMod 3) (LinearMap.ker f) = 3 := by
      have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := f) hf
      rw [hfinV] at h
      omega
    have hle_fin : Module.finrank (ZMod 3) S' ≤ Module.finrank (ZMod 3) (LinearMap.ker f) :=
      Submodule.finrank_mono hSle
    have hS'eq : S' = LinearMap.ker f :=
      Submodule.eq_of_le_of_finrank_eq hSle (by omega)
    refine ⟨i, ?_⟩
    have hmem : (Pi.single i (1 : ZMod 3) : Fin 4 → ZMod 3) ∈ S' := by
      rw [hS'eq]
      exact (LinearMap.mem_ker (f := f)).mpr hi
    exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
