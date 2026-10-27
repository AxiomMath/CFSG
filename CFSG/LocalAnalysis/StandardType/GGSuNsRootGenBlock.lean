module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock

public section

namespace CFSG.StandardType

namespace SuNsRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover
open CFSG.StandardType.TableBUE

variable {K : Type} [Field K] {d : ℕ}

theorem diagAt_of_commute_family {T : Set (Fin d → Kˣ)} {k : Fin d}
    (hsep : ∀ l, l ≠ k → ∃ σ ∈ T, σ k ≠ σ l) {g : GL (Fin d) K}
    (hg : ∀ σ ∈ T, g * diagHom d σ = diagHom d σ * g) :
    DiagAt k (g : Matrix (Fin d) (Fin d) K) := by
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · obtain ⟨σ, hσT, hσ⟩ := hsep l hl
    exact entry_eq_zero_of_commute (hg σ hσT) hσ
  · obtain ⟨σ, hσT, hσ⟩ := hsep l hl
    exact entry_eq_zero_of_commute (hg σ hσT) hσ.symm

private theorem diagAt_of_mul_eq_one {i : Fin d} {A B : Matrix (Fin d) (Fin d) K}
    (hA : DiagAt i A) (hAB : A * B = 1) (hBA : B * A = 1) : DiagAt i B := by
  have hne : A i i ≠ 0 := by
    intro h0
    have h := congrFun (congrFun hAB i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i
      (fun k _ hk => by rw [hA.1 k hk, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), h0, zero_mul, Matrix.one_apply_eq] at h
    exact zero_ne_one h
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have h := congrFun (congrFun hAB i) j
    rw [Matrix.mul_apply, Finset.sum_eq_single i
      (fun k _ hk => by rw [hA.1 k hk, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)] at h
    rw [Matrix.one_apply_ne (Ne.symm hj)] at h
    exact (mul_eq_zero.mp h).resolve_left hne
  · have h := congrFun (congrFun hBA j) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i
      (fun k _ hk => by rw [hA.2 k hk, mul_zero])
      (fun h => absurd (Finset.mem_univ i) h), Matrix.one_apply_ne hj] at h
    exact (mul_eq_zero.mp h).resolve_right hne

private theorem commutator_mem_blockSU_of_diagAt {n : ℕ} {S : Finset (Fin d)}
    {g g' : ↥(unitarySU 2 n K d)}
    (h1 : ∀ k ∉ S, DiagAt k ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (h2 : ∀ k ∉ S, DiagAt k ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    g * g' * g⁻¹ * g'⁻¹ ∈ blockSU S := by
  have h3 : ∀ k ∉ S, DiagAt k ((((g : GL (Fin d) K))⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) := fun k hk =>
    diagAt_of_mul_eq_one (h1 k hk) (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
      (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
  have h4 : ∀ k ∉ S, DiagAt k ((((g' : GL (Fin d) K))⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) := fun k hk =>
    diagAt_of_mul_eq_one (h2 k hk) (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
      (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
  have key : ∀ i ∉ S, DiagAt i
      ((((g * g' * g⁻¹ * g'⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) :
        Matrix (Fin d) (Fin d) K) ∧
      ((((g * g' * g⁻¹ * g'⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) :
        Matrix (Fin d) (Fin d) K) i i = 1 := by
    intro i hi
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    refine ⟨((h1 i hi).mul (h2 i hi)).mul (h3 i hi) |>.mul (h4 i hi), ?_⟩
    rw [(((h1 i hi).mul (h2 i hi)).mul (h3 i hi)).mul_apply (h4 i hi),
      ((h1 i hi).mul (h2 i hi)).mul_apply (h3 i hi), (h1 i hi).mul_apply (h2 i hi)]
    have e1 : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
        (((g : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = 1 := by
      rw [← (h1 i hi).mul_apply (h3 i hi), ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_apply_eq]
    have e2 : ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
        (((g' : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = 1 := by
      rw [← (h2 i hi).mul_apply (h4 i hi), ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_apply_eq]
    calc ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
          ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
          (((g : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
          (((g' : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i
        = (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
            (((g : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i) *
          (((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
            (((g' : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i) := by
          ring
      _ = 1 := by rw [e1, e2, mul_one]
  rintro i j (hi | hj)
  · obtain ⟨hd, h1⟩ := key i hi
    by_cases hij : j = i
    · subst hij
      rw [h1, Matrix.one_apply_eq]
    · rw [hd.1 j hij, Matrix.one_apply_ne (Ne.symm hij)]
  · obtain ⟨hd, h1⟩ := key j hj
    by_cases hij : i = j
    · subst hij
      rw [h1, Matrix.one_apply_eq]
    · rw [hd.2 i hij, Matrix.one_apply_ne hij]

theorem commutator_mem_blockSU_of_family {n : ℕ} {S : Finset (Fin d)}
    {T : Set (Fin d → Kˣ)}
    (hsep : ∀ k ∉ S, ∀ l, l ≠ k → ∃ σ ∈ T, σ k ≠ σ l) {g g' : ↥(unitarySU 2 n K d)}
    (hg : ∀ σ ∈ T, (g : GL (Fin d) K) * diagHom d σ = diagHom d σ * g)
    (hg' : ∀ σ ∈ T, (g' : GL (Fin d) K) * diagHom d σ = diagHom d σ * g') :
    g * g' * g⁻¹ * g'⁻¹ ∈ blockSU S :=
  commutator_mem_blockSU_of_diagAt
    (fun k hk => diagAt_of_commute_family (fun l hl => hsep k hk l hl) hg)
    (fun k hk => diagAt_of_commute_family (fun l hl => hsep k hk l hl) hg')

theorem conj_mem_blockSU_of_family {n : ℕ} {S : Finset (Fin d)}
    {T : Set (Fin d → Kˣ)}
    (hsep : ∀ k ∉ S, ∀ l, l ≠ k → ∃ σ ∈ T, σ k ≠ σ l)
    (hconst : ∀ σ ∈ T, ∀ a ∈ S, ∀ b ∈ S, σ a = σ b) {g x : ↥(unitarySU 2 n K d)}
    (hg : ∀ σ ∈ T, (g : GL (Fin d) K) * diagHom d σ = diagHom d σ * g)
    (hx : x ∈ blockSU (n := n) (K := K) S) :
    g * x * g⁻¹ ∈ blockSU S := by
  have hx' : ∀ σ ∈ T, (x : GL (Fin d) K) * diagHom d σ = diagHom d σ * x :=
    fun σ hσ => (diagHom_mul_comm_of_isBlockOn (hconst σ hσ) (mem_blockSU.mp hx)).symm
  have hcomm : g * x * g⁻¹ * x⁻¹ ∈ blockSU S :=
    commutator_mem_blockSU_of_family hsep hg hx'
  have hmul : (g * x * g⁻¹ * x⁻¹) * x ∈ blockSU S := (blockSU S).mul_mem hcomm hx
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul

end SuNsRootGen

end CFSG.StandardType
