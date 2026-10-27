module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdNode

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.SectionRank.OddCover CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD

variable {K : Type} [Field K] {n d : ℕ}

@[expose] def blockProj (K : Type) [Field K] (S : Finset (Fin d)) : Matrix (Fin d) (Fin d) K :=
  diagonal fun i => if i ∈ S then 1 else 0

theorem blockProj_sandwich (S : Finset (Fin d)) (X : Matrix (Fin d) (Fin d) K) (i j : Fin d) :
    (blockProj K S * X * blockProj K S) i j =
      (if i ∈ S then 1 else 0) * X i j * (if j ∈ S then 1 else 0) := by
  rw [blockProj, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem isBlockOn_iff_sandwich (S : Finset (Fin d)) (M : Matrix (Fin d) (Fin d) K) :
    IsBlockOn S M ↔ M - 1 = blockProj K S * (M - 1) * blockProj K S := by
  classical
  constructor
  · intro h
    ext i j
    rw [blockProj_sandwich]
    by_cases hi : i ∈ S
    · by_cases hj : j ∈ S
      · simp [hi, hj]
      · simp [hj, h i j (Or.inr hj)]
    · simp [hi, h i j (Or.inl hi)]
  · intro h i j hij
    have h1 := congrFun (congrFun h i) j
    rw [blockProj_sandwich] at h1
    have h2 : M i j - (1 : Matrix (Fin d) (Fin d) K) i j = 0 := by
      rw [← Matrix.sub_apply, h1]
      rcases hij with hi | hj
      · simp [hi]
      · simp [hj]
    exact sub_eq_zero.mp h2

theorem blockProj_mul_blockProj_eq_zero {S₁ S₂ : Finset (Fin d)} (hS : Disjoint S₁ S₂) :
    blockProj K S₁ * blockProj K S₂ = 0 := by
  rw [blockProj, blockProj, diagonal_mul_diagonal, ← diagonal_zero]
  congr 1
  funext i
  by_cases h₁ : i ∈ S₁
  · have h₂ : i ∉ S₂ := Finset.disjoint_left.mp hS h₁
    simp [h₂]
  · simp [h₁]

section Level

variable {S : Finset (Fin d)} {τ : Fin d → Kˣ} {v : Kˣ}

theorem commute_blockProj_of_commute (hS : ∀ i, i ∈ S ↔ τ i = v) {g : GL (Fin d) K}
    (hg : g * diagHom d τ = diagHom d τ * g) :
    (g : Matrix (Fin d) (Fin d) K) * blockProj K S = blockProj K S * g := by
  classical
  ext i j
  rw [blockProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : τ i = τ j
  · have : (i ∈ S ↔ j ∈ S) := by rw [hS, hS, hij]
    by_cases hj : j ∈ S
    · simp [hj, this.mpr hj]
    · simp [hj, show i ∉ S from fun hi => hj (this.mp hi)]
  · rw [entry_eq_zero_of_commute hg hij]
    simp

theorem conj_mem_blockSU_of_commute (hS : ∀ i, i ∈ S ↔ τ i = v) {s t : ↥(unitarySU 2 n K d)}
    (hs : (s : GL (Fin d) K) * diagHom d τ = diagHom d τ * s) (ht : t ∈ blockSU S) :
    s * t * s⁻¹ ∈ blockSU S := by
  have hsi : ((s⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * diagHom d τ =
      diagHom d τ * ((s⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) := by
    rw [Subgroup.coe_inv]
    exact (show Commute (s : GL (Fin d) K) (diagHom d τ) from hs).inv_left.eq
  set Pm : Matrix (Fin d) (Fin d) K := blockProj K S with hPm
  set Sm : Matrix (Fin d) (Fin d) K := ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hSm
  set Tm : Matrix (Fin d) (Fin d) K := ((t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hTm
  set Si : Matrix (Fin d) (Fin d) K :=
    (((s⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hSi
  have hP : Sm * Pm = Pm * Sm := commute_blockProj_of_commute hS hs
  have hPi : Si * Pm = Pm * Si := commute_blockProj_of_commute hS hsi
  have hSSi : Sm * Si = 1 := by
    rw [hSm, hSi, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  have ht' : Tm - 1 = Pm * (Tm - 1) * Pm := (isBlockOn_iff_sandwich S Tm).mp ht
  have e : Sm * Tm * Si - 1 = Sm * (Tm - 1) * Si := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hSSi]
  refine (isBlockOn_iff_sandwich S _).mpr ?_
  show Sm * Tm * Si - 1 = Pm * (Sm * Tm * Si - 1) * Pm
  rw [e]
  calc Sm * (Tm - 1) * Si = Sm * (Pm * (Tm - 1) * Pm) * Si := by rw [← ht']
    _ = (Sm * Pm) * (Tm - 1) * (Pm * Si) := by simp only [Matrix.mul_assoc]
    _ = (Pm * Sm) * (Tm - 1) * (Si * Pm) := by rw [hP, hPi]
    _ = Pm * (Sm * (Tm - 1) * Si) * Pm := by simp only [Matrix.mul_assoc]

end Level

theorem blockSU_commute_of_disjoint {S₁ S₂ : Finset (Fin d)} (hS : Disjoint S₁ S₂)
    {t₁ t₂ : ↥(unitarySU 2 n K d)} (h₁ : t₁ ∈ blockSU S₁) (h₂ : t₂ ∈ blockSU S₂) :
    t₁ * t₂ = t₂ * t₁ := by
  set A : Matrix (Fin d) (Fin d) K := ((t₁ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1 with hA
  set B : Matrix (Fin d) (Fin d) K := ((t₂ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1 with hB
  have hA' : A = blockProj K S₁ * A * blockProj K S₁ := (isBlockOn_iff_sandwich S₁ _).mp h₁
  have hB' : B = blockProj K S₂ * B * blockProj K S₂ := (isBlockOn_iff_sandwich S₂ _).mp h₂
  have h12 := blockProj_mul_blockProj_eq_zero (K := K) hS
  have h21 := blockProj_mul_blockProj_eq_zero (K := K) hS.symm
  have hAB : A * B = 0 := by
    rw [hA', hB']
    calc blockProj K S₁ * A * blockProj K S₁ * (blockProj K S₂ * B * blockProj K S₂) =
        blockProj K S₁ * A * (blockProj K S₁ * blockProj K S₂) * B * blockProj K S₂ := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h12]; simp
  have hBA : B * A = 0 := by
    rw [hA', hB']
    calc blockProj K S₂ * B * blockProj K S₂ * (blockProj K S₁ * A * blockProj K S₁) =
        blockProj K S₂ * B * (blockProj K S₂ * blockProj K S₁) * A * blockProj K S₁ := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h21]; simp
  apply Subtype.ext
  apply Units.ext
  show ((t₁ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (t₂ : GL (Fin d) K) =
    ((t₂ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (t₁ : GL (Fin d) K)
  have e1 : ((t₁ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + A := by rw [hA]; abel
  have e2 : ((t₂ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + B := by rw [hB]; abel
  rw [e1, e2]
  calc (1 + A) * (1 + B) = 1 + A + B + A * B := by noncomm_ring
    _ = 1 + B + A + B * A := by rw [hAB, hBA]; abel
    _ = (1 + B) * (1 + A) := by noncomm_ring

end CFSG.StandardType.Line63.H5

end
