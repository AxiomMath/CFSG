module

public import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclBasic
import CFSG.LocalAnalysis.UniquenessCase.UC6K322Lin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.GL3Excl

open Matrix CFSG.RepresentationTheory

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem false_of_isCyclic {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {W K : Subgroup (GL (Fin 3) (ZMod r))} (hnorm : ∀ g ∈ W, ∀ x ∈ K, g * x * g⁻¹ ∈ K)
    (hK : IsIrreducibleMatrixRep K.subtype) (hcyc : IsCyclic K) {t₁ : GL (Fin 3) (ZMod r)}
    (ht₁ : t₁ ∈ W) (ht₁d : (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![-1, 1, 1]) :
    False := by
  have hab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    intro x hx y hy
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    have h := congrArg Subtype.val (show (⟨x, hx⟩ : K) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ by
      rw [← ha, ← hb]
      exact zpow_mul_comm g a b)
    exact h
  have hfix : ∀ w : Fin 3 → ZMod r, w 0 = 0 → (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ w = w :=
    fun w hw => funext fun i => by
      rw [ht₁d, mulVec_diagonal]
      fin_cases i <;> simp [hw]
  have htt : t₁⁻¹ = t₁ := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    have h : (fun i => ![(-1 : ZMod r), 1, 1] i * ![-1, 1, 1] i) = fun _ => 1 := by
      funext i
      fin_cases i <;> simp
    rw [Units.val_mul, ht₁d, diagonal_mul_diagonal, h, diagonal_one, Units.val_one]
  have hc : ∀ k ∈ K, (k : Matrix (Fin 3) (Fin 3) (ZMod r)) * t₁ = t₁ * k := by
    intro k hk
    have hk' : t₁ * k * t₁ ∈ K := by
      have h := hnorm t₁ ht₁ k hk
      rwa [htt] at h
    have hDc : ∀ x ∈ K, (x : Matrix (Fin 3) (Fin 3) (ZMod r)) *
        (((t₁ * k * t₁ : GL (Fin 3) (ZMod r)) : Matrix (Fin 3) (Fin 3) (ZMod r)) - k) =
        (((t₁ * k * t₁ : GL (Fin 3) (ZMod r)) : Matrix (Fin 3) (Fin 3) (ZMod r)) - k) * x := by
      intro x hx
      rw [Matrix.mul_sub, Matrix.sub_mul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul,
        ← Units.val_mul, hab x hx _ hk', hab x hx k hk]
    obtain ⟨v, hv0, hv00, hkv⟩ : ∃ v : Fin 3 → ZMod r, v ≠ 0 ∧ v 0 = 0 ∧
        ((k : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ v) 0 = 0 := by
      by_cases h : (k : Matrix (Fin 3) (Fin 3) (ZMod r)) 0 1 = 0
      · refine ⟨![0, 1, 0], fun h' => by simpa using congrFun h' 1, rfl, ?_⟩
        simp [mulVec, dotProduct, Fin.sum_univ_three, h]
      · refine ⟨![0, (k : Matrix (Fin 3) (Fin 3) (ZMod r)) 0 2,
          -(k : Matrix (Fin 3) (Fin 3) (ZMod r)) 0 1], fun h' => h (by simpa using congrFun h' 2),
          rfl, ?_⟩
        simp [mulVec, dotProduct, Fin.sum_univ_three, mul_comm]
    have hDv : ((t₁ * k * t₁ : GL (Fin 3) (ZMod r)) : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ v =
        (k : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ v := by
      rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hfix v hv00,
        hfix _ hkv]
    rcases CFSG.LocalAnalysis.UniquenessCase.UC6.K322Lin.eq_zero_or_injective_of_commute hK hDc
      with h0 | hinj
    · have h1 : t₁ * k * t₁ = k := Units.ext (sub_eq_zero.mp h0)
      have h2 : k * t₁ = t₁ * k := by
        calc k * t₁ = t₁ * k * t₁ * t₁ := by rw [h1]
          _ = t₁ * k * (t₁ * t₁⁻¹) := by rw [htt, mul_assoc]
          _ = t₁ * k := by rw [mul_inv_cancel, mul_one]
      rw [← Units.val_mul, h2, Units.val_mul]
    · exact absurd (hinj v (by rw [sub_mulVec, hDv, sub_self])) hv0
  have h01 := diagonal_apply_eq_of_commute_irreducible hK (α := ![-1, 1, 1])
    (fun k hk => by rw [← ht₁d]; exact hc k hk) 0 1
  haveI : Fact (2 < r) := ⟨lt_of_le_of_ne (Fact.out : r.Prime).two_le (Ne.symm hr2)⟩
  exact ZMod.neg_one_ne_one (by simpa using h01)

end CFSG.LocalAnalysis.UniquenessCase.GL3Excl
