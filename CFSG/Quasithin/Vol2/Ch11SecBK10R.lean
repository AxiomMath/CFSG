module

public import CFSG.Quasithin.Vol2.Ch11SecBK10Q
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10.U3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K]

omit [Field K] in
theorem not_three_dvd_of_even (hf : Even f) : ¬ 3 ∣ 2 ^ f + 1 := by
  obtain ⟨k, rfl⟩ := hf
  have h1 : 2 ^ (k + k) % 3 = 1 := by
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  generalize 2 ^ (k + k) = N at h1 ⊢
  omega

theorem hq_of_even (h : UnitaryFieldData 2 f K) (hf : Even f) :
    ¬(2 * 1 + 1 = 3 ∧ 2 ^ f = 2) := by
  rintro ⟨-, h2⟩
  have h1 := h.one_le
  have h3 : f = 1 := Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 1 by rw [h2, pow_one])
  obtain ⟨k, rfl⟩ := hf
  omega

theorem trace_map_ringEquiv {ι : Type} [Fintype ι] (σ : K ≃+* K) (M : Matrix ι ι K) :
    (M.map σ).trace = σ M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]

variable (h : UnitaryFieldData p f K)

theorem exists_torus {u : Kˣ} (hu : h.bar (u : K) = u) :
    ∃ t : hypSU h 1 1, ((t : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      diagonal (torusEntries h (fun _ => u) (fun _ => 1)) := by
  obtain ⟨t, -, ht⟩ := torusMat_mem_hypSU h (r := 1) (ε := 1) (fun _ => u) (d := fun _ => 1)
    (fun _ => by simp [UnitaryFieldData.norm]) (by simp [torusRatio, hu, u.ne_zero])
  exact ⟨t, ht⟩

variable {h}

theorem fieldAutHom_torus {u : Kˣ} {t : hypSU h 1 1}
    (ht : ((t : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      diagonal (torusEntries h (fun _ => u) (fun _ => 1)))
    {σ : K ≃+* K} (hσ : σ (u : K) = u) :
    fieldAutHom h σ (hypProj h 1 1 t) = hypProj h 1 1 t := by
  obtain ⟨hg, e⟩ := fieldAutHom_apply h σ t
  rw [e]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_glAut, ht, diagonal_map (map_zero σ)]
  congr 1
  funext a
  rcases a with i | k | i <;> simp [torusEntries, hσ, map_bar_comm h]

theorem torus_pow_orderOf {u : Kˣ} (hu : h.bar (u : K) = u) {t : hypSU h 1 1}
    (ht : ((t : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      diagonal (torusEntries h (fun _ => u) (fun _ => 1))) : t ^ orderOf u = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, ht, diagonal_pow, OneMemClass.coe_one,
    Units.val_one, ← diagonal_one]
  congr 1
  funext a
  have h1 : (u : K) ^ orderOf u = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  rcases a with i | k | i <;> simp [torusEntries, hu, h1]

theorem trace_mul_torus {u : Kˣ} {t g : hypSU h 1 1}
    (ht : ((t : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      diagonal (torusEntries h (fun _ => u) (fun _ => 1)))
    (hg : g ∈ hypUnitriangular h 1 1) :
    (((g * t : hypSU h 1 1) : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K).trace = (u : K) + 1 + (h.bar (u : K))⁻¹ := by
  obtain ⟨hgT, hgD⟩ := mem_hypUnitriangular.mp hg
  have htT : ((t : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos := by
    rw [ht]
    exact blockTriangular_diagonal _
  have e : ∀ a, (((g * t : hypSU h 1 1) : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) a a = torusEntries h (fun _ => u) (fun _ => 1) a := by
    intro a
    rw [Subgroup.coe_mul, Units.val_mul,
      mul_apply_self_of_blockTriangular fullPos_injective hgT htT, hgD, one_mul, ht,
      diagonal_apply_eq]
  simp only [Matrix.trace, Matrix.diag_apply, e, Fintype.sum_sum_type, Finset.univ_unique,
    Finset.sum_singleton]
  simp only [torusEntries, Units.val_one]
  ring

theorem isSylowTwoOf_hyp (h : UnitaryFieldData 2 f K) :
    QuasithinUnique.IsSylowTwoOf (hypProjUnitriangular h 1 1) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := h.finite
  obtain ⟨-, -, -, -, ⟨Q, hQ⟩, -, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  rw [← hQ]
  refine ⟨le_top, Q.isPGroup', ?_⟩
  change ¬ 2 ∣ (Q : Subgroup (hypPSU h 1 1)).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact Q.not_dvd_index

end BK10.U3

end CFSG.Quasithin.Vol2.Ch11.SecD
