module

public import CFSG.Quasithin.Background.HOm4Aut
public import CFSG.Quasithin.Background.RonanH44Defs

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def embW (A : SL(2, K)) : SL(3, K) :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) K) 0 0, (A : Matrix (Fin 2) (Fin 2) K) 0 1, 0;
      (A : Matrix (Fin 2) (Fin 2) K) 1 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1, 0; 0, 0, 1], by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_three]
    simp
    linear_combination h⟩

@[expose] def embZ (A : SL(2, K)) : SL(3, K) :=
  ⟨!![1, 0, 0; 0, (A : Matrix (Fin 2) (Fin 2) K) 0 0, (A : Matrix (Fin 2) (Fin 2) K) 0 1;
      0, (A : Matrix (Fin 2) (Fin 2) K) 1 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1], by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_three]
    simp
    linear_combination h⟩

private theorem embW_one : embW (1 : SL(2, K)) = 1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embW]

private theorem embZ_one : embZ (1 : SL(2, K)) = 1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embZ]

theorem embW_mul (A B : SL(2, K)) : embW (A * B) = embW A * embW B := by
  refine Subtype.ext ?_
  change (embW (A * B) : Matrix (Fin 3) (Fin 3) K) =
    (embW A : Matrix (Fin 3) (Fin 3) K) * (embW B : Matrix (Fin 3) (Fin 3) K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embW, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem embZ_mul (A B : SL(2, K)) : embZ (A * B) = embZ A * embZ B := by
  refine Subtype.ext ?_
  change (embZ (A * B) : Matrix (Fin 3) (Fin 3) K) =
    (embZ A : Matrix (Fin 3) (Fin 3) K) * (embZ B : Matrix (Fin 3) (Fin 3) K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embZ, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem embW_mem_perfW (A : SL(2, K)) : embW A ∈ perfW K := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [embW]

theorem embZ_mem_perfZ (A : SL(2, K)) : embZ A ∈ perfZ K := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [embZ]

private theorem commutator_mem_perfW {x y : SL(3, K)} (hx : x ∈ stabW K) (hy : y ∈ stabW K) :
    ⁅x, y⁆ ∈ perfW K := by
  have hne : ∀ g : stabW K, ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    intro g h0
    obtain ⟨hg0, hg1⟩ := g.2
    have hdet := (g : SL(3, K)).2
    rw [Matrix.det_fin_three, hg0, hg1, h0] at hdet
    simp at hdet
  let ρ : stabW K →* Kˣ :=
    { toFun := fun g => Units.mk0 (((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2) (hne g)
      map_one' := by ext; simp
      map_mul' := fun g h => by
        obtain ⟨hg0, hg1⟩ := g.2
        obtain ⟨hh0, hh1⟩ := h.2
        ext
        simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1,
          hh0, hh1] }
  obtain ⟨a, rfl⟩ : ∃ a : stabW K, (a : SL(3, K)) = x := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b : stabW K, (b : SL(3, K)) = y := ⟨⟨y, hy⟩, rfl⟩
  have hρ : ρ ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have h22 : (((⁅a, b⁆ : stabW K) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 :=
    congrArg Units.val hρ
  have hc : ((⁅a, b⁆ : stabW K) : SL(3, K)) = ⁅(a : SL(3, K)), (b : SL(3, K))⁆ := rfl
  have hmem := (⁅a, b⁆ : stabW K).2
  rw [hc] at hmem h22
  obtain ⟨h20, h21⟩ := hmem
  exact ⟨h20, h21, h22⟩

private theorem commutator_mem_perfZ {x y : SL(3, K)} (hx : x ∈ stabZ K) (hy : y ∈ stabZ K) :
    ⁅x, y⁆ ∈ perfZ K := by
  have hne : ∀ g : stabZ K, ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro g h0
    obtain ⟨hg0, hg1⟩ := g.2
    have hdet := (g : SL(3, K)).2
    rw [Matrix.det_fin_three, hg0, hg1, h0] at hdet
    simp at hdet
  let ρ : stabZ K →* Kˣ :=
    { toFun := fun g => Units.mk0 (((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0) (hne g)
      map_one' := by ext; simp
      map_mul' := fun g h => by
        obtain ⟨hg0, hg1⟩ := g.2
        obtain ⟨hh0, hh1⟩ := h.2
        ext
        simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1,
          hh0, hh1] }
  obtain ⟨a, rfl⟩ : ∃ a : stabZ K, (a : SL(3, K)) = x := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b : stabZ K, (b : SL(3, K)) = y := ⟨⟨y, hy⟩, rfl⟩
  have hρ : ρ ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have h00 : (((⁅a, b⁆ : stabZ K) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 :=
    congrArg Units.val hρ
  have hc : ((⁅a, b⁆ : stabZ K) : SL(3, K)) = ⁅(a : SL(3, K)), (b : SL(3, K))⁆ := rfl
  have hmem := (⁅a, b⁆ : stabZ K).2
  rw [hc] at hmem h00
  obtain ⟨h10, h20⟩ := hmem
  exact ⟨h10, h20, h00⟩

theorem perfectCore_stabW_le : perfectCore (stabW K) ≤ perfW K := by
  refine (perfectCore_le_derivedSeriesOf (stabW K) 1).trans ?_
  have h1 : derivedSeriesOf (stabW K) 1 = ⁅stabW K, stabW K⁆ := derivedSeriesOf_succ (stabW K) 0
  rw [h1]
  exact Subgroup.commutator_le.mpr fun x hx y hy => commutator_mem_perfW hx hy

theorem perfectCore_stabZ_le : perfectCore (stabZ K) ≤ perfZ K := by
  refine (perfectCore_le_derivedSeriesOf (stabZ K) 1).trans ?_
  have h1 : derivedSeriesOf (stabZ K) 1 = ⁅stabZ K, stabZ K⁆ := derivedSeriesOf_succ (stabZ K) 0
  rw [h1]
  exact Subgroup.commutator_le.mpr fun x hx y hy => commutator_mem_perfZ hx hy

theorem embW_mem_perfectCore (h4 : 4 ≤ Nat.card K) (A : SL(2, K)) :
    embW A ∈ perfectCore (stabW K) := by
  let φ : SL(2, K) →* SL(3, K) := { toFun := embW, map_one' := embW_one, map_mul' := embW_mul }
  have hS : (⊤ : Subgroup SL(2, K)).map φ ≤ stabW K := by
    rintro _ ⟨B, -, rfl⟩
    refine ⟨?_, ?_⟩ <;> simp [φ, embW]
  have hP : ⁅(⊤ : Subgroup SL(2, K)).map φ, (⊤ : Subgroup SL(2, K)).map φ⁆ =
      (⊤ : Subgroup SL(2, K)).map φ := by
    rw [← Subgroup.map_commutator, Om4.sl2_commutator_eq_top h4]
  exact le_perfectCore_of_perfect hS hP (Subgroup.mem_map_of_mem φ (Subgroup.mem_top A))

theorem embZ_mem_perfectCore (h4 : 4 ≤ Nat.card K) (A : SL(2, K)) :
    embZ A ∈ perfectCore (stabZ K) := by
  let φ : SL(2, K) →* SL(3, K) := { toFun := embZ, map_one' := embZ_one, map_mul' := embZ_mul }
  have hS : (⊤ : Subgroup SL(2, K)).map φ ≤ stabZ K := by
    rintro _ ⟨B, -, rfl⟩
    refine ⟨?_, ?_⟩ <;> simp [φ, embZ]
  have hP : ⁅(⊤ : Subgroup SL(2, K)).map φ, (⊤ : Subgroup SL(2, K)).map φ⁆ =
      (⊤ : Subgroup SL(2, K)).map φ := by
    rw [← Subgroup.map_commutator, Om4.sl2_commutator_eq_top h4]
  exact le_perfectCore_of_perfect hS hP (Subgroup.mem_map_of_mem φ (Subgroup.mem_top A))

end CFSG.Quasithin.RonanH44
