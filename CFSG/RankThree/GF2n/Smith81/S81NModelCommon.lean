module

public import CFSG.RankThree.GF2n.Smith81.S81NBasis
public import CFSG.RankThree.GF2n.Smith81.S81A5KerRho

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open exteriorPower

variable {K : Type*} [Field K]

private theorem replSet_replSet {i j : Fin 6} (hij : i ≠ j) (I : Set.powersetCard (Fin 6) 3)
    (hj : j ∈ I.val) (hi : i ∉ I.val)
    (hJ : i ∈ (replSet I i j hj hi).val ∧ j ∉ (replSet I i j hj hi).val) :
    replSet (replSet I i j hj hi) j i hJ.1 hJ.2 = I := by
  apply Subtype.ext
  show insert j ((insert i (I.val.erase j)).erase i) = I.val
  have hi' : i ∉ I.val.erase j := fun h => hi (Finset.mem_of_mem_erase h)
  rw [Finset.erase_insert hi', Finset.insert_erase hj]

theorem fixed_support [CharP K 2] (Pos : Fin 6 → Fin 6 → Prop) {ξ : Cube K}
    (h : ∀ (i j : Fin 6) (hij : i ≠ j), Pos i j → rho K (transvGL K i j hij 1) ξ = ξ)
    (I : Set.powersetCard (Fin 6) 3) (i j : Fin 6) (hij : i ≠ j) (hP : Pos i j) (hj : j ∈ I.val)
    (hi : i ∉ I.val) : coord K ξ I = 0 := by
  have hJ : i ∈ (replSet I i j hj hi).val ∧ j ∉ (replSet I i j hj hi).val :=
    replSet_eq_imp hij hj hi rfl
  have key := coord_rho_transvGL_gen i j hij (1 : K) ξ (replSet I i j hj hi)
  rw [h i j hij hP, dif_pos hJ, replSet_replSet hij I hj hi hJ] at key
  simpa using key

theorem isPure_cubeBasis (I : Set.powersetCard (Fin 6) 3) : IsPure K (cubeBasis K I) :=
  ⟨_, cubeBasis_apply I⟩

theorem IsPure.smul {ξ : Cube K} (h : IsPure K ξ) (c : K) : IsPure K (c • ξ) := by
  obtain ⟨v, rfl⟩ := h
  refine ⟨![c • v 0, v 1, v 2], ?_⟩
  have hv : ιMulti K 3 v = ιMulti K 3 ![v 0, v 1, v 2] := by
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hv, ι3_smul_fst]

theorem range_le_ker_of_mul_self [CharP K 2] {t : GL (Fin 6) K} (ht : t * t = 1) :
    LinearMap.range (rho K t - 1) ≤ LinearMap.ker (rho K t - 1) := by
  rintro _ ⟨ξ, rfl⟩
  have h1 : rho K t (rho K t ξ) = ξ := by
    have := congrArg (fun g => rho K g ξ) ht
    simpa [rho_mul] using this
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h3 : ∀ x : Cube K, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  rw [LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, h1]
  have := h3 (rho K t ξ)
  have h4 := h3 ξ
  calc ξ - rho K t ξ - (rho K t ξ - ξ) = (ξ + ξ) - (rho K t ξ + rho K t ξ) := by abel
    _ = 0 := by rw [h4, this, sub_self]

end CFSG.RankThree.GF2n.Smith81.A5Cube
