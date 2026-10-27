module

public import CFSG.ClassicalGroups.Unitary.NaturalIrreducible

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

private theorem isotropic_closure_smul {K : Type} [Field K] {σ : K ≃+* K}
    (hσ : ∀ c, σ (σ c) = c) {n : ℕ} (c : K) {x : Fin n → K}
    (hx : x ∈ AddSubgroup.closure {v : Fin n → K | herm σ v v = 0}) :
    c • x ∈ AddSubgroup.closure {v : Fin n → K | herm σ v v = 0} := by
  let S : AddSubgroup (Fin n → K) :=
    { carrier := {y | c • y ∈ AddSubgroup.closure {v : Fin n → K | herm σ v v = 0}}
      zero_mem' := by
        show c • (0 : Fin n → K) ∈ AddSubgroup.closure {v : Fin n → K | herm σ v v = 0}
        rw [smul_zero]
        exact AddSubgroup.zero_mem _
      add_mem' := by
        intro y z hy hz
        show c • (y + z) ∈ AddSubgroup.closure {v : Fin n → K | herm σ v v = 0}
        rw [smul_add]
        exact AddSubgroup.add_mem _ hy hz
      neg_mem' := by
        intro y hy
        show c • (-y) ∈ AddSubgroup.closure {v : Fin n → K | herm σ v v = 0}
        rw [smul_neg]
        exact AddSubgroup.neg_mem _ hy }
  have hle : AddSubgroup.closure {v : Fin n → K | herm σ v v = 0} ≤ S := by
    refine (AddSubgroup.closure_le S).mpr ?_
    intro v hv
    have hv' : herm σ v v = 0 := hv
    show c • v ∈ AddSubgroup.closure {v : Fin n → K | herm σ v v = 0}
    exact AddSubgroup.subset_closure (herm_smul_smul_eq_zero hσ hv' c)
  exact hle hx

theorem hspan_isotropic {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {n : ℕ} (hn : 2 ≤ n) :
    AddSubgroup.closure {v : Fin n → K | herm σ v v = 0} = ⊤ := by
  obtain ⟨ω, hωn, hω1⟩ := hσ.exists_norm_one_ne_one
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hω0 : (1 : K) + ω ≠ 0 := by
    intro h
    apply hω1
    have hneg : ω = -1 := by linear_combination h
    rw [hneg, CharTwo.neg_eq]
  have hiso : ∀ (i j : Fin n) (t : K), i ≠ j → σ t * t = 1 →
      Pi.single i (1 : K) + Pi.single j t ∈
        AddSubgroup.closure {v : Fin n → K | herm σ v v = 0} := by
    intro i j t hij ht
    have hmem : herm σ (Pi.single i (1 : K) + Pi.single j t)
        (Pi.single i (1 : K) + Pi.single j t) = 0 := by
      rw [herm_single_add_single hij t, ht]
      exact h11
    exact AddSubgroup.subset_closure hmem
  have hj : ∀ j : Fin n,
      Pi.single j (1 : K) ∈ AddSubgroup.closure {v : Fin n → K | herm σ v v = 0} := by
    intro j
    obtain ⟨i, hij⟩ : ∃ i : Fin n, i ≠ j := by
      obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n)
        (by rw [Fintype.card_fin]; omega) j
      exact ⟨i, hi⟩
    have hp := hiso i j 1 hij (by rw [map_one, one_mul])
    have hq := hiso i j ω hij hωn
    have e1 : (Pi.single i (1 : K) : Fin n → K) + Pi.single i (1 : K) = 0 := by
      rw [← Pi.single_add, h11, Pi.single_zero]
    have e2 : (Pi.single j (1 : K) : Fin n → K) + Pi.single j ω =
        (1 + ω) • (Pi.single j (1 : K) : Fin n → K) := by
      rw [← Pi.single_add, ← Pi.single_smul, smul_eq_mul, mul_one]
    have hsum : ((Pi.single i (1 : K) : Fin n → K) + Pi.single j (1 : K)) +
        (Pi.single i (1 : K) + Pi.single j ω) = (1 + ω) • (Pi.single j (1 : K) : Fin n → K) := by
      have hre : ((Pi.single i (1 : K) : Fin n → K) + Pi.single j (1 : K)) +
          (Pi.single i (1 : K) + Pi.single j ω) =
          (Pi.single i (1 : K) + Pi.single i (1 : K)) + (Pi.single j (1 : K) + Pi.single j ω) := by
        abel
      rw [hre, e1, e2, zero_add]
    have hmem : (1 + ω) • Pi.single j (1 : K) ∈
        AddSubgroup.closure {v : Fin n → K | herm σ v v = 0} := by
      rw [← hsum]
      exact AddSubgroup.add_mem _ hp hq
    have h2 := isotropic_closure_smul hσ.invol (1 + ω)⁻¹ hmem
    rwa [inv_smul_smul₀ hω0] at h2
  refine eq_top_iff.mpr ?_
  intro v _
  have hv : v = ∑ j : Fin n, Pi.single j (v j) := (Finset.univ_sum_single v).symm
  rw [hv]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  have h3 := isotropic_closure_smul hσ.invol (v j) (hj j)
  rwa [← Pi.single_smul, smul_eq_mul, mul_one] at h3

theorem addSubgroup_eq_top_of_T_invariant_general {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {n : ℕ} (hn : 3 ≤ n) (W : AddSubgroup (Fin n → K))
    (hW : ∀ t ∈ T σ n, ∀ v ∈ W, t • v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  addSubgroup_eq_top_of_T_invariant_of_span hσ hn (hspan_isotropic hσ (by omega)) W hW

theorem addSubgroup_eq_top_of_SUid_invariant {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {n : ℕ} (hn : 3 ≤ n) (W : AddSubgroup (Fin n → K))
    (hW : ∀ g : SUid σ n, ∀ v ∈ W, g • v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  addSubgroup_eq_top_of_T_invariant_general hσ hn W (fun t _ v hv => hW t v hv)

end CFSG.RankThree.GF2n.Smith81.U6Cube
