module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587

private lemma lk0xpa0_marks_sum_ne_zero (T : GGKacType) :
    (∑ i : Fin (k0DiagOf T).marks.length,
      (((k0DiagOf T).marks.getD i.val 0 : ℕ) : ℤ)) ≠ 0 := by
  cases T <;> decide

private lemma lk0xpa0_eq_sum_single {n : ℕ} (v : Fin n → ℤ) :
    v = ∑ i, v i • Pi.single i (1 : ℤ) := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne, hb]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem PA0_marks_perm_invariant
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (i : Fin ρ.row.diagram.marks.length) :
    ρ.row.diagram.marks.getD (ρ.row.nodePerm i).val 0 = ρ.row.diagram.marks.getD i.val 0 := by
  let m : Fin ρ.row.diagram.marks.length → ℤ :=
    fun k => (ρ.row.diagram.marks.getD k.val 0 : ℤ)
  let σ := ρ.row.nodePerm
  let w : Fin ρ.row.diagram.marks.length → ℤ := fun k => ρ.epsilon * m (σ.symm k)
  have hε_cases : ρ.epsilon = 1 ∨ ρ.epsilon = -1 := by
    rw [ρ.epsilon_eq]
    by_cases hd : ρ.row.d = 1 <;> simp [hd]
  have hε : ρ.epsilon * ρ.epsilon = 1 := by
    rcases hε_cases with h | h <;> rw [h] <;> norm_num
  have hε_ne : ρ.epsilon ≠ 0 := by
    rcases hε_cases with h | h <;> rw [h] <;> norm_num
  have hnode : ∀ j, ρ.nodeMap (Pi.single (σ j) 1)
      = ρ.epsilon • ρ.frobLinear (ρ.nodeMap (Pi.single j 1)) := by
    intro j
    rw [ρ.frob_nodes j, smul_smul, hε, one_smul]
  have hm_mem : m ∈ ρ.nodeMap.ker := by
    rw [ρ.nodeMap_ker]
    exact Submodule.subset_span (by simp [m])
  have hm : ρ.nodeMap m = 0 := by
    rwa [LinearMap.mem_ker] at hm_mem
  have hvec_m : m = ∑ j, m j • Pi.single j 1 := lk0xpa0_eq_sum_single m
  have hvec_w : w = ∑ k, w k • Pi.single k 1 := lk0xpa0_eq_sum_single w
  have hmN : ρ.nodeMap m = ∑ j, m j • ρ.nodeMap (Pi.single j 1) := by
    have h := congrArg ρ.nodeMap hvec_m
    rw [map_sum] at h
    simpa only [map_smul] using h
  have hw0 : ρ.nodeMap w = 0 := by
    have hNw : ρ.nodeMap w = ∑ k, w k • ρ.nodeMap (Pi.single k 1) := by
      have h := congrArg ρ.nodeMap hvec_w
      rw [map_sum] at h
      simpa only [map_smul] using h
    rw [hNw]
    have hreindex : (∑ k, w k • ρ.nodeMap (Pi.single k 1))
        = ∑ j, w (σ j) • ρ.nodeMap (Pi.single (σ j) 1) :=
      Fintype.sum_equiv σ.symm
        (fun k => w k • ρ.nodeMap (Pi.single k 1))
        (fun j => w (σ j) • ρ.nodeMap (Pi.single (σ j) 1))
        (fun k => by simp only [Equiv.apply_symm_apply])
    rw [hreindex]
    have hterm : ∀ j, w (σ j) • ρ.nodeMap (Pi.single (σ j) 1)
        = ρ.frobLinear (m j • ρ.nodeMap (Pi.single j 1)) := by
      intro j
      rw [map_smul]
      dsimp only [w]
      rw [Equiv.symm_apply_apply, hnode j, smul_smul]
      have hcoef : (ρ.epsilon * m j) * ρ.epsilon = m j := by
        rw [mul_assoc, mul_comm (m j) ρ.epsilon, ← mul_assoc, hε, one_mul]
      rw [hcoef]
    simp only [hterm]
    rw [← map_sum, ← hmN, hm, map_zero]
  have hw_mem : w ∈ Submodule.span ℤ ({m} : Set (Fin ρ.row.diagram.marks.length → ℤ)) := by
    rw [← ρ.nodeMap_ker, LinearMap.mem_ker]
    exact hw0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw_mem
  have hS_ne : (∑ k, m k) ≠ 0 := by
    dsimp only [m]
    exact lk0xpa0_marks_sum_ne_zero ρ.row.T
  have hc_eq : c = ρ.epsilon := by
    have hsum : c * (∑ k, m k) = ρ.epsilon * (∑ k, m k) := by
      have h1 : (∑ k, (c • m) k) = ∑ k, w k := by rw [hc]
      have hL : (∑ k, (c • m) k) = c * ∑ k, m k := by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
      have hR : (∑ k, w k) = ρ.epsilon * ∑ k, m k := by
        have h := Fintype.sum_equiv σ.symm (fun k => w k) (fun j => ρ.epsilon * m j)
          (fun k => by dsimp only [w])
        rw [h, Finset.mul_sum]
      rw [← hL, h1, hR]
    exact mul_right_cancel₀ hS_ne hsum
  have hm_inv : ∀ k, m k = m (σ.symm k) := by
    intro k
    have hk := congrFun hc k
    dsimp only [w] at hk
    simp only [Pi.smul_apply, smul_eq_mul] at hk
    rw [hc_eq] at hk
    exact mul_left_cancel₀ hε_ne hk
  have hσ : m (σ i) = m i := by
    have h := hm_inv (σ i)
    simpa only [Equiv.symm_apply_apply] using h
  dsimp only [m, σ] at hσ
  exact_mod_cast hσ

end CFSG.StandardType.GGK0ExcCentreU

end
