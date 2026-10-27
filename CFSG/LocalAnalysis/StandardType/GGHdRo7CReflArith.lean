module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflSteps

public section

open scoped BigOperators

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7CArithAux_sq (x : ZMod 3) : x ^ 2 = if x ≠ 0 then 1 else 0 := by
  revert x
  decide

private lemma hdRo7CArithAux_sum_sq {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (u : V) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0), (b.coord i u) ^ 2)
      = ((Finset.univ.filter fun i : Fin (n + 1) => i ≠ 0 ∧ b.coord i u ≠ 0).card : ZMod 3) := by
  have hstep : (∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0), (b.coord i u) ^ 2)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0),
          (if b.coord i u ≠ 0 then (1 : ZMod 3) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hdRo7CArithAux_sq (b.coord i u)
  have hfin : (Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0)).filter
        (fun i => b.coord i u ≠ 0)
      = Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0 ∧ b.coord i u ≠ 0) := by
    ext i
    simp [Finset.mem_filter, and_assoc]
  rw [hstep, Finset.sum_boole, hfin]

theorem c2_reflArith_holds : C2ReflArithLeaf := by
  unfold C2ReflArithLeaf
  intro p hp hp3 n hn V instACG instMod b A r u φ hNF c hc
  subst hp3
  have hφu : φ u = 2 := hNF.hφu
  have hφ0 : φ (b 0) = 1 := hNF.hφ0
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => i ≠ 0)
  let f : Fin (n + 1) → ZMod 3 := fun i => b.coord i u * φ (b i)
  have hmap : φ u = ∑ i, f i := by
    rw [← b.sum_repr u, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, ← Module.Basis.coord_apply, smul_eq_mul]
  have hf0 : f 0 = b.coord 0 u := by
    simp [f, hφ0]
  have herase : (Finset.univ.erase (0 : Fin (n + 1))) = S := by
    ext x; simp [S]
  have hsplit : ∑ i, f i = b.coord 0 u + ∑ i ∈ S, f i := by
    rw [(Finset.add_sum_erase Finset.univ f (Finset.mem_univ (0 : Fin (n + 1)))).symm, herase, hf0]
  have hsumS : ∑ i ∈ S, f i = c * ∑ i ∈ S, (b.coord i u) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 : i ≠ 0 := by simpa [S] using hi
    simp only [f]
    rw [hc i hi0]
    ring
  have hsq := hdRo7CArithAux_sum_sq b u
  change (∑ i ∈ S, (b.coord i u) ^ 2)
      = ((Finset.univ.filter fun i : Fin (n + 1) => i ≠ 0 ∧ b.coord i u ≠ 0).card : ZMod 3) at hsq
  have h2 : b.coord 0 u
      + c * ((Finset.univ.filter fun i : Fin (n + 1) => i ≠ 0 ∧ b.coord i u ≠ 0).card : ZMod 3) = 2 := by
    calc
      b.coord 0 u + c * ((Finset.univ.filter fun i : Fin (n + 1) => i ≠ 0 ∧ b.coord i u ≠ 0).card : ZMod 3)
          = b.coord 0 u + c * (∑ i ∈ S, (b.coord i u) ^ 2) := by rw [hsq]
      _ = b.coord 0 u + ∑ i ∈ S, f i := by rw [hsumS]
      _ = ∑ i, f i := hsplit.symm
      _ = φ u := hmap.symm
      _ = 2 := hφu
  exact h2

end CFSG.StandardType.HdRo7C

end
