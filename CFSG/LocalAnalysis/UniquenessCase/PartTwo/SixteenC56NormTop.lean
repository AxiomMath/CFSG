module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Comm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

include S in
private theorem mul_self_eq_one' (w : W) : w * w = 1 := by
  apply S.vec_injective
  rw [S.vec_mul, S.vec_one]
  exact CharTwo.add_self_eq_zero (S.vec w)

include S in
private theorem inv_eq_self' (w : W) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_right (mul_self_eq_one' S w)

private theorem exists_ne_zero_ne_one (K : Type*) [Field K] [Finite K] [CharP K 2]
    (h : 4 ≤ Nat.card K) : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
  classical
  letI := Fintype.ofFinite K
  have hcard : 4 ≤ Fintype.card K := by simpa [Nat.card_eq_fintype_card] using h
  have h2 : ({0, 1} : Finset K).card = 2 := Finset.card_pair_eq_two_iff.mpr zero_ne_one
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [h2, Finset.card_univ]
    omega
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  exact ⟨a, ha.1, ha.2⟩

private theorem Q_ofVec_single (i : OmI) :
    S.Q (S.ofVec (Pi.single i 1)) = 0 := by
  rcases i with i | i <;> fin_cases i <;>
    simp [Q, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, S.vec_ofVec, Fin.sum_univ_two]

private theorem vec_prod (s : Finset OmI) (f : OmI → W) :
    S.vec (∏ i ∈ s, f i) = ∑ i ∈ s, S.vec (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [S.vec_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, S.vec_mul, ih]

private theorem ofVec_eq_prod (v : OmI → S.K) :
    S.ofVec v = ∏ i, S.smul (v i) (S.ofVec (Pi.single i 1)) := by
  apply S.vec_injective
  rw [S.vec_ofVec, vec_prod S]
  have hterm : ∀ i : OmI,
      S.vec (S.smul (v i) (S.ofVec (Pi.single i 1))) = (v i) • Pi.single i 1 := by
    intro i
    rw [S.vec_smul, S.vec_ofVec]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  exact pi_eq_sum_univ' v

private theorem smul_mem_commSub_of_ne_one {x : W} (hx : S.Q x = 0) {s : S.K}
    (hs : s ≠ 1) : S.smul s x ∈ commSub ⊤ S.omega := by
  have ht : s + 1 ≠ 0 := fun h => hs (CharTwo.add_eq_zero.mp h)
  obtain ⟨p, hp⟩ := S.exists_jHom_eq_smul_of_Q_eq_zero hx ht
  have hmemω : S.jHom p ∈ S.omega := S.omega0_le_omega ⟨p, rfl⟩
  have hcomm : S.smul (s + 1) x * x⁻¹ ∈ commSub ⊤ S.omega := by
    rw [← hp]
    exact Subgroup.subset_closure ⟨S.jHom p, hmemω, x, Subgroup.mem_top x, rfl⟩
  have hgoal : S.smul s x = S.smul (s + 1) x * x⁻¹ := by
    conv_lhs => rw [← CharTwo.add_cancel_right s 1]
    rw [S.smul_add_eq, S.smul_one_eq, inv_eq_self' S x]
  rw [hgoal]
  exact hcomm

private theorem smul_mem_commSub {x : W} (hx : S.Q x = 0) (c : S.K) :
    S.smul c x ∈ commSub ⊤ S.omega := by
  obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_ne_one S.K S.four_le
  by_cases hc : c = 1
  · subst hc
    have h1 : S.smul a x ∈ commSub ⊤ S.omega := smul_mem_commSub_of_ne_one S hx ha1
    have h2 : S.smul (a + 1) x ∈ commSub ⊤ S.omega :=
      smul_mem_commSub_of_ne_one S hx (by
        intro h
        apply ha0
        rw [← CharTwo.add_cancel_right a 1, h, CharTwo.add_self_eq_zero])
    have haa : a + (a + 1) = 1 := by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [← haa, S.smul_add_eq]
    exact mul_mem h1 h2
  · exact smul_mem_commSub_of_ne_one S hx hc

theorem commSub_top_omega : commSub ⊤ S.omega = ⊤ := by
  apply le_antisymm le_top
  intro w _
  rw [← S.ofVec_vec w, ofVec_eq_prod S]
  exact (commSub ⊤ S.omega).prod_mem
    (fun i _ => smul_mem_commSub S (Q_ofVec_single S i) (S.vec w i))

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
