module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCenter
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.Sec4.Item434Kit

theorem mem_zpowers_const_of_central {S : Type} [Group S] {z : Fin 3 → S} {t : S}
    (hf : WreathFacts z t) {u : S} (huW : u ∈ wreathW z t)
    (hucent : ∀ q ∈ wreathW z t, q * u = u * q) :
    u ∈ Subgroup.zpowers (vecElt z ![1, 1, 1]) := by
  haveI : IsMulCommutative (baseA z) := (isElemAbelian_baseA hf).1
  have hzW : ∀ i, z i ∈ wreathW z t := fun i => Subgroup.mem_sup_left (z_mem_baseA i)
  obtain ⟨v, j, rfl⟩ := mem_wreathW hf huW
  have hj : (j : ℕ) = 0 := by
    by_contra hj0
    have hjne : j ≠ 0 := fun h => hj0 (by rw [h]; rfl)
    have h1 := hucent (z 0) (hzW 0)
    have hcomm : z 0 * vecElt z v = vecElt z v * z 0 := by
      have hz0A := z_mem_baseA (z := z) 0
      have hvA := vecElt_mem_baseA hf v
      exact Subgroup.mul_comm_of_mem_isMulCommutative (baseA z) hz0A hvA
    have h2 : z 0 * t ^ (j : ℕ) = t ^ (j : ℕ) * z 0 := by
      have h3 : vecElt z v * (z 0 * t ^ (j : ℕ)) = vecElt z v * (t ^ (j : ℕ) * z 0) := by
        calc vecElt z v * (z 0 * t ^ (j : ℕ)) = (vecElt z v * z 0) * t ^ (j : ℕ) := by group
          _ = (z 0 * vecElt z v) * t ^ (j : ℕ) := by rw [hcomm]
          _ = z 0 * (vecElt z v * t ^ (j : ℕ)) := by group
          _ = (vecElt z v * t ^ (j : ℕ)) * z 0 := h1
          _ = vecElt z v * (t ^ (j : ℕ) * z 0) := by group
      exact mul_left_cancel h3
    have h4 := eq_of_commute hf (v := Pi.single 0 1) hjne (by
      rw [vecElt_single_one]; exact h2)
    have h5 := h4.1
    simp at h5
  have hj' : j = 0 := Fin.ext hj
  subst hj'
  simp only [Fin.val_zero, pow_zero, mul_one] at hucent ⊢
  have ht := hucent t t_mem_wreathW
  have h6 : t * vecElt z v * t⁻¹ = vecElt z v := by
    rw [ht, mul_inv_cancel_right]
  rw [conj_vecElt hf] at h6
  have h7 := vecElt_injective hf h6
  have e1 := congrFun h7 1
  have e2 := congrFun h7 2
  simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e1 e2
  exact vecElt_mem_zpowers_of_const hf e1 e2

theorem listRow_of_wreath3 {S : Type} [Group S] [Finite S] {z : Fin 3 → S} {t : S}
    (hf : WreathFacts z t) (hW : Nat.card (wreathW z t) = 81) (hS : ¬ 243 ∣ Nat.card S)
    (hflip : ∃ m : S, m * vecElt z ![1, 1, 1] * m⁻¹ ∈ baseA z ∧
      m * vecElt z ![1, 1, 1] * m⁻¹ ∉ Subgroup.zpowers (vecElt z ![1, 1, 1])) :
    ListRow S := by
  obtain ⟨m, hmA, hmn⟩ := hflip
  set c := vecElt z ![1, 1, 1] with hc
  have hW' : Nat.card (wreathW z t) = 3 ^ 4 := by rw [hW]; norm_num
  have hS' : ¬ 3 ^ (4 + 1) ∣ Nat.card S := by norm_num; exact hS
  haveI : IsMulCommutative (baseA z) := (isElemAbelian_baseA hf).1
  have hcA : c ∈ baseA z := vecElt_mem_baseA hf _
  have hAexp : ∀ x ∈ baseA z, x ^ 3 = 1 := (isElemAbelian_baseA hf).2
  have hc3 : c ^ 3 = 1 := hAexp c hcA
  refine listRow_of_sylow_center 4 (wreathW z t) hW' hS' fun u huW huo hucent => ?_
  have hu_in : u ∈ Subgroup.zpowers c := mem_zpowers_const_of_central hf huW hucent
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu_in
  have hyk : m * u * m⁻¹ = (m * c * m⁻¹) ^ k := by rw [← hk]; exact conj_zpow.symm
  refine ⟨m, ?_, ?_⟩
  · have hy : m * u * m⁻¹ ∈ baseA z := by
      rw [hyk]
      exact Subgroup.zpow_mem _ hmA k
    have huA : u ∈ baseA z := by rw [← hk]; exact Subgroup.zpow_mem _ hcA k
    exact Subgroup.mul_comm_of_mem_isMulCommutative (baseA z) hy huA
  · intro hmem
    set y := m * c * m⁻¹ with hy
    have hy3 : y ^ 3 = 1 := hAexp y hmA
    have hk3 : ¬ (3 : ℤ) ∣ k := by
      intro h3
      have hu1 : u = 1 := by
        rw [← hk]
        obtain ⟨l, rfl⟩ := h3
        rw [zpow_mul]
        have h33 : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
        rw [h33, one_zpow]
      rw [hu1, orderOf_one] at huo
      omega
    have hkk : y ^ (k * k) = y := by
      rw [zpow_eq_zpow_mod_three_of_pow_three hy3]
      have h' : k % 3 = 1 ∨ k % 3 = 2 := by omega
      have : k * k % 3 = 1 := by
        rcases h' with h | h <;> simp [Int.mul_emod, h]
      rw [this, zpow_one]
    have h1 : y ^ k ∈ Subgroup.zpowers c := (Subgroup.zpowers_le.mpr hu_in) (hyk ▸ hmem)
    have h2 : y ∈ Subgroup.zpowers c := by
      have : (y ^ k) ^ k ∈ Subgroup.zpowers c := Subgroup.zpow_mem _ h1 k
      rwa [← zpow_mul, hkk] at this
    exact hmn h2

end CFSG.RankThree.PartTwo.Sec4.RonanK432
