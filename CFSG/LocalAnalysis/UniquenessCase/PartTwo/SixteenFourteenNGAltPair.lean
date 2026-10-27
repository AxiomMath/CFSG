module

public import CFSG.Quasithin.Background.B5FinPerm
public import CFSG.Quasithin.Background.G6Swap
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6

variable {n : ℕ}

@[expose] def s1614_altPair (n : ℕ) (i j : Fin n) : PermMod n :=
  Multiplicative.ofAdd (Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2))

private theorem s1614_ap_altPair_comm (i j : Fin n) :
    s1614_altPair n i j = s1614_altPair n j i := by
  show Multiplicative.ofAdd ((Pi.single i (1 : ZMod 2) + Pi.single j 1 : Fin n → ZMod 2)) =
    Multiplicative.ofAdd ((Pi.single j (1 : ZMod 2) + Pi.single i 1 : Fin n → ZMod 2))
  rw [add_comm]

theorem s1614_altPair_mem_coreMod (i j : Fin n) : s1614_altPair n i j ∈ coreMod n := by
  rw [mem_coreMod]
  show ∑ l, ((Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2) : Fin n → ZMod 2)) l = 0
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, Fintype.sum_pi_single', Fintype.sum_pi_single']
  decide

theorem s1614_altPair_mul (i j k : Fin n) :
    s1614_altPair n i j * s1614_altPair n j k = s1614_altPair n i k := by
  apply Multiplicative.toAdd.injective
  funext l
  simp only [s1614_altPair, toAdd_mul, toAdd_ofAdd, Pi.add_apply, Pi.single_apply]
  by_cases hi : l = i <;> by_cases hj : l = j <;> by_cases hk : l = k <;>
    simp_all <;> decide

theorem s1614_permAct_altPair (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permAct n σ (s1614_altPair n i j) = s1614_altPair n (σ i) (σ j) := by
  apply Multiplicative.toAdd.injective
  funext l
  show ((Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2)) : Fin n → ZMod 2) (σ⁻¹ l) =
    ((Pi.single (σ i) (1 : ZMod 2) + Pi.single (σ j) (1 : ZMod 2)) : Fin n → ZMod 2) l
  simp only [Pi.add_apply, Pi.single_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_eq]

theorem s1614_permAct_allOnes (σ : Equiv.Perm (Fin n)) :
    permAct n σ (allOnes n) = allOnes n := by
  apply Multiplicative.toAdd.injective
  funext i
  rfl

theorem s1614_exists_three_pairs (hn : 6 ≤ n) {H : Subgroup (PermMod n)} (hHc : H ≤ coreMod n)
    (h2 : 2 * Nat.card ↥H = Nat.card ↥(coreMod n)) :
    ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      s1614_altPair n a b ∈ H ∧ s1614_altPair n a c ∈ H := by
  classical
  let H' : Subgroup ↥(coreMod n) := H.subgroupOf (coreMod n)
  have hcard : Nat.card ↥H' = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHc).toEquiv
  have hindex : H'.index = 2 := by
    have h := Subgroup.card_mul_index H'
    rw [hcard, ← h2, mul_comm 2 (Nat.card ↥H)] at h
    exact Nat.mul_left_cancel Nat.card_pos h
  let z : Fin n := ⟨0, by omega⟩
  have key : ∀ j k : Fin n, j ≠ z → k ≠ z →
      s1614_altPair n z j ∉ H → s1614_altPair n z k ∉ H →
      s1614_altPair n j k ∈ H := by
    intro j k _ _ hjH hkH
    have hjzc : s1614_altPair n j z ∈ coreMod n := s1614_altPair_mem_coreMod j z
    have hzkc : s1614_altPair n z k ∈ coreMod n := s1614_altPair_mem_coreMod z k
    have hu : (⟨s1614_altPair n j z, hjzc⟩ : coreMod n) ∉ H' := by
      intro hmem
      have h' : s1614_altPair n j z ∈ H := Subgroup.mem_subgroupOf.mp hmem
      exact hjH (by rwa [s1614_ap_altPair_comm] at h')
    have hv : (⟨s1614_altPair n z k, hzkc⟩ : coreMod n) ∉ H' := by
      rw [Subgroup.mem_subgroupOf]
      exact hkH
    have huv : (⟨s1614_altPair n j z, hjzc⟩ : coreMod n) *
        (⟨s1614_altPair n z k, hzkc⟩ : coreMod n) ∈ H' :=
      (Subgroup.mul_mem_iff_of_index_two hindex).2 (iff_of_false hu hv)
    have hcoe : ((⟨s1614_altPair n j z, hjzc⟩ : coreMod n) *
        (⟨s1614_altPair n z k, hzkc⟩ : coreMod n) : coreMod n) =
        ⟨s1614_altPair n j k, s1614_altPair_mem_coreMod j k⟩ := by
      apply Subtype.ext
      show s1614_altPair n j z * s1614_altPair n z k = s1614_altPair n j k
      rw [s1614_altPair_mul]
    rw [Subgroup.mem_subgroupOf, hcoe] at huv
    exact huv
  let T : Finset (Fin n) := Finset.univ.erase z
  let A : Finset (Fin n) := T.filter (fun j => s1614_altPair n z j ∈ H)
  let B : Finset (Fin n) := T.filter (fun j => s1614_altPair n z j ∉ H)
  have hsum : A.card + B.card = T.card := by
    simpa only [A, B] using
      Finset.card_filter_add_card_filter_not (s := T)
        (p := fun j => s1614_altPair n z j ∈ H)
  have hTcard : T.card = n - 1 := by
    simp only [T]
    rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, Fintype.card_fin]
  by_cases hA : 2 ≤ A.card
  · have hA2 : 1 < A.card := by omega
    obtain ⟨b, hbA, c, hcA, hbc⟩ := Finset.one_lt_card.mp hA2
    have hbT : b ∈ T := (Finset.mem_filter.mp hbA).1
    have hbH : s1614_altPair n z b ∈ H := (Finset.mem_filter.mp hbA).2
    have hcT : c ∈ T := (Finset.mem_filter.mp hcA).1
    have hcH : s1614_altPair n z c ∈ H := (Finset.mem_filter.mp hcA).2
    have hbz : b ≠ z := (Finset.mem_erase.mp hbT).1
    have hcz : c ≠ z := (Finset.mem_erase.mp hcT).1
    exact ⟨z, b, c, hbz.symm, hcz.symm, hbc, hbH, hcH⟩
  · have hAcard : A.card ≤ 1 := by omega
    obtain ⟨a, haB, b, hbB, c, hcB, hab, hac, hbc⟩ :=
      Finset.two_lt_card.mp (by
        have hT5 : 5 ≤ T.card := by rw [hTcard]; omega
        have hle : T.card ≤ B.card + 1 := by
          rw [← hsum]
          calc A.card + B.card ≤ 1 + B.card := Nat.add_le_add_right hAcard B.card
            _ = B.card + 1 := add_comm 1 B.card
        have h5 : 5 ≤ B.card + 1 := le_trans hT5 hle
        have hBcard : 4 ≤ B.card := Nat.succ_le_succ_iff.mp (by simpa using h5)
        exact lt_of_lt_of_le (by norm_num : 2 < 4) hBcard)
    have haT : a ∈ T := (Finset.mem_filter.mp haB).1
    have hbT : b ∈ T := (Finset.mem_filter.mp hbB).1
    have hcT : c ∈ T := (Finset.mem_filter.mp hcB).1
    have haz : a ≠ z := (Finset.mem_erase.mp haT).1
    have hbz : b ≠ z := (Finset.mem_erase.mp hbT).1
    have hcz : c ≠ z := (Finset.mem_erase.mp hcT).1
    have haH : s1614_altPair n z a ∉ H := (Finset.mem_filter.mp haB).2
    have hbH : s1614_altPair n z b ∉ H := (Finset.mem_filter.mp hbB).2
    have hcH : s1614_altPair n z c ∉ H := (Finset.mem_filter.mp hcB).2
    exact ⟨a, b, c, hab, hac, hbc, key a b haz hbz haH hbH, key a c haz hcz haH hcH⟩

theorem s1614_alt_faithful (hn : 5 ≤ n) (g : Equiv.Perm (Fin n))
    (hg : ∀ m ∈ coreMod n,
      permAct n g m * m⁻¹ ∈ Subgroup.zpowers (allOnes n) ⊓ coreMod n) : g = 1 := by
  classical
  have hpres : ∀ i j : Fin n, i ≠ j →
      s1614_altPair n (g i) (g j) = s1614_altPair n i j := by
    intro i j hij
    have hmc : s1614_altPair n i j ∈ coreMod n := s1614_altPair_mem_coreMod i j
    have hmul : permAct n g (s1614_altPair n i j) * (s1614_altPair n i j)⁻¹
        = s1614_altPair n (g i) (g j) * s1614_altPair n i j := by
      rw [s1614_permAct_altPair, permMod_inv_eq]
    have hpz : s1614_altPair n (g i) (g j) * s1614_altPair n i j
        ∈ Subgroup.zpowers (allOnes n) :=
      (Subgroup.mem_inf.mp (hmul ▸ hg (s1614_altPair n i j) hmc)).1
    have hp_ne : s1614_altPair n (g i) (g j) * s1614_altPair n i j ≠ allOnes n := by
      intro hp
      have hex : ∃ l : Fin n, l ∉ ({g i, g j, i, j} : Finset (Fin n)) := by
        have hlt : ({g i, g j, i, j} : Finset (Fin n)).card <
            (Finset.univ : Finset (Fin n)).card := by
          have h4 : ({g i, g j, i, j} : Finset (Fin n)).card ≤ 4 := by
            have h1 := Finset.card_insert_le (g i) ({g j, i, j} : Finset (Fin n))
            have h2 := Finset.card_insert_le (g j) ({i, j} : Finset (Fin n))
            have h3 := Finset.card_insert_le i ({j} : Finset (Fin n))
            have h4 : ({j} : Finset (Fin n)).card = 1 := Finset.card_singleton j
            omega
          rw [Finset.card_univ, Fintype.card_fin]
          omega
        obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card
          (s := ({g i, g j, i, j} : Finset (Fin n))) (t := Finset.univ) hlt
        exact ⟨l, hl⟩
      obtain ⟨l, hlS⟩ := hex
      have hlg : l ≠ g i := fun h => hlS (by simp [h])
      have hlg' : l ≠ g j := fun h => hlS (by simp [h])
      have hli : l ≠ i := fun h => hlS (by simp [h])
      have hlj : l ≠ j := fun h => hlS (by simp [h])
      have hp_l : Multiplicative.toAdd
          (s1614_altPair n (g i) (g j) * s1614_altPair n i j) l = 0 := by
        simp only [toAdd_mul, s1614_altPair, toAdd_ofAdd, Pi.add_apply, Pi.single_apply]
        rw [if_neg hlg, if_neg hlg', if_neg hli, if_neg hlj]
        decide
      have hall : Multiplicative.toAdd (allOnes n) l = 1 := rfl
      have hcongr := congrArg (fun x : PermMod n => Multiplicative.toAdd x l) hp
      rw [hp_l, hall] at hcongr
      exact one_ne_zero hcongr.symm
    rcases B5FinPerm.mem_zpowers_allOnes_iff.mp hpz with hp1 | hpall
    · have hinv : s1614_altPair n (g i) (g j) = (s1614_altPair n i j)⁻¹ :=
        (inv_eq_of_mul_eq_one_left hp1).symm
      rw [hinv, permMod_inv_eq]
    · exact absurd hpall hp_ne
  have hgi : ∀ i j : Fin n, i ≠ j → g i ∈ ({i, j} : Finset (Fin n)) := by
    intro i j hij
    have hcoord := congrArg (fun x : PermMod n => Multiplicative.toAdd x (g i))
      (hpres i j hij)
    simp only [s1614_altPair, toAdd_ofAdd, Pi.add_apply, Pi.single_apply] at hcoord
    rw [if_neg (fun h => hij (g.injective h))] at hcoord
    simp only [if_true, add_zero] at hcoord
    by_cases hi : g i = i
    · simp [hi]
    · by_cases hj : g i = j
      · simp [hj]
      · exfalso
        rw [if_neg hi, if_neg hj] at hcoord
        simp only [add_zero, zero_add] at hcoord
        exact one_ne_zero hcoord
  apply Equiv.ext
  intro i
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n)
    (by rw [Fintype.card_fin]; omega) i
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega : 2 < n)
  have h1 : g i ∈ ({i, j} : Finset (Fin n)) := hgi i j (Ne.symm hj)
  have h2 : g i ∈ ({i, k} : Finset (Fin n)) := hgi i k (Ne.symm hki)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact h2
    · exact absurd ((h1.symm.trans h2).symm) hkj

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
