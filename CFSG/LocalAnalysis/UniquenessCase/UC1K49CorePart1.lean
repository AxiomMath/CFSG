module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreProp
public import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal
public import CFSG.GroupTheory.SteinbergCBFTPSolvable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutator_le_commutator_left_of_normalizer {A B : Subgroup G}
    (hA : ⁅A, A⁆ = A)
    (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    ⁅A, B⁆ ≤ ⁅⁅A, B⁆, A⁆ := by
  have hTleA : ⁅A, B⁆ ≤ A := Subgroup.le_normalizer_iff_commutator_le_left.mp hBA
  have hNle : ⁅⁅A, B⁆, A⁆ ≤ A ⊔ B := by
    have h := (Subgroup.commutator_mono hTleA le_rfl).trans
      (le_sup_left : ⁅A, A⁆ ≤ ⁅A, A⁆ ⊔ B)
    simpa [hA] using h
  have hNnorm : A ⊔ B ≤ Subgroup.normalizer ((⁅⁅A, B⁆, A⁆ : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · exact CFSG.GroupTheory.FT63ChII.le_normalizer_commutator
        (Subgroup.normalizer_commutator_ge_left A B) Subgroup.le_normalizer
    · exact CFSG.GroupTheory.FT63ChII.le_normalizer_commutator
        (Subgroup.normalizer_commutator_ge_right A B) hBA
  have hrot := CFSG.GroupTheory.commutator_commutator_le_of_rotate_normal
    (M := A ⊔ B) (A := A) (B := B) (N := ⁅⁅A, B⁆, A⁆)
    le_sup_left le_sup_right hNle hNnorm le_rfl (by rw [Subgroup.commutator_comm B A])
  rwa [hA] at hrot

private theorem commutator_le_commutator_right_of_normalizer {A B : Subgroup G}
    (hB : ⁅B, B⁆ = B)
    (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    ⁅A, B⁆ ≤ ⁅⁅A, B⁆, B⁆ := by
  have h := commutator_le_commutator_left_of_normalizer (A := B) (B := A) hB hBA hAB
  rwa [Subgroup.commutator_comm B A] at h

theorem commutator_eq_bot_of_perfect_of_mutual {A B Q : Subgroup G}
    (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B)
    (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (hABQ : ⁅A, B⁆ ≤ Q)
    (hQAB : ⁅⁅Q, A⁆, B⁆ = ⊥) (hQBA : ⁅⁅Q, B⁆, A⁆ = ⊥) :
    ⁅A, B⁆ = ⊥ := by
  have hA_le : ⁅A, B⁆ ≤ ⁅⁅A, B⁆, A⁆ :=
    commutator_le_commutator_left_of_normalizer hA hAB hBA
  have hB_le : ⁅A, B⁆ ≤ ⁅⁅A, B⁆, B⁆ :=
    commutator_le_commutator_right_of_normalizer hB hAB hBA
  have hTleQB : ⁅A, B⁆ ≤ ⁅Q, B⁆ :=
    hB_le.trans (Subgroup.commutator_mono hABQ le_rfl)
  have hTA : ⁅⁅A, B⁆, A⁆ ≤ ⁅⁅Q, B⁆, A⁆ :=
    Subgroup.commutator_mono hTleQB le_rfl
  have hTAeq : ⁅⁅A, B⁆, A⁆ = ⊥ := by
    rw [hQBA] at hTA
    exact le_bot_iff.mp hTA
  rw [hTAeq] at hA_le
  exact le_bot_iff.mp hA_le

theorem zpowers_eq_triple {x y : G} (hord : orderOf x = 3) (hy : y ∈ Subgroup.zpowers x) :
    y = 1 ∨ y = x ∨ y = x ^ 2 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hmod : x ^ (m % (3 : ℤ)) = x ^ m := by
    have h := zpow_mod_orderOf x m
    rw [hord] at h
    exact h
  rw [← hmod]
  set k : ℤ := m % 3 with hk
  have h0 : 0 ≤ k := by rw [hk]; exact Int.emod_nonneg m (by norm_num)
  have h1 : k < 3 := by rw [hk]; exact Int.emod_lt_of_pos m (by norm_num)
  interval_cases k
  · left; rw [zpow_zero]
  · right; left; rw [zpow_one]
  · right; right; rw [zpow_ofNat]

private theorem commutator_commutator_conjugate_eq_bot {H X L Q I : Subgroup G}
    (h : Setup49 H X L Q I) {x₀ : G} (hx₀X : x₀ ∈ X) {N1 : Subgroup G} (hN1I : ⁅N1, I⁆ = ⊥)
    {V : ℕ → Subgroup G} (hVnat : ∀ i, i < 3 → ⁅Q, Lc L x₀ i⁆ ≤ V i)
    (hVcomm : ∀ i j, i < 3 → j < 3 → i ≠ j → ⁅V i, Lc L x₀ j⁆ ≤ N1)
    {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) :
    ⁅⁅Q, Lc L x₀ i⁆, Lc L x₀ j⁆ = ⊥ := by
  have hDj := (struct49 h).2.2.2.2.1 (x₀ ^ j) (X.pow_mem hx₀X j)
  refine CFSG.GroupTheory.CoprimeSection.commutator_eq_bot_of_two_step
    (D := Lc L x₀ j) (Y := ⁅Q, Lc L x₀ i⁆) (Y₁ := N1) ?_ ?_ ?_
  · exact CFSG.RankThree.PartTwo.Sec18.commutator_eq_of_mem_oTwoComponentsIn hDj.1
  · exact (Subgroup.commutator_mono (hVnat i hi) le_rfl).trans (hVcomm i j hi hj hij)
  · have hle : ⁅N1, Lc L x₀ j⁆ ≤ ⁅N1, I⁆ :=
      Subgroup.commutator_mono le_rfl (conjugate_le_I h (X.pow_mem hx₀X j))
    rw [hN1I] at hle
    exact le_bot_iff.mp hle

private theorem exists_lt_three_conjugate_eq_Lc {L : Subgroup G} {x₀ z : G}
    (hord : orderOf x₀ = 3) (hz : z ∈ Subgroup.zpowers x₀) :
    ∃ i : ℕ, i < 3 ∧ CFSG.conjugate L z = Lc L x₀ i := by
  rcases zpowers_eq_triple hord hz with h1 | h1 | h1
  · exact ⟨0, by norm_num, by rw [h1, Lc, pow_zero]⟩
  · exact ⟨1, by norm_num, by rw [h1, Lc, pow_one]⟩
  · exact ⟨2, by norm_num, by rw [h1, Lc]⟩

theorem part1_49 (hI : Inputs49) {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    (hK : KI49 X I) : Part1_49 X L := by
  obtain ⟨x₀, hx₀X, hxgen, -, -, -⟩ := exists_generator49 h
  have hord : orderOf x₀ = 3 := by
    have hc := Nat.card_zpowers x₀
    rw [← hxgen] at hc
    rw [h.card_X] at hc
    exact hc.symm
  obtain ⟨N0, N1, _, _, _, _, hN1I, _, _, hshape⟩ := propM49 hI h hxgen hK
  let V : ℕ → Subgroup G := fun i => ⁅N0, Lc L x₀ i⁆ ⊔ N1
  have hVeq : ∀ i, V i = ⁅N0, Lc L x₀ i⁆ ⊔ N1 := fun i => rfl
  obtain ⟨-, -, hVcommall, hVnatall⟩ := hshape V hVeq
  have hcomm : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j →
      ⁅⁅Q, Lc L x₀ i⁆, Lc L x₀ j⁆ = ⊥ :=
    fun i j hi hj hij => commutator_commutator_conjugate_eq_bot h hx₀X hN1I
      (fun i hi => (hVnatall i hi).1) hVcommall hi hj hij
  intro x hx y hy hne
  have hxidx : ∃ i : ℕ, i < 3 ∧ CFSG.conjugate L x = Lc L x₀ i :=
    exists_lt_three_conjugate_eq_Lc hord (hxgen ▸ hx)
  have hyidx : ∃ j : ℕ, j < 3 ∧ CFSG.conjugate L y = Lc L x₀ j :=
    exists_lt_three_conjugate_eq_Lc hord (hxgen ▸ hy)
  obtain ⟨i, hi, hxi⟩ := hxidx
  obtain ⟨j, hj, hyj⟩ := hyidx
  have hne' : Lc L x₀ i ≠ Lc L x₀ j := fun heq => hne (by rw [hxi, hyj, heq])
  have hij : i ≠ j := fun heq => hne' (by rw [heq])
  rw [hxi, hyj]
  exact commutator_eq_bot_of_perfect_of_mutual
    (CFSG.RankThree.PartTwo.Sec18.commutator_eq_of_mem_oTwoComponentsIn
      ((struct49 h).2.2.2.2.1 (x₀ ^ i) (X.pow_mem hx₀X i)).1)
    (CFSG.RankThree.PartTwo.Sec18.commutator_eq_of_mem_oTwoComponentsIn
      ((struct49 h).2.2.2.2.1 (x₀ ^ j) (X.pow_mem hx₀X j)).1)
    (conjugate_normalize_of_ne h (X.pow_mem hx₀X i) (X.pow_mem hx₀X j) hne')
    (conjugate_normalize_of_ne h (X.pow_mem hx₀X j) (X.pow_mem hx₀X i) hne'.symm)
    (commutator_conjugate_le h (X.pow_mem hx₀X i) (X.pow_mem hx₀X j) hne')
    (hcomm i j hi hj hij)
    (hcomm j i hj hi hij.symm)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
