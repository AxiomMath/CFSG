module

public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTwo
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessB
public import CFSG.RankThree.PartTwo.Census.Spin.CarrierBTheta

public section

namespace CFSG.RankThree.PartTwo.Census.Spin.CarrierB

open TauCeti TauCeti.TypeBSpinCarrier RootData
open scoped commutatorElement

section Generic

variable {n : ℕ} {K : Type} [Field K] {σ : K →+* K}
  {F : (rootData n K).G →* (rootData n K).G}

theorem B_long_neighbour (i j : Fin (n + 1)) (hi : i.val < n) (hj : j.val < n)
    (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    (rootData n K).CM j i = -1 ∧ (rootData n K).CM i j = -1 := by
  rw [rootData_CM, Matrix.transpose_apply, Matrix.transpose_apply, B_apply', B_apply',
    Nat.add_sub_cancel]
  constructor <;> split_ifs <;> omega

theorem long_mem_commutator (hF : (rootData n K).IsFrobenius σ F) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (hn : 2 ≤ n) (i : Fin (n + 1))
    (hi : i.val < n) {u : K} (hu : u ∈ RootData.fixedField σ) :
    (rootData n K).x i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ ∧
      (rootData n K).y i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  obtain ⟨j, hj, hij⟩ : ∃ j : Fin (n + 1), j.val < n ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    by_cases h : i.val + 1 < n
    · exact ⟨⟨i.val + 1, by omega⟩, h, Or.inl rfl⟩
    · exact ⟨⟨i.val - 1, by omega⟩, by simp only; omega, Or.inr (by simp only; omega)⟩
  have hne : i ≠ j := fun h => by
    rw [h] at hij
    omega
  obtain ⟨hji, hij'⟩ := B_long_neighbour (K := K) i j hi hj hij
  have hI := intRootData n
  have key : ∀ {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ},
      X * Y * X = 0 → intMap K X * intMap K Y * intMap K X = 0 :=
    fun h => by rw [← intMap_mul, ← intMap_mul, h, intMap_zero]
  have h1F : (1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).one_mem
  have hc1 : ∀ {g g' : (rootData n K).G}, g ∈ fixedSubgroup F → g' ∈ fixedSubgroup F →
      ⁅g, g'⁆ ∈ fixedSubgroup F := fun hg hg' => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hg')
      (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hg')
  constructor
  · rw [(rootData n K).x_eq_commutator hc hne hji (key (hI.serre_XX i j hij'))
      (key (hI.serre_XX j i hji)) u]
    exact Subgroup.commutator_mem_commutator
      (hc1 (x_mem_fixed hF h1F) (x_mem_fixed hF h1F)) (y_mem_fixed hF hu)
  · rw [(rootData n K).y_eq_commutator hc hne hji (key (hI.serre_YY i j hij'))
      (key (hI.serre_YY j i hji)) u]
    exact Subgroup.commutator_mem_commutator
      (hc1 (y_mem_fixed hF h1F) (y_mem_fixed hF h1F)) (x_mem_fixed hF hu)

theorem hasWitness_long_gen (hF : (rootData n K).IsFrobenius σ F) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (hchar : (2 : K) = 0) (hn : 9 ≤ n) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 4 := by
  have h1F : (1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).one_mem
  let J : Fin 4 → Fin (n + 1) := fun a => ⟨2 * a.val, by omega⟩
  have hJ : Function.Injective J := fun a b h => by
    have h' : 2 * a.val = 2 * b.val := congrArg Fin.val h
    exact Fin.ext (by omega)
  have horth : ∀ a b, a ≠ b → (rootData n K).CM (J a) (J b) = 0 := fun a b hab => by
    have h' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rw [rootData_CM, Matrix.transpose_apply, B_apply', Nat.add_sub_cancel]
    simp only [J]
    split_ifs <;> omega
  have hJlong : ∀ a, (J a).val < n := fun a => by simp only [J]; omega
  have h := (rootData n K).three_witness_node hchar J hJ horth
    (fun a => (long_mem_commutator hF hc (by omega) (J a) (hJlong a) h1F).1)
    (fun a => (long_mem_commutator hF hc (by omega) (J a) (hJlong a) h1F).2) ⟨8, by omega⟩
    (fun a h => by
      have h' := congrArg Fin.val h
      simp only [J] at h'
      omega)
    (fun a => by
      rw [rootData_CM, Matrix.transpose_apply, B_apply', Nat.add_sub_cancel]
      simp only [J]
      split_ifs <;> omega)
    (long_mem_commutator hF hc (by omega) ⟨8, by omega⟩ (by simp only; omega) h1F).1
    (long_mem_commutator hF hc (by omega) ⟨8, by omega⟩ (by simp only; omega) h1F).2
  rwa [Fintype.card_fin] at h

end Generic

variable (b : TypeBLieIndex)

theorem exists_unit_order_seven (h2 : b.1.characteristic = 2) :
    ∃ c : b.1.Closureˣ, ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1 := by
  have hcard : Nat.card (frobeniusFixedSubfield b.1.Closure b.1.characteristic 3) = 8 := by
    rw [card_frobeniusFixedSubfield]
    · rw [h2]
      norm_num
    · norm_num
  have : Finite (frobeniusFixedSubfield b.1.Closure b.1.characteristic 3) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨c, -, hc⟩ := exists_unit_orderOf_eq_card
    (frobeniusFixedSubfield b.1.Closure b.1.characteristic 3)
  rw [hcard] at hc
  refine ⟨c, fun k hk h1 h2' hck => ?_⟩
  have hdvd := orderOf_dvd_iff_zpow_eq_one.mpr hck
  rw [hc] at hdvd
  omega

theorem hasWitness_three (h2 : b.1.characteristic = 2) (hn : 9 ≤ b.carrierRank) :
    HasWitness b.Group 3 4 := by
  have hchar : (2 : b.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → b.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero b.1.Closure b.1.characteristic)
    exact_mod_cast h
  obtain ⟨c, hc⟩ := exists_unit_order_seven b h2
  exact hasWitness_long_gen (isFrobenius b) hc hchar hn

end CFSG.RankThree.PartTwo.Census.Spin.CarrierB
