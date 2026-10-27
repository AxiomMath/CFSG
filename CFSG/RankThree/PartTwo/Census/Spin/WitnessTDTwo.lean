module

public import CFSG.RankThree.PartTwo.Census.Spin.WitnessDTwo
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTD

public section

namespace CFSG.RankThree.PartTwo.Census.Spin.CarrierTD

open TauCeti TauCeti.TypeDSpinCarrier CarrierD RootData
open scoped commutatorElement

section Generic

variable {n : ℕ} {hn : 4 ≤ n} {K : Type} [Field K] {σ : K →+* K} {π : Equiv.Perm (Fin n)}
  {F : (rootData n hn K).G →* (rootData n hn K).G}

theorem fixed_mem_commutator (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (i : Fin n) (hi : i.val < n - 2)
    {u : K} (hu : σ u = u) :
    (rootData n hn K).x i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ ∧
      (rootData n hn K).y i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  obtain ⟨j, hj, hij⟩ : ∃ j : Fin n, j.val < n - 2 ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    by_cases h : i.val + 1 < n - 2
    · exact ⟨⟨i.val + 1, by omega⟩, h, Or.inl rfl⟩
    · exact ⟨⟨i.val - 1, by omega⟩, by simp only; omega, Or.inr (by simp only; omega)⟩
  have hne : i ≠ j := fun h => by
    rw [h] at hij
    omega
  have hji : (rootData n hn K).CM j i = -1 := by
    rw [rootData_CM, D_apply']
    split_ifs <;> omega
  have hij' : (rootData n hn K).CM i j = -1 := by
    rw [rootData_CM, D_apply']
    split_ifs <;> omega
  have hI := intRootData n hn
  have key : ∀ {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ},
      X * Y * X = 0 → intMap K X * intMap K Y * intMap K X = 0 :=
    fun h => by rw [← intMap_mul, ← intMap_mul, h, intMap_zero]
  have hc1 : ∀ {g g' : (rootData n hn K).G}, g ∈ fixedSubgroup F → g' ∈ fixedSubgroup F →
      ⁅g, g'⁆ ∈ fixedSubgroup F := fun hg hg' => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hg')
      (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hg')
  have h1 : σ 1 = 1 := map_one σ
  constructor
  · rw [(rootData n hn K).x_eq_commutator hc hne hji (key (hI.serre_XX i j hij'))
      (key (hI.serre_XX j i hji)) u]
    exact Subgroup.commutator_mem_commutator
      (hc1 (x_mem_fixed_tw hF (hπ i hi) h1) (x_mem_fixed_tw hF (hπ j hj) h1))
      (y_mem_fixed_tw hF (hπ j hj) hu)
  · rw [(rootData n hn K).y_eq_commutator hc hne hji (key (hI.serre_YY i j hij'))
      (key (hI.serre_YY j i hji)) u]
    exact Subgroup.commutator_mem_commutator
      (hc1 (y_mem_fixed_tw hF (hπ i hi) h1) (y_mem_fixed_tw hF (hπ j hj) h1))
      (x_mem_fixed_tw hF (hπ j hj) hu)

theorem hasWitness_three_gen (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (hchar : (2 : K) = 0) (h11 : 11 ≤ n) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 4 := by
  have h1 : σ 1 = 1 := map_one σ
  let J : Fin 4 → Fin n := fun a => ⟨2 * a.val, by omega⟩
  have hJ : Function.Injective J := fun a b h => by
    have h' : 2 * a.val = 2 * b.val := congrArg Fin.val h
    exact Fin.ext (by omega)
  have horth : ∀ a b, a ≠ b → (rootData n hn K).CM (J a) (J b) = 0 := fun a b hab => by
    have h' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rw [rootData_CM, D_apply']
    simp only [J]
    split_ifs <;> omega
  have hJf : ∀ a, (J a).val < n - 2 := fun a => by simp only [J]; omega
  have h := (rootData n hn K).three_witness_node hchar J hJ horth
    (fun a => (fixed_mem_commutator hF hπ hc (J a) (hJf a) h1).1)
    (fun a => (fixed_mem_commutator hF hπ hc (J a) (hJf a) h1).2) ⟨8, by omega⟩
    (fun a h => by
      have h' := congrArg Fin.val h
      simp only [J] at h'
      omega)
    (fun a => by
      rw [rootData_CM, D_apply']
      simp only [J]
      split_ifs <;> omega)
    (fixed_mem_commutator hF hπ hc ⟨8, by omega⟩ (by simp only; omega) h1).1
    (fixed_mem_commutator hF hπ hc ⟨8, by omega⟩ (by simp only; omega) h1).2
  rwa [Fintype.card_fin] at h

end Generic

variable (d : TypeTwistedDLieIndex)

theorem hasWitness_three (h2 : d.1.characteristic = 2) (h11 : 11 ≤ d.1.rank) :
    HasWitness d.Group 3 4 := by
  have hchar : (2 : d.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → d.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero d.1.Closure d.1.characteristic)
    exact_mod_cast h
  obtain ⟨c, hc⟩ := CarrierD.exists_unit_order_seven d.1 h2
  exact hasWitness_three_gen (isTwistedFrobenius d) (fun i hi => perm_of_lt d hi) hc hchar h11

end CFSG.RankThree.PartTwo.Census.Spin.CarrierTD
