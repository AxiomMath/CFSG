module

public import CFSG.RankThree.PartOne.SLB4A.Basic
public import CFSG.LieType.Ree.FixedPositiveBlocks

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

section Pow

variable {τ : Tag} {K : Type} [Field K]

theorem pinnedX_pow_one (α : Fin τ.rank → ℤ) (n : ℕ) :
    pinnedX τ K α 1 ^ n = pinnedX τ K α (n : K) := by
  induction n with
  | zero => simp [pinnedX_zero]
  | succ n ih => rw [pow_succ, ih, ← pinnedX_add, Nat.cast_succ]

end Pow

section Gen

variable
  {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem exists_two_pow_five_posRoots (G : Subgroup (ModGL τ K)) (α : Fin 5 → Fin τ.rank → ℤ)
    (hinj : Function.Injective α) (hroot : ∀ i, RootOps.isRootB τ (α i) = true)
    (hpos : ∀ i, 0 < height (α i)) (hnn : ∀ i k, 0 ≤ α i k) (hcol : ∀ i, ∃ k, 1 ≤ α i k)
    (hnr : ∀ i j, i ≠ j → ∀ a < 8, ∀ b < 8, 1 ≤ a → 1 ≤ b →
      RootOps.isRootB τ (a • α i + b • α j) = false)
    (hG : ∀ i, pinnedX τ K (α i) 1 ∈ G) :
    ∃ U : Subgroup G, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  have hr : ∀ i, IsRoot τ (α i) := fun i => RootOps.isRootB_iff.1 (hroot i)
  have hcomm : ∀ i j, Commute (pinnedX τ K (α i) 1) (pinnedX τ K (α j) 1) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · obtain ⟨k, hk⟩ := hcol i
      obtain ⟨l, hl⟩ := hcol j
      exact commute_pinnedX_of_not_isRoot K (hr i) (hr j) (hpos i) (hpos j)
        (fun h => hij (hinj h))
        (forall_not_isRoot_of_check (hnn i) (hnn j) hk hl (hnr i j hij)) 1 1
  refine exists_two_pow_five_of_commInvol (fun i => (⟨pinnedX τ K (α i) 1, hG i⟩ : G))
    (fun i j => Subtype.ext (hcomm i j).eq) (fun i => Subtype.ext ?_) ?_
  · show pinnedX τ K (α i) 1 * pinnedX τ K (α i) 1 = 1
    rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  · intro v hv
    have hv' := congrArg Subtype.val hv
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one, pinnedX_pow_one] at hv'
    have hinjp := (positive_root_product_injectivity τ K α hinj fun i => ⟨hr i, hpos i⟩).2
    have hprod : ∀ c : Fin 5 → K, (List.ofFn fun i => pinnedX τ K (α i) (c i)).prod =
        pinnedX τ K (α 0) (c 0) * (pinnedX τ K (α 1) (c 1) * (pinnedX τ K (α 2) (c 2) *
          (pinnedX τ K (α 3) (c 3) * pinnedX τ K (α 4) (c 4)))) := fun c => by
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
      rfl
    have h0 : (fun c : Fin 5 → K => (List.ofFn fun i => pinnedX τ K (α i) (c i)).prod)
        (fun i => ((ex (v i) : ℕ) : K)) =
        (fun c : Fin 5 → K => (List.ofFn fun i => pinnedX τ K (α i) (c i)).prod) 0 := by
      show (List.ofFn fun i => pinnedX τ K (α i) (((ex (v i) : ℕ) : K))).prod =
        (List.ofFn fun i => pinnedX τ K (α i) ((0 : Fin 5 → K) i)).prod
      rw [hprod, hprod]
      simp only [Pi.zero_apply, pinnedX_zero, mul_one]
      simpa only [mul_assoc] using hv'
    have h1 := congrFun (hinjp h0)
    have h2 : ∀ i, ex (v i) = 0 := fun i => by
      have h3 := h1 i
      rcases ex_cases (v i) with h | h
      · exact h
      · rw [h] at h3
        simp at h3
    funext k
    exact eq_one_of_ex_eq_zero (h2 k)

end Gen

section Data

@[expose] def rootsF4 : Fin 5 → Fin Tag.F4.rank → ℤ :=
  ![![0, 0, 0, 1], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 1, 1, 1], ![1, 2, 2, 2]]

@[expose] def rootsE6 : Fin 5 → Fin Tag.E6.rank → ℤ :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0],
    ![0, 0, 0, 1, 1, 1]]

@[expose] def rootsE7 : Fin 5 → Fin Tag.E7.rank → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0]]

@[expose] def rootsE8 : Fin 5 → Fin Tag.E8.rank → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0]]

@[expose] def PosRootData (τ : Tag) (α : Fin 5 → Fin τ.rank → ℤ) : Prop :=
  Function.Injective α ∧ (∀ i, RootOps.isRootB τ (α i) = true) ∧ (∀ i, 0 < height (α i)) ∧
    (∀ i k, 0 ≤ α i k) ∧ (∀ i, ∃ k, 1 ≤ α i k) ∧
    ∀ i j, i ≠ j → ∀ a < 8, ∀ b < 8, 1 ≤ a → 1 ≤ b →
      RootOps.isRootB τ (a • α i + b • α j) = false

instance (τ : Tag) (α : Fin 5 → Fin τ.rank → ℤ) : Decidable (PosRootData τ α) := by
  unfold PosRootData
  infer_instance

theorem posRootData_F4 : PosRootData Tag.F4 rootsF4 := by
  unfold PosRootData
  decide +kernel

theorem posRootData_E6 : PosRootData Tag.E6 rootsE6 := by
  unfold PosRootData
  decide +kernel

theorem posRootData_E7 : PosRootData Tag.E7 rootsE7 := by
  unfold PosRootData
  decide +kernel

theorem posRootData_E8 : PosRootData Tag.E8 rootsE8 := by
  unfold PosRootData
  decide +kernel

end Data

section Groups

variable
  {K : Type} [Field K] [CharP K 2]

theorem exists_two_pow_five_adjoint_even {τ : Tag} (α : Fin 5 → Fin τ.rank → ℤ)
    (h : PosRootData τ α) :
    ∃ U : Subgroup (adjointGroup τ K), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  obtain ⟨hinj, hroot, hpos, hnn, hcol, hnr⟩ := h
  exact exists_two_pow_five_posRoots (adjointGroup τ K) α hinj hroot hpos hnn hcol hnr
    fun i => pinnedX_mem_adjointGroup (α i) 1

theorem exists_two_pow_five_E6_even :
    ∃ U : Subgroup (adjointGroup Tag.E6 K), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 :=
  exists_two_pow_five_adjoint_even rootsE6 posRootData_E6

theorem exists_two_pow_five_E7_even :
    ∃ U : Subgroup (adjointGroup Tag.E7 K), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 :=
  exists_two_pow_five_adjoint_even rootsE7 posRootData_E7

theorem exists_two_pow_five_E8_even :
    ∃ U : Subgroup (adjointGroup Tag.E8 K), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 :=
  exists_two_pow_five_adjoint_even rootsE8 posRootData_E8

theorem exists_two_pow_five_F4_even :
    ∃ U : Subgroup (adjointGroup Tag.F4 K), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 :=
  exists_two_pow_five_adjoint_even rootsF4 posRootData_F4

end Groups

end CFSG.RankThree.PartOne.SLB4A
