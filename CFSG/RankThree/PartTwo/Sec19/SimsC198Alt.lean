module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.Sporadic.SchreierLemmas.OrderThree

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open Equiv Equiv.Perm
open scoped commutatorElement

namespace Alt

variable {α : Type*} [DecidableEq α] [Fintype α] {σ : Perm α}

private lemma comm_apply {g σ : Perm α} (hg : Commute g σ) (x : α) : g (σ x) = σ (g x) :=
  DFunLike.congr_fun hg.eq x

private lemma comm_zpow_apply {g σ : Perm α} (hg : Commute g σ) (j : ℤ) (x : α) :
    g ((σ ^ j) x) = (σ ^ j) (g x) :=
  comm_apply (hg.zpow_right j) x

private lemma apply_mem_support_of_commute {k : Perm α} (hk : Commute k σ) {x : α}
    (hx : x ∈ σ.support) : k x ∈ σ.support := by
  rw [mem_support] at hx ⊢
  intro h
  exact hx (k.injective (by rw [comm_apply hk, h]))

private lemma sameCycle_apply_of_forall_commute {g : Perm α}
    (hg : ∀ f ∈ σ.cycleFactorsFinset, Commute g f) {x : α} (hx : x ∈ σ.support) :
    σ.SameCycle x (g x) := by
  have hf : σ.cycleOf x ∈ σ.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.2 hx
  have hgf := hg _ hf
  have hxf : x ∈ (σ.cycleOf x).support := by
    rw [mem_support, cycleOf_apply_self]
    exact mem_support.1 hx
  have hgxf : g x ∈ (σ.cycleOf x).support := by
    rw [mem_support] at hxf ⊢
    rw [← comm_apply hgf x]
    intro h
    exact hxf (g.injective h)
  exact (mem_support_cycleOf_iff.1 hgxf).1

private lemma commutator_apply_eq_self {g h : Perm α} (hgσ : Commute g σ) (hhσ : Commute h σ)
    (hg : ∀ f ∈ σ.cycleFactorsFinset, Commute g f) (hh : ∀ f ∈ σ.cycleFactorsFinset, Commute h f)
    {y : α} (hy : y ∈ σ.support) : ⁅g, h⁆ y = y := by
  have hz : g⁻¹ (h⁻¹ y) ∈ σ.support :=
    apply_mem_support_of_commute hgσ.inv_left (apply_mem_support_of_commute hhσ.inv_left hy)
  generalize hzdef : g⁻¹ (h⁻¹ y) = z at hz
  obtain ⟨i, hi⟩ := sameCycle_apply_of_forall_commute hg hz
  obtain ⟨j, hj⟩ := sameCycle_apply_of_forall_commute hh hz
  have key : g (h z) = h (g z) :=
    calc g (h z) = g ((σ ^ j) z) := by rw [hj]
      _ = (σ ^ j) (g z) := comm_zpow_apply hgσ j z
      _ = (σ ^ j) ((σ ^ i) z) := by rw [hi]
      _ = (σ ^ (j + i)) z := by rw [zpow_add, Perm.mul_apply]
      _ = (σ ^ (i + j)) z := by rw [add_comm]
      _ = (σ ^ i) ((σ ^ j) z) := by rw [zpow_add, Perm.mul_apply]
      _ = (σ ^ i) (h z) := by rw [hj]
      _ = h ((σ ^ i) z) := (comm_zpow_apply hhσ i z).symm
      _ = h (g z) := by rw [hi]
  have hgz : g z = h⁻¹ y := by rw [← hzdef]; simp
  calc ⁅g, h⁆ y = g (h (g⁻¹ (h⁻¹ y))) := by simp [commutatorElement_def, Perm.mul_apply]
    _ = g (h z) := by rw [hzdef]
    _ = h (g z) := key
    _ = y := by rw [hgz]; simp

end Alt

open Alt in
theorem alternating_false_of_perfect_centralizer {n : ℕ} (hn : n ≤ 14)
    (c : alternatingGroup (Fin n)) (hc : orderOf c = 3)
    (L : Subgroup (alternatingGroup (Fin n))) (hLc : L ≤ Subgroup.centralizer ({c} : Set _))
    (hcL : c ∈ L) (hL : Group.IsPerfect L) : False := by
  set σ : Perm (Fin n) := (c : Perm (Fin n)) with hσ
  have hσ3 : orderOf σ = 3 := by rw [hσ, Subgroup.orderOf_coe, hc]
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ3
    omega
  obtain ⟨k, -, hk3, -, hkcard, -⟩ :=
    CFSG.Sporadic.SchreierLemmas.order_three_permutation_shape hσ3
  have hcard : Nat.card σ.cycleFactorsFinset ≤ 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hkcard]
    rw [Fintype.card_fin] at hk3
    omega
  haveI : Group.IsSolvable (Perm σ.cycleFactorsFinset) := Equiv.Perm.isSolvable hcard
  let ι : L →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp L.subtype
  have hcomm : ∀ l : L, Commute (ι l) σ := fun l => by
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hLc l.2)
    exact congrArg (fun a : alternatingGroup (Fin n) => (a : Perm (Fin n))) h
  let ι' : L →* Subgroup.centralizer {σ} :=
    ι.codRestrict _ (fun l => Subgroup.mem_centralizer_singleton_iff.2 (hcomm l).eq)
  let ψ : L →* Perm σ.cycleFactorsFinset := (OnCycleFactors.toPermHom σ).comp ι'
  haveI : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have hψ : ∀ l : L, ψ l = 1 := by
    by_contra hne
    obtain ⟨l, hl⟩ := not_forall.1 hne
    haveI : Nontrivial ψ.range :=
      ⟨⟨⟨ψ l, MonoidHom.mem_range.2 ⟨l, rfl⟩⟩, 1, fun h => hl (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable ψ.range inferInstance
  have hker : ∀ l : L, ∀ f ∈ σ.cycleFactorsFinset, Commute (ι l) f := fun l =>
    (OnCycleFactors.mem_ker_toPermHom_iff σ (ι' l)).1 (MonoidHom.mem_ker.2 (hψ l))
  let F : Subgroup L := (fixingSubgroup (Perm (Fin n)) (σ.support : Set (Fin n))).comap ι
  have hF : commutator L ≤ F := by
    rw [commutator_def, Subgroup.commutator_le]
    intro p _ q _
    rw [Subgroup.mem_comap, mem_fixingSubgroup_iff]
    intro y hy
    rw [Perm.smul_def, map_commutatorElement]
    exact commutator_apply_eq_self (hcomm p) (hcomm q) (hker p) (hker q) hy
  have hcF : (⟨c, hcL⟩ : L) ∈ F := hF (by rw [hL.commutator_eq_top]; exact Subgroup.mem_top _)
  rw [Subgroup.mem_comap, mem_fixingSubgroup_iff] at hcF
  apply hσ1
  refine Equiv.ext fun y => ?_
  rw [Perm.one_apply]
  by_cases hy : y ∈ σ.support
  · exact hcF y hy
  · exact notMem_support.1 hy

end CFSG.RankThree.PartTwo.Sec19.SimsC198
