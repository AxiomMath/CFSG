module

public import CFSG.Quasithin.Vol2.GoldschmidtA128LinWeight
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Std.Tactic.BVDecide.Normalize.Prop

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Vol2.A128.Lin

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] {n : ℕ}

open scoped Classical in
noncomputable def supp (R : (Fin n → ZMod 2) → Module.End F V) :
    Finset (Fin n → ZMod 2) :=
  Finset.univ.filter fun l => proj R l ≠ 0

variable {R : (Fin n → ZMod 2) → Module.End F V}

theorem mem_supp {l : Fin n → ZMod 2} : l ∈ supp R ↔ proj R l ≠ 0 := by
  simp [supp]

theorem proj_eq_zero_of_notMem_supp {l : Fin n → ZMod 2} (h : l ∉ supp R) : proj R l = 0 := by
  simpa [mem_supp] using h

theorem IsRep.sum_proj_apply (hR : IsRep R) (h2 : (2 : F) ≠ 0) (v : V) :
    ∑ l, proj R l v = v := by
  simpa [LinearMap.sum_apply] using congrArg (fun T => T v) (hR.sum_proj h2)

theorem IsRep.apply_eq_sum (hR : IsRep R) (h2 : (2 : F) ≠ 0) (x : Fin n → ZMod 2) (v : V) :
    R x v = ∑ l, chi F l x • proj R l v := by
  conv_lhs => rw [← hR.sum_proj_apply h2 v]
  rw [map_sum]
  exact Finset.sum_congr rfl fun l _ => hR.isWeight_proj l v x

theorem IsRep.exists_supp_dot_eq_one (hR : IsRep R) (h2 : (2 : F) ≠ 0)
    (hinj : Function.Injective R) {x : Fin n → ZMod 2} (hx : x ≠ 0) :
    ∃ l ∈ supp R, l ⬝ᵥ x = 1 := by
  by_contra hcon
  push Not at hcon
  refine hx (hinj ?_)
  rw [hR.rep_zero]
  ext v
  rw [hR.apply_eq_sum h2 x v, Module.End.one_apply]
  conv_rhs => rw [← hR.sum_proj_apply h2 v]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l ∈ supp R
  · rw [chi_eq_one ((zmod_two_cases _).resolve_right (hcon l hl)), one_smul]
  · simp [proj_eq_zero_of_notMem_supp hl]

theorem IsRep.eq_neg_one_of_supp (hR : IsRep R) (h2 : (2 : F) ≠ 0) {x : Fin n → ZMod 2}
    (h : ∀ l ∈ supp R, l ⬝ᵥ x = 1) : R x = -1 := by
  ext v
  rw [hR.apply_eq_sum h2 x v, LinearMap.neg_apply, Module.End.one_apply]
  conv_rhs => rw [← hR.sum_proj_apply h2 v]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l ∈ supp R
  · rw [chi_eq_neg_one (h l hl), neg_one_smul]
  · simp [proj_eq_zero_of_notMem_supp hl]

theorem IsRep.card_supp_filter_le [FiniteDimensional F V] (hR : IsRep R) (h2 : (2 : F) ≠ 0)
    {x : Fin n → ZMod 2} {d : ℕ} (hfix : Module.finrank F (LinearMap.ker (R x - 1)) ≤ d) :
    ((supp R).filter fun l => l ⬝ᵥ x = 0).card ≤ d := by
  classical
  set T := (supp R).filter fun l => l ⬝ᵥ x = 0 with hT
  have hne : ∀ l ∈ T, ∃ v, proj R l v ≠ 0 := fun l hl => by
    by_contra hcon
    push Not at hcon
    exact mem_supp.mp (Finset.mem_filter.mp hl).1 (LinearMap.ext hcon)
  choose! v hv using hne
  have hdot : ∀ i : T, i.1 ⬝ᵥ x = 0 := fun i => (Finset.mem_filter.mp i.2).2
  have hind : LinearIndependent F fun i : T => proj R i.1 (v i.1) :=
    linearIndependent_of_weights h2 Subtype.val_injective (fun i => hv i.1 i.2)
      (fun i => hR.isWeight_proj i.1 (v i.1))
  have hmem : ∀ i : T, proj R i.1 (v i.1) ∈ LinearMap.ker (R x - 1) := fun i => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hR.isWeight_proj i.1 (v i.1) x,
      chi_eq_one (hdot i), one_smul, Module.End.one_apply, sub_self]
  have hind' : LinearIndependent F fun i : T => (⟨_, hmem i⟩ : LinearMap.ker (R x - 1)) :=
    LinearIndependent.of_comp (LinearMap.ker (R x - 1)).subtype hind
  have hcard := hind'.fintype_card_le_finrank
  rw [Fintype.card_coe] at hcard
  exact hcard.trans hfix

end CFSG.Quasithin.Vol2.A128.Lin
