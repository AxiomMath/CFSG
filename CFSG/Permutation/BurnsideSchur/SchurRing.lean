module

public import CFSG.Permutation.BurnsideSchur.GroupRing
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

open MulAction
open scoped Pointwise

namespace BurnsideSchur

variable {C : Type*} [AddCommGroup C] (G : Subgroup (Equiv.Perm C))

@[expose] def IsStable (S : Set C) : Prop :=
  ∀ g ∈ G, g 0 = 0 → ∀ x, g x ∈ S ↔ x ∈ S

def suborbit (x : C) : Set C :=
  {y | ∃ g ∈ G, g 0 = 0 ∧ g x = y}

variable {G}

private theorem inv_apply_zero {g : Equiv.Perm C} (hg0 : g 0 = 0) : g⁻¹ 0 = 0 := by
  rw [Equiv.Perm.inv_eq_iff_eq, hg0]

private theorem isStable_of_forall_mem {S : Set C} (h : ∀ g ∈ G, g 0 = 0 → ∀ x ∈ S, g x ∈ S) :
    IsStable G S := by
  refine fun g hg hg0 x => ⟨fun hx => ?_, h g hg hg0 x⟩
  simpa using h g⁻¹ (inv_mem hg) (inv_apply_zero hg0) (g x) hx

private theorem isStable_zero : IsStable G ({0} : Set C) := by
  refine isStable_of_forall_mem fun g _ hg0 x hx => ?_
  simp_all

theorem mem_suborbit_self (x : C) : x ∈ suborbit G x :=
  ⟨1, one_mem G, rfl, rfl⟩

theorem isStable_suborbit (x : C) : IsStable G (suborbit G x) := by
  refine isStable_of_forall_mem fun g hg hg0 y ⟨k, hk, hk0, hky⟩ => ?_
  exact ⟨g * k, mul_mem hg hk, by simp [hk0, hg0], by simp [hky]⟩

private theorem IsStable.suborbit_subset {S : Set C} (hS : IsStable G S) {x : C} (hx : x ∈ S) :
    suborbit G x ⊆ S := by
  rintro _ ⟨g, hg, hg0, rfl⟩
  exact (hS g hg hg0 x).2 hx

theorem suborbit_eq_of_mem {x y : C} (h : y ∈ suborbit G x) : suborbit G y = suborbit G x := by
  refine ((isStable_suborbit x).suborbit_subset h).antisymm ?_
  obtain ⟨g, hg, hg0, rfl⟩ := h
  rintro _ ⟨k, hk, hk0, rfl⟩
  refine ⟨k * g⁻¹, mul_mem hk (inv_mem hg), ?_, by simp⟩
  rw [Equiv.Perm.mul_apply, inv_apply_zero hg0, hk0]

theorem suborbit_subset_or_disjoint {S : Set C} (hS : IsStable G S) (x : C) :
    suborbit G x ⊆ S ∨ Disjoint (suborbit G x) S := by
  refine or_iff_not_imp_right.2 fun h => ?_
  obtain ⟨y, hyx, hyS⟩ := Set.not_disjoint_iff.1 h
  exact suborbit_eq_of_mem hyx ▸ hS.suborbit_subset hyS

theorem zero_notMem_suborbit {x : C} (hx : x ≠ 0) : (0 : C) ∉ suborbit G x := by
  rintro ⟨g, -, hg0, hgx⟩
  exact hx (g.injective (hgx.trans hg0.symm))

section Translations

variable (hG : ∀ c : C, Equiv.addRight c ∈ G)
include hG

private theorem exists_mem_stabilizer {g : Equiv.Perm C} (hg : g ∈ G) (a : C) :
    ∃ k ∈ G, k 0 = 0 ∧ ∀ x, k x = g (x + a) - g a :=
  ⟨Equiv.addRight (-g a) * g * Equiv.addRight a,
    mul_mem (mul_mem (hG _) hg) (hG a), by simp, fun x => by simp [sub_eq_add_neg]⟩

theorem IsStable.sub_mem_iff {S : Set C} (hS : IsStable G S) {g : Equiv.Perm C} (hg : g ∈ G)
    (x y : C) : g x - g y ∈ S ↔ x - y ∈ S := by
  obtain ⟨k, hk, hk0, hkx⟩ := exists_mem_stabilizer hG hg y
  simpa [hkx] using hS k hk hk0 (x - y)

theorem IsStable.neg {S : Set C} (hS : IsStable G S) : IsStable G (-S) := by
  intro g hg hg0 x
  simpa [hg0] using hS.sub_mem_iff hG hg 0 x

theorem isMultiplyPretransitive_two_iff :
    IsMultiplyPretransitive G C 2 ↔ ∀ x : C, x ≠ 0 → suborbit G x = {0}ᶜ := by
  rw [is_two_pretransitive_iff]
  constructor
  · intro h x hx
    refine Set.Subset.antisymm (fun y hy hy0 => zero_notMem_suborbit hx (hy0 ▸ hy)) fun y hy => ?_
    obtain ⟨g, hg0, hgx⟩ := h hx.symm (Ne.symm hy)
    exact ⟨g, g.2, hg0, hgx⟩
  · intro h a b c d hab hcd
    have hdc : d - c ∈ suborbit G (b - a) := by
      rw [h _ (sub_ne_zero.2 hab.symm)]
      exact sub_ne_zero.2 hcd.symm
    obtain ⟨k, hk, hk0, hkd⟩ := hdc
    refine ⟨⟨Equiv.addRight c * k * Equiv.addRight (-a), mul_mem (mul_mem (hG c) hk) (hG _)⟩,
      ?_, ?_⟩
    · change k (a + -a) + c = c
      simp [hk0]
    · change k (b + -a) + c = d
      simp [← sub_eq_add_neg, hkd]

section SchurRing

variable [Fintype C]

variable (R : Type*) [CommRing R] in
def schurRing : Subring (AddMonoidAlgebra R C) where
  carrier := {a | ∀ g ∈ G, g 0 = 0 → ∀ x, a.coeff (g x) = a.coeff x}
  mul_mem' {a b} ha hb g hg hg0 x := by
    rw [coeff_mul_eq_sum, coeff_mul_eq_sum, ← Equiv.sum_comp g]
    refine Fintype.sum_congr _ _ fun y => ?_
    obtain ⟨k, hk, hk0, hky⟩ := exists_mem_stabilizer hG hg y
    rw [ha g hg hg0, ← hb k hk hk0 (x - y), hky, sub_add_cancel]
  one_mem' g _ hg0 x := by
    classical
    have h : 0 = g x ↔ 0 = x := ⟨fun h => g.injective (hg0.trans h), by rintro rfl; exact hg0.symm⟩
    simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, h]
  add_mem' ha hb g hg hg0 x := by simp [ha g hg hg0, hb g hg hg0]
  zero_mem' := by simp
  neg_mem' ha g hg hg0 x := by simp [ha g hg hg0]

variable {R : Type*} [CommRing R]

private theorem mem_schurRing {a : AddMonoidAlgebra R C} :
    a ∈ schurRing hG R ↔ ∀ g ∈ G, g 0 = 0 → ∀ x, a.coeff (g x) = a.coeff x :=
  Iff.rfl

theorem ofSet_mem_schurRing {S : Set C} (hS : IsStable G S) : ofSet R S ∈ schurRing hG R :=
  (mem_schurRing hG).2 fun g hg hg0 x => by classical simp [Set.indicator_apply, hS g hg hg0 x]

theorem isStable_setOf_coeff {a : AddMonoidAlgebra R C} (ha : a ∈ schurRing hG R)
    (P : R → Prop) : IsStable G {x | P (a.coeff x)} := by
  intro g hg hg0 x
  simp [(mem_schurRing hG).1 ha g hg hg0 x]

theorem coeff_eq_of_mem_suborbit {a : AddMonoidAlgebra R C} (ha : a ∈ schurRing hG R)
    {x y : C} (hy : y ∈ suborbit G x) : a.coeff y = a.coeff x := by
  obtain ⟨g, hg, hg0, rfl⟩ := hy
  exact (mem_schurRing hG).1 ha g hg hg0 x

end SchurRing

variable [Finite C]

private theorem IsStable.add {A B : Set C} (hA : IsStable G A) (hB : IsStable G B) :
    IsStable G (A + B) := by
  have := Fintype.ofFinite C
  have key : A + B = {c | (ofSet ℤ A * ofSet ℤ B).coeff c ≠ 0} := by
    ext c
    rw [Set.mem_ofPred_eq, coeff_ofSet_mul_ofSet, Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero,
      Set.ncard_pos, Set.mem_add]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hb⟩
    · rintro ⟨a, ha, hca⟩
      refine ⟨a, ha, c - a, ?_, add_sub_cancel a c⟩
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, neg_add_eq_sub] using hca
  rw [key]
  exact isStable_setOf_coeff hG (R := ℤ)
    (mul_mem (ofSet_mem_schurRing hG hA) (ofSet_mem_schurRing hG hB)) (· ≠ 0)

theorem IsStable.closure {S : Set C} (hS : IsStable G S) :
    IsStable G (AddSubgroup.closure S : Set C) := by
  have key (x : C) (hx : x ∈ AddSubgroup.closure S) :
      ∃ P, IsStable G P ∧ P ⊆ AddSubgroup.closure S ∧ x ∈ P := by
    induction hx using AddSubgroup.closure_induction with
    | mem x hx => exact ⟨S, hS, AddSubgroup.subset_closure, hx⟩
    | zero => exact ⟨{0}, isStable_zero, by simp, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨P, hP, hPS, hxP⟩ := hx
      obtain ⟨Q, hQ, hQS, hyQ⟩ := hy
      refine ⟨P + Q, hP.add hG hQ, ?_, Set.add_mem_add hxP hyQ⟩
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact add_mem (hPS ha) (hQS hb)
    | neg x _ hx =>
      obtain ⟨P, hP, hPS, hxP⟩ := hx
      exact ⟨-P, hP.neg hG, fun y hy => by simpa using neg_mem (hPS hy), by simpa using hxP⟩
  refine isStable_of_forall_mem fun g hg hg0 x hx => ?_
  obtain ⟨P, hP, hPS, hxP⟩ := key x hx
  exact hPS ((hP g hg hg0 x).2 hxP)

theorem IsStable.stabilizer {S : Set C} (hS : IsStable G S) :
    IsStable G (AddAction.stabilizer C S : Set C) := by
  have := Fintype.ofFinite C
  have key : (AddAction.stabilizer C S : Set C) =
      {c | (ofSet ℤ S * ofSet ℤ (-S)).coeff c = S.ncard} := by
    ext c
    rw [SetLike.mem_coe, AddAction.mem_stabilizer_iff, Set.mem_ofPred_eq, coeff_ofSet_mul_ofSet,
      neg_neg, Nat.cast_inj]
    refine ⟨fun h => by rw [h, Set.inter_self], fun h => ?_⟩
    have h' : S ∩ (c +ᵥ S) = S := Set.eq_of_subset_of_ncard_le Set.inter_subset_left h.ge
    exact (Set.eq_of_subset_of_ncard_le (Set.inter_eq_left.1 h') (Set.ncard_vadd_set c S).le).symm
  rw [key]
  exact isStable_setOf_coeff hG (R := ℤ)
    (mul_mem (ofSet_mem_schurRing hG hS) (ofSet_mem_schurRing hG (hS.neg hG))) (· = S.ncard)

theorem IsStable.eq_bot_or_eq_top [IsPreprimitive G C] {H : AddSubgroup C}
    (hH : IsStable G (H : Set C)) : H = ⊥ ∨ H = ⊤ := by
  have hblock : IsBlock G (H : Set C) := by
    refine isBlock_iff_smul_eq_of_mem.2 fun g x hx hgx => ?_
    refine Set.eq_of_subset_of_ncard_le ?_ (Set.ncard_smul_set g _).ge
    rintro _ ⟨y, hy, rfl⟩
    change (g : Equiv.Perm C) x ∈ H at hgx
    change (g : Equiv.Perm C) y ∈ H
    simpa using H.add_mem ((hH.sub_mem_iff hG g.2 y x).2 (H.sub_mem hy hx)) hgx
  rcases hblock.subsingleton_or_eq_univ with h | h
  · exact Or.inl ((AddSubgroup.eq_bot_iff_forall H).2 fun x hx => h hx H.zero_mem)
  · exact Or.inr (AddSubgroup.coe_eq_univ.1 h)
end Translations

end BurnsideSchur

end CFSG
