module

public import CFSG.Quasithin.Background.F420Basic
public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin.F420

open CFSG.Open (quasithinIsSylowTwo)
open Equiv

@[expose] def HeartFixed {m : ℕ} (σ : Perm (Fin m)) (x : Fin m → ZMod 2) : Prop :=
  ∀ i j : Fin m, x (σ⁻¹ i) - x i = x (σ⁻¹ j) - x j

instance {m : ℕ} (σ : Perm (Fin m)) (x : Fin m → ZMod 2) : Decidable (HeartFixed σ x) := by
  unfold HeartFixed
  infer_instance

theorem mem_constWeight_iff {m : ℕ} (σ : Perm (Fin m)) (x : ↥(CFSG.QuasithinUnique.evenWeight m)) :
    permWeight m σ x - x ∈ constWeight m ↔ HeartFixed σ (x : Fin m → ZMod 2) :=
  Iff.rfl

theorem heartFixed_conj_iff {m : ℕ} (h σ : Perm (Fin m)) (x : Fin m → ZMod 2) :
    HeartFixed (h * σ * h⁻¹) x ↔ HeartFixed σ (fun i => x (h i)) := by
  have key : ∀ i : Fin m, (h * σ * h⁻¹)⁻¹ (h i) = h (σ⁻¹ i) := by
    intro i
    simp [mul_inv_rev, Perm.mul_apply]
  constructor
  · intro H i j
    have := H (h i) (h j)
    rwa [key, key] at this
  · intro H i j
    obtain ⟨i', rfl⟩ := h.surjective i
    obtain ⟨j', rfl⟩ := h.surjective j
    rw [key, key]
    exact H i' j'

theorem heart_of_witness {m : ℕ} {T : Subgroup (alternatingGroup (Fin m))} (hT : IsPGroup 2 T)
    {g₀ : alternatingGroup (Fin m)} (hg₀ : orderOf g₀ = 3)
    (hchk : ∀ y : Fin m → ZMod 2, ∑ i, y i = 0 → (∀ t ∈ T, HeartFixed (t : Perm (Fin m)) y) →
      HeartFixed (g₀ : Perm (Fin m)) y)
    (S : Subgroup (alternatingGroup (Fin m))) (hS : quasithinIsSylowTwo S) :
    ∃ g : alternatingGroup (Fin m), orderOf g = 3 ∧
      ∀ x : ↥(CFSG.QuasithinUnique.evenWeight m),
        (∀ s ∈ S, permWeight m (s : Perm (Fin m)) x - x ∈ constWeight m) →
          permWeight m (g : Perm (Fin m)) x - x ∈ constWeight m := by
  obtain ⟨h, hh⟩ := exists_conj_mem_of_isPGroup hT hS
  refine ⟨h * g₀ * h⁻¹, ?_, fun x hx => ?_⟩
  · rw [show h * g₀ * h⁻¹ = MulAut.conj h g₀ from rfl, MulEquiv.orderOf_eq, hg₀]
  · rw [mem_constWeight_iff]
    have hcoe : ((h * g₀ * h⁻¹ : alternatingGroup (Fin m)) : Perm (Fin m)) =
        (h : Perm (Fin m)) * (g₀ : Perm (Fin m)) * (h : Perm (Fin m))⁻¹ := rfl
    rw [hcoe, heartFixed_conj_iff]
    have hsum : ∑ i, (x : Fin m → ZMod 2) ((h : Perm (Fin m)) i) = 0 := by
      have hx0 : ∑ i, (x : Fin m → ZMod 2) i = 0 := by
        have := x.2
        simpa [CFSG.QuasithinUnique.evenWeight] using this
      rw [Equiv.sum_comp (h : Perm (Fin m)) (fun i => (x : Fin m → ZMod 2) i), hx0]
    refine hchk _ hsum fun t ht => ?_
    have h1 := (mem_constWeight_iff _ x).mp (hx _ (hh t ht))
    have hcoe' : ((h * t * h⁻¹ : alternatingGroup (Fin m)) : Perm (Fin m)) =
        (h : Perm (Fin m)) * (t : Perm (Fin m)) * (h : Perm (Fin m))⁻¹ := rfl
    rw [hcoe', heartFixed_conj_iff] at h1
    exact h1

theorem mem_alternatingGroup_of_sign {m : ℕ} {σ : Perm (Fin m)} (h : Perm.sign σ = 1) :
    σ ∈ alternatingGroup (Fin m) :=
  Perm.mem_alternatingGroup.mpr h

theorem heart_of_cyclic {m : ℕ} (t g₀ : Perm (Fin m)) (ht : t ∈ alternatingGroup (Fin m))
    (hg : g₀ ∈ alternatingGroup (Fin m)) (ht4 : t ^ 4 = 1) (hg3 : g₀ ^ 3 = 1) (hg1 : g₀ ≠ 1)
    (hchk : ∀ y : Fin m → ZMod 2, ∑ i, y i = 0 → HeartFixed t y → HeartFixed g₀ y)
    (S : Subgroup (alternatingGroup (Fin m))) (hS : quasithinIsSylowTwo S) :
    ∃ g : alternatingGroup (Fin m), orderOf g = 3 ∧
      ∀ x : ↥(CFSG.QuasithinUnique.evenWeight m),
        (∀ s ∈ S, permWeight m (s : Perm (Fin m)) x - x ∈ constWeight m) →
          permWeight m (g : Perm (Fin m)) x - x ∈ constWeight m := by
  let t' : alternatingGroup (Fin m) := ⟨t, ht⟩
  let g' : alternatingGroup (Fin m) := ⟨g₀, hg⟩
  have hT : IsPGroup 2 (Subgroup.zpowers t') := by
    have h4 : t' ^ 4 = 1 := Subtype.ext (by simpa using ht4)
    rintro ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨2, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      show ((2 ^ 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, h4, one_zpow]
  have hgo : orderOf g' = 3 := by
    refine orderOf_eq_prime (Subtype.ext (by simpa using hg3)) ?_
    intro h1
    exact hg1 (congrArg Subtype.val h1)
  exact heart_of_witness hT hgo (fun y h0 hy => hchk y h0 (hy t' (Subgroup.mem_zpowers t'))) S hS

theorem heart_five (S : Subgroup (alternatingGroup (Fin 5))) (hS : quasithinIsSylowTwo S) :
    ∃ g : alternatingGroup (Fin 5), orderOf g = 3 ∧
      ∀ x : ↥(CFSG.QuasithinUnique.evenWeight 5),
        (∀ s ∈ S, permWeight 5 (s : Perm (Fin 5)) x - x ∈ constWeight 5) →
          permWeight 5 (g : Perm (Fin 5)) x - x ∈ constWeight 5 := by
  let a : alternatingGroup (Fin 5) :=
    ⟨swap 1 2 * swap 3 4, mem_alternatingGroup_of_sign (by decide)⟩
  let b : alternatingGroup (Fin 5) :=
    ⟨swap 1 3 * swap 2 4, mem_alternatingGroup_of_sign (by decide)⟩
  let g₀ : alternatingGroup (Fin 5) :=
    ⟨swap 2 4 * swap 2 3, mem_alternatingGroup_of_sign (by decide)⟩
  have hT : IsPGroup 2 (Subgroup.closure {a, b}) :=
    isPGroup_closure_pair (n := 1) (k := 1) (Subtype.ext (by decide)) (Subtype.ext (by decide))
      (Subtype.ext (by decide))
  have hgo : orderOf g₀ = 3 := by
    refine orderOf_eq_prime (Subtype.ext (by decide)) ?_
    intro h1
    exact absurd (congrArg Subtype.val h1) (by decide)
  have hchk : ∀ y : Fin 5 → ZMod 2, HeartFixed (swap 1 2 * swap 3 4) y →
      HeartFixed (swap 1 3 * swap 2 4) y → HeartFixed (swap 2 4 * swap 2 3) y := by
    decide +kernel
  refine heart_of_witness hT hgo (fun y _ hy => hchk y (hy a ?_) (hy b ?_)) S hS
  · exact Subgroup.subset_closure (Set.mem_insert a _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)

theorem heart_six (S : Subgroup (alternatingGroup (Fin 6))) (hS : quasithinIsSylowTwo S) :
    ∃ g : alternatingGroup (Fin 6), orderOf g = 3 ∧
      ∀ x : ↥(CFSG.QuasithinUnique.evenWeight 6),
        (∀ s ∈ S, permWeight 6 (s : Perm (Fin 6)) x - x ∈ constWeight 6) →
          permWeight 6 (g : Perm (Fin 6)) x - x ∈ constWeight 6 :=
  heart_of_cyclic (swap 0 1 * (swap 2 5 * swap 2 4 * swap 2 3)) (swap 3 5 * swap 3 4)
    (mem_alternatingGroup_of_sign (by decide)) (mem_alternatingGroup_of_sign (by decide))
    (by decide) (by decide) (by decide) (by decide +kernel) S hS

theorem heart_seven (S : Subgroup (alternatingGroup (Fin 7))) (hS : quasithinIsSylowTwo S) :
    ∃ g : alternatingGroup (Fin 7), orderOf g = 3 ∧
      ∀ x : ↥(CFSG.QuasithinUnique.evenWeight 7),
        (∀ s ∈ S, permWeight 7 (s : Perm (Fin 7)) x - x ∈ constWeight 7) →
          permWeight 7 (g : Perm (Fin 7)) x - x ∈ constWeight 7 :=
  heart_of_cyclic (swap 1 2 * (swap 3 6 * swap 3 5 * swap 3 4)) (swap 4 6 * swap 4 5)
    (mem_alternatingGroup_of_sign (by decide)) (mem_alternatingGroup_of_sign (by decide))
    (by decide) (by decide) (by decide) (by decide +kernel) S hS

theorem heart_eight (S : Subgroup (alternatingGroup (Fin 8))) (hS : quasithinIsSylowTwo S) :
    ∃ g : alternatingGroup (Fin 8), orderOf g = 3 ∧
      ∀ x : ↥(CFSG.QuasithinUnique.evenWeight 8),
        (∀ s ∈ S, permWeight 8 (s : Perm (Fin 8)) x - x ∈ constWeight 8) →
          permWeight 8 (g : Perm (Fin 8)) x - x ∈ constWeight 8 :=
  heart_of_cyclic (swap 2 3 * (swap 4 7 * swap 4 6 * swap 4 5)) (swap 5 7 * swap 5 6)
    (mem_alternatingGroup_of_sign (by decide)) (mem_alternatingGroup_of_sign (by decide))
    (by decide) (by decide) (by decide) (by decide +kernel) S hS

theorem exists_orderOf_eq_three_heart (m : ℕ) (h5 : 5 ≤ m) (h8 : m ≤ 8)
    (S : Subgroup (alternatingGroup (Fin m))) (hS : quasithinIsSylowTwo S) :
    ∃ g : alternatingGroup (Fin m), orderOf g = 3 ∧
      ∀ x : ↥(CFSG.QuasithinUnique.evenWeight m),
        (∀ s ∈ S, permWeight m (s : Perm (Fin m)) x - x ∈ constWeight m) →
          permWeight m (g : Perm (Fin m)) x - x ∈ constWeight m := by
  interval_cases m
  · exact heart_five S hS
  · exact heart_six S hS
  · exact heart_seven S hS
  · exact heart_eight S hS

end CFSG.Quasithin.F420
