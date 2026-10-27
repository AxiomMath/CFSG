module

public import CFSG.Permutation.FiveTransitive.ThreeSwapExplicitElements
public import CFSG.Permutation.FiveTransitive.ThreeSwapNormalizerConjugators

public section

namespace CFSG

namespace FiveTransitive.ThreeSwapNormalizerFixedPair

open Equiv

private theorem swap_cases {F : Type*} [Fintype F] [DecidableEq F]
    (e : Fin 6 ↪ F) (v : ThreeSwapTwoGroup.subgroup e) (hv : v.val.IsSwap) :
    v.val = swap (e 0) (e 1) ∨ v.val = swap (e 2) (e 3) ∨ v.val = swap (e 4) (e 5) := by
  let t0 := swap (e 0) (e 1)
  let t1 := swap (e 2) (e 3)
  let t2 := swap (e 4) (e 5)
  have hd (i j k l : Fin 6) (h : [i,j,k,l].Nodup) :
      (swap (e i) (e j)).Disjoint (swap (e k) (e l)) :=
    Perm.disjoint_swap_swap (by simpa only [List.map_cons,List.map_nil] using h.map e.injective)
  have hd01 : t0.Disjoint t1 := hd 0 1 2 3 (by decide)
  have hd02 : t0.Disjoint t2 := hd 0 1 4 5 (by decide)
  have hd12 : t1.Disjoint t2 := hd 2 3 4 5 (by decide)
  have ht (i j : Fin 6) (hij : i ≠ j) : (swap (e i) (e j)).cycleType = {2} :=
    Perm.isSwap_iff_cycleType.mp ⟨e i,e j,e.injective.ne hij,rfl⟩
  have ht0 : t0.cycleType = {2} := ht 0 1 (by decide)
  have ht1 : t1.cycleType = {2} := ht 2 3 (by decide)
  have ht2 : t2.cycleType = {2} := ht 4 5 (by decide)
  have hvt := Perm.isSwap_iff_cycleType.mp hv
  obtain ⟨b,c,d,he⟩ := ThreeSwapExplicitElements.exists_bits e v
  change v.val = (if b then t0 else 1) * (if c then t1 else 1) * (if d then t2 else 1) at he
  change v.val = t0 ∨ v.val = t1 ∨ v.val = t2
  cases b <;> cases c <;> cases d
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one] at he
  all_goals first | exact Or.inl he | exact Or.inr (Or.inl he) | exact Or.inr (Or.inr he) | skip
  all_goals rw [he] at hvt
  · simp at hvt
  · rw [hd12.cycleType_mul, ht1, ht2] at hvt
    contradiction
  · rw [hd02.cycleType_mul, ht0, ht2] at hvt
    contradiction
  · rw [hd01.cycleType_mul, ht0, ht1] at hvt
    contradiction
  · rw [(hd02.mul_left hd12).cycleType_mul, hd01.cycleType_mul, ht0, ht1, ht2] at hvt
    contradiction

theorem fixed_pair {F : Type*} [Fintype F] [DecidableEq F]
    (e : Fin 6 ↪ F) (s : Perm F)
    (hs : s ∈ Subgroup.normalizer (ThreeSwapTwoGroup.subgroup e : Set (Perm F)))
    (hs2 : s ^ 2 = 1) :
    (Commute s (swap (e 0) (e 1)) ∧ Commute s (swap (e 2) (e 3) * swap (e 4) (e 5))) ∨
    (Commute s (swap (e 2) (e 3)) ∧ Commute s (swap (e 0) (e 1) * swap (e 4) (e 5))) ∨
    (Commute s (swap (e 4) (e 5)) ∧ Commute s (swap (e 0) (e 1) * swap (e 2) (e 3))) := by
  let t0 := swap (e 0) (e 1)
  let t1 := swap (e 2) (e 3)
  let t2 := swap (e 4) (e 5)
  let α := MulAut.conj s
  have hd (i j k l : Fin 6) (h : [i,j,k,l].Nodup) :
      (swap (e i) (e j)).Disjoint (swap (e k) (e l)) :=
    Perm.disjoint_swap_swap (by simpa only [List.map_cons,List.map_nil] using h.map e.injective)
  have hc01 : Commute t0 t1 := (hd 0 1 2 3 (by decide)).commute
  have hc02 : Commute t0 t2 := (hd 0 1 4 5 (by decide)).commute
  have hc12 : Commute t1 t2 := (hd 2 3 4 5 (by decide)).commute
  have h01 : t0 ≠ t1 := by intro h; have := congrArg (fun p : Perm F => p (e 0)) h; simp [t0,t1,swap_apply_def,e.injective.eq_iff] at this
  have h02 : t0 ≠ t2 := by intro h; have := congrArg (fun p : Perm F => p (e 0)) h; simp [t0,t2,swap_apply_def,e.injective.eq_iff] at this
  have h12 : t1 ≠ t2 := by intro h; have := congrArg (fun p : Perm F => p (e 2)) h; simp [t1,t2,swap_apply_def,e.injective.eq_iff] at this
  have hchoices (t : Perm F) (htV : t ∈ ThreeSwapTwoGroup.subgroup e) (ht : t.IsSwap) :
      α t = t0 ∨ α t = t1 ∨ α t = t2 := by
    have hm : α t ∈ ThreeSwapTwoGroup.subgroup e :=
      (Subgroup.mem_normalizer_iff.mp hs t).mp htV
    have hswap : (α t).IsSwap := by
      obtain ⟨a,b,hab,rfl⟩ := ht
      change (s * swap a b * s⁻¹).IsSwap
      rw [ThreeSwapNormalizerConjugators.conjugate_swap]
      exact ⟨s a,s b,s.injective.ne hab,rfl⟩
    exact swap_cases e ⟨α t,hm⟩ hswap
  have hm0 : t0 ∈ ThreeSwapTwoGroup.subgroup e := Subgroup.subset_closure (by simp [t0])
  have hm1 : t1 ∈ ThreeSwapTwoGroup.subgroup e := Subgroup.subset_closure (by simp [t1])
  have hm2 : t2 ∈ ThreeSwapTwoGroup.subgroup e := Subgroup.subset_closure (by simp [t2])
  have h0 := hchoices t0 hm0 ⟨e 0,e 1,e.injective.ne (by decide),rfl⟩
  have h1 := hchoices t1 hm1 ⟨e 2,e 3,e.injective.ne (by decide),rfl⟩
  have h2 := hchoices t2 hm2 ⟨e 4,e 5,e.injective.ne (by decide),rfl⟩
  have hα (t : Perm F) : α (α t) = t := by
    change MulAut.conj s (MulAut.conj s t) = t
    have he : (MulAut.conj s) ^ 2 = 1 := by rw [← map_pow,hs2,map_one]
    exact congrArg (fun a : MulAut (Perm F) => a t) he
  have hi01 := α.injective.ne h01
  have hi02 := α.injective.ne h02
  have hi12 := α.injective.ne h12
  have ha0 := hα t0
  have ha1 := hα t1
  have ha2 := hα t2
  have hc (t : Perm F) : α t = t ↔ Commute s t := by
    change s * t * s⁻¹ = t ↔ s * t = t * s
    exact mul_inv_eq_iff_eq_mul
  change (Commute s t0 ∧ Commute s (t1*t2)) ∨
    (Commute s t1 ∧ Commute s (t0*t2)) ∨ (Commute s t2 ∧ Commute s (t0*t1))
  simp only [← hc, map_mul]
  clear hc
  rcases h0 with h0|h0|h0 <;> rcases h1 with h1|h1|h1 <;> rcases h2 with h2|h2|h2
  all_goals simp_all [hc01.eq, hc02.eq, hc12.eq]

end FiveTransitive.ThreeSwapNormalizerFixedPair

end CFSG
