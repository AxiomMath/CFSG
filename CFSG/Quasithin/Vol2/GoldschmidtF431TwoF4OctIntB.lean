module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctIntA

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open scoped Pointwise
open CFSG.GH74.BNPair (chainProd intList)
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
  {S : ℤ → ℤ → Set (Fin F4.tag.rank → ℤ)}

theorem chainProd_octRoot_eq (C : OctIntFacts S) {i j : ℤ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 8)
    {l : List ℤ} (hl : l.Nodup) (hlm : ∀ k, k ∈ l ↔ i ≤ k ∧ k ≤ j) :
    chainProd (octRoot K a) l = (((rootSpan F4.tag K (S i j) ⊓ F4.reeGamma K a).subgroupOf
      (F4.reeGamma K a) : Subgroup (Gm K a)) : Set (Gm K a)) := by
  have hBij := octColl_list (K := K) (a := a) C hi hij hj hl hlm
  have hpos : ∀ m : Fin l.length, 0 < l.get m := fun m => by
    have := ((hlm _).1 (List.get_mem l m)).1
    omega
  ext x
  constructor
  · intro hx
    obtain ⟨f, hf, rfl⟩ := exists_fun_of_mem_chainProd_oct (octRoot K a) l hl x hx
    have hy : ∀ m : Fin l.length, ((f (l.get m) : Gm K a) : ModGL F4.tag K) ∈
        largeReeBlockGroup K a (octPos (l.get m)) := fun m =>
      (mem_octRoot_pos (hpos m)).1 (hf _ (List.get_mem l m))
    have h1 := hBij.1 (fun m _ => hy m)
    refine Subgroup.mem_subgroupOf.2 ?_
    rw [Subgroup.val_list_prod, List.map_map, list_map_eq_ofFn]
    exact h1
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hBij.2.2 (Subgroup.mem_subgroupOf.1 hx)
    have hyΓ : ∀ m, y m ∈ F4.reeGamma K a := fun m =>
      (Subgroup.mem_inf.1 (hy m (Set.mem_univ m))).2
    have hinj : Function.Injective l.get := List.nodup_iff_injective_get.1 hl
    let g : Fin l.length → Gm K a := fun m => ⟨y m, hyΓ m⟩
    let f : ℤ → Gm K a := Function.extend l.get g (fun _ => 1)
    have hf : ∀ m, f (l.get m) = g m := fun m => hinj.extend_apply g _ m
    have hfk : ∀ k ∈ l, f k ∈ octRoot K a k := by
      intro k hk
      obtain ⟨m, rfl⟩ := List.mem_iff_get.1 hk
      rw [hf m, mem_octRoot_pos (hpos m)]
      exact hy m (Set.mem_univ m)
    have hxe : x = (l.map f).prod := by
      apply Subtype.ext
      rw [Subgroup.val_list_prod, List.map_map, list_map_eq_ofFn]
      simp only [Function.comp, hf, g]
      exact hyx.symm
    rw [hxe]
    exact prod_mem_chainProd _ f l hfk

theorem eq_of_prod_eq_octRoot (C : OctIntFacts S) {i j : ℤ} (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ 8) {l : List ℤ} (hl : l.Nodup) (hlm : ∀ k, k ∈ l ↔ i ≤ k ∧ k ≤ j)
    {f g : ℤ → Gm K a} (hf : ∀ k ∈ l, f k ∈ octRoot K a k) (hg : ∀ k ∈ l, g k ∈ octRoot K a k)
    (h : (l.map f).prod = (l.map g).prod) : ∀ k ∈ l, f k = g k := by
  have hBij := octColl_list (K := K) (a := a) C hi hij hj hl hlm
  have hpos : ∀ m : Fin l.length, 0 < l.get m := fun m => by
    have := ((hlm _).1 (List.get_mem l m)).1
    omega
  have key : (fun m : Fin l.length => ((f (l.get m) : Gm K a) : ModGL F4.tag K)) =
      fun m => ((g (l.get m) : Gm K a) : ModGL F4.tag K) := by
    refine hBij.2.1 (fun m _ => (mem_octRoot_pos (hpos m)).1 (hf _ (List.get_mem l m)))
      (fun m _ => (mem_octRoot_pos (hpos m)).1 (hg _ (List.get_mem l m))) ?_
    have := congrArg (fun z : Gm K a => (z : ModGL F4.tag K)) h
    simp only [Subgroup.val_list_prod, List.map_map] at this
    rw [list_map_eq_ofFn _ (Subtype.val ∘ f), list_map_eq_ofFn _ (Subtype.val ∘ g)] at this
    exact this
  intro k hk
  obtain ⟨m, rfl⟩ := List.mem_iff_get.1 hk
  exact Subtype.ext (congrFun key m)

end CFSG.Quasithin.H13.F431.TwoF4
