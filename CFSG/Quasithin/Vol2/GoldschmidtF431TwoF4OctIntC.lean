module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctIntB
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctSpec

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open scoped Pointwise
open CFSG.GH74.BNPair (chainProd intList)
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley

theorem nodup_intList_oct (i j : ℤ) : (intList i j).Nodup := by
  unfold intList
  refine List.Nodup.map (fun a b h => ?_) List.nodup_range
  have : (a : ℤ) = b := by simpa using h
  exact_mod_cast this


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
  {S : ℤ → ℤ → Set (Fin F4.tag.rank → ℤ)}

theorem octCarrier_of (C : OctIntFacts S) : OctCarrier K a := by
  have h := chainProd_octRoot_eq (K := K) (a := a) C (i := 1) (j := 8) le_rfl (by norm_num)
    le_rfl (nodup_intList_oct 1 8) (fun k => CFSG.GH74.BNPair.mem_intList_iff)
  unfold OctCarrier
  rw [h, C.one_eight]
  rfl

theorem octUnique_of (C : OctIntFacts S) : OctUnique K a := by
  intro f g hf hg h
  exact eq_of_prod_eq_octRoot (K := K) (a := a) C (i := 1) (j := 8) le_rfl (by norm_num) le_rfl
    (nodup_intList_oct 1 8) (fun k => CFSG.GH74.BNPair.mem_intList_iff) hf hg h

theorem octRev_of (C : OctIntFacts S) : OctRev K a := by
  intro i j hi hij hj
  rw [chainProd_octRoot_eq (K := K) (a := a) C hi hij hj (nodup_intList_oct i j)
      (fun k => CFSG.GH74.BNPair.mem_intList_iff),
    chainProd_octRoot_eq (K := K) (a := a) C hi hij hj
      (List.nodup_reverse.2 (nodup_intList_oct i j))
      (fun k => by rw [List.mem_reverse]; exact CFSG.GH74.BNPair.mem_intList_iff)]

theorem conj_mem_inf_of_ideal {J S' B : Set (Fin F4.tag.rank → ℤ)} (hJS : J ⊆ S')
    (hBS : B ⊆ S') (hS' : ∀ α ∈ S', IsRoot F4.tag α ∧ 0 < height α)
    (hideal : ∀ α ∈ S', ∀ β ∈ J, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot F4.tag (a • α + b • β) →
      a • α + b • β ∈ J)
    {x v : ModGL F4.tag K} (hx : x ∈ largeReeBlockGroup K a B)
    (hv : v ∈ rootSpan F4.tag K J ⊓ F4.reeGamma K a) :
    x * v * x⁻¹ ∈ rootSpan F4.tag K J ⊓ F4.reeGamma K a := by
  obtain ⟨hle, hnorm⟩ := positive_root_ideal_normality (τ := F4.tag) (R := K) hJS hS' hideal
  obtain ⟨hxR, hxΓ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hvR, hvΓ⟩ := Subgroup.mem_inf.1 hv
  have hx' : x ∈ rootSpan F4.tag K S' := rootSpan_mono hBS hxR
  have hmem := hnorm.conj_mem (⟨v, hle hvR⟩ : ↥(rootSpan F4.tag K S'))
    (Subgroup.mem_subgroupOf.2 hvR) ⟨x, hx'⟩
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hmem,
    mul_mem (mul_mem hxΓ hvΓ) (inv_mem hxΓ)⟩

theorem octSub_of (C : OctIntFacts S) : OctSub K a := by
  intro i j hi hij hj
  have hSpos : ∀ i' j' : ℤ, 1 ≤ i' → j' ≤ 8 → ∀ α ∈ S i' j', IsRoot F4.tag α ∧ 0 < height α := by
    intro i' j' hi' hj' α hα
    obtain ⟨k, hk1, hk2, hk⟩ := (C.mem_S i' j' α).1 hα
    exact C.isRoot k (by omega) (by omega) α hk
  have hblock : ∀ k i' j' : ℤ, i' ≤ k → k ≤ j' → octPos k ⊆ S i' j' := fun k i' j' h1 h2 α hα =>
    (C.mem_S i' j' α).2 ⟨k, h1, h2, hα⟩
  have hmono : ∀ i' j' i'' j'' : ℤ, i' ≤ i'' → j'' ≤ j' → S i'' j'' ⊆ S i' j' := by
    intro i' j' i'' j'' h1 h2 α hα
    obtain ⟨k, hk1, hk2, hk⟩ := (C.mem_S i'' j'' α).1 hα
    exact (C.mem_S i' j' α).2 ⟨k, by omega, by omega, hk⟩
  refine ⟨(rootSpan F4.tag K (S i j) ⊓ F4.reeGamma K a).subgroupOf (F4.reeGamma K a), ?_, ?_,
    ?_, ?_⟩
  · exact (chainProd_octRoot_eq (K := K) (a := a) C hi hij hj (nodup_intList_oct i j)
      (fun k => CFSG.GH74.BNPair.mem_intList_iff)).symm
  · intro x hx
    obtain ⟨hR, hΓ⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2
      ⟨rootSpan_le_posUnipotent (hSpos i j hi hj) hR, hΓ⟩)
  · intro hi1 x hx v hv
    have hx' := (mem_octRoot_pos (by omega)).1 hx
    exact Subgroup.mem_subgroupOf.2 (conj_mem_inf_of_ideal (hmono (i - 1) j i j (by omega) le_rfl)
      (hblock (i - 1) (i - 1) j le_rfl (by omega)) (hSpos (i - 1) j (by omega) hj)
      (fun α hα β hβ a b ha hb hr => C.ideal_left i j (by omega) hij hj α hα β hβ a b ha hb hr)
      hx' (Subgroup.mem_subgroupOf.1 hv))
  · intro hj1 x hx v hv
    have hx' := (mem_octRoot_pos (by omega)).1 hx
    exact Subgroup.mem_subgroupOf.2 (conj_mem_inf_of_ideal (hmono i (j + 1) i j le_rfl (by omega))
      (hblock (j + 1) i (j + 1) (by omega) le_rfl) (hSpos i (j + 1) hi (by omega))
      (fun α hα β hβ a b ha hb hr => C.ideal_right i j hi hij (by omega) α hα β hβ a b ha hb hr)
      hx' (Subgroup.mem_subgroupOf.1 hv))

end CFSG.Quasithin.H13.F431.TwoF4
