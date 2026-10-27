module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAD12

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType
open CFSG.StandardType.TypeAReflOver

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SmAAux_range_d9 :
    hdRo7SmAAux_d9Hom.range = smGroup 7 [sm7A7b, sm7A7a, sm7cx] := by
  have hrange : hdRo7SmAAux_d9Hom.range =
      Subgroup.closure (Set.range (fun i : Fin 8 =>
        hdRo7SmAAux_d9Hom (Equiv.swap i.castSucc i.succ))) := by
    rw [← Subgroup.map_top hdRo7SmAAux_d9Hom, ← hdRo7SmAAux_adj8_gen,
      MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [hrange, smGroup]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    dsimp only
    by_cases hk : i.val < 6
    · rw [hdRo7SmAAux_d9Hom_swap_inner' i hk]
      exact Subgroup.subset_closure (Or.inl (hdRo7SmAAux_isPerm_permLin _))
    · by_cases h6 : i.val = 6
      · have hi : i = (6 : Fin 8) := Fin.ext h6
        rw [hi]
        exact Subgroup.subset_closure (Or.inr
          ⟨sm7A7b, by simp, hdRo7SmAAux_d9Hom_swap_67_smRefl⟩)
      · have hi : i = (7 : Fin 8) := Fin.ext (by omega)
        rw [hi]
        exact Subgroup.subset_closure (Or.inr
          ⟨sm7cx, by simp, hdRo7SmAAux_d9Hom_swap_78_smRefl⟩)
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · have hset : x ∈ (hdRo7SmAAux_permLin 7).range := by
        obtain ⟨σ, hσ⟩ := hx
        exact ⟨σ, by ext v i; rw [hdRo7SmAAux_permLin_apply, hσ]⟩
      obtain ⟨σ, rfl⟩ := hset
      have hσ : σ ∈ Subgroup.closure (Set.range (fun i : Fin 6 =>
          Equiv.swap i.castSucc i.succ)) := by
        rw [hdRo7SmAAux_adj6_gen]; exact Subgroup.mem_top σ
      refine Subgroup.closure_induction
        (p := fun x _ => hdRo7SmAAux_permLin 7 x ∈ Subgroup.closure
          (Set.range fun i : Fin 8 => hdRo7SmAAux_d9Hom (Equiv.swap i.castSucc i.succ)))
        ?_ ?_ ?_ ?_ hσ
      · intro τ hτ
        obtain ⟨m, hm⟩ := hτ
        dsimp only at hm
        have hlt : m.val < 8 := Nat.lt_of_lt_of_le m.isLt (by norm_num)
        have hsw : (hdRo7SmAAux_permLin 7) (Equiv.swap m.castSucc m.succ) =
            hdRo7SmAAux_d9Hom (Equiv.swap (⟨m.val, hlt⟩ : Fin 8).castSucc
              (⟨m.val, hlt⟩ : Fin 8).succ) := by
          rw [hdRo7SmAAux_d9Hom_swap_inner' (⟨m.val, hlt⟩ : Fin 8) m.isLt]
          rfl
        rw [← hm, hsw]
        exact Subgroup.subset_closure (Set.mem_range.mpr ⟨⟨m.val, hlt⟩, rfl⟩)
      · exact Subgroup.one_mem _
      · intro a b ha hb iha ihb
        simpa only [map_mul] using Subgroup.mul_mem _ iha ihb
      · intro a ha iha
        simpa only [map_inv] using Subgroup.inv_mem _ iha
    · obtain ⟨q, hq, hxr⟩ := hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · have hx' : x = hdRo7SmAAux_d9Hom
            (Equiv.swap (6 : Fin 8).castSucc (6 : Fin 8).succ) := by
          apply LinearEquiv.ext; intro v
          rw [hxr.2 v]
          exact (hdRo7SmAAux_d9Hom_swap_67_apply v).symm
        rw [hx']
        exact Subgroup.subset_closure ⟨(6 : Fin 8), rfl⟩
      · have hx' : x = hdRo7SmAAux_d9Hom (Equiv.swap (0 : Fin 9) (Fin.last 8)) := by
          apply LinearEquiv.ext; intro v
          rw [hxr.2 v, hdRo7SmAAux_d9Hom_swap_08_apply v]
        rw [hx', ← hrange]
        exact MonoidHom.mem_range.mpr ⟨Equiv.swap (0 : Fin 9) (Fin.last 8), rfl⟩
      · have hx' : x = hdRo7SmAAux_d9Hom
            (Equiv.swap (7 : Fin 8).castSucc (7 : Fin 8).succ) := by
          apply LinearEquiv.ext; intro v
          rw [hxr.2 v]
          exact (hdRo7SmAAux_d9Hom_swap_78_apply v).symm
        rw [hx']
        exact Subgroup.subset_closure ⟨(7 : Fin 8), rfl⟩

theorem hdRo7SmAAux_case5 : ZS.LinWeyl 3 (smGroup 7 [sm7A7b, sm7A7a, sm7cx]) := by
  rw [← hdRo7SmAAux_range_d9]
  refine hdRo7SmAAux_linWeyl_of_perm _ 8 (by norm_num) ?_ ?_
  · refine MulEquiv.ofBijective
      (hdRo7SmAAux_d9Hom.codRestrict hdRo7SmAAux_d9Hom.range
        (fun σ => MonoidHom.mem_range.mpr ⟨σ, rfl⟩)) ?_
    constructor
    · intro a b h
      exact hdRo7SmAAux_d9Hom_injective (Subtype.ext_iff.mp h)
    · rintro ⟨g, hg⟩
      obtain ⟨σ, hσ⟩ := hg
      exact ⟨σ, Subtype.ext hσ⟩
  · intro k
    change GGLinRefl ((hdRo7SmAAux_d9Hom) (Equiv.swap k.castSucc k.succ))
    exact hdRo7SmAAux_d9Hom_swap_isRefl k

end CFSG.StandardType.HdRo7SU.Small
