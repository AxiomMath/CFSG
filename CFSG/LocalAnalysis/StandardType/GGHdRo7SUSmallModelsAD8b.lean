module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAD8

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType
open CFSG.StandardType.TypeAReflOver

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SmAAux_d8Hom_swap_last_apply (v : SMV 7) :
    hdRo7SmAAux_d8Hom (Equiv.swap (Fin.last 6).castSucc (Fin.last 6).succ) v =
      v - smDual sm7A7b.2 v • sm7A7b.1 := by
  ext i
  fin_cases i <;>
    simp [hdRo7SmAAux_d8Hom, hdRo7SmAAux_d8, hdRo7SmAAux_delProj, hdRo7SmAAux_delEmbed,
      hdRo7SmAAux_permLin_apply, LinearMap.pi_apply, Equiv.swap_apply_def, sm7A7b, smDual,
      Fin.sum_univ_seven, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
  ring_nf
  rw [show (4 : ZMod 3) = 1 by decide]
  ring

theorem hdRo7SmAAux_d8Hom_swap_last_smRefl :
    SMRefl (hdRo7SmAAux_d8Hom (Equiv.swap (Fin.last 6).castSucc (Fin.last 6).succ))
      sm7A7b.1 (smDual sm7A7b.2) :=
  ⟨by
    rw [hdRo7SmAAux_smDual_apply, smDot]
    simp [sm7A7b, Fin.sum_univ_seven],
   fun v => hdRo7SmAAux_d8Hom_swap_last_apply v⟩

theorem hdRo7SmAAux_d8Hom_swap_isRefl (k : Fin 7) :
    GGLinRefl (hdRo7SmAAux_d8Hom (Equiv.swap k.castSucc k.succ)) := by
  obtain ⟨m, hm⟩ | hlast := Fin.eq_castSucc_or_eq_last k
  · rw [hm, hdRo7SmAAux_d8Hom_swap_inner m]
    exact hdRo7SmAAux_permLin_swap_isRefl 6 m
  · rw [hlast]
    exact hdRo7SmAAux_isRefl_of_smRefl hdRo7SmAAux_d8Hom_swap_last_smRefl

theorem hdRo7SmAAux_adj6_gen :
    Subgroup.closure (Set.range (fun i : Fin 6 => Equiv.swap i.castSucc i.succ)) = ⊤ := by
  have hS : Set.range (fun i : Fin 6 => Equiv.swap i.castSucc i.succ)
      = CFSG.Permutation.SymmetricCoxeter.adjSwap 6 '' Set.Iio 6 := by
    ext σ; constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, by
        rw [CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt i.isLt]; rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, by
        rw [CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt hi]; rfl⟩
  rw [hS, CFSG.Permutation.SymmetricCoxeter.closure_adjSwap 6]

theorem hdRo7SmAAux_range_d8 : hdRo7SmAAux_d8Hom.range = smGroup 7 [sm7A7b] := by
  have hrange : hdRo7SmAAux_d8Hom.range =
      Subgroup.closure (Set.range (fun i : Fin 7 =>
        hdRo7SmAAux_d8Hom (Equiv.swap i.castSucc i.succ))) := by
    rw [← Subgroup.map_top hdRo7SmAAux_d8Hom, ← hdRo7SmAAux_adj7_gen,
      MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [hrange, smGroup]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    obtain ⟨m, hm⟩ | hlast := Fin.eq_castSucc_or_eq_last i
    · rw [hm]
      dsimp only
      rw [hdRo7SmAAux_d8Hom_swap_inner m]
      exact Subgroup.subset_closure (Or.inl (hdRo7SmAAux_isPerm_permLin _))
    · rw [hlast]
      dsimp only
      exact Subgroup.subset_closure (Or.inr
        ⟨sm7A7b, by simp, hdRo7SmAAux_d8Hom_swap_last_smRefl⟩)
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
          (Set.range fun i : Fin 7 => hdRo7SmAAux_d8Hom (Equiv.swap i.castSucc i.succ)))
        ?_ ?_ ?_ ?_ hσ
      · intro τ hτ
        obtain ⟨m, hm⟩ := hτ
        dsimp only at hm
        rw [← hm, ← hdRo7SmAAux_d8Hom_swap_inner m]
        exact Subgroup.subset_closure ⟨Fin.castSucc m, rfl⟩
      · exact Subgroup.one_mem _
      · intro a b ha hb iha ihb
        simpa only [map_mul] using Subgroup.mul_mem _ iha ihb
      · intro a ha iha
        simpa only [map_inv] using Subgroup.inv_mem _ iha
    · obtain ⟨q, hq, hxr⟩ := hx
      rw [List.mem_singleton] at hq
      subst hq
      have hx' : x = hdRo7SmAAux_d8Hom (Equiv.swap (Fin.last 6).castSucc (Fin.last 6).succ) := by
        apply LinearEquiv.ext; intro v
        rw [hxr.2 v, hdRo7SmAAux_d8Hom_swap_last_apply]
      rw [hx']
      exact Subgroup.subset_closure ⟨Fin.last 6, rfl⟩

theorem hdRo7SmAAux_case3 : ZS.LinWeyl 3 (smGroup 7 [sm7A7b]) := by
  rw [← hdRo7SmAAux_range_d8]
  refine hdRo7SmAAux_linWeyl_of_perm _ 7 (by norm_num) ?_ ?_
  · refine MulEquiv.ofBijective
      (hdRo7SmAAux_d8Hom.codRestrict hdRo7SmAAux_d8Hom.range
        (fun σ => MonoidHom.mem_range.mpr ⟨σ, rfl⟩)) ?_
    constructor
    · intro a b h
      exact hdRo7SmAAux_d8Hom_injective (Subtype.ext_iff.mp h)
    · rintro ⟨g, hg⟩
      obtain ⟨σ, hσ⟩ := hg
      exact ⟨σ, Subtype.ext hσ⟩
  · intro k
    change GGLinRefl ((hdRo7SmAAux_d8Hom) (Equiv.swap k.castSucc k.succ))
    exact hdRo7SmAAux_d8Hom_swap_isRefl k

end CFSG.StandardType.HdRo7SU.Small
