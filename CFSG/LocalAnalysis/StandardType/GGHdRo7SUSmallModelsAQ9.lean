module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAPerm

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType
open CFSG.StandardType.TypeAReflOver

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SmAAux_kRefl_mem : kRefl 3 7 ∈ smGroup 8 [sm8A8a] := by
  rw [smGroup]
  apply Subgroup.subset_closure
  right
  refine ⟨sm8A8a, by simp, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [hdRo7SmAAux_smDual_apply, smDot]; decide
  · intro v
    rw [kRefl_apply]
    have h2 : sm8A8a.2 = Pi.single (Fin.last 7) (1 : ZMod 3) := by
      ext i; fin_cases i <;> decide
    have hu : sm8A8a.1 = kRoot 3 7 := by ext i; fin_cases i <;> decide
    have hφ : smDual sm8A8a.2 v = v (Fin.last 7) := by
      rw [h2, hdRo7SmAAux_smDual_apply, hdRo7SmAAux_smDot_single]
    rw [hφ, hu]

theorem hdRo7SmAAux_adj8_gen :
    Subgroup.closure (Set.range (fun i : Fin 8 => Equiv.swap i.castSucc i.succ)) = ⊤ := by
  have hS : Set.range (fun i : Fin 8 => Equiv.swap i.castSucc i.succ)
      = CFSG.Permutation.SymmetricCoxeter.adjSwap 8 '' Set.Iio 8 := by
    ext σ; constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, by
        rw [CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt i.isLt]; rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, by
        rw [CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt hi]; rfl⟩
  rw [hS, CFSG.Permutation.SymmetricCoxeter.closure_adjSwap 8]

theorem hdRo7SmAAux_adj7_gen :
    Subgroup.closure (Set.range (fun i : Fin 7 => Equiv.swap i.castSucc i.succ)) = ⊤ := by
  have hS : Set.range (fun i : Fin 7 => Equiv.swap i.castSucc i.succ)
      = CFSG.Permutation.SymmetricCoxeter.adjSwap 7 '' Set.Iio 7 := by
    ext σ; constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, by
        rw [CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt i.isLt]; rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, by
        rw [CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt hi]; rfl⟩
  rw [hS, CFSG.Permutation.SymmetricCoxeter.closure_adjSwap 7]

theorem hdRo7SmAAux_q9Hom_swap_perm_castSucc (m : Fin 7) :
    hdRo7SmAAux_q9Hom (Equiv.swap (Fin.castSucc m).castSucc (Fin.castSucc m).succ) =
      hdRo7SmAAux_permLin 8 (Equiv.swap (Fin.castSucc m) (Fin.succ m)) :=
  hdRo7SmAAux_q9Hom_swap_perm m

theorem hdRo7SmAAux_q9Hom_swap_last_castSucc :
    hdRo7SmAAux_q9Hom (Equiv.swap (Fin.last 7).castSucc (Fin.last 7).succ) = kRefl 3 7 :=
  hdRo7SmAAux_q9Hom_swap_last

theorem hdRo7SmAAux_range_q9Hom : hdRo7SmAAux_q9Hom.range = smGroup 8 [sm8A8a] := by
  have hrange : hdRo7SmAAux_q9Hom.range =
      Subgroup.closure (Set.range (fun i : Fin 8 =>
        hdRo7SmAAux_q9Hom (Equiv.swap i.castSucc i.succ))) := by
    rw [← Subgroup.map_top hdRo7SmAAux_q9Hom, ← hdRo7SmAAux_adj8_gen,
      MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [hrange, smGroup]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    obtain ⟨m, hm⟩ | hlast := Fin.eq_castSucc_or_eq_last i
    · rw [hm]
      dsimp only
      rw [hdRo7SmAAux_q9Hom_swap_perm_castSucc m]
      exact Subgroup.subset_closure (Or.inl (hdRo7SmAAux_isPerm_permLin
        (Equiv.swap (Fin.castSucc m) (Fin.succ m))))
    · rw [hlast]
      dsimp only
      rw [hdRo7SmAAux_q9Hom_swap_last_castSucc]
      exact hdRo7SmAAux_kRefl_mem
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · have hset : x ∈ (hdRo7SmAAux_permLin 8).range := by
        obtain ⟨σ, hσ⟩ := hx
        exact ⟨σ, by ext v i; rw [hdRo7SmAAux_permLin_apply, hσ]⟩
      obtain ⟨σ, rfl⟩ := hset
      have hσ : σ ∈ Subgroup.closure (Set.range (fun i : Fin 7 =>
          Equiv.swap i.castSucc i.succ)) := by
        rw [hdRo7SmAAux_adj7_gen]; exact Subgroup.mem_top σ
      refine Subgroup.closure_induction
        (p := fun x _ => hdRo7SmAAux_permLin 8 x ∈ Subgroup.closure
          (Set.range fun i : Fin 8 => hdRo7SmAAux_q9Hom (Equiv.swap i.castSucc i.succ)))
        ?_ ?_ ?_ ?_ hσ
      · intro τ hτ
        obtain ⟨m, hm⟩ := hτ
        dsimp only at hm
        rw [← hm, ← hdRo7SmAAux_q9Hom_swap_perm_castSucc m]
        exact Subgroup.subset_closure ⟨Fin.castSucc m, rfl⟩
      · exact Subgroup.one_mem _
      · intro a b ha hb iha ihb
        simpa only [map_mul] using Subgroup.mul_mem _ iha ihb
      · intro a ha iha
        simpa only [map_inv] using Subgroup.inv_mem _ iha
    · obtain ⟨q, hq, hxr⟩ := hx
      rw [List.mem_singleton] at hq
      subst hq
      have hx' : x = kRefl 3 7 := by
        apply LinearEquiv.ext; intro v
        rw [hxr.2 v, kRefl_apply]
        have h2 : sm8A8a.2 = Pi.single (Fin.last 7) (1 : ZMod 3) := by
          ext i; fin_cases i <;> decide
        have hu : sm8A8a.1 = kRoot 3 7 := by ext i; fin_cases i <;> decide
        have hφ : smDual sm8A8a.2 v = v (Fin.last 7) := by
          rw [h2, hdRo7SmAAux_smDual_apply, hdRo7SmAAux_smDot_single]
        rw [hφ, hu]
      rw [hx', ← hdRo7SmAAux_q9Hom_swap_last_castSucc]
      exact Subgroup.subset_closure ⟨Fin.last 7, rfl⟩

theorem hdRo7SmAAux_case4 : ZS.LinWeyl 3 (smGroup 8 [sm8A8a]) := by
  rw [← hdRo7SmAAux_range_q9Hom]
  refine hdRo7SmAAux_linWeyl_of_perm _ 8 (by norm_num) ?_ ?_
  · refine MulEquiv.ofBijective
      (hdRo7SmAAux_q9Hom.codRestrict hdRo7SmAAux_q9Hom.range
        (fun σ => MonoidHom.mem_range.mpr ⟨σ, rfl⟩)) ?_
    constructor
    · intro a b h
      exact hdRo7SmAAux_q9Hom_injective (Subtype.ext_iff.mp h)
    · rintro ⟨g, hg⟩
      obtain ⟨σ, hσ⟩ := hg
      exact ⟨σ, Subtype.ext hσ⟩
  · intro k
    change GGLinRefl ((hdRo7SmAAux_q9Hom) (Equiv.swap k.castSucc k.succ))
    exact hdRo7SmAAux_q9Hom_swap_isRefl k

end CFSG.StandardType.HdRo7SU.Small
