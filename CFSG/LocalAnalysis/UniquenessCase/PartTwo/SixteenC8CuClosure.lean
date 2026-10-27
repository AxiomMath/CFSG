module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuGen
public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull

@[expose] noncomputable def g6Equiv : G6 ≃* ↥(CFSG.Open.StatedSp 3 (ZMod 2)) :=
  (MulEquiv.subgroupCongr spGrp_eq_map).trans
    (Subgroup.equivMapOfInjective _ reindexG.toMonoidHom reindexG.injective).symm

theorem reindexG_g6Equiv (g : G6) :
    reindexG (g6Equiv g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) = (g : GL (Fin 6) (ZMod 2)) :=
  congrArg Subtype.val
    ((Subgroup.equivMapOfInjective _ reindexG.toMonoidHom reindexG.injective).apply_symm_apply
      (MulEquiv.subgroupCongr spGrp_eq_map g))

@[expose] def ctr : Fin 3 ⊕ Fin 3 → ZMod 2 := vecOf 4 ∘ e6

theorem spEnd_g6Equiv (g : G6) (w : Fin 6 → ZMod 2) :
    spEnd (g6Equiv g) (w ∘ e6) = (gM g *ᵥ w) ∘ e6 := by
  have h : gM g = Matrix.reindex e6 e6
      ((g6Equiv g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) _) := by
    rw [← coe_reindexG, reindexG_g6Equiv]
  rw [spEnd_apply, h, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  funext a
  simp

theorem spForm_comp_e6 (w u : Fin 6 → ZMod 2) :
    spForm 3 (ZMod 2) (w ∘ e6) (u ∘ e6) = w ⬝ᵥ (gramJ *ᵥ u) := by
  rw [spForm_apply, ← reindex_gram, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv,
    Equiv.symm_symm]
  exact (dotProduct_comp_equiv_symm _ _ e6).symm

theorem g6Equiv_xE_two : g6Equiv (xE 2) = spTransvection ctr 1 := by
  have key : ∀ w : Fin 6 → ZMod 2,
      xM 2 *ᵥ w = w + (1 * (w ⬝ᵥ (gramJ *ᵥ vecOf 4))) • vecOf 4 := by
    decide +kernel
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (g6Equiv (xE 2)) y = spEnd (spTransvection ctr 1) y
  obtain ⟨w, rfl⟩ : ∃ w : Fin 6 → ZMod 2, y = w ∘ e6 := ⟨y ∘ e6.symm, by funext a; simp⟩
  rw [spEnd_g6Equiv, spEnd_spTransvection, ctr, spForm_comp_e6]
  funext a
  simpa using congrFun (key w) (e6 a)

theorem exists_spEnd_ctr {v : Fin 3 ⊕ Fin 3 → ZMod 2} (hv : v ≠ 0) :
    ∃ g ∈ Subgroup.closure ((Lgrp : Set G6) ∪ Set.range xE), spEnd (g6Equiv g) ctr = v := by
  obtain ⟨w, rfl⟩ : ∃ w : Fin 6 → ZMod 2, v = w ∘ e6 := ⟨v ∘ e6.symm, by funext a; simp⟩
  have hw : w ≠ 0 := fun h => hv (by rw [h]; rfl)
  have hsurj : ∀ w : Fin 6 → ZMod 2, w ≠ 0 → ∃ n : Fin 64, n ≠ 0 ∧ vecOf n = w := by
    decide +kernel
  obtain ⟨n, hn, rfl⟩ := hsurj w hw
  refine ⟨rootProd (trWord n), rootProd_mem_closure _, ?_⟩
  rw [ctr, spEnd_g6Equiv, rootProd_coe, trWord_spec n hn]

theorem spTransvection_zero_right (v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    spTransvection v (0 : ZMod 2) = 1 := by
  apply spLin_injective
  rw [map_one]
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spTransvection v 0) y = y
  rw [spEnd_spTransvection]
  simp

theorem closure_gens : Subgroup.closure ((Lgrp : Set G6) ∪ Set.range xE) = ⊤ := by
  set H := Subgroup.closure ((Lgrp : Set G6) ∪ Set.range xE) with hH
  have htop : H.map g6Equiv.toMonoidHom = ⊤ := by
    refine CFSG.RankThree.PartOne.CTP.eq_top_of_transCenter fun v t => ?_
    by_cases hv : v = 0
    · rw [hv, CFSG.RankThree.PartOne.CTP.spTransvection_zero]
      exact Subgroup.one_mem _
    by_cases ht : t = 0
    · rw [ht, spTransvection_zero_right]
      exact Subgroup.one_mem _
    have ht1 : t = 1 := (by decide : ∀ t : ZMod 2, t ≠ 0 → t = 1) t ht
    obtain ⟨g, hg, hgv⟩ := exists_spEnd_ctr hv
    have hx : g6Equiv (xE 2) ∈ H.map g6Equiv.toMonoidHom :=
      ⟨xE 2, Subgroup.subset_closure (Or.inr ⟨2, rfl⟩), rfl⟩
    have hg' : g6Equiv g ∈ H.map g6Equiv.toMonoidHom := ⟨g, hg, rfl⟩
    have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ hg' hx) (Subgroup.inv_mem _ hg')
    rwa [g6Equiv_xE_two, CFSG.RankThree.PartOne.CTP.spTransvection_conj, hgv, ← ht1] at h
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨h, hh, hhg⟩ : g6Equiv g ∈ H.map g6Equiv.toMonoidHom := htop ▸ Subgroup.mem_top _
  have e : h = g := g6Equiv.injective hhg
  exact e ▸ hh

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
