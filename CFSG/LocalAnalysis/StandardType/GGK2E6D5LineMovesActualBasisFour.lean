module

public import CFSG.LocalAnalysis.StandardType.GGK2E6D5LineMoves
public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def d5SwapLinear (i j : Fin 5) :
    (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3) where
  toFun := d5SwapVector i j
  invFun := d5SwapVector i j
  left_inv v := by ext k; simp [d5SwapVector]
  right_inv v := by ext k; simp [d5SwapVector]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[expose] def d5NegPairLinear (i j : Fin 5) :
    (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3) where
  toFun := d5NegPairVector i j
  invFun := d5NegPairVector i j
  left_inv v := by ext k; by_cases h : k = i.succ ∨ k = j.succ <;>
    simp [d5NegPairVector, h]
  right_inv v := by ext k; by_cases h : k = i.succ ∨ k = j.succ <;>
    simp [d5NegPairVector, h]
  map_add' v w := by ext k; by_cases h : k = i.succ ∨ k = j.succ <;>
    simp [d5NegPairVector, h] <;> ring
  map_smul' c v := by ext k; by_cases h : k = i.succ ∨ k = j.succ <;>
    simp [d5NegPairVector, h]

theorem d5_pair_signs_prod (i j : Fin 5) (hij : i ≠ j) :
    ∏ k : Fin 6, (if k = i.succ ∨ k = j.succ then (-1 : ZMod 3) else 1) = 1 := by
  have h : ∀ i j : Fin 5, i ≠ j →
      (∏ k : Fin 6, (if k = i.succ ∨ k = j.succ then (-1 : ZMod 3) else 1)) = 1 := by
    decide +kernel
  exact h i j hij

theorem d5_swap_basis_dsp
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin 6) (ZMod 3) V) (i j : Fin 5) :
    HdRo7D.DSP 3 b ((b.equivFun.trans (d5SwapLinear i j)).trans b.equivFun.symm) := by
  classical
  let e := b.equivFun
  let a := (e.trans (d5SwapLinear i j)).trans e.symm
  have hcoord (v : V) : e (a v) = d5SwapLinear i j (e v) := e.apply_symm_apply _
  refine ⟨Equiv.swap i.succ j.succ, fun _ => 1, ?_, rfl, fun _ => Or.inl rfl,
    by simp, ?_⟩
  · have h : ∀ i j : Fin 5, (Equiv.swap i.succ j.succ) 0 = 0 := by decide +kernel
    exact h i j
  · intro k
    apply e.injective
    rw [hcoord, one_smul]
    ext l
    change b.equivFun (b k) ((Equiv.swap i.succ j.succ) l) =
      b.equivFun (b ((Equiv.swap i.succ j.succ) k)) l
    simp only [Module.Basis.equivFun_self]
    by_cases h : k = (Equiv.swap i.succ j.succ) l
    · have h' : (Equiv.swap i.succ j.succ) k = l := by
        rw [h]
        simp
      simp [h, h']
    · have h' : (Equiv.swap i.succ j.succ) k ≠ l := by
        intro he
        apply h
        have he' := congrArg (Equiv.swap i.succ j.succ) he
        simpa using he'
      simp [h, h']

theorem d5_negPair_basis_dsp
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin 6) (ZMod 3) V) (i j : Fin 5) (hij : i ≠ j) :
    HdRo7D.DSP 3 b ((b.equivFun.trans (d5NegPairLinear i j)).trans b.equivFun.symm) := by
  classical
  let e := b.equivFun
  let a := (e.trans (d5NegPairLinear i j)).trans e.symm
  have hcoord (v : V) : e (a v) = d5NegPairLinear i j (e v) := e.apply_symm_apply _
  refine ⟨1, fun k => if k = i.succ ∨ k = j.succ then -1 else 1, rfl, ?_, ?_,
    d5_pair_signs_prod i j hij, ?_⟩
  · have h : ∀ i j : Fin 5,
        (if (0 : Fin 6) = i.succ ∨ 0 = j.succ then (-1 : ZMod 3) else 1) = 1 := by
      decide +kernel
    exact h i j
  · intro k
    change (if k = i.succ ∨ k = j.succ then (-1 : ZMod 3) else 1) = 1 ∨
      (if k = i.succ ∨ k = j.succ then (-1 : ZMod 3) else 1) = -1
    by_cases h : k = i.succ ∨ k = j.succ <;> simp [h]
  · intro k
    apply e.injective
    rw [hcoord, map_smul]
    ext l
    change (if l = i.succ ∨ l = j.succ then -b.equivFun (b k) l
        else b.equivFun (b k) l) =
      (if k = i.succ ∨ k = j.succ then (-1 : ZMod 3) else 1) * b.equivFun (b k) l
    rw [Module.Basis.equivFun_self]
    by_cases hkl : k = l
    · subst k
      by_cases h : l = i.succ ∨ l = j.succ <;> simp [h]
    · by_cases h : l = i.succ ∨ l = j.succ <;> simp [hkl, h, neg_zero] <;> decide +kernel

theorem d5_basis_exists_line_move
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin 6) (ZMod 3) V) {y : V}
    (hy : y ∉ Submodule.span (ZMod 3) ({b 0} : Set V)) :
    ∃ a : V ≃ₗ[ZMod 3] V, HdRo7D.DSP 3 b a ∧
      a y ∉ Submodule.span (ZMod 3) ({y} : Set V) := by
  classical
  have hnonaxis : ∃ k : Fin 5, b.equivFun y k.succ ≠ 0 := by
    by_contra! hzero
    have heq : y = b.equivFun y 0 • b 0 := by
      apply b.equivFun.injective
      ext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp [Module.Basis.equivFun_self]
      · simp [hzero, Module.Basis.equivFun_self]
    apply hy
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  obtain ⟨i, j, hij, hmove | hmove⟩ :=
    d5_nonaxis_exists_line_move (b.equivFun y) hnonaxis
  · let a := (b.equivFun.trans (d5SwapLinear i j)).trans b.equivFun.symm
    refine ⟨a, d5_swap_basis_dsp b i j, ?_⟩
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    apply hmove c
    have he := congrArg b.equivFun hc
    rw [map_smul] at he
    have hcoord : b.equivFun (a y) = d5SwapVector i j (b.equivFun y) :=
      b.equivFun.apply_symm_apply _
    rw [hcoord] at he
    exact he.symm
  · let a := (b.equivFun.trans (d5NegPairLinear i j)).trans b.equivFun.symm
    refine ⟨a, d5_negPair_basis_dsp b i j hij, ?_⟩
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    apply hmove c
    have he := congrArg b.equivFun hc
    rw [map_smul] at he
    have hcoord : b.equivFun (a y) = d5NegPairVector i j (b.equivFun y) :=
      b.equivFun.apply_symm_apply _
    rw [hcoord] at he
    exact he.symm

end CFSG.StandardType

end
