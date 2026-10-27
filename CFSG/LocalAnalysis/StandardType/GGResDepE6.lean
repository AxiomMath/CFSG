module

public import CFSG.LocalAnalysis.StandardType.GGResDepAFive
public import CFSG.LocalAnalysis.StandardType.GGDepEFrame
public import CFSG.LocalAnalysis.StandardType.GGDepERelation
public import CFSG.LocalAnalysis.StandardType.GGDepEKSide
public import CFSG.LocalAnalysis.StandardType.GGDepEDim6
public import CFSG.LocalAnalysis.StandardType.GGDepEPattern
public import CFSG.LocalAnalysis.StandardType.GGDepEModel
public import CFSG.LocalAnalysis.StandardType.GGDepECells
public import CFSG.LocalAnalysis.StandardType.GGResLeaves

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem ggResDepE6Input_of_inputs (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) :
    GGResDepE6Input := by
  intro G _ _ p B Bs x L D J y K hH _ hFork hStd hE6 hP
  obtain ⟨hp3, hdat, hnsh⟩ := hP
  have hdat' := hdat
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩,
    hAL, hAK, hdel, hJ⟩ := hdat
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hdep : ¬ LinearIndependent (ZMod p) fun i : Λ => h (some i) := hsel
  have hαL : ∀ c : Λ, α (some c) (h (some c)) = 2 := by
    intro c
    have h1 := hL c c
    rw [hCL.1 c] at h1
    simpa using h1
  obtain ⟨e, hbpos, hCart, F⟩ :=
    ggDepE_frame_of_config hFix hp3 hH hxBs hCL htyp hdel hφ hL hdep hAL
  obtain ⟨y', hy'x, hy'α⟩ := ggDepA_y_fixed hp2 hH hxBs hφ hαL hJ
  have hy : ∃ y : V, y ∉ Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hxBs⟩)} ∧
      ∀ c : Fin 6, c ≠ e.symm b → α (some (e c)) y = 0 := by
    refine ⟨y', hy'x, ?_⟩
    intro c hc
    exact hy'α (e c) (fun h => hc ((Equiv.symm_apply_apply e c).symm.trans (congrArg e.symm h)))
  obtain ⟨hαa, hw, hjoin, hnt⟩ :=
    ggDepE_kside hFix hFixK hH hxBs hWL hCL hWK hCK hφ hL hK hAL hAK e F
  obtain ⟨hlo, hhi⟩ := ggDepE_finrank_bounds F
  by_cases hdim6 : Module.finrank (ZMod p) V = 6
  · exfalso
    have hcard : Nat.card Bs = 3 ^ 6 := by
      rw [card_eq_of_ggLin ι, Module.natCard_eq_pow_finrank (K := ZMod p) (V := V),
        Nat.card_zmod, hdim6, hp3]
    exact hnsh ⟨hp3, hcard, ggDepE_dim6_shape hFix hH hdat' hcard hp3⟩
  · have hdim7 : Module.finrank (ZMod p) V = 7 := by omega
    have hJ' : ∀ i j : {i : Λ // i ≠ b}, (CK (some i) (some j) : ZMod 3) =
        ((CartanMatrix.E 6) (e.symm i.1) (e.symm j.1) : ZMod 3) := by
      subst hp3
      intro i j
      have hcart : CL i.1 j.1 = CartanMatrix.E 6 (e.symm i.1) (e.symm j.1) := by
        simpa using hCart (e.symm i.1) (e.symm j.1)
      calc (CK (some i) (some j) : ZMod 3)
          = α (some i.1) (h (some j.1)) := by
            simpa only [Option.map_some] using (hK (some i) (some j)).symm
        _ = (CL i.1 j.1 : ZMod 3) := hL i.1 j.1
        _ = (CartanMatrix.E 6 (e.symm i.1) (e.symm j.1) : ZMod 3) := by rw [hcart]
    have hKE : e.symm b = 1 → GGIsTypeE6 MK := by
      intro hbe
      have hcardΛ : Fintype.card Λ = 6 := by
        rw [← Fintype.card_congr e, Fintype.card_fin]
      have hcardK : Fintype.card (Option {i : Λ // i ≠ b}) = 6 := by
        rw [Fintype.card_option, Fintype.card_subtype_compl (fun i : Λ => i = b),
          Fintype.card_subtype_eq b, hcardΛ]
      have hrel : ∑ j : Fin 6,
          (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) j : ℕ) : ZMod p) • h (some (e j)) = 0 :=
        (ggDepE_relation F).1
      have hk1 : (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) 1 : ℕ) : ZMod p) = 0 := by norm_num
      refine ggDepE_K_type_of_dep hp3 hcardK hWK hCK
        (fun o : Option {i : Λ // i ≠ b} => h (o.map Subtype.val))
        (fun o : Option {i : Λ // i ≠ b} => α (o.map Subtype.val))
        (fun i j => hK i j) ?_
      rw [Fintype.not_linearIndependent_iff]
      have hrel' : ∑ j : {j : Fin 6 // j ≠ e.symm b},
          (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) j.1 : ℕ) : ZMod p) • h (some (e j.1)) = 0 := by
        have hsplit := Fintype.sum_eq_add_sum_subtype_ne
          (fun j : Fin 6 => (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) j : ℕ) : ZMod p) •
            h (some (e j))) (e.symm b)
        rw [hsplit] at hrel
        have hz : (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) (e.symm b) : ℕ) : ZMod p) •
            h (some (e (e.symm b))) = 0 := by simp [hbe, hk1]
        rw [hz, zero_add] at hrel
        simpa using hrel
      have hsum_some : ∑ i : {i : Λ // i ≠ b},
          (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) (e.symm i.1) : ℕ) : ZMod p) • h (some i.1) = 0 := by
        have hcomp := Equiv.sum_comp
          (Equiv.subtypeEquiv (p := fun j : Fin 6 => j ≠ e.symm b) (q := fun i : Λ => i ≠ b) e
            (fun j => by
              constructor
              · intro hj hcon
                exact hj (by rw [← hcon, Equiv.symm_apply_apply])
              · intro hcon hj
                exact hcon (by rw [hj, Equiv.apply_symm_apply])))
          (fun i : {i : Λ // i ≠ b} =>
            (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) (e.symm i.1) : ℕ) : ZMod p) • h (some i.1))
        rw [← hcomp]
        simp only [Equiv.subtypeEquiv_apply, Equiv.symm_apply_apply, Subtype.coe_mk]
        exact hrel'
      refine ⟨fun o => o.elim 0 (fun i =>
        (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) (e.symm i.1) : ℕ) : ZMod p)), ?_, ?_⟩
      · rw [Fintype.sum_option]
        simp only [Option.elim_none, Option.elim_some, Option.map_none, Option.map_some,
          zero_smul, zero_add]
        exact hsum_some
      · refine ⟨some ⟨e 0, ?_⟩, ?_⟩
        · intro hcon
          have h1 : e.symm b = 0 := by rw [← hcon, Equiv.symm_apply_apply]
          rw [hbe] at h1
          exact one_ne_zero h1
        · have hk0 : (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) 0 : ℕ) : ZMod p) = 1 := by norm_num
          show (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) (e.symm (e 0)) : ℕ) : ZMod p) ≠ 0
          rw [Equiv.symm_apply_apply, hk0]
          exact one_ne_zero
    obtain ⟨c0, m, n, hpat, hclause⟩ := ggDepE_pattern e hbpos hWK hCK hJ' hKE
    have hpair : ∀ c : Fin 6, c ≠ e.symm b →
        α none (h (some (e c))) = (if c = c0 then (m : ZMod p) else 0) ∧
        α (some (e c)) (h none) = (if c = c0 then (n : ZMod p) else 0) := by
      intro c hc
      have hcb : e c ≠ b := by
        intro hcon
        exact hc ((Equiv.symm_apply_apply e c).symm.trans (congrArg e.symm hcon))
      let i : {i : Λ // i ≠ b} := ⟨e c, hcb⟩
      have hii : e.symm i.1 = c := by simp [i]
      obtain ⟨h1, h2⟩ := hclause i
      rw [hii] at h1 h2
      constructor
      · calc α none (h (some (e c))) = (CK none (some i) : ZMod p) := hK none (some i)
          _ = ((if c = c0 then m else 0 : ℤ) : ZMod p) := by rw [h1]
          _ = (if c = c0 then (m : ZMod p) else 0) := by by_cases h : c = c0 <;> simp [h]
      · calc α (some (e c)) (h none) = (CK (some i) none : ZMod p) := hK (some i) none
          _ = ((if c = c0 then n else 0 : ℤ) : ZMod p) := by rw [h2]
          _ = (if c = c0 then (n : ZMod p) else 0) := by by_cases h : c = c0 <;> simp [h]
    exact (ggDepE_small_false ggDepE_cells F (fun i => ggLin (p := p) ι (φ (some (e i))))
      (fun i v => hφ (some (e i)) v) (ggLin (p := p) ι (φ none)) (h none) (α none)
      (fun v => hφ none v) hαa hw hdim7 (e.symm b) c0 m n hpat hpair hnt).elim

end CFSG.StandardType
