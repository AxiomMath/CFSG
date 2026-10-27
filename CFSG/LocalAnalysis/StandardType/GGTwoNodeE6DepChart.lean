module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6DepAllDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallSem
public import Certificates.Data.CFSGNative.DepFrame.E6
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.DepFrame

open CFSG.TwoNodeSmall

private lemma e6Dep_kernel_five :
    ∀ g : Fin 6 → ZMod 3,
      (∀ k : Fin 6, (∑ j : Fin 6, g j * (CartanMatrix.E 6 k j : ZMod 3)) = 0) →
      g 1 = 0 ∧ g 3 = 0 ∧ g 2 = 2 * g 0 ∧ g 4 = g 0 ∧ g 5 = 2 * g 0 := by
  decide +kernel

private lemma e6Dep_kernel_zero :
    ∀ g : Fin 6 → ZMod 3,
      (∀ k : Fin 6, (∑ j : Fin 6,
        g j * (if j = 5 then 0 else (CartanMatrix.E 6 k j : ZMod 3))) = 0) →
      g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 ∧ g 3 = 0 ∧ g 4 = 0 := by
  decide +kernel

theorem e6Dep_chart {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (hV : Module.finrank (ZMod 3) V = 6)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V) (x : V)
    (hfr : CFSG.StandardType.GGDepE6Frame h α x) :
    ∃ ε : V ≃ₗ[ZMod 3] (e6DepPt ()).V,
      (∀ i : Fin 6, ε (h i) = (e6DepPt ()).vec (e6DepH i)) ∧
      (∀ (i : Fin 6) w, α i w = (e6DepPt ()).dot ((e6DepPt ()).vec (e6DepF i)) (ε w)) ∧
      ε x = (e6DepPt ()).vec [0, 0, 0, 0, 0, 1] := by
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  obtain ⟨g, hg, i, hgi⟩ := Fintype.not_linearIndependent_iff.mp hfr.dep
  have hkey : ∀ k : Fin 6, (∑ j : Fin 6, g j * (CartanMatrix.E 6 k j : ZMod 3)) = 0 := by
    intro k
    have h := congrArg (α k) hg
    simpa only [map_sum, map_smul, map_zero, smul_eq_mul, hfr.pair] using h
  obtain ⟨hg1, hg3, hg2, hg4, hg5⟩ := e6Dep_kernel_five g hkey
  have hg0 : g 0 ≠ 0 := by
    intro h0
    apply hgi
    fin_cases i <;> simp [h0, hg1, hg2, hg3, hg4, hg5]
  have hexp : g 0 • h 0 + (2 : ZMod 3) • (g 0 • h 2) + g 0 • h 4 +
      (2 : ZMod 3) • (g 0 • h 5) = 0 := by
    have h := hg
    rw [Fin.sum_univ_six] at h
    rw [hg1, hg3, hg2, hg4, hg5] at h
    simpa only [zero_smul, add_zero, mul_smul] using h
  have hZ : h 0 + (2 : ZMod 3) • h 2 + h 4 + (2 : ZMod 3) • h 5 = 0 := by
    have hfac : g 0 • (h 0 + (2 : ZMod 3) • h 2 + h 4 + (2 : ZMod 3) • h 5) = 0 := by
      rw [smul_add, smul_add, smul_add]
      rw [smul_comm (g 0) (2 : ZMod 3) (h 2), smul_comm (g 0) (2 : ZMod 3) (h 5)]
      exact hexp
    exact (smul_eq_zero.mp hfac).resolve_left hg0
  have h2eq : (2 : ZMod 3) • h 5 = -(h 0 + (2 : ZMod 3) • h 2 + h 4) :=
    eq_neg_of_add_eq_zero_right hZ
  have h5rel : h 5 = h 0 + (2 : ZMod 3) • h 2 + h 4 := by
    calc h 5 = (2 * 2 : ZMod 3) • h 5 := by
          rw [show (2 * 2 : ZMod 3) = 1 by decide, one_smul]
      _ = (2 : ZMod 3) • ((2 : ZMod 3) • h 5) := by rw [smul_smul]
      _ = (2 : ZMod 3) • (-(h 0 + (2 : ZMod 3) • h 2 + h 4)) := by rw [h2eq]
      _ = h 0 + (2 : ZMod 3) • h 2 + h 4 := by
            rw [smul_neg, show (2 : ZMod 3) = -1 by decide, neg_smul, one_smul, neg_neg]
  let bfun : Fin 6 → V := ![h 0, h 1, h 2, h 3, h 4, x]
  have hb0 : bfun 0 = h 0 := by simp [bfun]
  have hb1 : bfun 1 = h 1 := by simp [bfun]
  have hb2 : bfun 2 = h 2 := by simp [bfun]
  have hb3 : bfun 3 = h 3 := by simp [bfun]
  have hb4 : bfun 4 = h 4 := by simp [bfun]
  have hbx : bfun 5 = x := by simp [bfun]
  have hbα : ∀ (k : Fin 6) (j : Fin 6),
      α k (bfun j) = (if j = 5 then 0 else (CartanMatrix.E 6 k j : ZMod 3)) := by
    intro k j
    fin_cases j <;> simp [bfun, hfr.pair, hfr.x_ker]
  have hb_lin : LinearIndependent (ZMod 3) bfun := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have key : ∀ k : Fin 6, (∑ j : Fin 6, g j • α k (bfun j)) = 0 := by
      intro k
      have h := congrArg (α k) hg
      simpa only [map_sum, map_smul, map_zero] using h
    have hker : ∀ k : Fin 6, (∑ j : Fin 6,
        g j * (if j = 5 then 0 else (CartanMatrix.E 6 k j : ZMod 3))) = 0 := by
      intro k
      simpa only [smul_eq_mul, hbα k] using key k
    obtain ⟨hz0, hz1, hz2, hz3, hz4⟩ := e6Dep_kernel_zero g hker
    have hg5 : g 5 = 0 := by
      have h := hg
      have row5 : (∑ j : Fin 6, g j • bfun j) = g 5 • bfun 5 := by
        refine Finset.sum_eq_single 5 ?_ ?_
        · intro j _ hj
          fin_cases j
          · simp [hz0]
          · simp [hz1]
          · simp [hz2]
          · simp [hz3]
          · simp [hz4]
          · exact absurd rfl hj
        · intro hh; exact absurd (Finset.mem_univ 5) hh
      rw [row5] at h
      rw [hbx] at h
      exact (smul_eq_zero.mp h).resolve_right hfr.x_ne
    intro j
    fin_cases j
    · exact hz0
    · exact hz1
    · exact hz2
    · exact hz3
    · exact hz4
    · exact hg5
  have hcard : Fintype.card (Fin 6) = Module.finrank (ZMod 3) V := by
    rw [Fintype.card_fin, hV]
  let b : Module.Basis (Fin 6) (ZMod 3) V :=
    basisOfLinearIndependentOfCardEqFinrank hb_lin hcard
  have hb_coe : (b : Fin 6 → V) = bfun :=
    coe_basisOfLinearIndependentOfCardEqFinrank hb_lin hcard
  have hb_apply : ∀ j : Fin 6, b j = bfun j := fun j => congrFun hb_coe j
  have hbε : ∀ j : Fin 6, b.equivFun (b j) = Pi.single j (1 : ZMod 3) := by
    intro j
    funext j'
    rw [Module.Basis.equivFun_self b j j']
    by_cases h : j = j'
    · subst h; simp
    · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]
  have hαb_eval : ∀ (i : Fin 6) (j : Fin 6),
      α i (b j) = ((e6DepPt ()).vec (e6DepF i)) j := by
    intro i j
    rw [hb_apply j, hbα]
    fin_cases j <;> fin_cases i <;> decide
  refine ⟨b.equivFun, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change b.equivFun (h 0) = (e6DepPt ()).vec (e6DepH 0)
      have hi : h 0 = b (0 : Fin 6) := by rw [hb_apply]; exact hb0.symm
      rw [hi, hbε]
      funext j; fin_cases j <;> decide
    · change b.equivFun (h 1) = (e6DepPt ()).vec (e6DepH 1)
      have hi : h 1 = b (1 : Fin 6) := by rw [hb_apply]; exact hb1.symm
      rw [hi, hbε]
      funext j; fin_cases j <;> decide
    · change b.equivFun (h 2) = (e6DepPt ()).vec (e6DepH 2)
      have hi : h 2 = b (2 : Fin 6) := by rw [hb_apply]; exact hb2.symm
      rw [hi, hbε]
      funext j; fin_cases j <;> decide
    · change b.equivFun (h 3) = (e6DepPt ()).vec (e6DepH 3)
      have hi : h 3 = b (3 : Fin 6) := by rw [hb_apply]; exact hb3.symm
      rw [hi, hbε]
      funext j; fin_cases j <;> decide
    · change b.equivFun (h 4) = (e6DepPt ()).vec (e6DepH 4)
      have hi : h 4 = b (4 : Fin 6) := by rw [hb_apply]; exact hb4.symm
      rw [hi, hbε]
      funext j; fin_cases j <;> decide
    · change b.equivFun (h 5) = (e6DepPt ()).vec (e6DepH 5)
      have h0 : h 0 = b (0 : Fin 6) := by rw [hb_apply]; exact hb0.symm
      have h2 : h 2 = b (2 : Fin 6) := by rw [hb_apply]; exact hb2.symm
      have h4 : h 4 = b (4 : Fin 6) := by rw [hb_apply]; exact hb4.symm
      rw [h5rel, h0, h2, h4]
      simp only [map_add, map_smul, hbε]
      funext j; fin_cases j <;> decide
  · intro i w
    have hw : w = ∑ j : Fin 6, b.equivFun w j • b j := by
      simpa [Module.Basis.equivFun_apply] using (b.sum_repr w).symm
    conv_lhs => rw [hw]
    rw [map_sum, Pt.dot]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hαb_eval i j]
    exact mul_comm _ _
  · have hx : x = b (5 : Fin 6) := by rw [hb_apply]; exact hbx.symm
    rw [hx, hbε]
    funext j; fin_cases j <;> decide

end CFSG.DepFrame

end
