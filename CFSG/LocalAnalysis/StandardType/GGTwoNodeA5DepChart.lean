module

public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallSem
public import Certificates.Data.CFSGNative.DepFrame.A5
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.DepFrame

open CFSG.TwoNodeSmall

theorem a5Dep_chart {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (hV : Module.finrank (ZMod 3) V = 6)
    (h : Fin (6 - 1) → V) (α : Fin (6 - 1) → Module.Dual (ZMod 3) V) (x : V)
    (hfr : CFSG.StandardType.GGDepAFrame 3 6 h α x) :
    ∃ ε : V ≃ₗ[ZMod 3] (a5DepPt ()).V,
      (∀ i : Fin 5, ε (h i) = (a5DepPt ()).vec (a5DepH i)) ∧
      (∀ (i : Fin 5) w, α i w = (a5DepPt ()).dot ((a5DepPt ()).vec (a5DepF i)) (ε w)) ∧
      ε x = (a5DepPt ()).vec [0, 0, 0, 0, 0, 1] := by
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  obtain ⟨hrel, -, -⟩ :=
    @CFSG.StandardType.ggDepA_relation 3 6 ⟨Nat.prime_three⟩ V _ _ h α x hfr
  have h4rel : h 4 = h 0 + (2 : ZMod 3) • h 1 + h 3 := by
    have h5 := hrel
    rw [Fin.sum_univ_five] at h5
    norm_num at h5
    have e2 : (3 : ZMod 3) • h 2 = 0 := by
      rw [show (3 : ZMod 3) = 0 from by decide, zero_smul]
    have e3 : (4 : ZMod 3) • h 3 = h 3 := by
      rw [show (4 : ZMod 3) = 1 from by decide, one_smul]
    have e4 : (5 : ZMod 3) • h 4 = (2 : ZMod 3) • h 4 := by
      rw [show (5 : ZMod 3) = 2 from by decide]
    rw [e2, e3, e4] at h5
    try simp only [one_smul, zero_smul, add_zero, zero_add] at h5
    have h2 : (2 : ZMod 3) • h 4 = -(h 0 + (2 : ZMod 3) • h 1 + h 3) :=
      eq_neg_of_add_eq_zero_right h5
    calc h 4 = (2 * 2 : ZMod 3) • h 4 := by
          rw [show (2 * 2 : ZMod 3) = 1 by decide, one_smul]
      _ = (2 : ZMod 3) • ((2 : ZMod 3) • h 4) := by rw [smul_smul]
      _ = (2 : ZMod 3) • (-(h 0 + (2 : ZMod 3) • h 1 + h 3)) := by rw [h2]
      _ = h 0 + (2 : ZMod 3) • h 1 + h 3 := by
            rw [smul_neg, show (2 : ZMod 3) = -1 from by decide, neg_smul, one_smul, neg_neg]
  let ψ : V →ₗ[ZMod 3] (Fin 5 → ZMod 3) :=
    { toFun := fun v i => α i v
      map_add' := by intro a b; funext i; simp
      map_smul' := by intro c a; funext i; simp }
  have hker : ψ.ker = Submodule.span (ZMod 3) ({x} : Set V) := by
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker] at hv
      apply hfr.fix v
      intro i
      have h1 := congrFun hv i
      simpa [ψ] using h1
    · rw [Submodule.span_le]
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      ext i
      simp [ψ, hfr.x_ker i]
  have hx1 : Module.finrank (ZMod 3) ↥(Submodule.span (ZMod 3) ({x} : Set V)) = 1 := by
    simpa using finrank_span_singleton (K := ZMod 3) (v := x) hfr.x_ne
  have hkerfin : Module.finrank (ZMod 3) ↥ψ.ker = 1 := by rw [hker]; exact hx1
  have hrk := LinearMap.finrank_range_add_finrank_ker ψ
  have hrange5 : Module.finrank (ZMod 3) ↥ψ.range = 5 := by
    rw [hV, hkerfin] at hrk
    omega
  have hcod5 : Module.finrank (ZMod 3) (Fin 5 → ZMod 3) = 5 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hrange_top : ψ.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrange5, hcod5]
  have hsurj : Function.Surjective ψ := LinearMap.range_eq_top.mp hrange_top
  obtain ⟨e, he⟩ := hsurj (Pi.single (0 : Fin 5) (1 : ZMod 3))
  have he' : ∀ k : Fin 5, α k e = if k = 0 then 1 else 0 := by
    intro k
    have h1 : α k e = (Pi.single (0 : Fin 5) (1 : ZMod 3) : Fin 5 → ZMod 3) k := by
      have := congrFun he k
      simpa [ψ] using this
    rw [h1]
    by_cases hk : k = 0
    · subst hk; simp
    · rw [Pi.single_eq_of_ne hk]; simp [hk]
  let bfun : Fin 6 → V := ![h 0, h 1, h 2, h 3, e, x]
  have hbh0 : bfun 0 = h 0 := by simp [bfun]
  have hbh1 : bfun 1 = h 1 := by simp [bfun]
  have hbh2 : bfun 2 = h 2 := by simp [bfun]
  have hbh3 : bfun 3 = h 3 := by simp [bfun]
  have hbe : bfun 4 = e := by simp [bfun]
  have hbx : bfun 5 = x := by simp [bfun]
  have hbα : ∀ (k : Fin 5) (j : Fin 6),
      α k (bfun j) =
        (if j = 0 then (CartanMatrix.A 5 k 0 : ZMod 3)
         else if j = 1 then (CartanMatrix.A 5 k 1 : ZMod 3)
         else if j = 2 then (CartanMatrix.A 5 k 2 : ZMod 3)
         else if j = 3 then (CartanMatrix.A 5 k 3 : ZMod 3)
         else if j = 4 then (if k = 0 then 1 else 0) else 0) := by
    intro k j
    fin_cases j <;> simp [bfun, hfr.pair, hfr.x_ker, he']
  have hb_lin : LinearIndependent (ZMod 3) bfun := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have key : ∀ k : Fin 5, (∑ j : Fin 6, g j • α k (bfun j)) = 0 := by
      intro k
      have h := congrArg (α k) hg
      simpa only [map_sum, map_smul, map_zero] using h
    have row4 : (∑ j : Fin 6, g j • α 4 (bfun j)) = g 3 • (2 : ZMod 3) := by
      rw [Fin.sum_univ_six]
      have h0 : α 4 (bfun 0) = 0 := by rw [hbh0, hfr.pair]; decide
      have h1 : α 4 (bfun 1) = 0 := by rw [hbh1, hfr.pair]; decide
      have h2 : α 4 (bfun 2) = 0 := by rw [hbh2, hfr.pair]; decide
      have h3 : α 4 (bfun 3) = 2 := by rw [hbh3, hfr.pair]; decide
      have h4 : α 4 (bfun 4) = 0 := by rw [hbe, he']; decide
      have h5 : α 4 (bfun 5) = 0 := by rw [hbx, hfr.x_ker]
      rw [h0, h1, h2, h3, h4, h5]
      simp
    have hg3 : g 3 = 0 := by
      have h := key 4
      rw [row4] at h
      exact (smul_eq_zero.mp h).resolve_right (by decide)
    have row3 : (∑ j : Fin 6, g j • α 3 (bfun j)) =
        g 2 • (2 : ZMod 3) + g 3 • (2 : ZMod 3) := by
      rw [Fin.sum_univ_six]
      have h0 : α 3 (bfun 0) = 0 := by rw [hbh0, hfr.pair]; decide
      have h1 : α 3 (bfun 1) = 0 := by rw [hbh1, hfr.pair]; decide
      have h2 : α 3 (bfun 2) = 2 := by rw [hbh2, hfr.pair]; decide
      have h3 : α 3 (bfun 3) = 2 := by rw [hbh3, hfr.pair]; decide
      have h4 : α 3 (bfun 4) = 0 := by rw [hbe, he']; decide
      have h5 : α 3 (bfun 5) = 0 := by rw [hbx, hfr.x_ker]
      rw [h0, h1, h2, h3, h4, h5]
      simp
    have hg2 : g 2 = 0 := by
      have h := key 3
      rw [row3] at h
      rw [hg3, zero_smul, add_zero] at h
      exact (smul_eq_zero.mp h).resolve_right (by decide)
    have row2 : (∑ j : Fin 6, g j • α 2 (bfun j)) =
        g 1 • (2 : ZMod 3) + g 2 • (2 : ZMod 3) + g 3 • (2 : ZMod 3) := by
      rw [Fin.sum_univ_six]
      have h0 : α 2 (bfun 0) = 0 := by rw [hbh0, hfr.pair]; decide
      have h1 : α 2 (bfun 1) = 2 := by rw [hbh1, hfr.pair]; decide
      have h2 : α 2 (bfun 2) = 2 := by rw [hbh2, hfr.pair]; decide
      have h3 : α 2 (bfun 3) = 2 := by rw [hbh3, hfr.pair]; decide
      have h4 : α 2 (bfun 4) = 0 := by rw [hbe, he']; decide
      have h5 : α 2 (bfun 5) = 0 := by rw [hbx, hfr.x_ker]
      rw [h0, h1, h2, h3, h4, h5]
      simp
    have hg1 : g 1 = 0 := by
      have h := key 2
      rw [row2] at h
      simp [hg2, hg3] at h
      exact h.resolve_right (by decide)
    have row1 : (∑ j : Fin 6, g j • α 1 (bfun j)) =
        g 0 • (2 : ZMod 3) + g 1 • (2 : ZMod 3) + g 2 • (2 : ZMod 3) := by
      rw [Fin.sum_univ_six]
      have h0 : α 1 (bfun 0) = 2 := by rw [hbh0, hfr.pair]; decide
      have h1 : α 1 (bfun 1) = 2 := by rw [hbh1, hfr.pair]; decide
      have h2 : α 1 (bfun 2) = 2 := by rw [hbh2, hfr.pair]; decide
      have h3 : α 1 (bfun 3) = 0 := by rw [hbh3, hfr.pair]; decide
      have h4 : α 1 (bfun 4) = 0 := by rw [hbe, he']; decide
      have h5 : α 1 (bfun 5) = 0 := by rw [hbx, hfr.x_ker]
      rw [h0, h1, h2, h3, h4, h5]
      simp
    have hg0 : g 0 = 0 := by
      have h := key 1
      rw [row1] at h
      simp [hg1, hg2] at h
      exact h.resolve_right (by decide)
    have row0 : (∑ j : Fin 6, g j • α 0 (bfun j)) =
        g 0 • (2 : ZMod 3) + g 1 • (2 : ZMod 3) + g 4 • (1 : ZMod 3) := by
      rw [Fin.sum_univ_six]
      have h0 : α 0 (bfun 0) = 2 := by rw [hbh0, hfr.pair]; decide
      have h1 : α 0 (bfun 1) = 2 := by rw [hbh1, hfr.pair]; decide
      have h2 : α 0 (bfun 2) = 0 := by rw [hbh2, hfr.pair]; decide
      have h3 : α 0 (bfun 3) = 0 := by rw [hbh3, hfr.pair]; decide
      have h4 : α 0 (bfun 4) = 1 := by rw [hbe, he']; decide
      have h5 : α 0 (bfun 5) = 0 := by rw [hbx, hfr.x_ker]
      rw [h0, h1, h2, h3, h4, h5]
      simp
    have hg4 : g 4 = 0 := by
      have h := key 0
      rw [row0] at h
      simp [hg0, hg1] at h
      exact h
    have hg5 : g 5 = 0 := by
      have h := hg
      have row5 : (∑ j : Fin 6, g j • bfun j) = g 5 • bfun 5 := by
        refine Finset.sum_eq_single 5 ?_ ?_
        · intro j _ hj
          fin_cases j
          · simp [hg0]
          · simp [hg1]
          · simp [hg2]
          · simp [hg3]
          · simp [hg4]
          · exact absurd rfl hj
        · intro hh; exact absurd (Finset.mem_univ 5) hh
      rw [row5] at h
      rw [hbx] at h
      exact (smul_eq_zero.mp h).resolve_right hfr.x_ne
    intro i
    fin_cases i <;> assumption
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
  have hαb_eval : ∀ (i : Fin 5) (j : Fin 6),
      α i (b j) = ((a5DepPt ()).vec (a5DepF i)) j := by
    intro i j
    rw [hb_apply j, hbα]
    fin_cases j <;> fin_cases i <;> decide
  refine ⟨b.equivFun, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change b.equivFun (h 0) = (a5DepPt ()).vec (a5DepH 0)
      have hi : h 0 = b (0 : Fin 6) := by rw [hb_apply]; exact hbh0.symm
      rw [hi, hbε]
      funext j; fin_cases j <;> decide
    · change b.equivFun (h 1) = (a5DepPt ()).vec (a5DepH 1)
      have hi : h 1 = b (1 : Fin 6) := by rw [hb_apply]; exact hbh1.symm
      rw [hi, hbε]
      funext j; fin_cases j <;> decide
    · change b.equivFun (h 2) = (a5DepPt ()).vec (a5DepH 2)
      have hi : h 2 = b (2 : Fin 6) := by rw [hb_apply]; exact hbh2.symm
      rw [hi, hbε]
      funext j; fin_cases j <;> decide
    · change b.equivFun (h 3) = (a5DepPt ()).vec (a5DepH 3)
      have hi : h 3 = b (3 : Fin 6) := by rw [hb_apply]; exact hbh3.symm
      rw [hi, hbε]
      funext j; fin_cases j <;> decide
    · change b.equivFun (h 4) = (a5DepPt ()).vec (a5DepH 4)
      have h0 : h 0 = b (0 : Fin 6) := by rw [hb_apply]; exact hbh0.symm
      have h1 : h 1 = b (1 : Fin 6) := by rw [hb_apply]; exact hbh1.symm
      have h3 : h 3 = b (3 : Fin 6) := by rw [hb_apply]; exact hbh3.symm
      rw [h4rel, h0, h1, h3]
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
