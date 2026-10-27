module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112ClassA
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112ClassD
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112ClassBC

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def ggQ2xKDg_succAboveEquiv (m : ℕ) (p : Fin (m + 1)) :
    Fin m ≃ {i : Fin (m + 1) // i ≠ p} :=
  Equiv.ofBijective
    (fun i => (⟨p.succAbove i, p.succAbove_ne i⟩ : {i : Fin (m + 1) // i ≠ p}))
    ⟨fun _ _ hij => Fin.succAbove_right_injective (congrArg Subtype.val hij), fun y => by
      obtain ⟨i, hi⟩ := show y.1 ∈ Set.range p.succAbove from by
        rw [Fin.range_succAbove]; exact y.2
      exact ⟨i, Subtype.ext hi⟩⟩

private lemma ggQ2xKDg_not_existsUnique_two {α : Type*} {p : α → Prop} {x y : α}
    (hx : p x) (hy : p y) (hxy : x ≠ y) : ¬ (∃! z, p z) := by
  rintro ⟨z, hz, huniq⟩
  exact hxy ((huniq x hx).trans (huniq y hy).symm)

private lemma ggQ2xKDg_E6_a0_noKernel :
    ¬ (∃ κ : {i : Fin 6 // i ≠ (0 : Fin 6)} → ZMod 3,
        κ ≠ 0 ∧ ∀ i : {i : Fin 6 // i ≠ 0}, ∑ j : {i : Fin 6 // i ≠ 0},
          ((CartanMatrix.E 6 i j : ℤ) : ZMod 3) * κ j = 0) := by
  decide +kernel

private lemma ggQ2xKDg_E6_a5_noKernel :
    ¬ (∃ κ : {i : Fin 6 // i ≠ (5 : Fin 6)} → ZMod 3,
        κ ≠ 0 ∧ ∀ i : {i : Fin 6 // i ≠ 5}, ∑ j : {i : Fin 6 // i ≠ 5},
          ((CartanMatrix.E 6 i j : ℤ) : ZMod 3) * κ j = 0) := by
  decide +kernel

private lemma ggQ2xKDg_E7_a0_noKernel :
    ¬ (∃ κ : {i : Fin 7 // i ≠ (0 : Fin 7)} → ZMod 3,
        κ ≠ 0 ∧ ∀ i : {i : Fin 7 // i ≠ 0}, ∑ j : {i : Fin 7 // i ≠ 0},
          ((CartanMatrix.E 7 i j : ℤ) : ZMod 3) * κ j = 0) := by
  decide +kernel

private lemma ggQ2xKDg_E7_a1_noKernel :
    ¬ (∃ κ : {i : Fin 7 // i ≠ (1 : Fin 7)} → ZMod 3,
        κ ≠ 0 ∧ ∀ i : {i : Fin 7 // i ≠ 1}, ∑ j : {i : Fin 7 // i ≠ 1},
          ((CartanMatrix.E 7 i j : ℤ) : ZMod 3) * κ j = 0) := by
  decide +kernel

private lemma ggQ2xKDg_E8_a0_noKernel :
    ¬ (∃ κ : {i : Fin 8 // i ≠ (0 : Fin 8)} → ZMod 3,
        κ ≠ 0 ∧ ∀ i : {i : Fin 8 // i ≠ 0}, ∑ j : {i : Fin 8 // i ≠ 0},
          ((CartanMatrix.E 8 i j : ℤ) : ZMod 3) * κ j = 0) := by
  decide +kernel

private lemma ggQ2xKDg_E8_a1_noKernel :
    ¬ (∃ κ : {i : Fin 8 // i ≠ (1 : Fin 8)} → ZMod 3,
        κ ≠ 0 ∧ ∀ i : {i : Fin 8 // i ≠ 1}, ∑ j : {i : Fin 8 // i ≠ 1},
          ((CartanMatrix.E 8 i j : ℤ) : ZMod 3) * κ j = 0) := by
  decide +kernel

private lemma ggQ2xKDg_E8_a7_noKernel :
    ¬ (∃ κ : {i : Fin 8 // i ≠ (7 : Fin 8)} → ZMod 3,
        κ ≠ 0 ∧ ∀ i : {i : Fin 8 // i ≠ 7}, ∑ j : {i : Fin 8 // i ≠ 7},
          ((CartanMatrix.E 8 i j : ℤ) : ZMod 3) * κ j = 0) := by
  decide +kernel

private theorem ggQ2xKD_class_E {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8) (a₀ : Fin n)
    (h : ggQ2xKD_ClassHyp n (CartanMatrix.E n) a₀) :
    ggQ2xKD_ClassConcl n (CartanMatrix.E n) a₀ := by
  rcases hn with rfl | rfl | rfl
  · fin_cases a₀
    · exact absurd h.2.2 ggQ2xKDg_E6_a0_noKernel
    · refine Or.inl ⟨2, by norm_num, ggQ2xKDg_succAboveEquiv 5 1, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j <;> decide +kernel
    · exact absurd h.1 (ggQ2xKDg_not_existsUnique_two
        (show (0 : Fin 6) ≠ 2 ∧ CartanMatrix.E 6 2 0 ≠ 0 by decide +kernel)
        (show (3 : Fin 6) ≠ 2 ∧ CartanMatrix.E 6 2 3 ≠ 0 by decide +kernel)
        (by decide +kernel))
    · exact absurd h.1 (ggQ2xKDg_not_existsUnique_two
        (show (1 : Fin 6) ≠ 3 ∧ CartanMatrix.E 6 3 1 ≠ 0 by decide +kernel)
        (show (2 : Fin 6) ≠ 3 ∧ CartanMatrix.E 6 3 2 ≠ 0 by decide +kernel)
        (by decide +kernel))
    · exact absurd h.1 (ggQ2xKDg_not_existsUnique_two
        (show (3 : Fin 6) ≠ 4 ∧ CartanMatrix.E 6 4 3 ≠ 0 by decide +kernel)
        (show (5 : Fin 6) ≠ 4 ∧ CartanMatrix.E 6 4 5 ≠ 0 by decide +kernel)
        (by decide +kernel))
    · exact absurd h.2.2 ggQ2xKDg_E6_a5_noKernel
  · fin_cases a₀
    · exact absurd h.2.2 ggQ2xKDg_E7_a0_noKernel
    · exact absurd h.2.2 ggQ2xKDg_E7_a1_noKernel
    · exact absurd h.1 (ggQ2xKDg_not_existsUnique_two
        (show (0 : Fin 7) ≠ 2 ∧ CartanMatrix.E 7 2 0 ≠ 0 by decide +kernel)
        (show (3 : Fin 7) ≠ 2 ∧ CartanMatrix.E 7 2 3 ≠ 0 by decide +kernel)
        (by decide +kernel))
    · exact absurd h.1 (ggQ2xKDg_not_existsUnique_two
        (show (1 : Fin 7) ≠ 3 ∧ CartanMatrix.E 7 3 1 ≠ 0 by decide +kernel)
        (show (2 : Fin 7) ≠ 3 ∧ CartanMatrix.E 7 3 2 ≠ 0 by decide +kernel)
        (by decide +kernel))
    · exact absurd h.1 (ggQ2xKDg_not_existsUnique_two
        (show (3 : Fin 7) ≠ 4 ∧ CartanMatrix.E 7 4 3 ≠ 0 by decide +kernel)
        (show (5 : Fin 7) ≠ 4 ∧ CartanMatrix.E 7 4 5 ≠ 0 by decide +kernel)
        (by decide +kernel))
    · exact absurd h.1 (ggQ2xKDg_not_existsUnique_two
        (show (4 : Fin 7) ≠ 5 ∧ CartanMatrix.E 7 5 4 ≠ 0 by decide +kernel)
        (show (6 : Fin 7) ≠ 5 ∧ CartanMatrix.E 7 5 6 ≠ 0 by decide +kernel)
        (by decide +kernel))
    · refine Or.inr ⟨ggQ2xKDg_succAboveEquiv 6 6, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j <;> decide +kernel
  · fin_cases a₀
    · exact absurd h.2.2 ggQ2xKDg_E8_a0_noKernel
    · exact absurd h.2.2 ggQ2xKDg_E8_a1_noKernel
    · exact absurd h.1 (ggQ2xKDg_not_existsUnique_two
        (show (0 : Fin 8) ≠ 2 ∧ CartanMatrix.E 8 2 0 ≠ 0 by decide +kernel)
        (show (3 : Fin 8) ≠ 2 ∧ CartanMatrix.E 8 2 3 ≠ 0 by decide +kernel)
        (by decide +kernel))
    · exact absurd h.1 (ggQ2xKDg_not_existsUnique_two
        (show (1 : Fin 8) ≠ 3 ∧ CartanMatrix.E 8 3 1 ≠ 0 by decide +kernel)
        (show (2 : Fin 8) ≠ 3 ∧ CartanMatrix.E 8 3 2 ≠ 0 by decide +kernel)
        (by decide +kernel))
    · exact absurd h.1 (ggQ2xKDg_not_existsUnique_two
        (show (3 : Fin 8) ≠ 4 ∧ CartanMatrix.E 8 4 3 ≠ 0 by decide +kernel)
        (show (5 : Fin 8) ≠ 4 ∧ CartanMatrix.E 8 4 5 ≠ 0 by decide +kernel)
        (by decide +kernel))
    · exact absurd h.1 (ggQ2xKDg_not_existsUnique_two
        (show (4 : Fin 8) ≠ 5 ∧ CartanMatrix.E 8 5 4 ≠ 0 by decide +kernel)
        (show (6 : Fin 8) ≠ 5 ∧ CartanMatrix.E 8 5 6 ≠ 0 by decide +kernel)
        (by decide +kernel))
    · exact absurd h.1 (ggQ2xKDg_not_existsUnique_two
        (show (5 : Fin 8) ≠ 6 ∧ CartanMatrix.E 8 6 5 ≠ 0 by decide +kernel)
        (show (7 : Fin 8) ≠ 6 ∧ CartanMatrix.E 8 6 7 ≠ 0 by decide +kernel)
        (by decide +kernel))
    · exact absurd h.2.2 ggQ2xKDg_E8_a7_noKernel

private noncomputable def ggQ2xKDc_subtypeEquiv {n : ℕ} (D : GGQ2Lin 3) (e : Fin n ≃ D.ι) :
    {i : Fin n // i ≠ e.symm D.a} ≃ {k // k ≠ D.a} :=
  Equiv.subtypeEquiv e (fun i => (not_congr (Equiv.apply_eq_iff_eq_symm_apply e)).symm)

private theorem ggQ2xKDc_kernel (D : GGQ2Lin 3) (xV : D.V) (hx0 : xV ≠ 0)
    (hspan : xV ∈ Submodule.span (ZMod 3) (Set.range fun i : {k // k ≠ D.a} => D.coroot i))
    (hxα : ∀ j : {k // k ≠ D.a}, D.root j xV = 0) :
    ∃ κ : {k // k ≠ D.a} → ZMod 3, κ ≠ 0 ∧
      ∀ i : {k // k ≠ D.a}, ∑ j : {k // k ≠ D.a}, (D.cartan i j : ZMod 3) * κ j = 0 := by
  rw [Submodule.mem_span_range_iff_exists_fun] at hspan
  obtain ⟨κ, hκsum⟩ := hspan
  have hκne : κ ≠ 0 := by
    intro h0
    apply hx0
    rw [← hκsum, h0]
    simp
  refine ⟨κ, hκne, fun i => ?_⟩
  have h := congrArg (D.root i) hκsum
  have hzero : ∑ j : {k // k ≠ D.a}, κ j * (D.cartan i j : ZMod 3) = 0 := by
    simpa only [map_sum, map_smul, smul_eq_mul, D.pairing, hxα i] using h
  calc ∑ j : {k // k ≠ D.a}, (D.cartan i j : ZMod 3) * κ j
      = ∑ j : {k // k ≠ D.a}, κ j * (D.cartan i j : ZMod 3) :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = 0 := hzero

private theorem ggQ2xKDc_classHyp_of {n : ℕ} {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (D : GGQ2Lin 3) (e : Fin n ≃ D.ι)
    (hc : ∀ i j, D.cartan (e i) (e j) = C₀ i j)
    (hker : ∃ κ : {k // k ≠ D.a} → ZMod 3, κ ≠ 0 ∧
      ∀ i : {k // k ≠ D.a}, ∑ j : {k // k ≠ D.a}, (D.cartan i j : ZMod 3) * κ j = 0)
    (hcard : 3 ≤ n - 1) : ggQ2xKD_ClassHyp n C₀ (e.symm D.a) := by
  let Φ := ggQ2xKDc_subtypeEquiv D e
  refine ⟨?_, hcard, ?_⟩
  · obtain ⟨c₀, hc₀, huniq⟩ := D.a_leaf
    refine ⟨e.symm c₀, ⟨?_, ?_⟩, ?_⟩
    · intro h
      exact hc₀.1 (e.symm.injective h)
    · rw [← hc (e.symm D.a) (e.symm c₀)]
      simpa using hc₀.2
    · rintro c ⟨hcne, hcz⟩
      have h1 : e c ≠ D.a := fun h => hcne (by
        have := congrArg e.symm h
        simpa using this)
      have h2 : D.cartan D.a (e c) ≠ 0 := by
        have hh : D.cartan (e (e.symm D.a)) (e c) = C₀ (e.symm D.a) c := hc (e.symm D.a) c
        rw [Equiv.apply_symm_apply] at hh
        rw [hh]
        exact hcz
      have h3 : e c = c₀ := huniq (e c) ⟨h1, h2⟩
      have := congrArg e.symm h3
      simpa using this
  · obtain ⟨κ, hκne, hκsum⟩ := hker
    refine ⟨fun i => κ (Φ i), ?_, ?_⟩
    · intro h0
      apply hκne
      funext k
      obtain ⟨i, rfl⟩ := Φ.surjective k
      exact congrFun h0 i
    · intro i
      have hcongr : ∑ j : {j : Fin n // j ≠ e.symm D.a}, (C₀ i j : ZMod 3) * κ (Φ j)
          = ∑ j : {j : Fin n // j ≠ e.symm D.a},
              (D.cartan (e i.1) (e j.1) : ZMod 3) * κ (Φ j) :=
        Finset.sum_congr rfl fun j _ => by rw [← hc i.1 j.1]
      have hre : ∑ j : {j : Fin n // j ≠ e.symm D.a},
            (D.cartan (e i.1) (e j.1) : ZMod 3) * κ (Φ j)
          = ∑ k : {k // k ≠ D.a}, (D.cartan (e i.1) k.1 : ZMod 3) * κ k :=
        Equiv.sum_comp Φ (fun k : {k // k ≠ D.a} =>
          (D.cartan (e i.1) k.1 : ZMod 3) * κ k)
      rw [hcongr, hre]
      exact hκsum ⟨e i.1, fun h => i.2 (by
        have := congrArg e.symm h
        simpa using this)⟩

private theorem ggQ2xKDc_concl_of {n : ℕ} {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (D : GGQ2Lin 3) (e : Fin n ≃ D.ι)
    (hc : ∀ i j, D.cartan (e i) (e j) = C₀ i j)
    (h : ggQ2xKD_ClassConcl n C₀ (e.symm D.a)) :
    (∃ k : ℕ, 2 ≤ k ∧ ∃ e' : Fin (3 * k - 1) ≃ {i // i ≠ D.a},
        ∀ i j, D.cartan (e' i) (e' j) = CartanMatrix.A (3 * k - 1) i j) ∨
      (∃ e' : Fin 6 ≃ {i // i ≠ D.a}, ∀ i j, D.cartan (e' i) (e' j) = CartanMatrix.E 6 i j) := by
  let Φ := ggQ2xKDc_subtypeEquiv D e
  rcases h with ⟨k, hk, f, hf⟩ | ⟨f, hf⟩
  · refine Or.inl ⟨k, hk, f.trans Φ, fun i j => ?_⟩
    show D.cartan (e (f i).1) (e (f j).1) = CartanMatrix.A (3 * k - 1) i j
    exact (hc (f i).1 (f j).1).trans (hf i j)
  · refine Or.inr ⟨f.trans Φ, fun i j => ?_⟩
    show D.cartan (e (f i).1) (e (f j).1) = CartanMatrix.E 6 i j
    exact (hc (f i).1 (f j).1).trans (hf i j)

private lemma ggQ2xKDc_F4_noKernel (a₀ : Fin 4)
    (hleaf : ∃! c, c ≠ a₀ ∧ CartanMatrix.F₄ a₀ c ≠ 0) :
    ¬ (∃ κ : {i : Fin 4 // i ≠ a₀} → ZMod 3, κ ≠ 0 ∧
      ∀ i : {i : Fin 4 // i ≠ a₀}, ∑ j : {i : Fin 4 // i ≠ a₀},
        ((CartanMatrix.F₄ i j : ℤ) : ZMod 3) * κ j = 0) := by
  fin_cases a₀
  · decide +kernel
  · exact absurd hleaf (ggQ2xKDg_not_existsUnique_two
      (show (0 : Fin 4) ≠ 1 ∧ CartanMatrix.F₄ 1 0 ≠ 0 by decide +kernel)
      (show (2 : Fin 4) ≠ 1 ∧ CartanMatrix.F₄ 1 2 ≠ 0 by decide +kernel)
      (by decide +kernel))
  · exact absurd hleaf (ggQ2xKDg_not_existsUnique_two
      (show (1 : Fin 4) ≠ 2 ∧ CartanMatrix.F₄ 2 1 ≠ 0 by decide +kernel)
      (show (3 : Fin 4) ≠ 2 ∧ CartanMatrix.F₄ 2 3 ≠ 0 by decide +kernel)
      (by decide +kernel))
  · decide +kernel

private lemma ggQ2xKDc_F4T_noKernel (a₀ : Fin 4)
    (hleaf : ∃! c, c ≠ a₀ ∧ CartanMatrix.F₄.transpose a₀ c ≠ 0) :
    ¬ (∃ κ : {i : Fin 4 // i ≠ a₀} → ZMod 3, κ ≠ 0 ∧
      ∀ i : {i : Fin 4 // i ≠ a₀}, ∑ j : {i : Fin 4 // i ≠ a₀},
        ((CartanMatrix.F₄.transpose i j : ℤ) : ZMod 3) * κ j = 0) := by
  fin_cases a₀
  · decide +kernel
  · exact absurd hleaf (ggQ2xKDg_not_existsUnique_two
      (show (0 : Fin 4) ≠ 1 ∧ CartanMatrix.F₄.transpose 1 0 ≠ 0 by decide +kernel)
      (show (2 : Fin 4) ≠ 1 ∧ CartanMatrix.F₄.transpose 1 2 ≠ 0 by decide +kernel)
      (by decide +kernel))
  · exact absurd hleaf (ggQ2xKDg_not_existsUnique_two
      (show (1 : Fin 4) ≠ 2 ∧ CartanMatrix.F₄.transpose 2 1 ≠ 0 by decide +kernel)
      (show (3 : Fin 4) ≠ 2 ∧ CartanMatrix.F₄.transpose 2 3 ≠ 0 by decide +kernel)
      (by decide +kernel))
  · decide +kernel

private lemma ggQ2xKDc_F4_false (a₀ : Fin 4) (h : ggQ2xKD_ClassHyp 4 CartanMatrix.F₄ a₀) :
    False :=
  ggQ2xKDc_F4_noKernel a₀ h.1 h.2.2

private lemma ggQ2xKDc_F4T_false (a₀ : Fin 4)
    (h : ggQ2xKD_ClassHyp 4 CartanMatrix.F₄.transpose a₀) : False :=
  ggQ2xKDc_F4T_noKernel a₀ h.1 h.2.2

theorem GGQ2Lin.compl_leaf_A_or_E6_of_ker (D : GGQ2Lin 3)
    (hker : ∃ κ : {k // k ≠ D.a} → ZMod 3, κ ≠ 0 ∧
      ∀ i : {k // k ≠ D.a}, ∑ j : {k // k ≠ D.a}, (D.cartan i j : ZMod 3) * κ j = 0)
    (hcard : 3 ≤ Fintype.card {k // k ≠ D.a}) :
    (∃ k : ℕ, 2 ≤ k ∧ ∃ e : Fin (3 * k - 1) ≃ {i // i ≠ D.a},
        ∀ i j, D.cartan (e i) (e j) = CartanMatrix.A (3 * k - 1) i j) ∨
      (∃ e : Fin 6 ≃ {i // i ≠ D.a}, ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 6 i j) := by
  rcases ggIntCartan_models D.isWeyl D.isCartan with
    ⟨n, e, hn, hABCD⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · have hcardn : 3 ≤ n - 1 := by
      have h1 : Fintype.card {i : Fin n // i ≠ e.symm D.a} = Fintype.card {k // k ≠ D.a} :=
        Fintype.card_congr (ggQ2xKDc_subtypeEquiv D e)
      have h2 : Fintype.card {i : Fin n // i ≠ e.symm D.a} = n - 1 := by
        have h := Set.card_ne_eq (e.symm D.a)
        rw [Fintype.card_fin] at h
        exact h
      omega
    rcases hABCD with hA | ⟨hn2, hB | hC⟩ | ⟨hn4, hD⟩
    · exact ggQ2xKDc_concl_of D e hA
        (ggQ2xKD_class_A (e.symm D.a) (ggQ2xKDc_classHyp_of D e hA hker hcardn))
    · exact ggQ2xKDc_concl_of D e hB
        (ggQ2xKD_class_B (e.symm D.a) (ggQ2xKDc_classHyp_of D e hB hker hcardn))
    · exact ggQ2xKDc_concl_of D e hC
        (ggQ2xKD_class_C (e.symm D.a) (ggQ2xKDc_classHyp_of D e hC hker hcardn))
    · exact ggQ2xKDc_concl_of D e hD
        (ggQ2xKD_class_D hn4 (e.symm D.a) (ggQ2xKDc_classHyp_of D e hD hker hcardn))
  · exact ggQ2xKDc_concl_of D e hE6
      (ggQ2xKD_class_E (Or.inl rfl) (e.symm D.a)
        (ggQ2xKDc_classHyp_of D e hE6 hker (by norm_num)))
  · exact ggQ2xKDc_concl_of D e hE7
      (ggQ2xKD_class_E (Or.inr (Or.inl rfl)) (e.symm D.a)
        (ggQ2xKDc_classHyp_of D e hE7 hker (by norm_num)))
  · exact ggQ2xKDc_concl_of D e hE8
      (ggQ2xKD_class_E (Or.inr (Or.inr rfl)) (e.symm D.a)
        (ggQ2xKDc_classHyp_of D e hE8 hker (by norm_num)))
  · rcases hF4 with hdirect | htrans
    · exact (ggQ2xKDc_F4_false (e.symm D.a)
        (ggQ2xKDc_classHyp_of D e hdirect hker (by norm_num))).elim
    · exact (ggQ2xKDc_F4T_false (e.symm D.a)
        (ggQ2xKDc_classHyp_of D e htrans hker (by norm_num))).elim
  · have hcι : Fintype.card D.ι = 2 := by
      rw [← Fintype.card_fin 2]
      exact Fintype.card_congr e.symm
    have hsub : Fintype.card {k // k ≠ D.a} = 1 := by
      have h : Fintype.card {k // k ≠ D.a} = Fintype.card D.ι - 1 := Set.card_ne_eq D.a
      omega
    omega

theorem GGQ2Lin.compl_leaf_A_or_E6 (D : GGQ2Lin 3) (xV : D.V) (hx0 : xV ≠ 0)
    (hspan : xV ∈ Submodule.span (ZMod 3) (Set.range fun i : {k // k ≠ D.a} => D.coroot i))
    (hxα : ∀ j : {k // k ≠ D.a}, D.root j xV = 0)
    (hcard : 3 ≤ Fintype.card {k // k ≠ D.a}) :
    (∃ k : ℕ, 2 ≤ k ∧ ∃ e : Fin (3 * k - 1) ≃ {i // i ≠ D.a},
        ∀ i j, D.cartan (e i) (e j) = CartanMatrix.A (3 * k - 1) i j) ∨
      (∃ e : Fin 6 ≃ {i // i ≠ D.a}, ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 6 i j) :=
  GGQ2Lin.compl_leaf_A_or_E6_of_ker D (ggQ2xKDc_kernel D xV hx0 hspan hxα) hcard
end CFSG.StandardType

end
