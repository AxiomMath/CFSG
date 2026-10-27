module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms

public section

namespace CFSG.StandardType

open Module CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private lemma ggQ2se_E7_entry (i j : Fin 7) :
    CartanMatrix.E 7 i j = Tag.E7.cartan i j := by
  fin_cases i <;> fin_cases j <;> decide

private lemma ggQ2se_E8_entry (i j : Fin 8) :
    CartanMatrix.E 8 i j = Tag.E8.cartan i j := by
  fin_cases i <;> fin_cases j <;> decide

private lemma ggQ2se_E7_offdiag (x y : Fin 7) (h : x ≠ y) :
    CartanMatrix.E 7 x y = -1 ∨ CartanMatrix.E 7 x y = 0 := by
  fin_cases x <;> fin_cases y <;> simp_all <;> decide

private lemma ggQ2se_E8_offdiag (x y : Fin 8) (h : x ≠ y) :
    CartanMatrix.E 8 x y = -1 ∨ CartanMatrix.E 8 x y = 0 := by
  fin_cases x <;> fin_cases y <;> simp_all <;> decide

private lemma ggQ2se_E7_two_iff (x y : Fin 7) :
    CartanMatrix.E 7 x y = 2 ↔ x = y := by
  fin_cases x <;> fin_cases y <;> decide

private lemma ggQ2se_E8_two_iff (x y : Fin 8) :
    CartanMatrix.E 8 x y = 2 ↔ x = y := by
  fin_cases x <;> fin_cases y <;> decide

private lemma ggQ2se_E7_mod3_trichotomy (x y : Fin 7) :
    (CartanMatrix.E 7 x y : ZMod 3) = 0 ∨ (CartanMatrix.E 7 x y : ZMod 3) = 2 := by
  fin_cases x <;> fin_cases y <;> decide

private lemma ggQ2se_E8_mod3_trichotomy (x y : Fin 8) :
    (CartanMatrix.E 8 x y : ZMod 3) = 0 ∨ (CartanMatrix.E 8 x y : ZMod 3) = 2 := by
  fin_cases x <;> fin_cases y <;> decide

private lemma ggQ2se_mul_eq_zero {a b : ZMod 3} (ha : a ≠ 0) (h : a * b = 0) :
    b = 0 := by
  revert a b
  decide

private lemma ggQ2se_mul_two_ne_zero {a : ZMod 3} (ha : a ≠ 0) : a * 2 ≠ 0 := by
  revert a
  decide

private lemma ggQ2se_one_or_neg_one {x : ZMod 3} (h : x ≠ 0) :
    x = 1 ∨ x = -1 := by
  revert x
  decide

private lemma ggQ2se_E7_mod3_pres (σ : Equiv.Perm (Fin 7)) (ν : Fin 7 → ZMod 3)
    (hν : ∀ i, ν i ≠ 0)
    (hrel : ∀ i j, ν i * (CartanMatrix.E 7 i j : ZMod 3) =
      ν j * (CartanMatrix.E 7 (σ i) (σ j) : ZMod 3)) :
    ∀ i j, (CartanMatrix.E 7 (σ i) (σ j) : ZMod 3) = (CartanMatrix.E 7 i j : ZMod 3) := by
  intro i j
  rcases ggQ2se_E7_mod3_trichotomy i j with h | h
  · have h0 : ν j * (CartanMatrix.E 7 (σ i) (σ j) : ZMod 3) = 0 := by
      rw [← hrel i j, h, mul_zero]
    have h1 := ggQ2se_mul_eq_zero (hν j) h0
    rw [h1, h]
  · have h2 : (CartanMatrix.E 7 (σ i) (σ j) : ZMod 3) ≠ 0 := by
      intro hc
      have hh : ν i * (CartanMatrix.E 7 i j : ZMod 3) = 0 := by rw [hrel i j, hc, mul_zero]
      rw [h] at hh
      exact ggQ2se_mul_two_ne_zero (hν i) hh
    rcases ggQ2se_E7_mod3_trichotomy (σ i) (σ j) with hc | hc
    · exact absurd hc h2
    · rw [hc, h]

private lemma ggQ2se_E8_mod3_pres (σ : Equiv.Perm (Fin 8)) (ν : Fin 8 → ZMod 3)
    (hν : ∀ i, ν i ≠ 0)
    (hrel : ∀ i j, ν i * (CartanMatrix.E 8 i j : ZMod 3) =
      ν j * (CartanMatrix.E 8 (σ i) (σ j) : ZMod 3)) :
    ∀ i j, (CartanMatrix.E 8 (σ i) (σ j) : ZMod 3) = (CartanMatrix.E 8 i j : ZMod 3) := by
  intro i j
  rcases ggQ2se_E8_mod3_trichotomy i j with h | h
  · have h0 : ν j * (CartanMatrix.E 8 (σ i) (σ j) : ZMod 3) = 0 := by
      rw [← hrel i j, h, mul_zero]
    have h1 := ggQ2se_mul_eq_zero (hν j) h0
    rw [h1, h]
  · have h2 : (CartanMatrix.E 8 (σ i) (σ j) : ZMod 3) ≠ 0 := by
      intro hc
      have hh : ν i * (CartanMatrix.E 8 i j : ZMod 3) = 0 := by rw [hrel i j, hc, mul_zero]
      rw [h] at hh
      exact ggQ2se_mul_two_ne_zero (hν i) hh
    rcases ggQ2se_E8_mod3_trichotomy (σ i) (σ j) with hc | hc
    · exact absurd hc h2
    · rw [hc, h]

private lemma ggQ2se_E7_full_pres (σ : Equiv.Perm (Fin 7))
    (hmod : ∀ i j, (CartanMatrix.E 7 (σ i) (σ j) : ZMod 3) = (CartanMatrix.E 7 i j : ZMod 3)) :
    ∀ i j, CartanMatrix.E 7 (σ i) (σ j) = CartanMatrix.E 7 i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [(ggQ2se_E7_two_iff _ _).mpr rfl, (ggQ2se_E7_two_iff _ _).mpr rfl]
  · have hne : σ i ≠ σ j := fun h => hij (σ.injective h)
    rcases ggQ2se_E7_offdiag i j hij with h1 | h1 <;>
      rcases ggQ2se_E7_offdiag (σ i) (σ j) hne with h2 | h2
    · rw [h1, h2]
    · exfalso
      have hh := hmod i j
      rw [h2, h1] at hh
      exact absurd hh (by decide)
    · exfalso
      have hh := hmod i j
      rw [h2, h1] at hh
      exact absurd hh (by decide)
    · rw [h1, h2]

private lemma ggQ2se_E8_full_pres (σ : Equiv.Perm (Fin 8))
    (hmod : ∀ i j, (CartanMatrix.E 8 (σ i) (σ j) : ZMod 3) = (CartanMatrix.E 8 i j : ZMod 3)) :
    ∀ i j, CartanMatrix.E 8 (σ i) (σ j) = CartanMatrix.E 8 i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [(ggQ2se_E8_two_iff _ _).mpr rfl, (ggQ2se_E8_two_iff _ _).mpr rfl]
  · have hne : σ i ≠ σ j := fun h => hij (σ.injective h)
    rcases ggQ2se_E8_offdiag i j hij with h1 | h1 <;>
      rcases ggQ2se_E8_offdiag (σ i) (σ j) hne with h2 | h2
    · rw [h1, h2]
    · exfalso
      have hh := hmod i j
      rw [h2, h1] at hh
      exact absurd hh (by decide)
    · exfalso
      have hh := hmod i j
      rw [h2, h1] at hh
      exact absurd hh (by decide)
    · rw [h1, h2]

private lemma ggQ2se_E7_perm_eq_one (σ : Equiv.Perm (Fin 7))
    (hmod : ∀ i j, (CartanMatrix.E 7 (σ i) (σ j) : ZMod 3) = (CartanMatrix.E 7 i j : ZMod 3)) :
    σ = 1 := by
  apply perm_eq_one_of_cartan_E7
  intro i j
  exact (ggQ2se_E7_entry (σ i) (σ j)).symm.trans
    ((ggQ2se_E7_full_pres σ hmod i j).trans (ggQ2se_E7_entry i j))

private lemma ggQ2se_E8_perm_eq_one (σ : Equiv.Perm (Fin 8))
    (hmod : ∀ i j, (CartanMatrix.E 8 (σ i) (σ j) : ZMod 3) = (CartanMatrix.E 8 i j : ZMod 3)) :
    σ = 1 := by
  apply perm_eq_one_of_cartan_E8
  intro i j
  exact (ggQ2se_E8_entry (σ i) (σ j)).symm.trans
    ((ggQ2se_E8_full_pres σ hmod i j).trans (ggQ2se_E8_entry i j))

private lemma ggQ2se_scalarModW_of_const {D : GGQ2Lin 3} {π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}}
    {μ : {k // k ≠ D.a} → ZMod 3} (ε : ZMod 3) (hπ : π = 1) (hμ : ∀ i, μ i = ε)
    (hne : ε ≠ 0) : D.ScalarModW D.a π μ := by
  obtain h1 | h1 := ggQ2se_one_or_neg_one hne
  · refine ⟨ε, Or.inl h1, 1, Subgroup.one_mem _, ?_⟩
    intro i
    have hi : π i = i := by rw [hπ]; rfl
    rw [hi, hμ i]
    simp
  · refine ⟨ε, Or.inr h1, 1, Subgroup.one_mem _, ?_⟩
    intro i
    have hi : π i = i := by rw [hπ]; rfl
    rw [hi, hμ i]
    simp

theorem ggQ2s5_of_E78 (D : GGQ2Lin 3)
    (hf : (∃ f : Fin 7 ≃ {k // k ≠ D.a}, ∀ i j, D.cartan (f i) (f j) = CartanMatrix.E 7 i j) ∨
      (∃ f : Fin 8 ≃ {k // k ≠ D.a}, ∀ i j, D.cartan (f i) (f j) = CartanMatrix.E 8 i j))
    {π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}} {μ : {k // k ≠ D.a} → ZMod 3}
    (h : D.ScaledAut D.a π μ) : D.ScalarModW D.a π μ := by
  obtain ⟨hμne, hrel0⟩ := h
  rcases hf with ⟨f, hf⟩ | ⟨f, hf⟩
  ·
    let π' : Equiv.Perm (Fin 7) := (f.trans π).trans f.symm
    let ν : Fin 7 → ZMod 3 := fun i => μ (f i)
    have hν : ∀ i, ν i ≠ 0 := fun i => hμne (f i)
    have hrel : ∀ i j, ν i * (CartanMatrix.E 7 i j : ZMod 3) =
        ν j * (CartanMatrix.E 7 (π' i) (π' j) : ZMod 3) := by
      intro i j
      have h1 : π (f i) = f (π' i) := by simp [π']
      have h2 : π (f j) = f (π' j) := by simp [π']
      have hh := hrel0 (f i) (f j)
      rw [hf i j, h1, h2, hf (π' i) (π' j)] at hh
      simpa [ν] using hh
    have hmod := ggQ2se_E7_mod3_pres π' ν hν hrel
    have hπ' : π' = 1 := ggQ2se_E7_perm_eq_one π' hmod
    have hπ : π = 1 := by
      ext k
      obtain ⟨i, rfl⟩ := f.surjective k
      have hi : π' i = i := by rw [hπ']; rfl
      have hsym : f.symm (π (f i)) = i := by simpa [π'] using hi
      have := congrArg Subtype.val (congrArg f hsym)
      simpa using this
    have hedge : ∀ i j : Fin 7, CartanMatrix.E 7 i j = -1 → ν i = ν j := by
      intro i j hij
      have hc : (CartanMatrix.E 7 (π' i) (π' j) : ZMod 3) = (CartanMatrix.E 7 i j : ZMod 3) :=
        hmod i j
      rw [hij] at hc
      have hh := hrel i j
      rw [hij, hc] at hh
      exact neg_inj.mp (by simpa using hh)
    have h20 : ν 2 = ν 0 := hedge 2 0 (by decide)
    have h30 : ν 3 = ν 0 := (hedge 3 2 (by decide)).trans h20
    have h10 : ν 1 = ν 0 := (hedge 1 3 (by decide)).trans h30
    have h40 : ν 4 = ν 0 := (hedge 4 3 (by decide)).trans h30
    have h50 : ν 5 = ν 0 := (hedge 5 4 (by decide)).trans h40
    have h60 : ν 6 = ν 0 := (hedge 6 5 (by decide)).trans h50
    have hconst : ∀ i : Fin 7, ν i = ν 0 := by
      intro i
      fin_cases i <;> first | rfl | assumption
    have hμconst : ∀ k : {k // k ≠ D.a}, μ k = μ (f 0) := by
      intro k
      obtain ⟨i, rfl⟩ := f.surjective k
      simpa [ν] using hconst i
    exact ggQ2se_scalarModW_of_const (μ (f 0)) hπ hμconst (hμne (f 0))
  ·
    let π' : Equiv.Perm (Fin 8) := (f.trans π).trans f.symm
    let ν : Fin 8 → ZMod 3 := fun i => μ (f i)
    have hν : ∀ i, ν i ≠ 0 := fun i => hμne (f i)
    have hrel : ∀ i j, ν i * (CartanMatrix.E 8 i j : ZMod 3) =
        ν j * (CartanMatrix.E 8 (π' i) (π' j) : ZMod 3) := by
      intro i j
      have h1 : π (f i) = f (π' i) := by simp [π']
      have h2 : π (f j) = f (π' j) := by simp [π']
      have hh := hrel0 (f i) (f j)
      rw [hf i j, h1, h2, hf (π' i) (π' j)] at hh
      simpa [ν] using hh
    have hmod := ggQ2se_E8_mod3_pres π' ν hν hrel
    have hπ' : π' = 1 := ggQ2se_E8_perm_eq_one π' hmod
    have hπ : π = 1 := by
      ext k
      obtain ⟨i, rfl⟩ := f.surjective k
      have hi : π' i = i := by rw [hπ']; rfl
      have hsym : f.symm (π (f i)) = i := by simpa [π'] using hi
      have := congrArg Subtype.val (congrArg f hsym)
      simpa using this
    have hedge : ∀ i j : Fin 8, CartanMatrix.E 8 i j = -1 → ν i = ν j := by
      intro i j hij
      have hc : (CartanMatrix.E 8 (π' i) (π' j) : ZMod 3) = (CartanMatrix.E 8 i j : ZMod 3) :=
        hmod i j
      rw [hij] at hc
      have hh := hrel i j
      rw [hij, hc] at hh
      exact neg_inj.mp (by simpa using hh)
    have h20 : ν 2 = ν 0 := hedge 2 0 (by decide)
    have h30 : ν 3 = ν 0 := (hedge 3 2 (by decide)).trans h20
    have h10 : ν 1 = ν 0 := (hedge 1 3 (by decide)).trans h30
    have h40 : ν 4 = ν 0 := (hedge 4 3 (by decide)).trans h30
    have h50 : ν 5 = ν 0 := (hedge 5 4 (by decide)).trans h40
    have h60 : ν 6 = ν 0 := (hedge 6 5 (by decide)).trans h50
    have h70 : ν 7 = ν 0 := (hedge 7 6 (by decide)).trans h60
    have hconst : ∀ i : Fin 8, ν i = ν 0 := by
      intro i
      fin_cases i <;> first | rfl | assumption
    have hμconst : ∀ k : {k // k ≠ D.a}, μ k = μ (f 0) := by
      intro k
      obtain ⟨i, rfl⟩ := f.surjective k
      simpa [ν] using hconst i
    exact ggQ2se_scalarModW_of_const (μ (f 0)) hπ hμconst (hμne (f 0))

end CFSG.StandardType

end
