module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs

public section

namespace CFSG.StandardType

open Module

private def ggQ2s4e_nbrs {n : ℕ} (X : Matrix (Fin n) (Fin n) ℤ) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun c => c ≠ x ∧ X x c ≠ 0)

private lemma ggQ2s4e_nbrs_card {n : ℕ} {X : Matrix (Fin n) (Fin n) ℤ} {x : Fin n}
    (h : ∃! c : Fin n, c ≠ x ∧ X x c ≠ 0) : (ggQ2s4e_nbrs X x).card = 1 := by
  obtain ⟨c, hc, huniq⟩ := h
  rw [Finset.card_eq_one]
  refine ⟨c, ?_⟩
  ext y
  simp only [ggQ2s4e_nbrs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hy => huniq y hy, fun hy => by rw [hy]; exact hc⟩

private lemma ggQ2s4e_leaf_fin {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {n : ℕ} (e : Fin n ≃ D.ι)
    {X : Matrix (Fin n) (Fin n) ℤ} (he : ∀ i j, D.cartan (e i) (e j) = X i j) :
    ∃! c : Fin n, c ≠ e.symm D.a ∧ X (e.symm D.a) c ≠ 0 := by
  obtain ⟨c, ⟨hcne, hcnz⟩, huniq⟩ := D.a_leaf
  refine ⟨e.symm c, ⟨?_, ?_⟩, ?_⟩
  · intro h
    apply hcne
    simpa only [e.apply_symm_apply] using congrArg e h
  · rw [← he, e.apply_symm_apply, e.apply_symm_apply]
    exact hcnz
  · intro y hy
    have h1 : e y ≠ D.a := fun hh => hy.1 (by rw [← e.symm_apply_apply y, hh])
    have h2 : D.cartan D.a (e y) ≠ 0 := by
      rw [← e.apply_symm_apply D.a, he]
      exact hy.2
    have h3 : e y = c := huniq (e y) ⟨h1, h2⟩
    rw [← e.symm_apply_apply y, h3]

private lemma ggQ2s4e_mk {m n' : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ}
    {Y : Matrix (Fin n') (Fin n') ℤ} {a₀ : Fin (m + 1)} (g : Fin n' → Fin m)
    (hg : Function.Bijective g)
    (h : ∀ i j, X (a₀.succAbove (g i)) (a₀.succAbove (g j)) = Y i j) :
    ∃ f : Fin n' ≃ {i : Fin (m + 1) // i ≠ a₀}, ∀ i j, X (f i).1 (f j).1 = Y i j := by
  refine ⟨(Equiv.ofBijective g hg).trans (finSuccAboveEquiv a₀), ?_⟩
  intro i j
  have h1 : (((Equiv.ofBijective g hg).trans (finSuccAboveEquiv a₀)) i).1
      = a₀.succAbove (g i) := rfl
  have h2 : (((Equiv.ofBijective g hg).trans (finSuccAboveEquiv a₀)) j).1
      = a₀.succAbove (g j) := rfl
  rw [h1, h2]
  exact h i j

private lemma ggQ2s4e_transfer {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {n n' : ℕ}
    (e : Fin n ≃ D.ι) {X : Matrix (Fin n) (Fin n) ℤ} (he : ∀ i j, D.cartan (e i) (e j) = X i j)
    (a₀ : Fin n) (ha₀ : e a₀ = D.a) {Y : Matrix (Fin n') (Fin n') ℤ}
    (h : ∃ f : Fin n' ≃ {i : Fin n // i ≠ a₀}, ∀ i j, X (f i).1 (f j).1 = Y i j) :
    ∃ f : Fin n' ≃ {k : D.ι // k ≠ D.a}, ∀ i j, D.cartan (f i) (f j) = Y i j := by
  obtain ⟨f₀, hf₀⟩ := h
  have hpred : ∀ i : Fin n, (i ≠ a₀) ↔ (e i ≠ D.a) := by
    intro i
    constructor
    · intro hi hei; exact hi (e.injective (by rw [hei, ha₀]))
    · intro hei hi; exact hei (by rw [hi, ha₀])
  refine ⟨f₀.trans (Equiv.subtypeEquiv (q := fun k : D.ι => k ≠ D.a) e hpred), ?_⟩
  intro i j
  have h1 : ((f₀.trans (Equiv.subtypeEquiv (q := fun k : D.ι => k ≠ D.a) e hpred)) i).1
      = e (f₀ i).1 := rfl
  have h2 : ((f₀.trans (Equiv.subtypeEquiv (q := fun k : D.ι => k ≠ D.a) e hpred)) j).1
      = e (f₀ j).1 := rfl
  rw [h1, h2, he]
  exact hf₀ i j

private lemma ggQ2s4e_leaf_E6 {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e : Fin 6 ≃ D.ι)
    (he : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 6 i j) : D.LeafModels D.a := by
  have hleaf := ggQ2s4e_leaf_fin D e he
  have hmem : e.symm D.a = 0 ∨ e.symm D.a = 1 ∨ e.symm D.a = 5 :=
    (by decide : ∀ x : Fin 6, (ggQ2s4e_nbrs (CartanMatrix.E 6) x).card = 1 →
      x = 0 ∨ x = 1 ∨ x = 5) (e.symm D.a) (ggQ2s4e_nbrs_card hleaf)
  rcases hmem with h | h | h
  · have ha₀ : e 0 = D.a := by rw [← h, e.apply_symm_apply]
    obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 0 ha₀
      (ggQ2s4e_mk (m := 5) (a₀ := 0) (Y := CartanMatrix.D 5)
        (g := ![4, 3, 2, 0, 1]) (by decide)
        (by intro i j; fin_cases i <;> fin_cases j <;> decide))
    exact Or.inl ⟨5, f, by norm_num, Or.inr (Or.inr ⟨by norm_num, hf⟩)⟩
  · have ha₀ : e 1 = D.a := by rw [← h, e.apply_symm_apply]
    obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 1 ha₀
      (ggQ2s4e_mk (m := 5) (a₀ := 1) (Y := CartanMatrix.A 5)
        (g := ![0, 1, 2, 3, 4]) (by decide)
        (by intro i j; fin_cases i <;> fin_cases j <;> decide))
    exact Or.inl ⟨5, f, by norm_num, Or.inl hf⟩
  · have ha₀ : e 5 = D.a := by rw [← h, e.apply_symm_apply]
    obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 5 ha₀
      (ggQ2s4e_mk (m := 5) (a₀ := 5) (Y := CartanMatrix.D 5)
        (g := ![0, 2, 3, 1, 4]) (by decide)
        (by intro i j; fin_cases i <;> fin_cases j <;> decide))
    exact Or.inl ⟨5, f, by norm_num, Or.inr (Or.inr ⟨by norm_num, hf⟩)⟩

private lemma ggQ2s4e_leaf_E7 {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e : Fin 7 ≃ D.ι)
    (he : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 7 i j) : D.LeafModels D.a := by
  have hleaf := ggQ2s4e_leaf_fin D e he
  have hmem : e.symm D.a = 0 ∨ e.symm D.a = 1 ∨ e.symm D.a = 6 :=
    (by decide : ∀ x : Fin 7, (ggQ2s4e_nbrs (CartanMatrix.E 7) x).card = 1 →
      x = 0 ∨ x = 1 ∨ x = 6) (e.symm D.a) (ggQ2s4e_nbrs_card hleaf)
  rcases hmem with h | h | h
  · have ha₀ : e 0 = D.a := by rw [← h, e.apply_symm_apply]
    obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 0 ha₀
      (ggQ2s4e_mk (m := 6) (a₀ := 0) (Y := CartanMatrix.D 6)
        (g := ![5, 4, 3, 2, 0, 1]) (by decide)
        (by intro i j; fin_cases i <;> fin_cases j <;> decide))
    exact Or.inl ⟨6, f, by norm_num, Or.inr (Or.inr ⟨by norm_num, hf⟩)⟩
  · have ha₀ : e 1 = D.a := by rw [← h, e.apply_symm_apply]
    obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 1 ha₀
      (ggQ2s4e_mk (m := 6) (a₀ := 1) (Y := CartanMatrix.A 6)
        (g := ![0, 1, 2, 3, 4, 5]) (by decide)
        (by intro i j; fin_cases i <;> fin_cases j <;> decide))
    exact Or.inl ⟨6, f, by norm_num, Or.inl hf⟩
  · have ha₀ : e 6 = D.a := by rw [← h, e.apply_symm_apply]
    obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 6 ha₀
      (ggQ2s4e_mk (m := 6) (a₀ := 6) (Y := CartanMatrix.E 6)
        (g := ![0, 1, 2, 3, 4, 5]) (by decide)
        (by intro i j; fin_cases i <;> fin_cases j <;> decide))
    exact Or.inr (Or.inl ⟨f, hf⟩)

private lemma ggQ2s4e_leaf_E8 {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e : Fin 8 ≃ D.ι)
    (he : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 8 i j) : D.LeafModels D.a := by
  have hleaf := ggQ2s4e_leaf_fin D e he
  have hmem : e.symm D.a = 0 ∨ e.symm D.a = 1 ∨ e.symm D.a = 7 :=
    (by decide : ∀ x : Fin 8, (ggQ2s4e_nbrs (CartanMatrix.E 8) x).card = 1 →
      x = 0 ∨ x = 1 ∨ x = 7) (e.symm D.a) (ggQ2s4e_nbrs_card hleaf)
  rcases hmem with h | h | h
  · have ha₀ : e 0 = D.a := by rw [← h, e.apply_symm_apply]
    obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 0 ha₀
      (ggQ2s4e_mk (m := 7) (a₀ := 0) (Y := CartanMatrix.D 7)
        (g := ![6, 5, 4, 3, 2, 0, 1]) (by decide)
        (by intro i j; fin_cases i <;> fin_cases j <;> decide))
    exact Or.inl ⟨7, f, by norm_num, Or.inr (Or.inr ⟨by norm_num, hf⟩)⟩
  · have ha₀ : e 1 = D.a := by rw [← h, e.apply_symm_apply]
    obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 1 ha₀
      (ggQ2s4e_mk (m := 7) (a₀ := 1) (Y := CartanMatrix.A 7)
        (g := ![0, 1, 2, 3, 4, 5, 6]) (by decide)
        (by intro i j; fin_cases i <;> fin_cases j <;> decide))
    exact Or.inl ⟨7, f, by norm_num, Or.inl hf⟩
  · have ha₀ : e 7 = D.a := by rw [← h, e.apply_symm_apply]
    obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 7 ha₀
      (ggQ2s4e_mk (m := 7) (a₀ := 7) (Y := CartanMatrix.E 7)
        (g := ![0, 1, 2, 3, 4, 5, 6]) (by decide)
        (by intro i j; fin_cases i <;> fin_cases j <;> decide))
    exact Or.inr (Or.inr (Or.inl ⟨f, hf⟩))

private lemma ggQ2s4e_leaf_F4 {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e : Fin 4 ≃ D.ι)
    (he : (∀ i j, D.cartan (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, D.cartan (e i) (e j) = CartanMatrix.F₄ j i)) : D.LeafModels D.a := by
  rcases he with he | he
  · have hleaf := ggQ2s4e_leaf_fin D e he
    have hmem : e.symm D.a = 0 ∨ e.symm D.a = 3 :=
      (by decide : ∀ x : Fin 4, (ggQ2s4e_nbrs (CartanMatrix.F₄) x).card = 1 →
        x = 0 ∨ x = 3) (e.symm D.a) (ggQ2s4e_nbrs_card hleaf)
    rcases hmem with h | h
    · have ha₀ : e 0 = D.a := by rw [← h, e.apply_symm_apply]
      obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 0 ha₀
        (ggQ2s4e_mk (m := 3) (a₀ := 0) (Y := CartanMatrix.C 3)
          (g := ![2, 1, 0]) (by decide)
          (by intro i j; fin_cases i <;> fin_cases j <;> decide))
      exact Or.inl ⟨3, f, by norm_num, Or.inr (Or.inl ⟨by norm_num, Or.inr hf⟩)⟩
    · have ha₀ : e 3 = D.a := by rw [← h, e.apply_symm_apply]
      obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 3 ha₀
        (ggQ2s4e_mk (m := 3) (a₀ := 3) (Y := CartanMatrix.B 3)
          (g := ![0, 1, 2]) (by decide)
          (by intro i j; fin_cases i <;> fin_cases j <;> decide))
      exact Or.inl ⟨3, f, by norm_num, Or.inr (Or.inl ⟨by norm_num, Or.inl hf⟩)⟩
  · have he' : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.F₄.transpose i j := by
      intro i j; rw [he]; rfl
    have hleaf := ggQ2s4e_leaf_fin D e he'
    have hmem : e.symm D.a = 0 ∨ e.symm D.a = 3 :=
      (by decide : ∀ x : Fin 4, (ggQ2s4e_nbrs (CartanMatrix.F₄.transpose) x).card = 1 →
        x = 0 ∨ x = 3) (e.symm D.a) (ggQ2s4e_nbrs_card hleaf)
    rcases hmem with h | h
    · have ha₀ : e 0 = D.a := by rw [← h, e.apply_symm_apply]
      obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he' 0 ha₀
        (ggQ2s4e_mk (m := 3) (a₀ := 0) (Y := CartanMatrix.B 3)
          (g := ![2, 1, 0]) (by decide)
          (by intro i j; fin_cases i <;> fin_cases j <;> decide))
      exact Or.inl ⟨3, f, by norm_num, Or.inr (Or.inl ⟨by norm_num, Or.inl hf⟩)⟩
    · have ha₀ : e 3 = D.a := by rw [← h, e.apply_symm_apply]
      obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he' 3 ha₀
        (ggQ2s4e_mk (m := 3) (a₀ := 3) (Y := CartanMatrix.C 3)
          (g := ![0, 1, 2]) (by decide)
          (by intro i j; fin_cases i <;> fin_cases j <;> decide))
      exact Or.inl ⟨3, f, by norm_num, Or.inr (Or.inl ⟨by norm_num, Or.inr hf⟩)⟩

private lemma ggQ2s4e_leaf_G2 {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e : Fin 2 ≃ D.ι)
    (he : (∀ i j, D.cartan (e i) (e j) = CartanMatrix.G₂ i j) ∨
      (∀ i j, D.cartan (e i) (e j) = CartanMatrix.G₂ j i)) : D.LeafModels D.a := by
  rcases he with he | he
  · have hleaf := ggQ2s4e_leaf_fin D e he
    have hmem : e.symm D.a = 0 ∨ e.symm D.a = 1 :=
      (by decide : ∀ x : Fin 2, (ggQ2s4e_nbrs (CartanMatrix.G₂) x).card = 1 →
        x = 0 ∨ x = 1) (e.symm D.a) (ggQ2s4e_nbrs_card hleaf)
    rcases hmem with h | h
    · have ha₀ : e 0 = D.a := by rw [← h, e.apply_symm_apply]
      obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 0 ha₀
        (ggQ2s4e_mk (m := 1) (a₀ := 0) (Y := CartanMatrix.A 1)
          (g := ![0]) (by decide)
          (by intro i j; fin_cases i <;> fin_cases j <;> decide))
      exact Or.inl ⟨1, f, by norm_num, Or.inl hf⟩
    · have ha₀ : e 1 = D.a := by rw [← h, e.apply_symm_apply]
      obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he 1 ha₀
        (ggQ2s4e_mk (m := 1) (a₀ := 1) (Y := CartanMatrix.A 1)
          (g := ![0]) (by decide)
          (by intro i j; fin_cases i <;> fin_cases j <;> decide))
      exact Or.inl ⟨1, f, by norm_num, Or.inl hf⟩
  · have he' : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.G₂.transpose i j := by
      intro i j; rw [he]; rfl
    have hleaf := ggQ2s4e_leaf_fin D e he'
    have hmem : e.symm D.a = 0 ∨ e.symm D.a = 1 :=
      (by decide : ∀ x : Fin 2, (ggQ2s4e_nbrs (CartanMatrix.G₂.transpose) x).card = 1 →
        x = 0 ∨ x = 1) (e.symm D.a) (ggQ2s4e_nbrs_card hleaf)
    rcases hmem with h | h
    · have ha₀ : e 0 = D.a := by rw [← h, e.apply_symm_apply]
      obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he' 0 ha₀
        (ggQ2s4e_mk (m := 1) (a₀ := 0) (Y := CartanMatrix.A 1)
          (g := ![0]) (by decide)
          (by intro i j; fin_cases i <;> fin_cases j <;> decide))
      exact Or.inl ⟨1, f, by norm_num, Or.inl hf⟩
    · have ha₀ : e 1 = D.a := by rw [← h, e.apply_symm_apply]
      obtain ⟨f, hf⟩ := ggQ2s4e_transfer D e he' 1 ha₀
        (ggQ2s4e_mk (m := 1) (a₀ := 1) (Y := CartanMatrix.A 1)
          (g := ![0]) (by decide)
          (by intro i j; fin_cases i <;> fin_cases j <;> decide))
      exact Or.inl ⟨1, f, by norm_num, Or.inl hf⟩

theorem ggQ2s4_leaf_exceptional {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    (h : (∃ e : Fin 6 ≃ D.ι, ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 6 i j) ∨
      (∃ e : Fin 7 ≃ D.ι, ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 7 i j) ∨
      (∃ e : Fin 8 ≃ D.ι, ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 8 i j) ∨
      (∃ e : Fin 4 ≃ D.ι, (∀ i j, D.cartan (e i) (e j) = CartanMatrix.F₄ i j) ∨
        (∀ i j, D.cartan (e i) (e j) = CartanMatrix.F₄ j i)) ∨
      (∃ e : Fin 2 ≃ D.ι, (∀ i j, D.cartan (e i) (e j) = CartanMatrix.G₂ i j) ∨
        (∀ i j, D.cartan (e i) (e j) = CartanMatrix.G₂ j i))) :
    D.LeafModels D.a := by
  rcases h with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · exact ggQ2s4e_leaf_E6 D e he
  · exact ggQ2s4e_leaf_E7 D e he
  · exact ggQ2s4e_leaf_E8 D e he
  · exact ggQ2s4e_leaf_F4 D e he
  · exact ggQ2s4e_leaf_G2 D e he

end CFSG.StandardType

end

