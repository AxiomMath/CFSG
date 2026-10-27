module

public import CFSG.LocalAnalysis.StandardType.GGQTwoThmB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private theorem ggQ2xCL1_two_nbrs {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {c d : D.ι}
    (hcd : c ≠ d) (hc : c ≠ D.a) (hd : d ≠ D.a)
    (hc0 : D.cartan D.a c ≠ 0) (hd0 : D.cartan D.a d ≠ 0) : False := by
  obtain ⟨c₀, ⟨-, -⟩, huniq⟩ := D.a_leaf
  exact hcd ((huniq c ⟨hc, hc0⟩).trans (huniq d ⟨hd, hd0⟩).symm)

private theorem ggQ2xCL1_nbr {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    {M₀ : CoxeterMatrix (Fin 4)} (e : Fin 4 ≃ D.ι) (hM : D.coxeter = M₀.reindex e)
    {i j : Fin 4} (hij : i ≠ j) (h3 : 3 ≤ M₀ i j) : D.cartan (e i) (e j) ≠ 0 := by
  have heij : e i ≠ e j := fun h => hij (e.injective h)
  have hMe : D.coxeter (e i) (e j) = M₀ i j := by
    rw [hM, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases D.isCartan.2 (e i) (e j) heij with ⟨hm, -, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ |
    ⟨-, h1, -⟩
  · rw [hMe] at hm; omega
  · rw [h1]; norm_num
  · intro hc; rw [hc, zero_mul] at h1; norm_num at h1
  · intro hc; rw [hc, zero_mul] at h1; norm_num at h1

private theorem ggQ2xCL_typeA (D : GGQ2Lin 3) (e : Fin 4 ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A 4).reindex e) (h4 : Fintype.card D.ι = 4)
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24)) : False := by
  obtain ⟨i, hi⟩ := e.surjective D.a
  have hmem : D.a = e 0 ∨ D.a = e 3 := by
    fin_cases i
    · exact Or.inl hi.symm
    · exfalso
      have hDa : D.a = e 1 := hi.symm
      have hc0 : D.cartan D.a (e 0) ≠ 0 := by
        rw [hDa]
        exact ggQ2xCL1_nbr D e hA (i := 1) (j := 0) (by decide) (by decide)
      have hd0 : D.cartan D.a (e 2) ≠ 0 := by
        rw [hDa]
        exact ggQ2xCL1_nbr D e hA (i := 1) (j := 2) (by decide) (by decide)
      exact ggQ2xCL1_two_nbrs D (c := e 0) (d := e 2)
        (by intro h; exact (by decide : (0 : Fin 4) ≠ 2) (e.injective h))
        (by rw [hDa]; intro h; exact (by decide : (0 : Fin 4) ≠ 1) (e.injective h))
        (by rw [hDa]; intro h; exact (by decide : (2 : Fin 4) ≠ 1) (e.injective h))
        hc0 hd0
    · exfalso
      have hDa : D.a = e 2 := hi.symm
      have hc0 : D.cartan D.a (e 3) ≠ 0 := by
        rw [hDa]
        exact ggQ2xCL1_nbr D e hA (i := 2) (j := 3) (by decide) (by decide)
      have hd0 : D.cartan D.a (e 1) ≠ 0 := by
        rw [hDa]
        exact ggQ2xCL1_nbr D e hA (i := 2) (j := 1) (by decide) (by decide)
      exact ggQ2xCL1_two_nbrs D (c := e 3) (d := e 1)
        (by intro h; exact (by decide : (3 : Fin 4) ≠ 1) (e.injective h))
        (by rw [hDa]; intro h; exact (by decide : (3 : Fin 4) ≠ 2) (e.injective h))
        (by rw [hDa]; intro h; exact (by decide : (1 : Fin 4) ≠ 2) (e.injective h))
        hc0 hd0
    · exact Or.inr hi.symm
  rcases hmem with ha | ha
  · exact hA3 ⟨h4, ggQ2_parab_card_A3 D e (Or.inl ⟨hA, Or.inl ha⟩)⟩
  · exact hA3 ⟨h4, ggQ2_parab_card_A3 D e (Or.inl ⟨hA, Or.inr ha⟩)⟩

private theorem ggQ2xCL_typeD (D : GGQ2Lin 3) (e : Fin 4 ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD 4).reindex e) (h4 : Fintype.card D.ι = 4)
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24)) : False := by
  obtain ⟨i, hi⟩ := e.surjective D.a
  have hmem : D.a = e 0 ∨ D.a = e 2 ∨ D.a = e 3 := by
    fin_cases i
    · exact Or.inl hi.symm
    · exfalso
      have hDa : D.a = e 1 := hi.symm
      have hc0 : D.cartan D.a (e 0) ≠ 0 := by
        rw [hDa]
        exact ggQ2xCL1_nbr D e hD (i := 1) (j := 0) (by decide) (by decide)
      have hd0 : D.cartan D.a (e 2) ≠ 0 := by
        rw [hDa]
        exact ggQ2xCL1_nbr D e hD (i := 1) (j := 2) (by decide) (by decide)
      exact ggQ2xCL1_two_nbrs D (c := e 0) (d := e 2)
        (by intro h; exact (by decide : (0 : Fin 4) ≠ 2) (e.injective h))
        (by rw [hDa]; intro h; exact (by decide : (0 : Fin 4) ≠ 1) (e.injective h))
        (by rw [hDa]; intro h; exact (by decide : (2 : Fin 4) ≠ 1) (e.injective h))
        hc0 hd0
    · exact Or.inr (Or.inl hi.symm)
    · exact Or.inr (Or.inr hi.symm)
  rcases hmem with ha | ha | ha
  · exact hA3 ⟨h4, ggQ2_parab_card_A3 D e (Or.inr (Or.inl ⟨hD, Or.inl ha⟩))⟩
  · exact hA3 ⟨h4, ggQ2_parab_card_A3 D e (Or.inr (Or.inl ⟨hD, Or.inr (Or.inl ha)⟩))⟩
  · exact hA3 ⟨h4, ggQ2_parab_card_A3 D e (Or.inr (Or.inl ⟨hD, Or.inr (Or.inr ha)⟩))⟩

private theorem ggQ2xCL_typeB (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 4 ≃ D.ι)
    (hB : D.coxeter = (CoxeterMatrix.B 4).reindex e) (x y : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (hy : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.b}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {y})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24))
    (hF : D.FCell A) :
    (∃ u ∈ Submodule.span (ZMod 3) {x, y}, u ≠ 0 ∧ ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ u} = Submodule.span (ZMod 3) {r u}) ∨
    (∀ φ ∈ A, ∀ w ∈ Submodule.span (ZMod 3) {x, y}, w ≠ 0 → ∃ r ∈ reflGp A,
      ∃ w' ∈ Submodule.span (ZMod 3) {x, y}, w' ≠ 0 ∧
        Submodule.span (ZMod 3) {φ w} = Submodule.span (ZMod 3) {r w'}) := by
  obtain ⟨i, hi⟩ := e.surjective D.a
  have hmem : D.a = e 0 ∨ D.a = e 3 := by
    fin_cases i
    · exact Or.inl hi.symm
    · exfalso
      have hDa : D.a = e 1 := hi.symm
      have hc0 : D.cartan D.a (e 0) ≠ 0 := by
        rw [hDa]
        exact ggQ2xCL1_nbr D e hB (i := 1) (j := 0) (by decide) (by decide)
      have hd0 : D.cartan D.a (e 2) ≠ 0 := by
        rw [hDa]
        exact ggQ2xCL1_nbr D e hB (i := 1) (j := 2) (by decide) (by decide)
      exact ggQ2xCL1_two_nbrs D (c := e 0) (d := e 2)
        (by intro h; exact (by decide : (0 : Fin 4) ≠ 2) (e.injective h))
        (by rw [hDa]; intro h; exact (by decide : (0 : Fin 4) ≠ 1) (e.injective h))
        (by rw [hDa]; intro h; exact (by decide : (2 : Fin 4) ≠ 1) (e.injective h))
        hc0 hd0
    · exfalso
      have hDa : D.a = e 2 := hi.symm
      have hc0 : D.cartan D.a (e 1) ≠ 0 := by
        rw [hDa]
        exact ggQ2xCL1_nbr D e hB (i := 2) (j := 1) (by decide) (by decide)
      have hd0 : D.cartan D.a (e 3) ≠ 0 := by
        rw [hDa]
        exact ggQ2xCL1_nbr D e hB (i := 2) (j := 3) (by decide) (by decide)
      exact ggQ2xCL1_two_nbrs D (c := e 1) (d := e 3)
        (by intro h; exact (by decide : (1 : Fin 4) ≠ 3) (e.injective h))
        (by rw [hDa]; intro h; exact (by decide : (1 : Fin 4) ≠ 2) (e.injective h))
        (by rw [hDa]; intro h; exact (by decide : (3 : Fin 4) ≠ 2) (e.injective h))
        hc0 hd0
    · exact Or.inr hi.symm
  rcases hmem with ha | ha
  · exact ggQ2_cell_BC4 D hbas e hB ha x y hx hy A hW hTF hF
  · exact (hA3 ⟨hF.1, ggQ2_parab_card_A3 D e (Or.inr (Or.inr ⟨hB, ha⟩))⟩).elim

theorem ggQ2_cell_lin {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (hbas : D.Basis)
    (hnd : (D.cartan.det : ZMod p) ≠ 0) (x y : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod p) {x})
    (hy : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.b}, g v = v) ↔ v ∈ Submodule.span (ZMod p) {y})
    (A : Subgroup (D.V ≃ₗ[ZMod p] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24))
    (hF : D.FCell A) :
    (∃ u ∈ Submodule.span (ZMod p) {x, y}, u ≠ 0 ∧ ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod p) {φ u} = Submodule.span (ZMod p) {r u}) ∨
    (∀ φ ∈ A, ∀ w ∈ Submodule.span (ZMod p) {x, y}, w ≠ 0 → ∃ r ∈ reflGp A,
      ∃ w' ∈ Submodule.span (ZMod p) {x, y}, w' ≠ 0 ∧
        Submodule.span (ZMod p) {φ w} = Submodule.span (ZMod p) {r w'}) := by
  subst hp
  have h4 : Fintype.card D.ι = 4 := hF.1
  rcases D.isWeyl with ⟨n, e, hn1, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ |
    ⟨e, hF'⟩ | ⟨e, hG⟩
  · have hn : n = 4 := by
      have h := Fintype.card_congr e
      rw [Fintype.card_fin, h4] at h
      exact h
    subst hn
    exact (ggQ2xCL_typeA D e hA h4 hA3).elim
  · have hn : n = 4 := by
      have h := Fintype.card_congr e
      rw [Fintype.card_fin, h4] at h
      exact h
    subst hn
    exact ggQ2xCL_typeB D hbas e hB x y hx hy A hW hTF hA3 hF
  · have hn : n = 4 := by
      have h := Fintype.card_congr e
      rw [Fintype.card_fin, h4] at h
      exact h
    subst hn
    exact (ggQ2xCL_typeD D e hD h4 hA3).elim
  · have h := Fintype.card_congr e
    rw [Fintype.card_fin, h4] at h
    omega
  · have h := Fintype.card_congr e
    rw [Fintype.card_fin, h4] at h
    omega
  · have h := Fintype.card_congr e
    rw [Fintype.card_fin, h4] at h
    omega
  · exact ggQ2_cell_F4 D hbas e hF' x y hx hy A hW hTF
  · have h := Fintype.card_congr e
    rw [Fintype.card_fin, h4] at h
    omega

end CFSG.StandardType

end
