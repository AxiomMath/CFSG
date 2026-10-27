module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

private def ggQ2x_F4 (i j : Fin 4) : ℕ := CoxeterMatrix.F₄ i j

private lemma ggQ2x_F4_apply (i j : Fin 4) : ggQ2x_F4 i j = CoxeterMatrix.F₄ i j := rfl

private lemma ggQ2x_A5_no :
    ∀ f : Fin 4 → Fin 5, Function.Injective f →
      ∃ i j : Fin 4, CoxeterMatrix.A 5 (f i) (f j) ≠ ggQ2x_F4 i j := by
  decide +kernel

private lemma ggQ2x_B5_no :
    ∀ f : Fin 4 → Fin 5, Function.Injective f →
      ∃ i j : Fin 4, CoxeterMatrix.B 5 (f i) (f j) ≠ ggQ2x_F4 i j := by
  decide +kernel

private lemma ggQ2x_D5_no :
    ∀ f : Fin 4 → Fin 5, Function.Injective f →
      ∃ i j : Fin 4, ggCoxeterMatrixD 5 (f i) (f j) ≠ ggQ2x_F4 i j := by
  decide +kernel

private lemma ggQ2x_reindex {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : CoxeterMatrix ι} {N : CoxeterMatrix (Fin 5)} {e' : Fin 5 ≃ ι}
    (hM : M = N.reindex e') (a : ι) (e : Fin 4 ≃ {k // k ≠ a})
    (hN : ∀ f : Fin 4 → Fin 5, Function.Injective f →
      ∃ i j : Fin 4, N (f i) (f j) ≠ ggQ2x_F4 i j) :
    ∃ i j, M (e i) (e j) ≠ CoxeterMatrix.F₄ i j := by
  rw [hM]
  let f : Fin 4 → Fin 5 := fun k => e'.symm (e k)
  have hf : Function.Injective f := by
    intro x y hxy
    exact e.injective (Subtype.ext (e'.symm.injective hxy))
  obtain ⟨i, j, hij⟩ := hN f hf
  refine ⟨i, j, ?_⟩
  rw [ggQ2x_F4_apply] at hij
  rw [CoxeterMatrix.reindex_apply]
  exact hij

theorem ggQ2_no_F4_leaf {ι : Type} [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι)
    (hW : GGIsWeylMatrix M) (a : ι) (e : Fin 4 ≃ {k // k ≠ a}) :
    ∃ i j, M (e i) (e j) ≠ CoxeterMatrix.F₄ i j := by
  classical
  have hcard : Fintype.card ι = 5 := by
    have h4 : Fintype.card {k // k ≠ a} = 4 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    have hsub : Fintype.card {k // k ≠ a} = Fintype.card ι - 1 := Set.card_ne_eq a
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨a⟩
    omega
  rcases hW with hfam | ⟨e6, h6⟩ | ⟨e7, h7⟩ | ⟨e8, h8⟩ | ⟨e4, h4⟩ | ⟨e2, h2⟩
  · obtain ⟨n, e', hn, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ := hfam
    · have hn5 : n = 5 := by
        have : n = Fintype.card ι := by
          rw [← Fintype.card_fin n]; exact Fintype.card_congr e'
        omega
      subst n
      exact ggQ2x_reindex hA a e ggQ2x_A5_no
    · have hn5 : n = 5 := by
        have : n = Fintype.card ι := by
          rw [← Fintype.card_fin n]; exact Fintype.card_congr e'
        omega
      subst n
      exact ggQ2x_reindex hB a e ggQ2x_B5_no
    · have hn5 : n = 5 := by
        have : n = Fintype.card ι := by
          rw [← Fintype.card_fin n]; exact Fintype.card_congr e'
        omega
      subst n
      exact ggQ2x_reindex hD a e ggQ2x_D5_no
  · exfalso
    have hc : Fintype.card ι = 6 := by
      rw [← Fintype.card_congr e6, Fintype.card_fin]
    omega
  · exfalso
    have hc : Fintype.card ι = 7 := by
      rw [← Fintype.card_congr e7, Fintype.card_fin]
    omega
  · exfalso
    have hc : Fintype.card ι = 8 := by
      rw [← Fintype.card_congr e8, Fintype.card_fin]
    omega
  · exfalso
    have hc : Fintype.card ι = 4 := by
      rw [← Fintype.card_congr e4, Fintype.card_fin]
    omega
  · exfalso
    have hc : Fintype.card ι = 2 := by
      rw [← Fintype.card_congr e2, Fintype.card_fin]
    omega

end CFSG.StandardType

end
