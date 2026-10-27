module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphClassD
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphClassE

public section

namespace CFSG.StandardType

private lemma ggQ2g_D_offdiag {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    CartanMatrix.D m i j = -1 ∨ CartanMatrix.D m i j = 0 := by
  rw [CartanMatrix.D, Matrix.of_apply]
  simp only [hij, if_false]
  split_ifs <;> omega

private lemma ggQ2g_D_tail {m : ℕ} (hm : 5 ≤ m) (j : Fin m) (hj : j.val ≠ 0) :
    CartanMatrix.D m ⟨0, by omega⟩ j ≠ 0 ↔ j.val = 1 := by
  have hne : (⟨0, by omega⟩ : Fin m) ≠ j := fun h => hj (by rw [← h])
  rw [CartanMatrix.D, Matrix.of_apply]
  simp only [hne, if_false]
  split_ifs <;> simp_all <;> omega

private theorem ggQ2g_coxeter_of_D {ι : Type} (M : CoxeterMatrix ι) (C : Matrix ι ι ℤ)
    (hC : GGIntCartan M C) {n : ℕ} (e : Fin n ≃ ι)
    (he : ∀ i j, C (e i) (e j) = CartanMatrix.D n i j) :
    M = (ggCoxeterMatrixD n).reindex e := by
  ext a b
  obtain ⟨i, rfl⟩ := e.surjective a
  obtain ⟨j, rfl⟩ := e.surjective b
  rw [CoxeterMatrix.reindex_apply, e.symm_apply_apply, e.symm_apply_apply, ggCoxeterMatrixD_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij]
    have hne : e i ≠ e j := fun h => hij (e.injective h)
    have h1 := he i j
    have h2 := he j i
    have hij' := ggQ2g_D_offdiag hij
    have hji' := ggQ2g_D_offdiag (Ne.symm hij)
    rcases hC.2 (e i) (e j) hne with ⟨hm, hc, -⟩ | ⟨hm, hc, -⟩ | ⟨hm, hp, hn1, hn2⟩ |
      ⟨hm, hp, hn1, hn2⟩
    · rw [hm, if_pos (by rw [← h1]; exact hc)]
    · rw [hm, if_neg (by rw [← h1, hc]; norm_num)]
    · exfalso
      rw [h1, h2] at hp
      rw [h1] at hn1
      rw [h2] at hn2
      rcases hij' with h | h <;> rcases hji' with h' | h' <;> simp_all
    · exfalso
      rw [h1, h2] at hp
      rw [h1] at hn1
      rw [h2] at hn2
      rcases hij' with h | h <;> rcases hji' with h' | h' <;> simp_all

theorem ggQ2g_classify {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e₀ c : D.ι) (hce : c ≠ e₀)
    (hcl : ∃! d, d ≠ c ∧ D.cartan c d ≠ 0) {k : ℕ} (hk : 2 ≤ k)
    (f : Fin (2 * k) ≃ {i // i ≠ e₀})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D (2 * k) i j) :
    (∃ e : Fin (2 * k + 1) ≃ D.ι,
        (∀ i j, D.cartan (e i) (e j) = CartanMatrix.D (2 * k + 1) i j) ∧
        D.coxeter = (ggCoxeterMatrixD (2 * k + 1)).reindex e ∧
        e₀ = e ⟨0, by omega⟩ ∧ (c = e ⟨2 * k - 1, by omega⟩ ∨ c = e ⟨2 * k, by omega⟩)) ∨
    (k = 3 ∧ ∃ e : Fin 7 ≃ D.ι, (∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 7 i j) ∧
        e₀ = e 0 ∧ (c = e 1 ∨ c = e 6)) := by
  classical
  obtain ⟨hA, hE6, hE8, hF4, hG2⟩ := ggQ2g_no_D_complement D.cartan e₀ hk f hf
  rcases ggIntCartan_models D.isWeyl D.isCartan with
    ⟨n, e, hn, hA' | ⟨hn2, hB | hC⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6'⟩ | ⟨e, hE7⟩ | ⟨e, hE8'⟩ |
      ⟨e, hF4' | hF4T⟩ | ⟨e, hG | hGT⟩
  · exact absurd ⟨n, e, hn, Or.inl hA'⟩ hA
  · exact absurd ⟨n, e, hn, Or.inr ⟨hn2, Or.inl hB⟩⟩ hA
  · exact absurd ⟨n, e, hn, Or.inr ⟨hn2, Or.inr hC⟩⟩ hA
  · obtain ⟨hn', he0, hc⟩ := ggQ2g_classD D hn4 e hD e₀ c hce hcl hk f hf
    subst hn'
    refine Or.inl ⟨e, hD, ggQ2g_coxeter_of_D D.coxeter D.cartan D.isCartan e hD, he0, ?_⟩
    rcases hc with h | h
    · exact Or.inl (h.trans (congrArg e (Fin.ext (by show 2 * k + 1 - 2 = 2 * k - 1; omega))))
    · exact Or.inr (h.trans (congrArg e (Fin.ext (by show 2 * k + 1 - 1 = 2 * k; omega))))
  · exact absurd ⟨e, hE6'⟩ hE6
  · obtain ⟨hk3, he0, hc⟩ := ggQ2g_classE7 D.cartan e hE7 e₀ c hce hcl hk f hf
    exact Or.inr ⟨hk3, e, hE7, he0, hc⟩
  · exact absurd ⟨e, hE8'⟩ hE8
  · exact absurd ⟨e, Or.inl hF4'⟩ hF4
  · exact absurd ⟨e, Or.inr hF4T⟩ hF4
  · exact absurd ⟨e, Or.inl hG⟩ hG2
  · exact absurd ⟨e, Or.inr hGT⟩ hG2

theorem ggQ2g_leaf_of_D {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e₀ c : D.ι) (hce : c ≠ e₀)
    (hcl : ∃! d, d ≠ c ∧ D.cartan c d ≠ 0) {k : ℕ} (hk : 2 ≤ k)
    (f : Fin (2 * k) ≃ {i // i ≠ e₀})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D (2 * k) i j) :
    ∃! d, d ≠ e₀ ∧ D.cartan e₀ d ≠ 0 := by
  rcases ggQ2g_classify D e₀ c hce hcl hk f hf with
    ⟨e, hecart, -, he0, -⟩ | ⟨-, e, hecart, he0, -⟩
  · subst he0
    refine ⟨e ⟨1, by omega⟩, ⟨?_, ?_⟩, ?_⟩
    · intro h
      have := congrArg Fin.val (e.injective h)
      simp at this
    · rw [hecart]
      exact (ggQ2g_D_tail (by omega) ⟨1, by omega⟩ (by simp)).mpr rfl
    · rintro d ⟨hd1, hd2⟩
      obtain ⟨j, rfl⟩ := e.surjective d
      rw [hecart] at hd2
      have hj0 : j.val ≠ 0 := fun h => hd1 (congrArg e (Fin.ext (by simpa using h)))
      exact congrArg e (Fin.ext ((ggQ2g_D_tail (by omega) j hj0).mp hd2))
  · subst he0
    refine ⟨e 2, ⟨?_, ?_⟩, ?_⟩
    · intro h
      exact absurd (e.injective h) (by decide)
    · rw [hecart]
      decide
    · rintro d ⟨hd1, hd2⟩
      obtain ⟨j, rfl⟩ := e.surjective d
      rw [hecart] at hd2
      have hj0 : j ≠ 0 := fun h => hd1 (by rw [h])
      refine congrArg e ?_
      revert hj0 hd2
      fin_cases j <;> simp [CartanMatrix.E]

end CFSG.StandardType

end
