module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthB5Model

public section

namespace CFSG.StandardType.OrthF3

theorem ggOrthB5_false {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    (hdim : Module.finrank (ZMod 3) V = 5)
    (r : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hrefl : ∀ i, ∃ c : ZMod 3, c ≠ 0 ∧ OrthReflOfNorm Q c (r i))
    (hord : ∀ i j, i ≠ j → orderOf (r i * r j) = (CoxeterMatrix.B 5).M i j)
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r)) = 3840)
    {AK AL : Subgroup (V ≃ₗ[ZMod 3] V)} (hKW : AK ≤ Subgroup.closure (Set.range r))
    (hLW : AL ≤ Subgroup.closure (Set.range r))
    (hKcard : Nat.card ↥AK = 384) (hLcard : Nat.card ↥AL = 192)
    {x y : V} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ∉ Submodule.span (ZMod 3) {y})
    (hKy : ∀ a ∈ AK, a y = y) (hLx : ∀ a ∈ AL, a x = x)
    (hstar : ∀ φ : ↥AK,
      ((φ : V ≃ₗ[ZMod 3] V) * (φ : V ≃ₗ[ZMod 3] V) = 1 ∧
        Module.finrank (ZMod 3) (LinearMap.range ((φ : V ≃ₗ[ZMod 3] V).toLinearMap - LinearMap.id)) = 1) →
      Nat.card {ψ : ↥AK // IsConj φ ψ} = 4 → (φ : V ≃ₗ[ZMod 3] V) x ≠ x) :
    False := by
  obtain ⟨f, hf⟩ := ggOrthB5_model hdim r hrefl hord hcard
  have hAKW : AK ≤ ggOrthSignedPerms f := hKW.trans (le_of_eq hf)
  have hALW : AL ≤ ggOrthSignedPerms f := hLW.trans (le_of_eq hf)
  obtain ⟨j, hyj⟩ :=
    ggOrthSP_exists_eq_pm_basis_of_fixed f hAKW (by rw [hKcard]; norm_num) hy0 hKy
  obtain ⟨t, hxt⟩ :=
    ggOrthSP_exists_eq_pm_basis_of_fixed f hALW (by rw [hLcard]; norm_num) hx0 hLx
  have hfixj : ∀ a ∈ AK, a (f j) = f j := by
    intro a ha
    rcases hyj with hy | hy
    · rw [← hy]; exact hKy a ha
    · have h := hKy a ha
      rw [hy, map_neg] at h
      exact neg_inj.mp h
  have hAKle : AK ≤ ggOrthStabSP f j := by
    refine le_inf hAKW ?_
    intro a ha
    rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]
    exact hfixj a ha
  have hAKeq : AK = ggOrthStabSP f j := by
    have : Finite ↥(ggOrthStabSP f j) :=
      Nat.finite_of_card_ne_zero (by rw [card_ggOrthStabSP]; norm_num)
    refine Subgroup.eq_of_le_of_card_ge hAKle ?_
    rw [card_ggOrthStabSP, hKcard]
  have htj : t ≠ j := by
    intro htj_eq
    have hxt' : x = f j ∨ x = -f j := by simpa [htj_eq] using hxt
    apply hxy
    have h1 : f j ∈ Submodule.span (ZMod 3) {y} := by
      rcases hyj with hy | hy
      · exact Submodule.mem_span_singleton.mpr ⟨1, by rw [hy, one_smul]⟩
      · exact Submodule.mem_span_singleton.mpr ⟨-1, by rw [hy, neg_one_smul, neg_neg]⟩
    rcases hxt' with hx | hx
    · rw [hx]; exact h1
    · rw [hx]; exact Submodule.neg_mem _ h1
  obtain ⟨i, hij, hit⟩ : ∃ i : Fin 5, i ≠ j ∧ i ≠ t := by
    have h2 : Finset.card ({j, t} : Finset (Fin 5)) ≤ 2 := by
      simpa using Finset.card_insert_le j ({t} : Finset (Fin 5))
    have hlt : Finset.card ({j, t} : Finset (Fin 5)) <
        Finset.card (Finset.univ : Finset (Fin 5)) := by
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card (s := ({j, t} : Finset (Fin 5)))
        (t := Finset.univ) hlt
    exact ⟨i, by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hi⟩
  subst AK
  have hmem : ggOrthSignChange f i ∈ ggOrthStabSP f j := ggOrthSignChange_mem_stabSP f hij
  let φ : ↥(ggOrthStabSP f j) := ⟨ggOrthSignChange f i, hmem⟩
  have hrefl : (φ : V ≃ₗ[ZMod 3] V) * (φ : V ≃ₗ[ZMod 3] V) = 1 ∧
      Module.finrank (ZMod 3)
        (LinearMap.range ((φ : V ≃ₗ[ZMod 3] V).toLinearMap - LinearMap.id)) = 1 := by
    simpa using ggOrthSignChange_isRefl f i
  have hclass : Nat.card {ψ : ↥(ggOrthStabSP f j) // IsConj φ ψ} = 4 :=
    card_conj_ggOrthSignChange f hij φ rfl
  have hfixx : (φ : V ≃ₗ[ZMod 3] V) x = x := by
    have hφcoe : (φ : V ≃ₗ[ZMod 3] V) = ggOrthSignChange f i := rfl
    rw [hφcoe]
    rcases hxt with hx | hx
    · rw [hx, ggOrthSignChange_apply_of_ne f hit.symm]
    · rw [hx, map_neg, ggOrthSignChange_apply_of_ne f hit.symm]
  exact (hstar φ hrefl hclass) hfixx

end CFSG.StandardType.OrthF3

end
