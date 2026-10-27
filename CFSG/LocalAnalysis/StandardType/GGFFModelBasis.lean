module

public import CFSG.LocalAnalysis.StandardType.GGFFModel

@[expose] public section

namespace CFSG.StandardType.GGFF

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt vecElt_single vecElt_single_one)

theorem Model.exists_conj_of_tor_eq {H : Type} [Group H] {z w : Fin 3 → H} (hz : Model H z)
    (hw : Model H w) (htor : ∀ x : H, (∃ v, x = vecElt z v) ↔ ∃ v, x = vecElt w v) :
    ∃ h : H, ∀ i, z i = h * w i * h⁻¹ := by
  have hα : ∀ v, ∃ u, vecElt z v = vecElt w u := fun v => by
    obtain ⟨u, hu⟩ := (htor (vecElt z v)).1 ⟨v, rfl⟩
    exact ⟨u, hu⟩
  choose f hf using hα
  have hfi : Function.Injective f := fun v v' hvv' =>
    hz.vecElt_inj (by rw [hf, hf, hvv'])
  have hf0 : f 0 = 0 := hw.vecElt_inj (by rw [← hf, vecElt_zero, vecElt_zero])
  have hfne : ∀ v, v ≠ 0 → f v ≠ 0 := fun v hv h0 => hv (hfi (h0.trans hf0.symm))
  have hconj : ∀ v v', IsConj (vecElt w (f v)) (vecElt w (f v')) ↔
      IsConj (vecElt z v) (vecElt z v') := fun v v' => by
    rw [← hf, ← hf]
  have hcoord : ∀ i : Fin 3, ∃ j : Fin 3, ∃ a : ZMod 3, a ≠ 0 ∧ z i = w j ^ a.val := fun i => by
    set u : Fin 3 → ZMod 3 := Pi.single i 1 with hudef
    have hu : u ≠ 0 := fun h0 => by
      have := congrFun h0 i
      simp [u] at this
    have hwu : wt u = 1 := by fin_cases i <;> decide
    have key : ∀ v, v ≠ 0 → (wt (f v) = wt (f u) ↔ wt v = 1) := fun v hv => by
      rw [← hwu, ← hw.conj_iff (f v) (f u) (hfne v hv) (hfne u hu), hconj,
        hz.conj_iff v u hv hu]
    have hset : (Finset.univ.filter fun v => wt v = wt (f u)) =
        (Finset.univ.filter fun v => wt v = 1).image f := by
      ext w'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hw'
        obtain ⟨v, rfl⟩ := Finite.surjective_of_injective hfi w'
        have hv : v ≠ 0 := fun h0 => by
          rw [h0, hf0] at hw'
          exact hfne u hu ((wt_eq_zero_iff _).mp (hw'.symm.trans ((wt_eq_zero_iff 0).mpr rfl)))
        exact ⟨v, (key v hv).mp hw', rfl⟩
      · rintro ⟨v, hv1, rfl⟩
        have hv : v ≠ 0 := fun h0 => by
          rw [h0, (wt_eq_zero_iff 0).mpr rfl] at hv1
          exact absurd hv1 (by decide)
        exact (key v hv).mpr hv1
    have hcard := congrArg Finset.card hset
    rw [Finset.card_image_of_injective _ hfi, card_wt, card_wt] at hcard
    have hk : wt (f u) = 1 := by
      have hne : wt (f u) ≠ 0 := fun h0 => hfne u hu ((wt_eq_zero_iff _).mp h0)
      have hle : wt (f u) ≤ 3 := (Finset.card_filter_le _ _).trans (by simp)
      interval_cases hx : wt (f u) <;> simp_all
    obtain ⟨j, a, ha, hja⟩ := eq_single_of_wt_eq_one (f u) hk
    refine ⟨j, a, ha, ?_⟩
    rw [← vecElt_single_one (z := z) i, ← hudef, hf, hja, vecElt_single]
  choose j a ha hja using hcoord
  have hpow : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = 2 := by decide
  have hinj : Function.Injective j := fun i i' hii' => by
    refine hz.eq_of_z_eq ?_
    have hwj := hw.pow_z (j i')
    have h1 := hja i
    have h2 := hja i'
    rw [hii'] at h1
    rcases hpow _ (ha i) with h3 | h3 <;> rcases hpow _ (ha i') with h4 | h4 <;>
      rw [h3] at h1 <;> rw [h4] at h2
    · exact Or.inl (h1.trans h2.symm)
    · refine Or.inr ?_
      rw [h1, h2, show (1 : ZMod 3).val = 1 from rfl, show (2 : ZMod 3).val = 2 from rfl, pow_one,
        eq_inv_iff_mul_eq_one, ← pow_succ', hwj]
    · refine Or.inr ?_
      rw [h1, h2, show (1 : ZMod 3).val = 1 from rfl, show (2 : ZMod 3).val = 2 from rfl, pow_one,
        eq_inv_iff_mul_eq_one, ← pow_succ, hwj]
    · exact Or.inl (h1.trans h2.symm)
  obtain ⟨h, hh⟩ := hw.mono (Equiv.ofBijective j (Finite.injective_iff_bijective.mp hinj)) a ha
  exact ⟨h, fun i => by rw [hja i, hh i, Equiv.ofBijective_apply]⟩

end CFSG.StandardType.GGFF

end
