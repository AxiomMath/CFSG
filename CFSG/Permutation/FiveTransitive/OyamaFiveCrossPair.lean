module

public import CFSG.Permutation.FiveTransitive.FixedFiveInvolutionGeometry

public section

namespace CFSG

namespace FiveTransitive.OyamaFiveCrossPair

open MulAction FixedFiveInvolutionGeometry

theorem cross_pair
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (hmax : ∀ g : G, g * g = 1 → g ≠ 1 → (fixedBy X g).ncard ≤ 5)
    (e : Fin 13 ↪ X) (a c d f : G)
    (ha : a * a = 1) (hd : d * d = 1) (hf : f * f = 1) (hf1 : f ≠ 1)
    (had : a * d = d * a) (haf : a * f = f * a) (hdf : d * f = f * d)
    (hfixa : fixedBy X a = {e 0, e 1, e 2, e 3, e 4})
    (hfixd : fixedBy X d = {e 0, e 9, e 10, e 11, e 12})
    (ha56 : a • e 5 = e 6) (ha65 : a • e 6 = e 5)
    (ha78 : a • e 7 = e 8) (ha87 : a • e 8 = e 7)
    (hd34 : d • e 3 = e 4)
    (hd56 : d • e 5 = e 6) (hd65 : d • e 6 = e 5)
    (hd78 : d • e 7 = e 8) (hd87 : d • e 8 = e 7)
    (hc0 : c • e 0 = e 0) (hc1 : c • e 1 = e 1) (hc2 : c • e 2 = e 2)
    (hc34 : c • e 3 = e 4) (hc43 : c • e 4 = e 3)
    (hc78 : c • e 7 = e 8) (hc87 : c • e 8 = e 7)
    (hf1fix : f • e 1 = e 1) (hf2fix : f • e 2 = e 2)
    (hf9fix : f • e 9 = e 9) (hf10fix : f • e 10 = e 10) :
    (∀ z ∈ fixedBy X a, (c * f) • z = z) ∧
      ((c * f) • e 5 = e 7 ∨ (c * f) • e 5 = e 8) := by
  have hAF (i : Fin 13) (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) :
      a • e i = e i := by
    change e i ∈ fixedBy X a
    rw [hfixa]
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp
  have ha0 := hAF 0 (Or.inl rfl)
  have ha1 := hAF 1 (Or.inr (Or.inl rfl))
  have ha2 := hAF 2 (Or.inr (Or.inr (Or.inl rfl)))
  have ha3 := hAF 3 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have ha4 := hAF 4 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hd0 : d • e 0 = e 0 := by change e 0 ∈ fixedBy X d; rw [hfixd]; simp
  have hf0 : f • e 0 = e 0 := by
    have hfa := mem_fixedBy_smul_of_commute a f haf ha0
    have hfd := mem_fixedBy_smul_of_commute d f hdf hd0
    rw [hfixa] at hfa
    rw [hfixd] at hfd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfa hfd
    rcases hfa with h | h | h | h | h <;>
      rcases hfd with k | k | k | k | k <;>
      simp_all [e.injective.eq_iff]
  have hfixf : fixedBy X f = {e 0, e 1, e 2, e 9, e 10} := by
    apply fixedBy_eq_of_five f (hmax f hf hf1) _
    · simp [e.injective.eq_iff]
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      · exact hf0
      · exact hf1fix
      · exact hf2fix
      · exact hf9fix
      · exact hf10fix
  have hf3ne : f • e 3 ≠ e 3 := by
    intro h
    have hm : e 3 ∈ fixedBy X f := h
    rw [hfixf] at hm
    simp [e.injective.eq_iff] at hm
  have hf34 : f • e 3 = e 4 := by
    have hm := mem_fixedBy_smul_of_commute a f haf ha3
    rw [hfixa] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h | h | h
    · have := (MulAction.injective f) (h.trans hf0.symm); simp [e.injective.eq_iff] at this
    · have := (MulAction.injective f) (h.trans hf1fix.symm); simp [e.injective.eq_iff] at this
    · have := (MulAction.injective f) (h.trans hf2fix.symm); simp [e.injective.eq_iff] at this
    · exact (hf3ne h).elim
    · exact h
  have hff (z : X) : f • (f • z) = z := by rw [← mul_smul, hf, one_smul]
  have hf43 : f • e 4 = e 3 := by rw [← hf34, hff]
  have had1 : a * d ≠ 1 := by
    intro h
    have hh : (a * d) • e 3 = e 3 := by rw [h, one_smul]
    rw [mul_smul, hd34, ha4] at hh
    have := e.injective hh
    omega
  have hfixad : fixedBy X (a * d) = {e 0, e 5, e 6, e 7, e 8} := by
    apply fixedBy_eq_of_five (a * d) (hmax _ (mul_square_one a d ha hd had) had1) _
    · simp [e.injective.eq_iff]
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;>
        change (a * d) • _ = _ <;>
        simp only [mul_smul, hd0, ha0, hd56, hd65, hd78, hd87, ha56, ha65, ha78, ha87]
  have hadf : (a * d) * f = f * (a * d) := by
    calc
      (a * d) * f = a * (d * f) := mul_assoc _ _ _
      _ = a * (f * d) := by rw [hdf]
      _ = (a * f) * d := (mul_assoc _ _ _).symm
      _ = (f * a) * d := by rw [haf]
      _ = f * (a * d) := mul_assoc _ _ _
  have hfmem (i : Fin 13) (hi : i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) :
      f • e i = e 5 ∨ f • e i = e 6 ∨ f • e i = e 7 ∨ f • e i = e 8 := by
    have him : e i ∈ fixedBy X (a * d) := by
      rw [hfixad]
      rcases hi with rfl | rfl | rfl | rfl <;> simp
    have hm := mem_fixedBy_smul_of_commute (a * d) f hadf him
    rw [hfixad] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h
    · have hh := (MulAction.injective f) (h.trans hf0.symm)
      have hh' := e.injective hh
      rcases hi with rfl | rfl | rfl | rfl <;> omega
    · exact h
  have hfnofix (i : Fin 13) (hi : i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) : f • e i ≠ e i := by
    intro h
    have hm : e i ∈ fixedBy X f := h
    rw [hfixf] at hm
    rcases hi with rfl | rfl | rfl | rfl <;> simp [e.injective.eq_iff] at hm
  have hf56not : f • e 5 ≠ e 6 := by
    intro hf56
    have hf65 : f • e 6 = e 5 := by rw [← hf56, hff]
    have hf78 : f • e 7 = e 8 := by
      rcases hfmem 7 (Or.inr (Or.inr (Or.inl rfl))) with h | h | h | h
      · have hh := (MulAction.injective f) (h.trans hf65.symm)
        have := e.injective hh; omega
      · have hh := (MulAction.injective f) (h.trans hf56.symm)
        have := e.injective hh; omega
      · exact (hfnofix 7 (Or.inr (Or.inr (Or.inl rfl))) h).elim
      · exact h
    have hf87 : f • e 8 = e 7 := by rw [← hf78, hff]
    have haf1 : a * f ≠ 1 := by
      intro h
      have hh : (a * f) • e 3 = e 3 := by rw [h, one_smul]
      rw [mul_smul, hf34, ha4] at hh
      have := e.injective hh; omega
    have hsub : ({e 0, e 1, e 2, e 5, e 6, e 7, e 8} : Set X) ⊆ fixedBy X (a * f) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        change (a * f) • _ = _ <;>
        simp only [mul_smul, hf0, hf1fix, hf2fix, hf56, hf65, hf78, hf87, ha0, ha1, ha2, ha56, ha65, ha78, ha87]
    have hseven : ({e 0, e 1, e 2, e 5, e 6, e 7, e 8} : Set X).ncard = 7 := by
      simp [e.injective.eq_iff]
    have hlo := Set.ncard_le_ncard hsub
    have hhi := hmax (a * f) (mul_square_one a f ha hf haf) haf1
    omega
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [hfixa] at hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;>
      simp only [mul_smul, hf0, hf1fix, hf2fix, hf34, hf43, hc0, hc1, hc2, hc34, hc43]
  · rcases hfmem 5 (Or.inl rfl) with h | h | h | h
    · exact (hfnofix 5 (Or.inl rfl) h).elim
    · exact (hf56not h).elim
    · exact Or.inr (by rw [mul_smul, h, hc78])
    · exact Or.inl (by rw [mul_smul, h, hc87])

end FiveTransitive.OyamaFiveCrossPair

end CFSG
