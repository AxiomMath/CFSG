module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomBasic
public import CFSG.RankThree.GF2n.Smith81.S81VGeomCount
public import CFSG.RankThree.GF2n.Smith81.S81VGeomHyp

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

private theorem e4_mem_orth_span {a x : Fin 6 → F} (h : herm σ a x = 0) :
    x ∈ orth σ (Submodule.span F {a}) := by
  rw [mem_orth]
  intro u hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
  rw [herm_smul_left, h, mul_zero]

private theorem e4_span_pair_eq {L : Submodule F (Fin 6 → F)} {x y : Fin 6 → F}
    (hxL : x ∈ L) (hyL : y ∈ L) (hx0 : x ≠ 0) (hyx : y ∉ Submodule.span F {x})
    (hL : finrank F L = 2) : Submodule.span F {x, y} = L := by
  have hli : LinearIndependent F ![x, y] :=
    (LinearIndependent.pair_iff' hx0).mpr fun a ha =>
      hyx (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)
  have hfin : finrank F (Submodule.span F {x, y}) = 2 := by
    have h := finrank_span_eq_card hli
    rw [Matrix.range_cons_cons_empty x y ![], Fintype.card_fin] at h
    exact h
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact hxL
    · rw [hz]
      exact hyL
  · rw [hfin, hL]

private theorem e4_exists_gen [Finite F] [CharP F 2] {L a : Submodule F (Fin 6 → F)}
    (ha : a ∈ IsoPtsOn σ L) : ∃ w ∈ L, w ≠ 0 ∧ herm σ w w = 0 ∧ a = Submodule.span F {w} := by
  simp only [IsoPtsOn, Set.mem_setOf_eq] at ha
  obtain ⟨haL, hafin, hai⟩ := ha
  have ha0 : a ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot] at hafin
    exact zero_ne_one hafin
  obtain ⟨w, hwa, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha0
  exact ⟨w, haL hwa, hw0, hai w hwa, eq_span_singleton_of_mem_of_finrank_eq_one hafin hwa hw0⟩

private theorem e4_card_le_cover {X : Type} (P Q R : X → Prop) (hQ : ∀ x, Q x → P x)
    (hR : ∀ x, R x → P x) (hcov : ∀ x, P x → Q x ∨ R x)
    (hQ0 : Nat.card {x // Q x} ≠ 0) (hR0 : Nat.card {x // R x} ≠ 0) :
    Nat.card {x // P x} ≤ Nat.card {x // Q x} + Nat.card {x // R x} := by
  haveI := Nat.finite_of_card_ne_zero hQ0
  haveI := Nat.finite_of_card_ne_zero hR0
  let g : {x // Q x} ⊕ {x // R x} → {x // P x} :=
    Sum.elim (fun a => ⟨a.1, hQ a.1 a.2⟩) (fun b => ⟨b.1, hR b.1 b.2⟩)
  have hg : Function.Surjective g := by
    rintro ⟨x, hx⟩
    rcases hcov x hx with h | h
    · exact ⟨Sum.inl ⟨x, h⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x, h⟩, rfl⟩
  have h := Nat.card_le_card_of_surjective g hg
  rwa [Nat.card_sum] at h

theorem lemmaE_caseII [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {S : Set (Fin 6 → F)} (hS : ClosedPts σ S) {P4 : Submodule F (Fin 6 → F)}
    (h4 : finrank F P4 = 4) (hn4 : NonDeg σ P4) {p₄ : Fin 6 → F} (hp4P : p₄ ∈ P4) (hp40 : p₄ ≠ 0)
    (hp4i : herm σ p₄ p₄ = 0)
    (hI : ∀ p'' ∈ P4, p'' ≠ 0 → herm σ p'' p'' = 0 → herm σ p'' p₄ ≠ 0 → p'' ∈ S)
    {p : Fin 6 → F} (hpP : p ∈ P4) (hp0 : p ≠ 0) (hpi : herm σ p p = 0)
    (hp4p : herm σ p₄ p = 0) : p ∈ S := by
  have hσi : ∀ c, σ (σ c) = c := hσ.invol
  have hspP : Submodule.span F {p} ≤ P4 := (Submodule.span_singleton_le_iff_mem p P4).2 hpP
  have hspP4 : Submodule.span F {p₄} ≤ P4 := (Submodule.span_singleton_le_iff_mem p₄ P4).2 hp4P
  have hU1d := finrank_inf_orth hσi hn4 hspP
  have hU2d := finrank_inf_orth hσi hn4 hspP4
  rw [h4, finrank_span_singleton hp0] at hU1d
  rw [h4, finrank_span_singleton hp40] at hU2d
  have hU1 : finrank F ↥(P4 ⊓ orth σ (Submodule.span F {p})) = 3 := by omega
  have hU2 : finrank F ↥(P4 ⊓ orth σ (Submodule.span F {p₄})) = 3 := by omega
  have hpU1 : p ∈ P4 ⊓ orth σ (Submodule.span F {p}) :=
    Submodule.mem_inf.2 ⟨hpP, e4_mem_orth_span hpi⟩
  have hpU2 : p ∈ P4 ⊓ orth σ (Submodule.span F {p₄}) :=
    Submodule.mem_inf.2 ⟨hpP, e4_mem_orth_span hp4p⟩
  have hcount4 : Nat.card {L : Submodule F (Fin 6 → F) // L ≤ P4 ∧ p ∈ L ∧ finrank F L = 2} =
      Nat.card F ^ 2 + Nat.card F + 1 :=
    card_lines_through_four h4 hpP hp0
  have hcount1 : Nat.card {L : Submodule F (Fin 6 → F) //
      L ≤ P4 ⊓ orth σ (Submodule.span F {p}) ∧ p ∈ L ∧ finrank F L = 2} = Nat.card F + 1 :=
    card_lines_through_three hU1 hpU1 hp0
  have hcount2 : Nat.card {L : Submodule F (Fin 6 → F) //
      L ≤ P4 ⊓ orth σ (Submodule.span F {p₄}) ∧ p ∈ L ∧ finrank F L = 2} = Nat.card F + 1 :=
    card_lines_through_three hU2 hpU2 hp0
  have hn2 : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨L, hLP4, hpL, hLfin, hL1, hL2⟩ :
      ∃ L : Submodule F (Fin 6 → F), L ≤ P4 ∧ p ∈ L ∧ finrank F L = 2 ∧
        ¬ L ≤ P4 ⊓ orth σ (Submodule.span F {p}) ∧
        ¬ L ≤ P4 ⊓ orth σ (Submodule.span F {p₄}) := by
    by_contra hcon
    have hcov : ∀ L : Submodule F (Fin 6 → F), (L ≤ P4 ∧ p ∈ L ∧ finrank F L = 2) →
        (L ≤ P4 ⊓ orth σ (Submodule.span F {p}) ∧ p ∈ L ∧ finrank F L = 2) ∨
        (L ≤ P4 ⊓ orth σ (Submodule.span F {p₄}) ∧ p ∈ L ∧ finrank F L = 2) := by
      rintro L ⟨hLP4, hpL, hLfin⟩
      by_cases h1 : L ≤ P4 ⊓ orth σ (Submodule.span F {p})
      · exact Or.inl ⟨h1, hpL, hLfin⟩
      by_cases h2 : L ≤ P4 ⊓ orth σ (Submodule.span F {p₄})
      · exact Or.inr ⟨h2, hpL, hLfin⟩
      exact (hcon ⟨L, hLP4, hpL, hLfin, h1, h2⟩).elim
    have hle : Nat.card {L : Submodule F (Fin 6 → F) // L ≤ P4 ∧ p ∈ L ∧ finrank F L = 2} ≤
        Nat.card {L : Submodule F (Fin 6 → F) //
          L ≤ P4 ⊓ orth σ (Submodule.span F {p}) ∧ p ∈ L ∧ finrank F L = 2} +
        Nat.card {L : Submodule F (Fin 6 → F) //
          L ≤ P4 ⊓ orth σ (Submodule.span F {p₄}) ∧ p ∈ L ∧ finrank F L = 2} :=
      e4_card_le_cover (fun L => L ≤ P4 ∧ p ∈ L ∧ finrank F L = 2)
        (fun L => L ≤ P4 ⊓ orth σ (Submodule.span F {p}) ∧ p ∈ L ∧ finrank F L = 2)
        (fun L => L ≤ P4 ⊓ orth σ (Submodule.span F {p₄}) ∧ p ∈ L ∧ finrank F L = 2)
        (fun L h => ⟨h.1.trans inf_le_left, h.2⟩) (fun L h => ⟨h.1.trans inf_le_left, h.2⟩)
        hcov (by rw [hcount1]; omega) (by rw [hcount2]; omega)
    rw [hcount4, hcount1, hcount2] at hle
    nlinarith
  obtain ⟨y, hyL, hpy⟩ : ∃ y ∈ L, herm σ p y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hL1
    intro v hv
    exact Submodule.mem_inf.2 ⟨hLP4 hv, e4_mem_orth_span (hcon v hv)⟩
  obtain ⟨a, haL, hpa⟩ : ∃ a ∈ L, herm σ p a = 1 :=
    ⟨(herm σ p y)⁻¹ • y, L.smul_mem _ hyL, by rw [herm_smul_right, inv_mul_cancel₀ hpy]⟩
  obtain ⟨c, hc⟩ := exists_isotropize hσ hpi hpa
  obtain ⟨y', hy'L, hpy', hy'i⟩ : ∃ y' ∈ L, herm σ p y' = 1 ∧ herm σ y' y' = 0 :=
    ⟨a + c • p, L.add_mem haL (L.smul_mem c hpL), by
      rw [herm_add_right, herm_smul_right, hpi, mul_zero, add_zero, hpa], hc⟩
  have hy'p : y' ∉ Submodule.span F {p} := by
    intro h
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 h
    rw [← hc', herm_smul_right, hpi, mul_zero] at hpy'
    exact zero_ne_one hpy'
  have hspan : Submodule.span F {p, y'} = L := e4_span_pair_eq hpL hy'L hp0 hy'p hLfin
  have hq2 : 1 < Nat.card (Fσ σ) := Finite.one_lt_card
  have hcardL : Nat.card (IsoPtsOn σ L) = Nat.card (Fσ σ) + 1 := by
    rw [← hspan]
    exact card_isoPtsOn_pair hσ hpi hy'i (by rw [hpy']; exact one_ne_zero)
  have hTcard : (IsoPtsOn σ L).ncard = Nat.card (Fσ σ) + 1 := by
    rw [← Nat.card_coe_set_eq]
    exact hcardL
  have hTfin : (IsoPtsOn σ L).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hpmem : Submodule.span F {p} ∈ IsoPtsOn σ L := by
    simp only [IsoPtsOn, Set.mem_setOf_eq]
    refine ⟨(Submodule.span_singleton_le_iff_mem p L).2 hpL, finrank_span_singleton hp0, ?_⟩
    intro v hv
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [herm_smul_left, herm_smul_right, hpi, mul_zero, mul_zero]
  have hTd : 1 < ((IsoPtsOn σ L) \ {Submodule.span F {p}}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hpmem, hTcard]
    omega
  obtain ⟨A, B, hA, hB, hAB⟩ :=
    (Set.one_lt_ncard_iff (hTfin.subset Set.diff_subset)).1 hTd
  have hA1 : A ∈ IsoPtsOn σ L := ((Set.mem_diff A).1 hA).1
  have hB1 : B ∈ IsoPtsOn σ L := ((Set.mem_diff B).1 hB).1
  have hA2 : A ≠ Submodule.span F {p} := fun h =>
    ((Set.mem_diff A).1 hA).2 (Set.mem_singleton_iff.2 h)
  have hB2 : B ≠ Submodule.span F {p} := fun h =>
    ((Set.mem_diff B).1 hB).2 (Set.mem_singleton_iff.2 h)
  obtain ⟨w1, hw1L, hw10, hw1i, hAw⟩ := e4_exists_gen hA1
  obtain ⟨w2, hw2L, hw20, hw2i, hBw⟩ := e4_exists_gen hB1
  have hw1p : w1 ∉ Submodule.span F {p} := by
    intro h
    apply hA2
    rw [hAw]
    exact Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem w1 (Submodule.span F {p})).2 h)
      (by rw [finrank_span_singleton hw10, finrank_span_singleton hp0])
  have hw2p : w2 ∉ Submodule.span F {p} := by
    intro h
    apply hB2
    rw [hBw]
    exact Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem w2 (Submodule.span F {p})).2 h)
      (by rw [finrank_span_singleton hw20, finrank_span_singleton hp0])
  have hw21 : w2 ∉ Submodule.span F {w1} := by
    intro h
    apply hAB
    rw [hAw, hBw]
    exact (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem w2 (Submodule.span F {w1})).2 h)
      (by rw [finrank_span_singleton hw20, finrank_span_singleton hw10])).symm
  have hiso : ∀ w ∈ L, w ∉ Submodule.span F {p} → herm σ w p₄ ≠ 0 := by
    intro w hwL hwp hw4
    have hw4' : herm σ p₄ w = 0 := herm_eq_zero_comm σ hσi hw4
    have hpw : Submodule.span F {p, w} = L := e4_span_pair_eq hpL hwL hp0 hwp hLfin
    apply hL2
    rw [← hpw, Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Submodule.mem_inf.2 ⟨hpP, e4_mem_orth_span hp4p⟩
    · rw [hz]
      exact Submodule.mem_inf.2 ⟨hLP4 hwL, e4_mem_orth_span hw4'⟩
  have hno : ∀ L' : Submodule F (Fin 6 → F), L' ≤ L → finrank F L' = 2 → ¬ IsTotIso σ L' := by
    intro L' hL'L hL'fin hti
    have heq : L' = L := Submodule.eq_of_le_of_finrank_eq hL'L (by rw [hL'fin, hLfin])
    rw [heq] at hti
    have h0 : herm σ p y' = 0 := hti p hpL y' hy'L
    rw [hpy'] at h0
    exact one_ne_zero h0
  have hne : herm σ w1 w2 ≠ 0 := herm_ne_zero_of_noTI hσi hno hw1L hw2L hw10 hw21 hw1i hw2i
  have hw1S : w1 ∈ S := hI w1 (hLP4 hw1L) hw10 hw1i (hiso w1 hw1L hw1p)
  have hw2S : w2 ∈ S := hI w2 (hLP4 hw2L) hw20 hw2i (hiso w2 hw2L hw2p)
  have hspan12 : Submodule.span F {w1, w2} = L := e4_span_pair_eq hw1L hw2L hw10 hw21 hLfin
  have hpspan : p ∈ Submodule.span F {w1, w2} := by
    rw [hspan12]
    exact hpL
  exact hS.secant w1 hw1S w2 hw2S hne p hp0 hpi hpspan

end CFSG.RankThree.GF2n.Smith81.S81V
