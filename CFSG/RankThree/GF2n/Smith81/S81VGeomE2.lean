module

public import CFSG.RankThree.GF2n.Smith81.S81VOrth
public import CFSG.RankThree.GF2n.Smith81.S81UElem
public import CFSG.RankThree.GF2n.Smith81.S81VGeomCount
public import CFSG.RankThree.GF2n.Smith81.S81VGeomHyp

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

private instance gE2_finite_submodule [Finite F] : Finite (Submodule F (Fin 6 → F)) :=
  Finite.of_injective (fun L : Submodule F (Fin 6 → F) => (L : Set (Fin 6 → F)))
    SetLike.coe_injective

private theorem gE2_mem_orth {S : Submodule F (Fin 6 → F)} {v : Fin 6 → F} :
    v ∈ orth σ S ↔ ∀ w ∈ S, herm σ w v = 0 := Iff.rfl

private theorem gE2_span_inf_bot {p : Fin 6 → F} {C D : Submodule F (Fin 6 → F)} (hD : D ≤ C)
    (hp : p ∉ C) : Submodule.span F {p} ⊓ D = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx1
  by_cases ha : a = 0
  · simp [ha]
  · exfalso
    apply hp
    have h := C.smul_mem a⁻¹ (hD hx2)
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h

private theorem gE2_line_eq {L D : Submodule F (Fin 6 → F)} {p : Fin 6 → F} (hp0 : p ≠ 0)
    (hpL : p ∈ L) (hDL : D ≤ L) (hD : finrank F D = 1) (hL : finrank F L = 2)
    (hpD : Submodule.span F {p} ⊓ D = ⊥) : Submodule.span F {p} ⊔ D = L := by
  refine Submodule.eq_of_le_of_finrank_eq
    (sup_le ((Submodule.span_singleton_le_iff_mem p L).2 hpL) hDL) ?_
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F {p}) D
  rw [hpD, finrank_bot, finrank_span_singleton hp0, hD] at h
  omega

private theorem gE2_finrank_inf {P3 P2 L : Submodule F (Fin 6 → F)} {p : Fin 6 → F}
    (h3 : finrank F P3 = 3) (h2 : finrank F P2 = 2) (hP2P3 : P2 ≤ P3) (hLP3 : L ≤ P3)
    (hL : finrank F L = 2) (hpL : p ∈ L) (hpP2 : p ∉ P2) :
    finrank F ↥(L ⊓ P2) = 1 := by
  have hup := Submodule.finrank_mono (sup_le hLP3 hP2P3)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq L P2
  have hmono := Submodule.finrank_mono (inf_le_left : L ⊓ P2 ≤ L)
  have hne : L ⊓ P2 ≠ L := by
    intro h'
    apply hpP2
    have hp : p ∈ L ⊓ P2 := by
      rw [h']
      exact hpL
    exact (Submodule.mem_inf.1 hp).2
  have hne2 : finrank F ↥(L ⊓ P2) ≠ 2 := by
    intro h2'
    exact hne (Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega))
  omega

private theorem gE2_rad_facts {L : Submodule F (Fin 6 → F)} {p : Fin 6 → F} (hpL : p ∈ L)
    (hpi : herm σ p p ≠ 0) (hL : finrank F L = 2) (hnd : ¬ NonDeg σ L) :
    finrank F ↥(L ⊓ orth σ L) = 1 ∧ p ∉ L ⊓ orth σ L := by
  have hpR : p ∉ L ⊓ orth σ L := fun h =>
    hpi (gE2_mem_orth.1 (Submodule.mem_inf.1 h).2 p hpL)
  refine ⟨?_, hpR⟩
  have hne : L ⊓ orth σ L ≠ ⊥ := by
    intro h
    unfold NonDeg at hnd
    push Not at hnd
    obtain ⟨x, hxL, hxo, hx0⟩ := hnd
    have hmem : x ∈ L ⊓ orth σ L := Submodule.mem_inf.2 ⟨hxL, gE2_mem_orth.2 hxo⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hx0 hmem
  have hne0 : finrank F ↥(L ⊓ orth σ L) ≠ 0 := by
    intro h0
    exact hne (Submodule.finrank_eq_zero.1 h0)
  have hne2 : finrank F ↥(L ⊓ orth σ L) ≠ 2 := by
    intro h2
    have heq : L ⊓ orth σ L = L := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    apply hpR
    rw [heq]
    exact hpL
  have hmono := Submodule.finrank_mono (inf_le_left : L ⊓ orth σ L ≤ L)
  omega

private theorem gE2_rad_le {P3 L : Submodule F (Fin 6 → F)} {p : Fin 6 → F} (hLP3 : L ≤ P3)
    (hpL : p ∈ L) : L ⊓ orth σ L ≤ P3 ⊓ orth σ (Submodule.span F {p}) := by
  intro x hx
  obtain ⟨hxL, hxo⟩ := Submodule.mem_inf.1 hx
  refine Submodule.mem_inf.2 ⟨hLP3 hxL, gE2_mem_orth.2 ?_⟩
  intro w hw
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [herm_smul_left, gE2_mem_orth.1 hxo p hpL, mul_zero]

private theorem gE2_plane (hσ : IsUnitaryInvolution σ) {P3 : Submodule F (Fin 6 → F)}
    (h3 : finrank F P3 = 3) (hn3 : NonDeg σ P3) {p : Fin 6 → F} (hpP3 : p ∈ P3)
    (hpi : herm σ p p ≠ 0) :
    finrank F ↥(P3 ⊓ orth σ (Submodule.span F {p})) = 2 ∧
      NonDeg σ (P3 ⊓ orth σ (Submodule.span F {p})) := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hpi (herm_zero_left σ 0)
  have hspanP3 : Submodule.span F {p} ≤ P3 :=
    (Submodule.span_singleton_le_iff_mem p P3).2 hpP3
  have hfin := finrank_inf_orth hσ.invol hn3 hspanP3
  rw [finrank_span_singleton hp0, h3] at hfin
  have hM2 : finrank F ↥(P3 ⊓ orth σ (Submodule.span F {p})) = 2 := by omega
  have hpM : p ∉ P3 ⊓ orth σ (Submodule.span F {p}) := fun h =>
    hpi (gE2_mem_orth.1 (Submodule.mem_inf.1 h).2 p (Submodule.mem_span_singleton_self p))
  have hdisj : Submodule.span F {p} ⊓ (P3 ⊓ orth σ (Submodule.span F {p})) = ⊥ :=
    gE2_span_inf_bot le_rfl hpM
  have hsup : Submodule.span F {p} ⊔ (P3 ⊓ orth σ (Submodule.span F {p})) = P3 := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le hspanP3 inf_le_left) ?_
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F {p})
      (P3 ⊓ orth σ (Submodule.span F {p}))
    rw [hdisj, finrank_bot, finrank_span_singleton hp0, hM2] at h
    omega
  refine ⟨hM2, ?_⟩
  intro x hx hxo
  have hxP3 : x ∈ P3 := (Submodule.mem_inf.1 hx).1
  have hpx : herm σ p x = 0 :=
    gE2_mem_orth.1 (Submodule.mem_inf.1 hx).2 p (Submodule.mem_span_singleton_self p)
  refine hn3 x hxP3 fun y hy => ?_
  have hy' : y ∈ Submodule.span F {p} ⊔ (P3 ⊓ orth σ (Submodule.span F {p})) := by
    rw [hsup]
    exact hy
  obtain ⟨s, hs, m, hm, rfl⟩ := Submodule.mem_sup.1 hy'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hs
  rw [herm_add_left, herm_smul_left, hpx, mul_zero, hxo m hm, zero_add]

private theorem gE2_pigeon {α : Type} [Finite α] (S A B : Set α) {n : ℕ}
    (hS : 2 * n < S.ncard) (hA : A.ncard ≤ n) (hB : B.ncard ≤ n) :
    ∃ x ∈ S, x ∉ A ∧ x ∉ B := by
  by_contra hcon
  push Not at hcon
  have hsub : S ⊆ A ∪ B := fun x hx => by
    by_cases hxA : x ∈ A
    · exact Set.mem_union_left B hxA
    · exact Set.mem_union_right A (hcon x hx hxA)
  have h1 := Set.ncard_le_ncard hsub
  have h2 := Set.ncard_union_le A B
  omega

theorem exists_good_line [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    (hq : 3 ≤ Nat.card (Fσ σ)) {P3 P2 : Submodule F (Fin 6 → F)} (h3 : finrank F P3 = 3)
    (h2 : finrank F P2 = 2) (hn3 : NonDeg σ P3) (hn2 : NonDeg σ P2) {p₄ : Fin 6 → F}
    (hperp : P3 ⊓ orth σ (Submodule.span F {p₄}) = P2) {p' : Fin 6 → F} (hp'3 : p' ∈ P3)
    (hp'i : herm σ p' p' ≠ 0) (hp'p4 : herm σ p' p₄ ≠ 0) :
    ∃ (L : Submodule F (Fin 6 → F)) (r : Fin 6 → F), L ≤ P3 ∧ p' ∈ L ∧ finrank F L = 2 ∧
      NonDeg σ L ∧ r ∈ L ∧ herm σ r r ≠ 0 ∧ herm σ p₄ r = 0 ∧
      ∀ l ∈ L, herm σ p₄ l = 0 → l ∈ Submodule.span F {r} := by
  have hp0 : p' ≠ 0 := by
    rintro rfl
    exact hp'i (herm_zero_left σ 0)
  have hP2P3 : P2 ≤ P3 := by
    rw [← hperp]
    exact inf_le_left
  have hr4 : ∀ r ∈ P2, herm σ p₄ r = 0 := fun r hr => by
    rw [← hperp] at hr
    exact gE2_mem_orth.1 (Submodule.mem_inf.1 hr).2 p₄ (Submodule.mem_span_singleton_self p₄)
  have hP2mem : ∀ l ∈ P3, herm σ p₄ l = 0 → l ∈ P2 := by
    intro l hl hl4
    rw [← hperp]
    refine Submodule.mem_inf.2 ⟨hl, gE2_mem_orth.2 ?_⟩
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [herm_smul_left, hl4, mul_zero]
  have hp'P2 : p' ∉ P2 := by
    intro h
    apply hp'p4
    apply herm_eq_zero_comm σ hσ.invol
    exact hr4 p' h
  have hcardL : Set.ncard {L : Submodule F (Fin 6 → F) | L ≤ P3 ∧ p' ∈ L ∧ finrank F L = 2} =
      Nat.card (Fσ σ) ^ 2 + 1 := by
    rw [← Nat.card_coe_set_eq, card_Fσ_sq hσ]
    exact card_lines_through_three h3 hp'3 hp0
  have hB₁ : Set.ncard {L : Submodule F (Fin 6 → F) |
      (L ≤ P3 ∧ p' ∈ L ∧ finrank F L = 2) ∧ ∀ v ∈ L ⊓ P2, herm σ v v = 0} ≤
        Nat.card (Fσ σ) + 1 := by
    have hiso : (IsoPtsOn σ P2).ncard ≤ Nat.card (Fσ σ) + 1 := by
      rw [← Nat.card_coe_set_eq]
      exact card_isoPtsOn_le hσ h2 hn2
    refine le_trans (Set.ncard_le_ncard_of_injOn (fun L : Submodule F (Fin 6 → F) => L ⊓ P2)
      ?_ ?_) hiso
    · rintro L ⟨⟨hLP3, hpL, hL⟩, hiso'⟩
      show L ⊓ P2 ∈ IsoPtsOn σ P2
      simp only [IsoPtsOn, Set.mem_setOf_eq]
      exact ⟨inf_le_right, gE2_finrank_inf h3 h2 hP2P3 hLP3 hL hpL hp'P2, hiso'⟩
    · rintro L ⟨⟨hLP3, hpL, hL⟩, _⟩ L' ⟨⟨hLP3', hpL', hL'⟩, _⟩ hEq
      have hEq' : L ⊓ P2 = L' ⊓ P2 := hEq
      have eL := gE2_line_eq hp0 hpL inf_le_left
        (gE2_finrank_inf h3 h2 hP2P3 hLP3 hL hpL hp'P2) hL
        (gE2_span_inf_bot inf_le_right hp'P2)
      have eL' := gE2_line_eq hp0 hpL' inf_le_left
        (gE2_finrank_inf h3 h2 hP2P3 hLP3' hL' hpL' hp'P2) hL'
        (gE2_span_inf_bot inf_le_right hp'P2)
      calc L = Submodule.span F {p'} ⊔ (L ⊓ P2) := eL.symm
        _ = Submodule.span F {p'} ⊔ (L' ⊓ P2) := by rw [hEq']
        _ = L' := eL'
  have hB₂ : Set.ncard {L : Submodule F (Fin 6 → F) |
      (L ≤ P3 ∧ p' ∈ L ∧ finrank F L = 2) ∧ ¬ NonDeg σ L} ≤ Nat.card (Fσ σ) + 1 := by
    have hM := gE2_plane hσ h3 hn3 hp'3 hp'i
    have hiso : (IsoPtsOn σ (P3 ⊓ orth σ (Submodule.span F {p'}))).ncard ≤
        Nat.card (Fσ σ) + 1 := by
      rw [← Nat.card_coe_set_eq]
      exact card_isoPtsOn_le hσ hM.1 hM.2
    refine le_trans (Set.ncard_le_ncard_of_injOn
      (fun L : Submodule F (Fin 6 → F) => L ⊓ orth σ L) ?_ ?_) hiso
    · rintro L ⟨⟨hLP3, hpL, hL⟩, hnd⟩
      obtain ⟨hfin, _⟩ := gE2_rad_facts hpL hp'i hL hnd
      show L ⊓ orth σ L ∈ IsoPtsOn σ (P3 ⊓ orth σ (Submodule.span F {p'}))
      simp only [IsoPtsOn, Set.mem_setOf_eq]
      refine ⟨gE2_rad_le hLP3 hpL, hfin, ?_⟩
      intro v hv
      exact gE2_mem_orth.1 (Submodule.mem_inf.1 hv).2 v (Submodule.mem_inf.1 hv).1
    · rintro L ⟨⟨hLP3, hpL, hL⟩, hnd⟩ L' ⟨⟨hLP3', hpL', hL'⟩, hnd'⟩ hEq
      have hEq' : L ⊓ orth σ L = L' ⊓ orth σ L' := hEq
      obtain ⟨hfin, hpR⟩ := gE2_rad_facts hpL hp'i hL hnd
      obtain ⟨hfin', hpR'⟩ := gE2_rad_facts hpL' hp'i hL' hnd'
      have eL := gE2_line_eq hp0 hpL inf_le_left hfin hL (gE2_span_inf_bot le_rfl hpR)
      have eL' := gE2_line_eq hp0 hpL' inf_le_left hfin' hL' (gE2_span_inf_bot le_rfl hpR')
      calc L = Submodule.span F {p'} ⊔ (L ⊓ orth σ L) := eL.symm
        _ = Submodule.span F {p'} ⊔ (L' ⊓ orth σ L') := by rw [hEq']
        _ = L' := eL'
  have hSize : 2 * (Nat.card (Fσ σ) + 1) <
      Set.ncard {L : Submodule F (Fin 6 → F) | L ≤ P3 ∧ p' ∈ L ∧ finrank F L = 2} := by
    rw [hcardL]
    nlinarith
  obtain ⟨L, hLS, hLB₁, hLB₂⟩ := gE2_pigeon _ _ _ hSize hB₁ hB₂
  obtain ⟨hLP3, hpL, hL2⟩ := hLS
  have hLnd : NonDeg σ L := by
    by_contra hnd
    exact hLB₂ ⟨⟨hLP3, hpL, hL2⟩, hnd⟩
  obtain ⟨r, hr, hri⟩ : ∃ r ∈ L ⊓ P2, herm σ r r ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hLB₁ ⟨⟨hLP3, hpL, hL2⟩, hcon⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hri (herm_zero_left σ 0)
  have hD1 := gE2_finrank_inf h3 h2 hP2P3 hLP3 hL2 hpL hp'P2
  have hspan : Submodule.span F {r} = L ⊓ P2 :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem r _).2 hr)
      (by rw [finrank_span_singleton hr0, hD1])
  refine ⟨L, r, hLP3, hpL, hL2, hLnd, (Submodule.mem_inf.1 hr).1, hri,
    hr4 r (Submodule.mem_inf.1 hr).2, ?_⟩
  intro l hl hl4
  rw [hspan]
  exact Submodule.mem_inf.2 ⟨hl, hP2mem l (hLP3 hl) hl4⟩

end CFSG.RankThree.GF2n.Smith81.S81V
