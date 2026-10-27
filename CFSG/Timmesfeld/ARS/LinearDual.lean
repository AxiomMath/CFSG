module

public import CFSG.Timmesfeld.ARS.LinearDict

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Linear

@[expose] def axis (Δ : Set (Subgroup G)) (X : Subgroup G) : Set (Set (Subgroup G)) :=
  {P | IsPoint Δ P ∧ X ≤ stabSet P}

@[expose] def dualPoint (R Δ : Set (Subgroup G)) (C : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ R ∧ axis Δ B = axis Δ C}

section Conj

variable {Δ : Set (Subgroup G)}

theorem conjSet_inv_conjSet (P : Set (Subgroup G)) (g : G) : conjSet (conjSet P g⁻¹) g = P := by
  rw [← conjSet_mul, mul_inv_cancel, conjSet_one]

theorem conjSub_le_stabSet_conjSet_iff {X : Subgroup G} {P : Set (Subgroup G)} (g : G) :
    conjSub X g ≤ stabSet (conjSet P g) ↔ X ≤ stabSet P := by
  have key : ∀ (X : Subgroup G) (P : Set (Subgroup G)) (g : G),
      X ≤ stabSet P → conjSub X g ≤ stabSet (conjSet P g) := by
    rintro X P g h _ ⟨x, hx, rfl⟩
    change conjSet (conjSet P g) (g * x * g⁻¹) = conjSet P g
    rw [← conjSet_mul, show g * x * g⁻¹ * g = g * x by group, conjSet_mul, mem_stabSet.1 (h hx)]
  refine ⟨fun h => ?_, key X P g⟩
  have := key _ _ g⁻¹ h
  rwa [← conjSub_mul, inv_mul_cancel, conjSub_one, conjSet_conjSet_inv] at this

theorem mem_axis_conjSub_iff {X : Subgroup G} {P : Set (Subgroup G)} (g : G) :
    P ∈ axis Δ (conjSub X g) ↔ conjSet P g⁻¹ ∈ axis Δ X := by
  constructor
  · rintro ⟨hP, hXP⟩
    refine ⟨hP.conj g⁻¹, ?_⟩
    have := (conjSub_le_stabSet_conjSet_iff g⁻¹).2 hXP
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
  · rintro ⟨hP, hXP⟩
    refine ⟨?_, ?_⟩
    · have := hP.conj g
      rwa [conjSet_inv_conjSet] at this
    · have := (conjSub_le_stabSet_conjSet_iff g).2 hXP
      rwa [conjSet_inv_conjSet] at this

theorem dualPoint_conjSub (hR : IsRootClass R) (C : Subgroup G) (g : G) :
    dualPoint R Δ (conjSub C g) = conjSet (dualPoint R Δ C) g := by
  ext B
  rw [mem_conjSet]
  change B ∈ R ∧ axis Δ B = axis Δ (conjSub C g) ↔
    conjSub B g⁻¹ ∈ R ∧ axis Δ (conjSub B g⁻¹) = axis Δ C
  have hBR : B ∈ R ↔ conjSub B g⁻¹ ∈ R := by
    refine ⟨fun h => hR.conjSub_mem h _, fun h => ?_⟩
    have := hR.conjSub_mem h g
    rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this
  rw [← hBR]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · ext P
    rw [mem_axis_conjSub_iff, inv_inv, h, mem_axis_conjSub_iff, conjSet_conjSet_inv]
  · ext P
    rw [mem_axis_conjSub_iff, ← h, mem_axis_conjSub_iff, inv_inv, conjSet_inv_conjSet]

end Conj

section Dual

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A)
  {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ)
include hR hiso hnd hΩ hΔ

theorem axis_eq_of_mem_lambdaSet {P : Set (Subgroup G)} (hP : IsPoint Δ P) {C B : Subgroup G}
    (hC : C ∈ P) (hB : B ∈ lambdaSet R C) (hBP : B ∉ P) : axis Δ B = axis Δ C := by
  have hCR : C ∈ R := (hP.isWeakTI hR hΔ).1 hC
  have hBR : B ∈ R := hB.1.1
  obtain ⟨Q, hQ, hBQ⟩ := exists_isPoint_mem hR hΔ hBR
  have hCQ : C ∉ Q := fun h => hBP (IsPoint.eq_of_mem hR hΔ hQ hP h hC ▸ hBQ)
  ext P'
  refine ⟨fun ⟨hP', h⟩ => ⟨hP', ?_⟩, fun ⟨hP', h⟩ => ⟨hP',
    le_stabSet_of_mem_lambdaSet hR hiso hnd hΩ hΔ hP hC hB hBP hP' h⟩⟩
  exact le_stabSet_of_mem_lambdaSet hR hiso hnd hΩ hΔ hQ hBQ (mem_lambdaSet_comm hCR hB) hCQ hP' h

theorem eq_of_axis_eq {P : Set (Subgroup G)} (hP : IsPoint Δ P) {C Z : Subgroup G} (hC : C ∈ P)
    (hZ : Z ∈ P) (h : axis Δ C = axis Δ Z) : C = Z := by
  refine eq_of_forall_le_stabSet_iff hR hiso hnd hΩ hΔ hP hC hZ fun P' hP' => ?_
  constructor
  · intro hC'
    have : P' ∈ axis Δ Z := h ▸ (⟨hP', hC'⟩ : P' ∈ axis Δ C)
    exact this.2
  · intro hZ'
    have : P' ∈ axis Δ C := h.symm ▸ (⟨hP', hZ'⟩ : P' ∈ axis Δ Z)
    exact this.2

theorem mem_dualPoint_iff {P : Set (Subgroup G)} (hP : IsPoint Δ P) {C : Subgroup G}
    (hC : C ∈ P) {B : Subgroup G} :
    B ∈ dualPoint R Δ C ↔ B = C ∨ (B ∈ lambdaSet R C ∧ B ∉ P) := by
  have hPw := hP.isWeakTI hR hΔ
  have hCR : C ∈ R := hPw.1 hC
  constructor
  · rintro ⟨hBR, hax⟩
    by_cases hBP : B ∈ P
    · exact Or.inl (eq_of_axis_eq hR hiso hnd hΩ hΔ hP hBP hC hax)
    right
    refine ⟨?_, hBP⟩
    have hBst : B ≤ stabSet P := by
      have : P ∈ axis Δ C := ⟨hP, Sec5.le_stabSet_of_commuting hR hPw hCR hC
        (hR.commuting_self hCR)⟩
      rw [← hax] at this
      exact this.2
    obtain ⟨Z, hZ, hBZ⟩ := exists_mem_lambdaSet_of_le_stabSet hR hiso hnd hΩ hΔ hP hBR hBP hBst
    have hZC : Z = C := eq_of_axis_eq hR hiso hnd hΩ hΔ hP hZ hC
      ((axis_eq_of_mem_lambdaSet hR hiso hnd hΩ hΔ hP hZ hBZ hBP).symm.trans hax)
    exact hZC ▸ hBZ
  · rintro (rfl | ⟨hB, hBP⟩)
    · exact ⟨hCR, rfl⟩
    · exact ⟨hB.1.1, axis_eq_of_mem_lambdaSet hR hiso hnd hΩ hΔ hP hC hB hBP⟩

omit [Finite G] hR hiso hnd hΩ hΔ in
theorem mem_dualPoint_self {C : Subgroup G} (hC : C ∈ R) : C ∈ dualPoint R Δ C := ⟨hC, rfl⟩

omit [Finite G] hR hiso hnd hΩ hΔ in
theorem dualPoint_eq_of_mem {C B : Subgroup G} (hB : B ∈ dualPoint R Δ C) :
    dualPoint R Δ B = dualPoint R Δ C := by
  ext E
  change E ∈ R ∧ axis Δ E = axis Δ B ↔ E ∈ R ∧ axis Δ E = axis Δ C
  rw [hB.2]

omit [Finite G] hR hiso hnd hΩ hΔ in
theorem dualPoint_subset (C : Subgroup G) : dualPoint R Δ C ⊆ R := fun _ hB => hB.1

theorem isTI_dualPoint {C : Subgroup G} (hC : C ∈ R) : IsTI R (dualPoint R Δ C) := by
  obtain ⟨P, hP, hCP⟩ := exists_isPoint_mem hR hΔ hC
  have hPw := hP.isWeakTI hR hΔ
  refine ⟨dualPoint_subset C, ?_, fun h => ?_, fun g => ?_⟩
  ·
    obtain ⟨B, hB, hBP⟩ : ∃ B ∈ lambdaSet R C, B ∉ P := by
      by_contra! hall
      have hM : M R C ≤ gen P := sup_le (le_gen hCP) (iSup₂_le fun B hB => le_gen (hall B hB))
      have hcomm := (commuting_gen_of_isWeakTI_of hR hiso hnd hPw).mono hM hM
      have hMC := (Q_eq_M_of_omegaSet hR hiso hnd hΩ hC).2.2.1
      rw [commuting_iff_commutator_eq_bot.1 hcomm] at hMC
      exact hR.ne_bot C hC hMC.symm
    exact ⟨C, mem_dualPoint_self (Δ := Δ) hC, B,
      (mem_dualPoint_iff hR hiso hnd hΩ hΔ hP hCP).2 (Or.inr ⟨hB, hBP⟩), fun e => hB.1.2.1 e.symm⟩
  ·
    obtain ⟨E, hE, hCE⟩ := hiso C hC
    have hEmem : E ∈ dualPoint R Δ C := by rw [h]; exact hE
    rcases (mem_dualPoint_iff hR hiso hnd hΩ hΔ hP hCP).1 hEmem with rfl | ⟨hEl, -⟩
    · exact hCE.1 rfl
    · exact hCE.not_commuting (hR.ne_bot C hC) hEl.1.2.2
  · rw [← dualPoint_conjSub hR C g]
    by_cases hint : (dualPoint R Δ C ∩ dualPoint R Δ (conjSub C g)).Nonempty
    · obtain ⟨E, hE1, hE2⟩ := hint
      right
      rw [← dualPoint_eq_of_mem hE1, ← dualPoint_eq_of_mem hE2, Set.inter_self]
    · left
      exact Set.not_nonempty_iff_eq_empty.1 hint

theorem inter_dualPoint_nonempty_iff {P : Set (Subgroup G)} (hP : IsPoint Δ P) {Y : Subgroup G}
    (hY : Y ∈ R) : (P ∩ dualPoint R Δ Y).Nonempty ↔ Y ≤ stabSet P := by
  have hPw := hP.isWeakTI hR hΔ
  constructor
  · rintro ⟨Z, hZP, hZY⟩
    have : P ∈ axis Δ Z :=
      ⟨hP, Sec5.le_stabSet_of_commuting hR hPw (hPw.1 hZP) hZP (hR.commuting_self (hPw.1 hZP))⟩
    rw [hZY.2] at this
    exact this.2
  · intro h
    by_cases hYP : Y ∈ P
    · exact ⟨Y, hYP, mem_dualPoint_self (Δ := Δ) hY⟩
    obtain ⟨Z, hZ, hYZ⟩ := exists_mem_lambdaSet_of_le_stabSet hR hiso hnd hΩ hΔ hP hY hYP h
    refine ⟨Z, hZ, hPw.1 hZ, ?_⟩
    exact (axis_eq_of_mem_lambdaSet hR hiso hnd hΩ hΔ hP hZ hYZ hYP).symm

theorem eq_of_mem_dualPoint {P : Set (Subgroup G)} (hP : IsPoint Δ P) {C Y Z : Subgroup G}
    (hY : Y ∈ P) (hZ : Z ∈ P) (hYC : Y ∈ dualPoint R Δ C) (hZC : Z ∈ dualPoint R Δ C) :
    Y = Z :=
  eq_of_axis_eq hR hiso hnd hΩ hΔ hP hY hZ (hYC.2.trans hZC.2.symm)

theorem mem_or_mem_dualPoint {P : Set (Subgroup G)} (hP : IsPoint Δ P) {C B : Subgroup G}
    (hC : C ∈ P) (hB : B ∈ lambdaSet R C) : B ∈ P ∨ B ∈ dualPoint R Δ C := by
  by_cases hBP : B ∈ P
  · exact Or.inl hBP
  · exact Or.inr ((mem_dualPoint_iff hR hiso hnd hΩ hΔ hP hC).2 (Or.inr ⟨hB, hBP⟩))

end Dual

end Linear

end CFSG.Timmesfeld.ARS
