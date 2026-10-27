module

public import CFSG.Timmesfeld.ARS.LinearDual

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Linear

section Hyper

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A)
  {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ)
include hR hiso hnd hΩ hΔ

theorem exists_opposite_of_ne {P P' : Set (Subgroup G)} (hP : IsPoint Δ P) (hP' : IsPoint Δ P')
    (hne : P ≠ P') : ∃ A ∈ P, ∃ B ∈ P', Opposite A B := by
  have hPw := hP.isWeakTI hR hΔ
  have hP'w := hP'.isWeakTI hR hΔ
  by_contra! hno
  have h1 : gen P ≤ Subgroup.normalizer ((gen P' : Subgroup G) : Set G) :=
    (gen_le fun A hA => le_stabSet_of_forall_not_opposite hR hiso hnd hΩ hΔ hP' (hPw.1 hA)
      fun B hB => hno A hA B hB).trans (Sec5.stabSet_le_normalizer_gen P')
  have h2 : gen P' ≤ Subgroup.normalizer ((gen P : Subgroup G) : Set G) :=
    (gen_le fun B hB => le_stabSet_of_forall_not_opposite hR hiso hnd hΩ hΔ hP (hP'w.1 hB)
      fun A hA hBA => hno A hA B hB hBA.symm).trans (Sec5.stabSet_le_normalizer_gen P)
  have hc : Commuting (gen P') (gen P) := by
    rw [commuting_iff_commutator_eq_bot, eq_bot_iff,
      ← gen_inf_gen_eq_bot hR hiso hnd hΩ hΔ hP' hP (Ne.symm hne)]
    exact le_inf (commutator_le_of_le_normalizer' le_rfl h1)
      (commutator_le_of_le_normalizer h2 le_rfl)
  obtain ⟨B, hB, -⟩ := hP'w.2.1
  exact hne (IsPoint.eq_of_mem hR hΔ hP hP' (Sec5.mem_of_commuting_gen hR hiso hnd hΩ hPw
    (hP'w.1 hB) (hc.mono (le_gen hB) le_rfl)) hB)

theorem card_gen_eq_card_mul_card_inf {P P' : Set (Subgroup G)} (hP : IsPoint Δ P)
    (hP' : IsPoint Δ P') (hne : P ≠ P') {E : Subgroup G} (hE : E ∈ R) :
    Nat.card (gen P) = Nat.card E * Nat.card ↥(gen P ⊓ stabSet P') := by
  have hPw := hP.isWeakTI hR hΔ
  have hP'w := hP'.isWeakTI hR hΔ
  obtain ⟨A, hA, B, hB, hAB⟩ := exists_opposite_of_ne hR hiso hnd hΩ hΔ hP hP' hne
  have hAR := hPw.1 hA
  have hBR := hP'w.1 hB
  set H := gen P ⊓ stabSet P' with hH
  have hBP : ¬ B ≤ stabSet P := not_le_stabSet_of_opposite hR hiso hnd hΩ hΔ hP hBR hA hAB.symm
  have hAH : A ⊓ H = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    by_contra hx1
    exact not_le_stabSet_of_opposite hR hiso hnd hΩ hΔ hP' hAR hB hAB
      (le_stabSet_of_mem_stabSet hR hiso hnd hΩ hΔ hP' hAR hx.1 hx1 hx.2.2)
  have hψ : ∀ C ∈ P, Special R C B → C ≤ H := by
    intro C hC hCB
    rcases le_stabSet_or_le_stabSet_of_special hR hiso hnd hΩ hΔ hP hP' hC hB hCB with h | h
    · exact le_inf (le_gen hC) h
    · exact absurd h hBP
  have hall : ∀ C ∈ P, C ≤ A ⊔ H := by
    intro C hC
    have hCR := hPw.1 hC
    by_cases hCA : C = A
    · exact hCA ▸ le_sup_left
    have hCB : ¬ Commuting C B := fun h =>
      hBP (Sec5.le_stabSet_of_commuting hR hPw hBR hC h.symm)
    have hne' : C ≠ B := fun e => hCB (e ▸ hR.commuting_self hCR)
    rcases hR.rel C hCR B hBR hne' with h | h | h
    · exact absurd h hCB
    · have hCl : C ∈ lambdaSet R A := Sec5.mem_lambdaSet hR hiso hnd hΩ hPw hA hC (Ne.symm hCA)
      obtain ⟨D, ⟨hDR, hDle, hDψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hAR hBR hAB hCl
      have hDP : D ∈ P := Sec5.mem_of_le_sup hR hiso hPw hA hC hCl hDR hDle
      have hDA : D ≠ A := by
        rintro rfl
        exact Special.not_opposite hR hBR hDψ.2 hAB.symm
      have hsup := sup_eq_of_le_of_commuting hR hiso hAR hCR hAR hDR hCl.1.2.2 le_sup_left hDle
        (Ne.symm hDA)
      calc C ≤ A ⊔ C := le_sup_right
        _ = A ⊔ D := hsup.symm
        _ ≤ A ⊔ H := sup_le_sup_left (hψ D hDP hDψ.2.symm) A
    · exact (hψ C hC h).trans le_sup_right
  have hgen : gen P = A ⊔ H :=
    le_antisymm (gen_le hall) (sup_le (le_gen hA) inf_le_left)
  have hcomm : Commuting A H :=
    (commuting_gen_of_isWeakTI_of hR hiso hnd hPw).mono (le_gen hA) inf_le_left
  rw [hgen, hR.card_eq hE hAR]
  exact le_antisymm (card_sup_le_of_commuting hcomm) (card_mul_card_le_card_sup hAH)

theorem not_gen_le_stabSet {P P' : Set (Subgroup G)} (hP : IsPoint Δ P) (hP' : IsPoint Δ P')
    (hne : P ≠ P') : ¬ gen P ≤ stabSet P' := by
  intro h
  obtain ⟨A, hA, -⟩ := (hP.isWeakTI hR hΔ).2.1
  have hAR := (hP.isWeakTI hR hΔ).1 hA
  have hcard := card_gen_eq_card_mul_card_inf hR hiso hnd hΩ hΔ hP hP' hne hAR
  rw [inf_of_le_left h] at hcard
  have hpos : 0 < Nat.card (gen P) := Nat.card_pos
  have h2 : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 (hR.ne_bot A hAR)
  have h1 : Nat.card A * Nat.card (gen P) = 1 * Nat.card (gen P) := by
    rw [one_mul]
    exact hcard.symm
  exact absurd (Nat.eq_of_mul_eq_mul_right hpos h1) h2.ne'

end Hyper

section Duality

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A)
  {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ) {C₀ : Subgroup G} (hC₀ : C₀ ∈ R)
include hR hiso hnd hΩ hΔ hC₀

omit [Finite G] hiso hnd hΩ hΔ in
theorem isPoint_dualPoint_iff {P : Set (Subgroup G)} :
    IsPoint (dualPoint R Δ C₀) P ↔ ∃ B ∈ R, P = dualPoint R Δ B := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨conjSub C₀ g, hR.conjSub_mem hC₀ g, (dualPoint_conjSub hR C₀ g).symm⟩
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hC₀ hB
    exact ⟨g, (dualPoint_conjSub hR C₀ g).symm⟩

theorem dualPoint_dualPoint {P : Set (Subgroup G)} (hP : IsPoint Δ P) {B : Subgroup G}
    (hB : B ∈ P) : dualPoint R (dualPoint R Δ C₀) B = P := by
  have hPw := hP.isWeakTI hR hΔ
  have hBR := hPw.1 hB
  have hΔ' := isTI_dualPoint hR hiso hnd hΩ hΔ hC₀
  have hP' : IsPoint (dualPoint R Δ C₀) (dualPoint R Δ B) :=
    (isPoint_dualPoint_iff hR hC₀).2 ⟨B, hBR, rfl⟩
  ext E
  rw [mem_dualPoint_iff hR hiso hnd hΩ hΔ' hP' (mem_dualPoint_self hBR)]
  constructor
  · rintro (rfl | ⟨hE, hEB⟩)
    · exact hB
    · rcases mem_or_mem_dualPoint hR hiso hnd hΩ hΔ hP hB hE with h | h
      · exact h
      · exact absurd h hEB
  · intro hE
    by_cases hEB : E = B
    · exact Or.inl hEB
    refine Or.inr ⟨Sec5.mem_lambdaSet hR hiso hnd hΩ hPw hB hE (Ne.symm hEB), fun h => hEB ?_⟩
    exact eq_of_mem_dualPoint hR hiso hnd hΩ hΔ hP hE hB h (mem_dualPoint_self hBR)

theorem le_stabSet_dualPoint_iff {P : Set (Subgroup G)} (hP : IsPoint Δ P) {X Y : Subgroup G}
    (hX : X ∈ P) (hY : Y ∈ R) : X ≤ stabSet (dualPoint R Δ Y) ↔ Y ≤ stabSet P := by
  have hXR := (hP.isWeakTI hR hΔ).1 hX
  have hΔ' := isTI_dualPoint hR hiso hnd hΩ hΔ hC₀
  have hP' : IsPoint (dualPoint R Δ C₀) (dualPoint R Δ Y) :=
    (isPoint_dualPoint_iff hR hC₀).2 ⟨Y, hY, rfl⟩
  rw [← inter_dualPoint_nonempty_iff hR hiso hnd hΩ hΔ' hP' hXR,
    dualPoint_dualPoint hR hiso hnd hΩ hΔ hC₀ hP hX, Set.inter_comm,
    inter_dualPoint_nonempty_iff hR hiso hnd hΩ hΔ hP hY]

end Duality

end Linear

end CFSG.Timmesfeld.ARS
