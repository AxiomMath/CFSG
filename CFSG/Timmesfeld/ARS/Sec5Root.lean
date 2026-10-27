module

public import CFSG.Timmesfeld.ARS.Sec5Nine

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec5

@[expose] def rootConj (R Δ : Set (Subgroup G)) : Set (Set (Subgroup G)) :=
  {Θ | ∃ d : G, (d = 1 ∨ d ∈ rootElts R) ∧ Θ = conjSet Δ d}

theorem eq_or_inter_eq_empty_of_mem_rootConj (hR : IsRootClass R) {Δ Θ : Set (Subgroup G)}
    (hΔ : IsWeakTI R Δ) (hΘ : Θ ∈ rootConj R Δ) : Θ = Δ ∨ Δ ∩ Θ = ∅ := by
  obtain ⟨d, rfl | hd, rfl⟩ := hΘ
  · exact Or.inl (conjSet_one Δ)
  · rcases ((isWeakTI_iff hR).1 hΔ).2.2.2 d hd with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem eq_of_mem_rootConj_of_mem (hR : IsRootClass R) {Δ Θ : Set (Subgroup G)}
    (hΔ : IsWeakTI R Δ) (hΘ : Θ ∈ rootConj R Δ) {X : Subgroup G} (hX : X ∈ Δ) (hXΘ : X ∈ Θ) :
    Θ = Δ := by
  rcases eq_or_inter_eq_empty_of_mem_rootConj hR hΔ hΘ with h | h
  · exact h
  · exact absurd (h ▸ (⟨hX, hXΘ⟩ : X ∈ Δ ∩ Θ)) (Set.notMem_empty X)

section Root

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {Δ : Set (Subgroup G)}
include hR hiso hnd hΩ

theorem exists_mem_rootConj (hΔ : IsWeakTI R Δ) {E : Subgroup G} (hE : E ∈ R) :
    ∃ Θ ∈ rootConj R Δ, E ∈ Θ := by
  by_cases hEΔ : E ∈ Δ
  · exact ⟨Δ, ⟨1, Or.inl rfl, (conjSet_one Δ).symm⟩, hEΔ⟩
  by_cases hc : ∃ D ∈ Δ, Commuting E D
  · obtain ⟨D, hD, hED⟩ := hc
    obtain ⟨P, hP, hEl⟩ := exists_mem_lambdaSet_of_commuting hR hiso hnd hΩ hΔ hE hEΔ hD hED
    have hPR := hΔ.1 hP
    obtain ⟨Y, hY, hYle, hYP, hYE⟩ := exists_mem_le_sup_ne_ne hR hiso hPR hEl P E
    obtain ⟨hPY, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hPR hEl hY hYle hPR le_sup_left hYP
    obtain ⟨U, hU, u, hu, hPu⟩ := exists_mem_lambdaSet_conjSub_eq hR hiso hY hPY hPR le_sup_right
      (Ne.symm hYP) hE (hsup ▸ le_sup_right) (Ne.symm hYE)
    have hu1 : u ≠ 1 := by
      rintro rfl
      rw [conjSub_one] at hPu
      exact hEΔ (hPu ▸ hP)
    exact ⟨_, ⟨u, Or.inr ⟨U, hU.1.1, hu, hu1⟩, rfl⟩, hPu ▸ conjSub_mem_conjSet hP u⟩
  · simp only [not_exists, not_and] at hc
    obtain ⟨A, hA, hAE⟩ := exists_opposite_of_forall_not_commuting hR hiso hnd hΩ hΔ hE hc
    obtain ⟨a, -, -, w, hw, hw1, -, hAw, -⟩ := exists_swap hR (hΔ.1 hA) hE hAE
    exact ⟨_, ⟨w, Or.inr ⟨_, hR.conjSub_mem hE a, hw, hw1⟩, rfl⟩, hAw ▸ conjSub_mem_conjSet hA w⟩

theorem eq_conjSet_swap (hΔ : IsWeakTI R Δ) {A E : Subgroup G} (hA : A ∈ Δ) (hE : E ∈ R)
    (hEΔ : ∀ D ∈ Δ, ¬ Commuting E D) (hAE : Opposite A E) {w : G} (hwF : w * w = 1)
    (hwX : w ∈ A ⊔ E) (hEw : conjSub E w = A) {Θ : Set (Subgroup G)} (hΘ : Θ ∈ rootConj R Δ)
    (hEΘ : E ∈ Θ) : Θ = conjSet Δ w := by
  have hAR := hΔ.1 hA
  have hEnΔ : E ∉ Δ := fun h => hEΔ E h (hR.commuting_self hE)
  obtain ⟨d, rfl | ⟨D, hD, hd, hd1⟩, rfl⟩ := hΘ
  · rw [conjSet_one] at hEΘ
    exact absurd hEΘ hEnΔ
  have hΘw := isWeakTI_conjSet hR hΔ d
  obtain ⟨A', hA'def⟩ : ∃ A', A' = conjSub A d := ⟨_, rfl⟩
  have hA'Θ : A' ∈ conjSet Δ d := hA'def ▸ conjSub_mem_conjSet hA d
  have hA'R : A' ∈ R := hA'def ▸ hR.conjSub_mem hAR d
  have hA'le : A' ≤ A ⊔ D := hA'def ▸ conjSub_le le_sup_left (Subgroup.mem_sup_right hd)
  have hA'A : A' ≠ A := by
    intro e
    have := eq_of_mem_rootConj_of_mem hR hΔ ⟨d, Or.inr ⟨D, hD, hd, hd1⟩, rfl⟩ hA (e ▸ hA'Θ)
    exact hEnΔ (this ▸ hEΘ)
  by_cases hA'E : A' = E
  ·
    have hAD : Opposite A D := opposite_of_conjSub hR hAR hD hd (hA'def ▸ hA'A)
      (by rw [← hA'def, hA'E]; exact hAE.not_commuting (hR.ne_bot A hAR))
    have hDX : D ≤ A ⊔ E := by
      have hsupeq := sup_eq_of_le hR hAR hE hAR hAD hAE.1 (sup_le le_sup_left (hA'E ▸ hA'le))
      exact le_sup_right.trans hsupeq.ge
    obtain ⟨X₀, hX₀, hX₀A⟩ : ∃ X₀ ∈ Δ, X₀ ≠ A := by
      obtain ⟨X, hX, Y, hY, hXY⟩ := hΔ.2.1
      by_cases h : X = A
      · exact ⟨Y, hY, fun e => hXY (h.trans e.symm)⟩
      · exact ⟨X, hX, h⟩
    have hX₀l := mem_lambdaSet hR hiso hnd hΩ hΔ hA hX₀ (Ne.symm hX₀A)
    obtain ⟨B, ⟨hBR, hBle, hBψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hAR hE hAE hX₀l
    have hBΔ : B ∈ Δ := mem_of_le_sup hR hiso hΔ hA hX₀ hX₀l hBR hBle
    have hBA : B ≠ A := fun e => Special.not_opposite hR hE hBψ.2 (e ▸ hAE.symm)
    have hBl : B ∈ lambdaSet R A := mem_lambdaSet hR hiso hnd hΩ hΔ hA hBΔ (Ne.symm hBA)
    have hn : w * d ∈ A ⊔ E := Subgroup.mul_mem _ hwX (hDX hd)
    have hAn : conjSub A (w * d) = A := by rw [conjSub_mul, ← hA'def, hA'E, hEw]
    have hBn : conjSub B (w * d) = B := by
      refine QD.eq_of_le_of_mem hR hiso (hR.conjSub_mem hBR _) hBR fun y hy => ?_
      have hyN : y ∈ B ⊔ ⁅E, B⁆ := by
        rw [← Sec3.conjSub_sup_commutator_eq hR hiso hAR hE hAE hBl hBψ hn]
        exact Subgroup.map_mono le_sup_left hy
      refine Sec3.mem_of_forall_commute_of_mem_sup hR hiso hAR hE hAE hBl hBψ hyN fun a ha => ?_
      have h1 := hBl.1.2.2.conjSub (w * d)
      rw [hAn] at h1
      exact h1 a ha y hy
    have hΔn : conjSet Δ (w * d) = Δ := by
      refine eq_of_mem_of_mem hR hiso hnd hΩ hΔ (isWeakTI_conjSet hR hΔ _) (card_conjSet Δ _) hA
        (hAn ▸ conjSub_mem_conjSet hA _) hBΔ (hBn ▸ conjSub_mem_conjSet hBΔ _) (Ne.symm hBA)
    rw [show d = w * (w * d) by rw [← mul_assoc, hwF, one_mul], conjSet_mul, hΔn]
  ·
    have hA'l : A' ∈ lambdaSet R E := mem_lambdaSet hR hiso hnd hΩ hΘw hEΘ hA'Θ (Ne.symm hA'E)
    have hnc : ¬ Commuting A A' := not_commuting_of_opposite_of_mem_lambdaSet hR hAR hAE hA'l
    have hAD : Opposite A D := opposite_of_conjSub hR hAR hD hd (hA'def ▸ hA'A) (hA'def ▸ hnc)
    have hAA' : Opposite A A' := hA'def ▸ opposite_conjSub_self hAD hd hd1
    have hDX : D ≤ A' ⊔ A := by
      have hsupeq := sup_eq_of_le hR hAR hA'R hAR hAD hA'A.symm (sup_le le_sup_left hA'le)
      rw [sup_comm]
      exact le_sup_right.trans hsupeq.ge
    obtain ⟨P, ⟨hPR, hPle, hPψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hE hAR hAE.symm hA'l
    have hPE : E ≠ P := fun e => Special.not_opposite hR hAR hPψ.2 (e ▸ hAE)
    have hPA' : A' ≠ P := fun e => Special.not_opposite hR hAR hPψ.2 (e ▸ hAA')
    have hPl := (mem_lambdaSet_of_le_sup hR hiso hE hA'l hE le_sup_left hPR hPle hPE).1
    have hPl' := (mem_lambdaSet_of_le_sup hR hiso hE hA'l hA'R le_sup_right hPR hPle hPA').1
    have hPΘ : P ∈ conjSet Δ d := mem_of_le_sup hR hiso hΘw hEΘ hA'Θ hA'l hPR hPle
    have hwX' : w ∈ E ⊔ A := sup_comm A E ▸ hwX
    have hEn : conjSub E (d * w) = A' := by rw [conjSub_mul, hEw, hA'def]
    have hQN : conjSub P w ≤ P ⊔ ⁅A, P⁆ := by
      rw [← Sec3.conjSub_sup_commutator_eq hR hiso hE hAR hAE.symm hPl hPψ hwX']
      exact Subgroup.map_mono le_sup_left
    have hPn : conjSub P (d * w) = P := by
      refine QD.eq_of_le_of_mem hR hiso (hR.conjSub_mem hPR _) hPR fun y hy => ?_
      rw [conjSub_mul] at hy
      have hyN : y ∈ P ⊔ ⁅A, P⁆ := by
        rw [← Sec3.conjSub_sup_commutator_eq hR hiso hA'R hAR hAA'.symm hPl' hPψ (hDX hd)]
        exact Subgroup.map_mono hQN hy
      refine Sec3.mem_of_forall_commute_of_mem_sup hR hiso hA'R hAR hAA'.symm hPl' hPψ hyN
        fun a' ha' => ?_
      have h1 := (hPl.1.2.2.conjSub w).conjSub d
      rw [hEw, ← hA'def] at h1
      exact h1 a' ha' y hy
    have hΘn : conjSet (conjSet Δ d) (d * w) = conjSet Δ d :=
      eq_of_mem_of_mem hR hiso hnd hΩ hΘw (isWeakTI_conjSet hR hΘw _) (card_conjSet _ _) hA'Θ
        (hEn ▸ conjSub_mem_conjSet hEΘ _) hPΘ (hPn ▸ conjSub_mem_conjSet hPΘ _) hPA'
    apply conjSet_injective (d * w)
    change conjSet (conjSet Δ d) (d * w) = conjSet (conjSet Δ w) (d * w)
    rw [hΘn, ← conjSet_mul, mul_assoc, hwF, mul_one]

theorem eq_of_mem_rootConj (hΔ : IsWeakTI R Δ)
    (hsec : ∀ P ∈ Δ, ∃ g : G, P ∈ conjSet Δ g ∧ conjSet Δ g ≠ Δ)
    (h2 : ∀ (X : Subgroup G) (g₁ g₂ g₃ : G), X ∈ conjSet Δ g₁ → X ∈ conjSet Δ g₂ →
      X ∈ conjSet Δ g₃ → conjSet Δ g₁ = conjSet Δ g₂ ∨ conjSet Δ g₁ = conjSet Δ g₃ ∨
        conjSet Δ g₂ = conjSet Δ g₃)
    {Θ₁ Θ₂ : Set (Subgroup G)} (h₁ : Θ₁ ∈ rootConj R Δ) (h₂ : Θ₂ ∈ rootConj R Δ)
    {E : Subgroup G} (hE₁ : E ∈ Θ₁) (hE₂ : E ∈ Θ₂) : Θ₁ = Θ₂ := by
  obtain ⟨d₁, hd₁, rfl⟩ := h₁
  obtain ⟨d₂, hd₂, rfl⟩ := h₂
  have hER : E ∈ R := (isWeakTI_conjSet hR hΔ d₁).1 hE₁
  by_cases hEΔ : E ∈ Δ
  · rw [eq_of_mem_rootConj_of_mem hR hΔ ⟨d₁, hd₁, rfl⟩ hEΔ hE₁,
      eq_of_mem_rootConj_of_mem hR hΔ ⟨d₂, hd₂, rfl⟩ hEΔ hE₂]
  by_cases hc : ∃ D ∈ Δ, Commuting E D
  · obtain ⟨D, hD, hED⟩ := hc
    obtain ⟨P, hP, hEl⟩ := exists_mem_lambdaSet_of_commuting hR hiso hnd hΩ hΔ hER hEΔ hD hED
    obtain ⟨g, hPg, hg⟩ := hsec P hP
    have hEg := mem_conjSet_of_mem_lambdaSet hR hiso hnd hΩ hΔ hsec h2 hP hEl hEΔ hPg hg
    have hne : ∀ d, (d = 1 ∨ d ∈ rootElts R) → E ∈ conjSet Δ d → conjSet Δ d ≠ conjSet Δ g := by
      intro d hd hEd e
      have := eq_of_mem_rootConj_of_mem hR hΔ ⟨d, hd, rfl⟩ hP (e ▸ hPg)
      exact hEΔ (this ▸ hEd)
    rcases h2 E d₁ d₂ g hE₁ hE₂ hEg with h | h | h
    · exact h
    · exact absurd h (hne d₁ hd₁ hE₁)
    · exact absurd h (hne d₂ hd₂ hE₂)
  · simp only [not_exists, not_and] at hc
    obtain ⟨A, hA, hAE⟩ := exists_opposite_of_forall_not_commuting hR hiso hnd hΩ hΔ hER hc
    obtain ⟨a, -, -, w, hw, -, hwX, -, hEw⟩ := exists_swap hR (hΔ.1 hA) hER hAE
    have hwF : w * w = 1 := hR.mul_self _ (hR.conjSub_mem hER a) w hw
    rw [eq_conjSet_swap hR hiso hnd hΩ hΔ hA hER hc hAE hwF hwX hEw ⟨d₁, hd₁, rfl⟩ hE₁,
      eq_conjSet_swap hR hiso hnd hΩ hΔ hA hER hc hAE hwF hwX hEw ⟨d₂, hd₂, rfl⟩ hE₂]

end Root

end Sec5

end CFSG.Timmesfeld.ARS
