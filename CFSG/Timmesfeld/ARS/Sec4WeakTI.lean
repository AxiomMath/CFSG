module

public import CFSG.Timmesfeld.ARS.Sec4Lines
public import CFSG.Timmesfeld.ARS.Sec3Special

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

section WeakTI

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
include hR hiso hnd

theorem eq_of_forall_exists_opposite {Δ : Set (Subgroup G)} (hΔ : Δ ⊆ R) (hne : Δ.Nonempty)
    (hst : ∀ D ∈ R, ∀ d ∈ D, ∀ E ∈ Δ, conjSub E d = E → ∀ F ∈ Δ, conjSub F d ∈ Δ)
    (hopp : ∀ A ∈ Δ, ∃ C ∈ Δ, Opposite A C) : Δ = R := by
  refine eq_of_forall_lambdaSet_subset hR hiso hnd hΔ hne fun A hA B hB => ?_
  have hAR := hΔ hA
  obtain ⟨C, hCΔ, hAC⟩ := hopp A hA
  have hCR := hΔ hCΔ
  obtain ⟨B₁, ⟨hB₁R, hB₁le, hB₁ψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hAR hCR hAC hB
  have hAB₁ : A ≠ B₁ := by
    rintro rfl
    exact Special.not_opposite hR hCR hB₁ψ.2 hAC.symm
  obtain ⟨hB₁Λ, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hAR hB hAR le_sup_left hB₁R hB₁le hAB₁
  have hS := Sec3.setOf_mem_le_sup_eq hR hiso hAR hCR hAC hB₁Λ hB₁ψ
  rw [hsup] at hS
  have hN := Sec3.commuting_sup_commutator hR hB₁Λ hB₁ψ
  have hpt : ∀ T ∈ R, T ≤ A ⊔ B → T ≠ B₁ → T ∈ Δ := by
    intro T hT hTle hTB₁
    have hmem : T ∈ {D | D ∈ R ∧ D ≤ A ⊔ B} := ⟨hT, hTle⟩
    rw [hS] at hmem
    rcases hmem with h | ⟨⟨n, hn⟩, rfl⟩
    · exact absurd h hTB₁
    obtain ⟨c, hc, e, he, rfl⟩ := (Sec3.mem_sup_commutator_iff hB₁ψ).1 hn
    have hce : c * e = e * c :=
      (hN c (Subgroup.mem_sup_left hc) e (Subgroup.mem_sup_right he)).eq
    change conjSub A (c * e) ∈ Δ
    rw [hce, conjSub_mul, conjSub_of_forall_commute fun a ha => (hB₁Λ.1.2.2 a ha c hc).symm]
    exact hst _ hB₁ψ.2.1 e he C hCΔ
      (conjSub_of_forall_commute fun x hx => hB₁ψ.2.2.1 e he x hx) A hA
  have hB₁Δ : B₁ ∈ Δ := by
    obtain ⟨Q, hQ, hQle, hQA, hQB₁⟩ := exists_mem_le_sup_ne_ne hR hiso hAR hB A B₁
    obtain ⟨U, hU, u, hu, hQu⟩ :=
      exists_mem_lambdaSet_conjSub_eq hR hiso hAR hB hQ hQle hQA hB₁R hB₁le hAB₁.symm
    rw [← hQu]
    exact hst U hU.1.1 u hu A hA
      (conjSub_of_forall_commute fun a ha => (hU.1.2.2 a ha u hu).symm) Q (hpt Q hQ hQle hQB₁)
  by_cases hBB₁ : B = B₁
  · exact hBB₁ ▸ hB₁Δ
  · exact hpt B hB.1.1 le_sup_right hBB₁

variable {Δ : Set (Subgroup G)}

theorem not_opposite_of_isWeakTI (hΔ : IsWeakTI R Δ) {A B : Subgroup G} (hA : A ∈ Δ)
    (hB : B ∈ Δ) : ¬ Opposite A B := by
  intro hAB
  set Δ' := {D | D ∈ Δ ∧ ∃ E ∈ Δ, Opposite D E} with hΔ'
  have hΔ'eq : Δ' = R := by
    refine eq_of_forall_exists_opposite hR hiso hnd (fun D hD => hΔ.1 hD.1) ⟨A, hA, B, hB, hAB⟩
      ?_ ?_
    · rintro D hD d hd E ⟨hEΔ, -⟩ hEd F ⟨hFΔ, F', hF'Δ, hFF'⟩
      exact ⟨hΔ.conjSub_mem hR hD hd hEΔ hEd hFΔ, conjSub F' d,
        hΔ.conjSub_mem hR hD hd hEΔ hEd hF'Δ, Opposite.conj hFF' d⟩
    · rintro D ⟨hDΔ, E, hEΔ, hDE⟩
      exact ⟨E, ⟨hEΔ, D, hDΔ, hDE.symm⟩, hDE⟩
  exact hΔ.2.2.1 (Set.Subset.antisymm hΔ.1 fun E hE => (hΔ'eq ▸ hE : E ∈ Δ').1)

theorem isPGroup_gen_of_isWeakTI (hΔ : IsWeakTI R Δ) : IsPGroup 2 (gen Δ) :=
  isPGroup_of_forall_isPGroup_sup (S := Δ) (fun _ hE => le_gen hE) le_rfl
    (fun _ hE _ hm => conjSub_mem_of_mem_stabSet (hΔ.gen_le_stabSet hR hm) hE)
    (fun _ hE _ hF => isPGroup_sup_of_not_opposite hR (hΔ.1 hE) (hΔ.1 hF)
      (not_opposite_of_isWeakTI hR hiso hnd hΔ hE hF))

omit hnd in
theorem exists_mem_stabSet_conjSub_eq_commutator (hΔ : IsWeakTI R Δ) {A B : Subgroup G}
    (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : Special R A B) :
    ∃ g ∈ stabSet Δ, conjSub A g = ⁅A, B⁆ := by
  have hAR := hΔ.1 hA
  have hBR := hΔ.1 hB
  have hCR : ⁅A, B⁆ ∈ R := hAB.1
  have hCΛ : ⁅A, B⁆ ∈ lambdaSet R A :=
    mem_lambdaSet_comm hCR (mem_lambdaSet_commutator hR hiso hAR hBR hAB).1
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hBR
  have hA'R : conjSub A b ∈ R := hR.conjSub_mem hAR b
  have hA'Δ : conjSub A b ∈ Δ := hΔ.conjSub_mem hR hBR hb hB (conjSub_of_mem hb) hA
  have hA'le : conjSub A b ≤ A ⊔ ⁅A, B⁆ := (conjSub_le_commutator_sup hb).trans (sup_comm _ _).le
  have hA'A : conjSub A b ≠ A := Sec3.conjSub_ne_of_special hR hiso hBR hAR hAB.symm hb hb1
  have hA'C : conjSub A b ≠ ⁅A, B⁆ := by
    intro e
    apply hAB.not_commuting hR
    have h1 : Commuting (conjSub A b) B := e ▸ hAB.2.2
    have h2 := h1.conjSub b⁻¹
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one, conjSub_of_mem (B.inv_mem hb)] at h2
  obtain ⟨hAΛ, hsup⟩ :=
    mem_lambdaSet_of_le_sup hR hiso hAR hCΛ hA'R hA'le hAR le_sup_left hA'A
  obtain ⟨U, hU, u, hu, hAu⟩ := exists_mem_lambdaSet_conjSub_eq hR hiso hA'R hAΛ hAR
    le_sup_right hA'A.symm hCR (hsup ▸ le_sup_right) hA'C.symm
  refine ⟨u, mem_stabSet_of_mul_self (hR.mul_self U hU.1.1 u hu) fun F hF => ?_, hAu⟩
  exact hΔ.conjSub_mem hR hU.1.1 hu hA'Δ
    (conjSub_of_forall_commute fun x hx => (hU.1.2.2 x hx u hu).symm) hF

omit [Finite G] hR hiso hnd in
theorem conjSub_lowerCentralSeries_gen {g : G} (hg : g ∈ stabSet Δ) (n : ℕ) :
    conjSub ((gen Δ).lowerCentralSeries n) g = (gen Δ).lowerCentralSeries n := by
  have hX : conjSub (gen Δ) g = gen Δ := by rw [conjSub_gen, mem_stabSet.1 hg]
  induction n with
  | zero => rwa [Subgroup.lowerCentralSeries_zero]
  | succ n ih => rw [Subgroup.lowerCentralSeries_succ, conjSub, Subgroup.map_commutator, ← conjSub,
      ← conjSub, ih, hX]

theorem not_special_of_isWeakTI (hΔ : IsWeakTI R Δ) {A B : Subgroup G} (hA : A ∈ Δ)
    (hB : B ∈ Δ) : ¬ Special R A B := by
  intro hAB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries (gen Δ)).1
    (isPGroup_gen_of_isWeakTI hR hiso hnd hΔ).isNilpotent
  have key : ∀ i : ℕ, ∀ A ∈ Δ, ∀ B ∈ Δ, Special R A B → A ≤ (gen Δ).lowerCentralSeries i := by
    intro i
    induction i with
    | zero => exact fun A hA _ _ _ => by rw [Subgroup.lowerCentralSeries_zero]; exact le_gen hA
    | succ i ih =>
      intro A hA B hB hAB
      obtain ⟨g, hg, hAg⟩ := exists_mem_stabSet_conjSub_eq_commutator hR hiso hΔ hA hB hAB
      have hC : conjSub A g ≤ (gen Δ).lowerCentralSeries (i + 1) := by
        rw [hAg, Subgroup.lowerCentralSeries_succ]
        exact Subgroup.commutator_mono (ih A hA B hB hAB) (le_gen hB)
      have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hC
      rwa [← conjSub, ← conjSub, ← conjSub_mul, inv_mul_cancel, conjSub_one,
        conjSub_lowerCentralSeries_gen (Subgroup.inv_mem _ hg)] at this
  apply hR.ne_bot A (hΔ.1 hA)
  rw [eq_bot_iff, ← hn]
  exact key n A hA B hB hAB

theorem commuting_gen_of_isWeakTI_of (hΔ : IsWeakTI R Δ) : Commuting (gen Δ) (gen Δ) := by
  refine commuting_gen_of_pairwise fun B hB C hC => ?_
  by_cases hBC : B = C
  · rw [hBC]
    exact hR.commuting_self (hΔ.1 hC)
  rcases hR.rel B (hΔ.1 hB) C (hΔ.1 hC) hBC with h | h | h
  · exact h
  · exact absurd h (not_opposite_of_isWeakTI hR hiso hnd hΔ hB hC)
  · exact absurd h (not_special_of_isWeakTI hR hiso hnd hΔ hB hC)

end WeakTI

theorem commuting_gen_of_isWeakTI (h : Hyp G R) {Δ : Set (Subgroup G)} (hΔ : IsWeakTI R Δ) :
    Commuting (gen Δ) (gen Δ) := by
  have := h.finite
  exact commuting_gen_of_isWeakTI_of h.root h.noIsolated h.nondeg hΔ

end CFSG.Timmesfeld.ARS
