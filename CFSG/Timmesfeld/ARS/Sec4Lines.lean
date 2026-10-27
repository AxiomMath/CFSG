module

public import CFSG.Timmesfeld.ARS.Sec4Defs
public import CFSG.Timmesfeld.ARS.Sec3Lines

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

section Lines

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
include hR hiso

theorem mem_lambdaSet_of_le_sup {Y P Q₁ Q₂ : Subgroup G} (hY : Y ∈ R) (hP : P ∈ lambdaSet R Y)
    (hQ₁ : Q₁ ∈ R) (hQ₁le : Q₁ ≤ Y ⊔ P) (hQ₂ : Q₂ ∈ R) (hQ₂le : Q₂ ≤ Y ⊔ P) (hne : Q₁ ≠ Q₂) :
    Q₂ ∈ lambdaSet R Q₁ ∧ Q₁ ⊔ Q₂ = Y ⊔ P := by
  have hPR : P ∈ R := hP.1.1
  have hline : Commuting (Y ⊔ P) (Y ⊔ P) :=
    Commuting.sup_left (Commuting.sup_right (hR.commuting_self hY) hP.1.2.2)
      (Commuting.sup_right hP.1.2.2.symm (hR.commuting_self hPR))
  have hsup := sup_eq_of_le_of_commuting hR hiso hY hPR hQ₁ hQ₂ hP.1.2.2 hQ₁le hQ₂le hne
  exact ⟨⟨⟨hQ₂, hne.symm, hline.mono hQ₁le hQ₂le⟩, hsup ▸ hP.2⟩, hsup⟩

theorem ncard_setOf_mem_le_sup {Y P : Subgroup G} (hY : Y ∈ R) (hP : P ∈ lambdaSet R Y) :
    {Q | Q ∈ R ∧ Q ≤ Y ⊔ P}.ncard = Nat.card Y + 1 := by
  have h := (line_card_and_transitive hR hiso hY hP).1
  rw [hR.card_eq hP.1.1 hY, sup_comm] at h
  rw [← Nat.card_coe_set_eq]
  exact h

theorem exists_mem_le_sup_notMem {Y P : Subgroup G} (hY : Y ∈ R) (hP : P ∈ lambdaSet R Y)
    {s : Set (Subgroup G)} (hs : s.ncard ≤ Nat.card Y) : ∃ Q ∈ R, Q ≤ Y ⊔ P ∧ Q ∉ s := by
  by_contra! h
  have hsub : {Q | Q ∈ R ∧ Q ≤ Y ⊔ P} ⊆ s := fun Q hQ => h Q hQ.1 hQ.2
  have := Set.ncard_le_ncard hsub (Set.toFinite s)
  rw [ncard_setOf_mem_le_sup hR hiso hY hP] at this
  omega

theorem exists_mem_le_sup_ne_ne {Y P : Subgroup G} (hY : Y ∈ R) (hP : P ∈ lambdaSet R Y)
    (Q₁ Q₂ : Subgroup G) : ∃ Q ∈ R, Q ≤ Y ⊔ P ∧ Q ≠ Q₁ ∧ Q ≠ Q₂ := by
  have hY2 : 2 ≤ Nat.card Y := (Subgroup.one_lt_card_iff_ne_bot Y).2 (hR.ne_bot Y hY)
  have hs : ({Q₁, Q₂} : Set (Subgroup G)).ncard ≤ Nat.card Y :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]; omega)
  obtain ⟨Q, hQ, hQle, hQs⟩ := exists_mem_le_sup_notMem hR hiso hY hP hs
  exact ⟨Q, hQ, hQle, fun e => hQs (Or.inl e), fun e => hQs (Or.inr e)⟩

theorem exists_mem_lambdaSet_conjSub_eq {Y P Q Q' : Subgroup G} (hY : Y ∈ R)
    (hP : P ∈ lambdaSet R Y) (hQ : Q ∈ R) (hQle : Q ≤ Y ⊔ P) (hQY : Q ≠ Y) (hQ' : Q' ∈ R)
    (hQ'le : Q' ≤ Y ⊔ P) (hQ'Y : Q' ≠ Y) : ∃ U ∈ lambdaSet R Y, ∃ u ∈ U, conjSub Q u = Q' := by
  obtain ⟨-, E, -, F, -, -, hnorm, htrans, -⟩ := line_card_and_transitive hR hiso hY hP
  obtain ⟨D₀, hD₀, hYD₀⟩ := hiso Y hY
  obtain ⟨S, ⟨hSR, hSle, hSψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hY hD₀ hYD₀ hP
  have hSY : S ≠ Y := by
    rintro rfl
    exact Special.not_opposite hR hD₀ hSψ.2 hYD₀.symm
  obtain ⟨x, hx, hxS⟩ := htrans S hSR (sup_comm Y P ▸ hSle) Y hY le_sup_right
  set Y' := conjSub Y x with hY'def
  have hY'R : Y' ∈ R := hR.conjSub_mem hY x
  have hY'le : Y' ≤ Y ⊔ P := by
    have h1 : conjSub Y x ≤ conjSub (P ⊔ Y) x := Subgroup.map_mono le_sup_right
    rw [hnorm x hx, sup_comm] at h1
    exact h1
  have hY'Y : Y' ≠ Y := fun e => hSY (map_conj_inj.1 (hxS.trans e.symm))
  set D' := conjSub D₀ x with hD'def
  have hD'R : D' ∈ R := hR.conjSub_mem hD₀ x
  have hD'sp : Special R D' Y := by
    have := Sec3.special_conjSub hR hSψ.2 x
    rwa [hxS] at this
  have hY'D' : Opposite Y' D' := Opposite.conj hYD₀ x
  obtain ⟨hYΛ, hline⟩ := mem_lambdaSet_of_le_sup hR hiso hY hP hY'R hY'le hY le_sup_left hY'Y
  have hS := Sec3.setOf_mem_le_sup_eq hR hiso hY'R hD'R hY'D' hYΛ ⟨hY, hD'sp⟩
  rw [hline] at hS
  have hUR : ⁅D', Y⁆ ∈ R := hD'sp.1
  have hUΛ : ⁅D', Y⁆ ∈ lambdaSet R Y :=
    mem_lambdaSet_comm hUR (mem_lambdaSet_commutator hR hiso hD'R hY hD'sp).2
  have hN := Sec3.commuting_sup_commutator hR hYΛ ⟨hY, hD'sp⟩
  have hpt : ∀ T ∈ R, T ≤ Y ⊔ P → T ≠ Y → ∃ u ∈ ⁅D', Y⁆, conjSub Y' u = T := by
    intro T hT hTle hTY
    have hmem : T ∈ {D | D ∈ R ∧ D ≤ Y ⊔ P} := ⟨hT, hTle⟩
    rw [hS] at hmem
    rcases hmem with h | ⟨⟨n, hn⟩, rfl⟩
    · exact absurd h hTY
    obtain ⟨y, hy, u, hu, rfl⟩ := (Sec3.mem_sup_commutator_iff ⟨hY, hD'sp⟩).1 hn
    refine ⟨u, hu, ?_⟩
    have hyu : y * u = u * y :=
      (hN y (Subgroup.mem_sup_left hy) u (Subgroup.mem_sup_right hu)).eq
    change conjSub Y' u = conjSub Y' (y * u)
    rw [hyu, conjSub_mul, conjSub_of_forall_commute fun z hz => (hYΛ.1.2.2 z hz y hy).symm]
  obtain ⟨u, hu, rfl⟩ := hpt Q hQ hQle hQY
  obtain ⟨u', hu', rfl⟩ := hpt Q' hQ' hQ'le hQ'Y
  refine ⟨_, hUΛ, u' * u⁻¹, Subgroup.mul_mem _ hu' (Subgroup.inv_mem _ hu), ?_⟩
  rw [← conjSub_mul, inv_mul_cancel_right]

end Lines

section Closure

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
include hR hiso hnd

theorem lambdaSet_nonempty {A : Subgroup G} (hA : A ∈ R) : (lambdaSet R A).Nonempty := by
  obtain ⟨E, hE, F, hF, hEF⟩ := hnd
  have hEΛ := (mem_lambdaSet_commutator hR hiso hE hF hEF).1
  obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hEF.1 hA
  exact ⟨_, conjSub_mem_lambdaSet hR hEΛ g⟩

theorem eq_of_forall_lambdaSet_subset {Δ : Set (Subgroup G)} (hΔ : Δ ⊆ R) (hne : Δ.Nonempty)
    (hΛ : ∀ A ∈ Δ, lambdaSet R A ⊆ Δ) : Δ = R := by
  have hΨ : ∀ D ∈ Δ, ∀ C ∈ R, Special R D C → C ∈ Δ := by
    intro D hD C hC hs
    have h1 := mem_lambdaSet_commutator hR hiso (hΔ hD) hC hs
    exact hΛ _ (hΛ D hD (mem_lambdaSet_comm hs.1 h1.1)) h1.2
  have hΩ : ∀ A ∈ Δ, ∀ C ∈ R, Opposite A C → C ∈ Δ := by
    intro A hA C hC hAC
    have hAR := hΔ hA
    obtain ⟨B, hB⟩ := lambdaSet_nonempty hR hiso hnd hAR
    have hCB : ¬ Commuting C B := not_commuting_of_opposite_of_mem_lambdaSet hR hC hAC.symm hB
    have hne : C ≠ B := fun e => hCB (e ▸ hR.commuting_self hC)
    rcases hR.rel C hC B hB.1.1 hne with h | h | h
    · exact absurd h hCB
    · obtain ⟨D, ⟨hDR, hDle, hDψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hAR hC hAC hB
      have hDA : A ≠ D := by
        rintro rfl
        exact Special.not_opposite hR hC hDψ.2 hAC.symm
      have hDΛ := (mem_lambdaSet_of_le_sup hR hiso hAR hB hAR le_sup_left hDR hDle hDA).1
      exact hΨ D (hΛ A hA hDΛ) C hC hDψ.2.symm
    · exact hΨ B (hΛ A hA hB) C hC h.symm
  apply Set.Subset.antisymm hΔ
  intro E hE
  obtain ⟨A₀, hA₀⟩ := hne
  have hpath := opposite_reflTransGen hR hiso (hΔ hA₀) hE
  induction hpath with
  | refl => exact hA₀
  | tail _ hCD ih => exact hΩ _ (ih hCD.1) _ hCD.2.1 hCD.2.2

theorem lambdaSet_reflTransGen {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) :
    Relation.ReflTransGen (fun C D => D ∈ lambdaSet R C) A B := by
  set Δ := {D | Relation.ReflTransGen (fun C D => D ∈ lambdaSet R C) A D} with hΔ
  have hΔR : Δ ⊆ R := by
    intro D hD
    induction hD with
    | refl => exact hA
    | tail _ h _ => exact h.1.1
  have hΔeq := eq_of_forall_lambdaSet_subset hR hiso hnd hΔR ⟨A, Relation.ReflTransGen.refl⟩
    fun D hD E hE => Relation.ReflTransGen.tail hD hE
  exact (hΔeq ▸ hB : B ∈ Δ)

end Closure

section Gen

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
include hR hiso hnd

theorem le_gen_lambdaSet {A : Subgroup G} (hA : A ∈ R) : A ≤ gen (lambdaSet R A) := by
  obtain ⟨C, hC⟩ := lambdaSet_nonempty hR hiso hnd hA
  obtain ⟨Q, hQ, hQle, hQA, hQC⟩ := exists_mem_le_sup_ne_ne hR hiso hA hC A C
  have hQΛ := (mem_lambdaSet_of_le_sup hR hiso hA hC hA le_sup_left hQ hQle hQA.symm).1
  have hsup := (mem_lambdaSet_of_le_sup hR hiso hA hC hQ hQle hC.1.1 le_sup_right hQC).2
  calc A ≤ A ⊔ C := le_sup_left
    _ = Q ⊔ C := hsup.symm
    _ ≤ gen (lambdaSet R A) := sup_le (le_gen hQΛ) (le_gen hC)

theorem gen_lambdaSet_sup_eq_top_of {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ omegaSet R A) :
    gen (lambdaSet R A) ⊔ B = ⊤ := by
  set X := gen (lambdaSet R A) ⊔ B with hX
  have hBR : B ∈ R := hB.1
  have hAB : Opposite A B := hB.2
  have hΛX : ∀ C ∈ lambdaSet R A, C ≤ X := fun C hC => (le_gen hC).trans le_sup_left
  set Δ := {E | ∃ x ∈ X, conjSub A x = E} with hΔ
  have hΔR : Δ ⊆ R := by
    rintro _ ⟨x, -, rfl⟩
    exact hR.conjSub_mem hA x
  have hAΔ : A ∈ Δ := ⟨1, one_mem _, conjSub_one A⟩
  have hΛΔ : lambdaSet R A ⊆ Δ := by
    intro C hC
    obtain ⟨P, ⟨hPR, hPle, hPψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hBR hAB hC
    have hAP : A ≠ P := by
      rintro rfl
      exact Special.not_opposite hR hBR hPψ.2 hAB.symm
    obtain ⟨hPΛ, hsupP⟩ := mem_lambdaSet_of_le_sup hR hiso hA hC hA le_sup_left hPR hPle hAP
    have hS := Sec3.setOf_mem_le_sup_eq hR hiso hA hBR hAB hPΛ hPψ
    rw [hsupP] at hS
    have hNX : P ⊔ ⁅B, P⁆ ≤ X := by
      refine sup_le (hΛX P hPΛ) ?_
      rw [Subgroup.commutator_le]
      intro b hb p hp
      have hbX : b ∈ X := Subgroup.mem_sup_right hb
      have hpX : p ∈ X := hΛX P hPΛ hp
      rw [commutatorElement_def]
      exact X.mul_mem (X.mul_mem (X.mul_mem hbX hpX) (X.inv_mem hbX)) (X.inv_mem hpX)
    have hpt : ∀ T ∈ R, T ≤ A ⊔ C → T ≠ P → T ∈ Δ := by
      intro T hT hTle hTP
      have hmem : T ∈ {D | D ∈ R ∧ D ≤ A ⊔ C} := ⟨hT, hTle⟩
      rw [hS] at hmem
      rcases hmem with h | ⟨⟨n, hn⟩, rfl⟩
      · exact absurd h hTP
      · exact ⟨n, hNX hn, rfl⟩
    have hP : P ∈ Δ := by
      obtain ⟨Q, hQ, hQle, hQA, hQP⟩ := exists_mem_le_sup_ne_ne hR hiso hA hC A P
      obtain ⟨x, hx, rfl⟩ := hpt Q hQ hQle hQP
      obtain ⟨U, hU, u, hu, hQu⟩ :=
        exists_mem_lambdaSet_conjSub_eq hR hiso hA hC hQ hQle hQA hPR hPle hAP.symm
      refine ⟨u * x, X.mul_mem (hΛX U hU hu) hx, ?_⟩
      rw [conjSub_mul, hQu]
    by_cases hCP : C = P
    · exact hCP ▸ hP
    · exact hpt C hC.1.1 le_sup_right hCP
  have hcl : ∀ E ∈ Δ, lambdaSet R E ⊆ Δ := by
    rintro _ ⟨x, hx, rfl⟩ F hF
    have hF' := conjSub_mem_lambdaSet hR hF x⁻¹
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at hF'
    obtain ⟨y, hy, hFy⟩ := hΛΔ hF'
    refine ⟨x * y, X.mul_mem hx hy, ?_⟩
    rw [conjSub_mul, hFy, ← conjSub_mul, mul_inv_cancel, conjSub_one]
  have hΔeq := eq_of_forall_lambdaSet_subset hR hiso hnd hΔR ⟨A, hAΔ⟩ hcl
  have hAX : A ≤ X := (le_gen_lambdaSet hR hiso hnd hA).trans le_sup_left
  refine eq_top_iff.2 (hR.gen ▸ iSup₂_le fun E hE => ?_)
  obtain ⟨x, hx, rfl⟩ := (hΔeq ▸ hE : E ∈ Δ)
  exact conjSub_le hAX hx

end Gen

theorem Hyp.noIsolated (h : Hyp G R) : NoIsolated R := by
  have := h.finite
  have hR := h.root
  by_contra hcon
  simp only [NoIsolated, not_forall, not_exists, not_and] at hcon
  obtain ⟨A, hA, hno⟩ := hcon
  have hnop : ∀ E ∈ R, ∀ F ∈ R, ¬ Opposite E F := by
    intro E hE F hF hEF
    obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hA hE
    have := Opposite.conj hEF g⁻¹
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
    exact hno _ (hR.conjSub_mem hF g⁻¹) this
  have hP : IsPGroup 2 (⊤ : Subgroup G) :=
    isPGroup_of_forall_isPGroup_sup (S := R) (fun _ _ => le_top) (hR.gen ▸ le_rfl)
      (fun E hE m _ => hR.conjSub_mem hE m)
      (fun E hE F hF => isPGroup_sup_of_not_opposite hR hE hF (hnop E hE F hF))
  have htop := h.twoCore ⊤ Subgroup.normal_top hP
  apply hR.ne_bot A hA
  rw [eq_bot_iff, ← htop]
  exact le_top

theorem gen_lambdaSet_sup_eq_top (h : Hyp G R) {A B : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ omegaSet R A) : gen (lambdaSet R A) ⊔ B = ⊤ := by
  have := h.finite
  exact gen_lambdaSet_sup_eq_top_of h.root h.noIsolated h.nondeg hA hB

end CFSG.Timmesfeld.ARS
