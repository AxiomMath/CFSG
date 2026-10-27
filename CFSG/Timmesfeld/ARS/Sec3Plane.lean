module

public import CFSG.Timmesfeld.ARS.Sec3Pairs
public import CFSG.Timmesfeld.ARS.Sec4Lines

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Plane

section Lines

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
include hR hiso

theorem exists_opposite_special {Y P S : Subgroup G} (hY : Y ∈ R) (hP : P ∈ lambdaSet R Y)
    (hS : S ∈ R) (hSle : S ≤ Y ⊔ P) (hSY : S ≠ Y) :
    ∃ F ∈ R, Opposite Y F ∧ S ∈ psiSet R F := by
  obtain ⟨D₀, hD₀, hYD₀⟩ := hiso Y hY
  obtain ⟨S₀, ⟨hS₀R, hS₀le, hS₀ψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hY hD₀ hYD₀ hP
  have hS₀Y : S₀ ≠ Y := by
    rintro rfl
    exact Special.not_opposite hR hD₀ hS₀ψ.2 hYD₀.symm
  obtain ⟨U, hU, u, hu, hS₀u⟩ :=
    exists_mem_lambdaSet_conjSub_eq hR hiso hY hP hS₀R hS₀le hS₀Y hS hSle hSY
  refine ⟨conjSub D₀ u, hR.conjSub_mem hD₀ u, ?_, hS, ?_⟩
  · have := Opposite.conj hYD₀ u
    rwa [conjSub_of_forall_commute fun y hy => (hU.1.2.2 y hy u hu).symm] at this
  · have := Sec3.special_conjSub hR hS₀ψ.2 u
    rwa [hS₀u] at this

theorem opposite_of_mem_psiSet {Y P S F : Subgroup G} (hY : Y ∈ R) (hP : P ∈ lambdaSet R Y)
    (hF : F ∈ R) (hYF : Opposite Y F) (hS : S ∈ R) (hSle : S ≤ Y ⊔ P) (hSF : S ∈ psiSet R F)
    (hPS : P ≠ S) : Opposite P F := by
  have hPR : P ∈ R := hP.1.1
  have hnc : ¬ Commuting F P := not_commuting_of_opposite_of_mem_lambdaSet hR hF hYF.symm hP
  have hne : P ≠ F := fun e => hnc (e ▸ hR.commuting_self hPR)
  obtain ⟨D, -, huniq⟩ := existsUnique_mem_psiSet_of_le hR hiso hY hF hYF hP
  rcases hR.rel P hPR F hF hne with h | h | h
  · exact absurd h.symm hnc
  · exact h
  · exact absurd ((huniq P ⟨hPR, le_sup_right, hPR, h.symm⟩).trans
      (huniq S ⟨hS, hSle, hSF⟩).symm) hPS

end Lines

section General

variable (hR : IsRootClass R) in
include hR in
theorem forall_mem_lambdaSet_conjSub {N P : Subgroup G}
    (hP : ∀ Q ∈ R, Q ≤ N → Q ≠ P → Q ∈ lambdaSet R P) {g : G} (hg : conjSub N g = N) :
    ∀ Q ∈ R, Q ≤ N → Q ≠ conjSub P g → Q ∈ lambdaSet R (conjSub P g) := by
  intro Q hQ hQle hQP
  have hg' : conjSub N g⁻¹ = N :=
    calc conjSub N g⁻¹ = conjSub (conjSub N g) g⁻¹ := by rw [hg]
      _ = N := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  have h1 : conjSub Q g⁻¹ ≤ N := hg' ▸ Subgroup.map_mono hQle
  have h2 : conjSub Q g⁻¹ ≠ P := fun e =>
    hQP (by rw [← e, ← conjSub_mul, mul_inv_cancel, conjSub_one])
  have := conjSub_mem_lambdaSet hR (hP _ (hR.conjSub_mem hQ _) h1 h2) g
  rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this

theorem iSup_le_normalizer (R : Set (Subgroup G)) (N : Subgroup G) :
    (⨆ E ∈ {E : Subgroup G | E ∈ R ∧ ∀ x ∈ E, conjSub N x = N}, E) ≤
      Subgroup.normalizer (N : Set G) :=
  iSup₂_le fun _ hE => le_normalizer_of_conjSub_le fun x hx => (hE.2 x hx).le

end General

section Configuration

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {A B C : Subgroup G}
  (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ lambdaSet R B)
  (hline : ∀ D ∈ R, D ≤ B ⊔ C → D ∈ lambdaSet R A)

omit [Finite G] in
include hB hC hline in
theorem commuting_sup : Commuting A (B ⊔ C) :=
  Commuting.sup_right (hline B hB le_sup_left).1.2.2 (hline C hC.1.1 le_sup_right).1.2.2

omit [Finite G] in
include hR hA hB hC hline in
theorem commuting_sup_sup : Commuting (A ⊔ B ⊔ C) (A ⊔ B ⊔ C) := by
  have hCR : C ∈ R := hC.1.1
  have hABC := commuting_sup hB hC hline
  have hBC : Commuting (B ⊔ C) (B ⊔ C) :=
    Commuting.sup_left (Commuting.sup_right (hR.commuting_self hB) hC.1.2.2)
      (Commuting.sup_right hC.1.2.2.symm (hR.commuting_self hCR))
  rw [sup_assoc]
  exact Commuting.sup_left (Commuting.sup_right (hR.commuting_self hA) hABC)
    (Commuting.sup_right hABC.symm hBC)

omit [Finite G] in
include hA hline in
theorem not_le_sup : ¬ A ≤ B ⊔ C := fun h => (hline A hA h).1.2.1 rfl

omit [Finite G] in
include hR hiso hA hC hline in
theorem inf_sup_eq_bot : A ⊓ (B ⊔ C) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  by_contra hx1
  obtain ⟨D, hD, hDle, hxD⟩ := hC.2 x hx.2 hx1
  have := Sec3.eq_of_mem_of_mem hR hiso hA hD hx.1 hxD hx1
  exact not_le_sup hA hline (this ▸ hDle)

include hR hiso hB hC in
theorem card_sup : Nat.card ↥(B ⊔ C) = Nat.card B ^ 2 := by
  have hCR : C ∈ R := hC.1.1
  have hcard : Nat.card C = Nat.card B := hR.card_eq hCR hB
  refine le_antisymm ?_ ?_
  · calc Nat.card ↥(B ⊔ C) ≤ Nat.card B * Nat.card C := card_sup_le_of_commuting hC.1.2.2
      _ = Nat.card B ^ 2 := by rw [hcard, sq]
  · calc Nat.card B ^ 2 = Nat.card B * Nat.card C := by rw [hcard, sq]
      _ ≤ Nat.card ↥(B ⊔ C) :=
          card_mul_card_le_card_sup (inf_eq_bot hR hiso hB hCR hC.1.2.1.symm)

include hR hiso hA hB hC hline in
theorem card_sup_sup : Nat.card ↥(A ⊔ B ⊔ C) = Nat.card A ^ 3 := by
  have hBC : Nat.card ↥(B ⊔ C) = Nat.card A ^ 2 := by
    rw [card_sup hR hiso hB hC, hR.card_eq hB hA]
  have h3 : Nat.card A ^ 3 = Nat.card A * Nat.card ↥(B ⊔ C) := by rw [hBC, pow_succ']
  rw [sup_assoc, h3]
  exact le_antisymm (card_sup_le_of_commuting (commuting_sup hB hC hline))
    (card_mul_card_le_card_sup (inf_sup_eq_bot hR hiso hA hC hline))

omit [Finite G] in
include hB hC hline in
theorem exists_mul_eq_of_mem {x : G} (hx : x ∈ A ⊔ B ⊔ C) :
    ∃ a ∈ A, ∃ m ∈ B ⊔ C, a * m = x := by
  have hle : B ⊔ C ≤ Subgroup.normalizer (A : Set G) :=
    (commuting_iff_le_centralizer.1 (commuting_sup hB hC hline)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hx' : x ∈ ((A ⊔ (B ⊔ C) : Subgroup G) : Set G) := by rw [← sup_assoc]; exact hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A _ hle] at hx'
  obtain ⟨a, ha, m, hm, rfl⟩ := hx'
  exact ⟨a, ha, m, hm, rfl⟩

omit [Finite G] in
include hR hiso hA hB hC hline in
theorem exists_le_sup_of_le {Q : Subgroup G} (hQ : Q ∈ R) (hQle : Q ≤ A ⊔ B ⊔ C)
    (hQA : Q ≠ A) : ∃ B' ∈ R, B' ≤ B ⊔ C ∧ Q ≤ A ⊔ B' := by
  obtain ⟨q, hq, hq1⟩ := hR.exists_ne_one hQ
  obtain ⟨a, ha, m, hm, rfl⟩ := exists_mul_eq_of_mem hB hC hline (hQle hq)
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hq hq1
    exact absurd (Sec3.eq_of_mem_of_mem hR hiso hQ hA hq ha hq1) hQA
  obtain ⟨B', hB', hB'le, hmB'⟩ := hC.2 m hm hm1
  obtain ⟨Q', hQ', hQ'le, hqQ'⟩ := (hline B' hB' hB'le).2 (a * m)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hmB')) hq1
  exact ⟨B', hB', hB'le, Sec3.eq_of_mem_of_mem hR hiso hQ hQ' hq hqQ' hq1 ▸ hQ'le⟩

include hR hiso hA hB hC hline in
theorem mem_lambdaSet_of_le {Q : Subgroup G} (hQ : Q ∈ R) (hQle : Q ≤ A ⊔ B ⊔ C)
    (hQA : Q ≠ A) : Q ∈ lambdaSet R A := by
  obtain ⟨B', hB', hB'le, hQB'⟩ := exists_le_sup_of_le hR hiso hA hB hC hline hQ hQle hQA
  exact (mem_lambdaSet_of_le_sup hR hiso hA (hline B' hB' hB'le) hA le_sup_left hQ hQB'
    hQA.symm).1

omit [Finite G] in
include hA hB hC hline in
theorem coveredBy_sup_sup : CoveredBy R (A ⊔ B ⊔ C) := by
  intro x hx hx1
  obtain ⟨a, ha, m, hm, rfl⟩ := exists_mul_eq_of_mem hB hC hline hx
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hx1 ⊢
    exact ⟨A, hA, le_sup_left.trans le_sup_left, ha⟩
  obtain ⟨B', hB', hB'le, hmB'⟩ := hC.2 m hm hm1
  obtain ⟨Q', hQ', hQ'le, hxQ'⟩ := (hline B' hB' hB'le).2 (a * m)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hmB')) hx1
  refine ⟨Q', hQ', hQ'le.trans (sup_le (le_sup_left.trans le_sup_left) ?_), hxQ'⟩
  exact hB'le.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)

include hR hiso hA hB hC hline in
theorem conjSub_sup_sup_eq {F X Y : Subgroup G} (hF : F ∈ R) (hAF : Opposite A F)
    (hX : X ∈ R) (hXle : X ≤ B ⊔ C) (hXF : X ∈ psiSet R F) (hY : Y ∈ R) (hYle : Y ≤ B ⊔ C)
    (hYF : Opposite Y F) :
    (∀ n ∈ X ⊔ ⁅F, X⁆, conjSub (A ⊔ B ⊔ C) n = A ⊔ B ⊔ C) ∧
      ∀ P ∈ R, P ≤ A ⊔ X → P ≠ X → ∃ n ∈ X ⊔ ⁅F, X⁆, conjSub A n = P := by
  have hXA := hline X hX hXle
  have hXY : X ≠ Y := fun e => Special.not_opposite hR hF hXF.2 (e ▸ hYF.symm)
  obtain ⟨hXYl, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hB hC hY hYle hX hXle hXY.symm
  have hS₁ := Sec3.setOf_mem_le_sup_eq hR hiso hA hF hAF hXA hXF
  have hS₂ := Sec3.setOf_mem_le_sup_eq hR hiso hY hF hYF hXYl hXF
  have hM := Sec3.commuting_sup_commutator hR hXA hXF
  have hmem : ∀ n ∈ X ⊔ ⁅F, X⁆, conjSub A n ≤ A ⊔ X ∧ conjSub Y n ≤ Y ⊔ X := by
    intro n hn
    have h1 : conjSub A n ∈ {D | D ∈ R ∧ D ≤ A ⊔ X} := by
      rw [hS₁]
      exact Or.inr ⟨⟨n, hn⟩, rfl⟩
    have h2 : conjSub Y n ∈ {D | D ∈ R ∧ D ≤ Y ⊔ X} := by
      rw [hS₂]
      exact Or.inr ⟨⟨n, hn⟩, rfl⟩
    exact ⟨h1.2, h2.2⟩
  have hN : A ⊔ B ⊔ C = A ⊔ (Y ⊔ X) := by rw [sup_assoc, hsup]
  have hle : X ⊔ ⁅F, X⁆ ≤ Subgroup.normalizer ((A ⊔ B ⊔ C : Subgroup G) : Set G) := by
    refine le_normalizer_of_conjSub_le fun n hn => ?_
    rw [hN, conjSub, Subgroup.map_sup, Subgroup.map_sup, ← conjSub, ← conjSub, ← conjSub,
      conjSub_of_forall_commute fun x hx => hM n hn x (Subgroup.mem_sup_left hx)]
    obtain ⟨h1, h2⟩ := hmem n hn
    exact sup_le (h1.trans (sup_le le_sup_left (le_sup_right.trans le_sup_right)))
      (sup_le (h2.trans le_sup_right) (le_sup_right.trans le_sup_right))
  refine ⟨fun n hn => conjSub_eq_self_iff.2 (hle hn), fun P hP hPle hPX => ?_⟩
  have hPmem : P ∈ {D | D ∈ R ∧ D ≤ A ⊔ X} := ⟨hP, hPle⟩
  rw [hS₁] at hPmem
  rcases hPmem with h | ⟨⟨n, hn⟩, rfl⟩
  · exact absurd h hPX
  · exact ⟨n, hn, rfl⟩

include hR hiso hA hB hC hline in
theorem exists_opposite_special_opposite {X : Subgroup G} (hX : X ∈ R) (hXle : X ≤ B ⊔ C) :
    ∃ F ∈ R, Opposite A F ∧ X ∈ psiSet R F ∧ ∃ Y ∈ R, Y ≤ B ⊔ C ∧ Opposite Y F := by
  have hXA := hline X hX hXle
  have hXA' : X ≠ A := fun e => not_le_sup hA hline (e ▸ hXle)
  obtain ⟨Y, hY, hYle, hYX, -⟩ := exists_mem_le_sup_ne_ne hR hiso hB hC X X
  obtain ⟨Y', hY', hY'le, hY'X, hY'Y⟩ := exists_mem_le_sup_ne_ne hR hiso hB hC X Y
  have hYA := hline Y hY hYle
  have hY'A := hline Y' hY' hY'le
  obtain ⟨F₂, hF₂, hAF₂, hXF₂⟩ := exists_opposite_special hR hiso hA hXA hX le_sup_right hXA'
  by_cases hYF₂ : Opposite Y F₂
  · exact ⟨F₂, hF₂, hAF₂, hXF₂, Y, hY, hYle, hYF₂⟩
  have hYF₂s : Special R F₂ Y := by
    have hnc : ¬ Commuting F₂ Y :=
      not_commuting_of_opposite_of_mem_lambdaSet hR hF₂ hAF₂.symm hYA
    have hne : F₂ ≠ Y := fun e => hnc (e ▸ hR.commuting_self hF₂)
    rcases hR.rel F₂ hF₂ Y hY hne with h | h | h
    · exact absurd h hnc
    · exact absurd h.symm hYF₂
    · exact h
  obtain ⟨hXYl, -⟩ := mem_lambdaSet_of_le_sup hR hiso hB hC hY hYle hX hXle hYX
  obtain ⟨F₁, hF₁, hYF₁, hXF₁⟩ :=
    exists_opposite_special hR hiso hY hXYl hX le_sup_right hYX.symm
  by_cases hAF₁ : Opposite A F₁
  · exact ⟨F₁, hF₁, hAF₁, hXF₁, Y, hY, hYle, hYF₁⟩
  have hAY : A ∈ lambdaSet R Y := mem_lambdaSet_comm hA hYA
  have hAF₁s : Special R F₁ A := by
    have hnc : ¬ Commuting F₁ A :=
      not_commuting_of_opposite_of_mem_lambdaSet hR hF₁ hYF₁.symm hAY
    have hne : F₁ ≠ A := fun e => hnc (e ▸ hR.commuting_self hF₁)
    rcases hR.rel F₁ hF₁ A hA hne with h | h | h
    · exact absurd h hnc
    · exact absurd h.symm hAF₁
    · exact h
  obtain ⟨hY'Yl, hsupYY'⟩ :=
    mem_lambdaSet_of_le_sup hR hiso hB hC hY hYle hY' hY'le hY'Y.symm
  have hXYY' : X ≤ Y ⊔ Y' := by rw [hsupYY']; exact hXle
  have hY'F₁ : Opposite Y' F₁ :=
    opposite_of_mem_psiSet hR hiso hY hY'Yl hF₁ hYF₁ hX hXYY' hXF₁ hY'X
  obtain ⟨-, -, hcomm, -, -⟩ := natural_modules_of_opposite_opposite hR hiso hF₁ hY hY'
    hYF₁.symm hY'F₁.symm ⟨hA, hAF₁s⟩ (mem_lambdaSet_comm hY hY'Yl) hYA hY'A hXYY' hXF₁
  have hS := Sec3.setOf_mem_le_sup_eq hR hiso hY hF₁ hYF₁ hAY ⟨hA, hAF₁s⟩
  have hM := Sec3.commuting_sup_commutator hR hAY ⟨hA, hAF₁s⟩
  obtain ⟨P, hP, hPle, hPA, hPY⟩ := exists_mem_le_sup_ne_ne hR hiso hA hYA A Y
  obtain ⟨hPAl, hsupAP⟩ :=
    mem_lambdaSet_of_le_sup hR hiso hA hYA hA le_sup_left hP hPle hPA.symm
  have hYAP : Y ≤ A ⊔ P := by rw [hsupAP]; exact le_sup_right
  have hPF₂ : Opposite P F₂ :=
    opposite_of_mem_psiSet hR hiso hA hPAl hF₂ hAF₂ hY hYAP ⟨hY, hYF₂s⟩ hPY
  have hPmem : P ∈ {D | D ∈ R ∧ D ≤ Y ⊔ A} := ⟨hP, sup_comm A Y ▸ hPle⟩
  rw [hS] at hPmem
  rcases hPmem with h | ⟨⟨n, hn⟩, hnP⟩
  · exact absurd h hPA
  change conjSub Y n = P at hnP
  have hn' : n⁻¹ ∈ A ⊔ ⁅F₁, A⁆ := Subgroup.inv_mem _ hn
  have hAn : conjSub A n⁻¹ = A :=
    conjSub_of_forall_commute fun a ha => hM _ hn' a (Subgroup.mem_sup_left ha)
  have hXn : conjSub X n⁻¹ = X :=
    conjSub_of_forall_commute fun x hx => hcomm _ hn' x (Subgroup.mem_sup_left hx)
  have hPn : conjSub P n⁻¹ = Y := by rw [← hnP, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  refine ⟨conjSub F₂ n⁻¹, hR.conjSub_mem hF₂ _, ?_, ⟨hX, ?_⟩, Y, hY, hYle, ?_⟩
  · have := Opposite.conj hAF₂ n⁻¹
    rwa [hAn] at this
  · have := Sec3.special_conjSub hR hXF₂.2 n⁻¹
    rwa [hXn] at this
  · have := Opposite.conj hPF₂ n⁻¹
    rwa [hPn] at this

include hR hiso hA hB hC hline in
theorem exists_mem_iSup_conjSub_eq_of_not_le {P : Subgroup G} (hP : P ∈ R)
    (hPle : P ≤ A ⊔ B ⊔ C) (hPBC : ¬ P ≤ B ⊔ C) :
    ∃ g ∈ ⨆ E ∈ {E : Subgroup G | E ∈ R ∧ ∀ x ∈ E, conjSub (A ⊔ B ⊔ C) x = A ⊔ B ⊔ C}, E,
      conjSub A g = P := by
  by_cases hPA : P = A
  · exact ⟨1, one_mem _, by rw [conjSub_one, hPA]⟩
  obtain ⟨X, hX, hXle, hPX⟩ := exists_le_sup_of_le hR hiso hA hB hC hline hP hPle hPA
  have hPX' : P ≠ X := fun e => hPBC (e ▸ hXle)
  obtain ⟨F, hF, hAF, hXF, Y, hY, hYle, hYF⟩ :=
    exists_opposite_special_opposite hR hiso hA hB hC hline hX hXle
  obtain ⟨hnorm, hpts⟩ :=
    conjSub_sup_sup_eq hR hiso hA hB hC hline hF hAF hX hXle hXF hY hYle hYF
  obtain ⟨n, hn, rfl⟩ := hpts P hP hPX hPX'
  have hN := commuting_sup_sup hR hA hB hC hline
  have hXN : X ≤ A ⊔ B ⊔ C :=
    hXle.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hle : X ⊔ ⁅F, X⁆ ≤ ⨆ E ∈ {E : Subgroup G | E ∈ R ∧
      ∀ x ∈ E, conjSub (A ⊔ B ⊔ C) x = A ⊔ B ⊔ C}, E := by
    refine sup_le ?_ ?_
    · exact le_iSup₂ (f := fun E (_ : E ∈ {E : Subgroup G | E ∈ R ∧
        ∀ x ∈ E, conjSub (A ⊔ B ⊔ C) x = A ⊔ B ⊔ C}) => E) X
        ⟨hX, fun x hx => conjSub_of_forall_commute fun y hy => hN x (hXN hx) y hy⟩
    · exact le_iSup₂ (f := fun E (_ : E ∈ {E : Subgroup G | E ∈ R ∧
        ∀ x ∈ E, conjSub (A ⊔ B ⊔ C) x = A ⊔ B ⊔ C}) => E) ⁅F, X⁆
        ⟨hXF.2.1, fun t ht => hnorm t (Subgroup.mem_sup_right ht)⟩
  exact ⟨n, hle hn, rfl⟩

include hR hiso hA hB hC hline in
theorem mem_lambdaSet_of_le_of_le {P Q : Subgroup G} (hP : P ∈ R) (hPle : P ≤ A ⊔ B ⊔ C)
    (hQ : Q ∈ R) (hQle : Q ≤ A ⊔ B ⊔ C) (hPQ : P ≠ Q) : Q ∈ lambdaSet R P := by
  have hcenter : ∀ P ∈ R, P ≤ A ⊔ B ⊔ C → ¬ P ≤ B ⊔ C →
      ∀ Q ∈ R, Q ≤ A ⊔ B ⊔ C → Q ≠ P → Q ∈ lambdaSet R P := by
    intro P hP hPle hPBC
    obtain ⟨g, hg, rfl⟩ := exists_mem_iSup_conjSub_eq_of_not_le hR hiso hA hB hC hline hP hPle hPBC
    exact forall_mem_lambdaSet_conjSub hR
      (fun Q hQ hQle hQA => mem_lambdaSet_of_le hR hiso hA hB hC hline hQ hQle hQA)
      (conjSub_eq_self_iff.2 (iSup_le_normalizer R _ hg))
  by_cases hPBC : P ≤ B ⊔ C
  · by_cases hQBC : Q ≤ B ⊔ C
    · exact (mem_lambdaSet_of_le_sup hR hiso hB hC hP hPBC hQ hQBC hPQ).1
    · exact mem_lambdaSet_comm hQ (hcenter Q hQ hQle hQBC P hP hPle hPQ)
  · exact hcenter P hP hPle hPBC Q hQ hQle hPQ.symm

omit [Finite G] in
theorem card_subtype_mem_ne_one (H : Subgroup G) :
    Nat.card {x : G // x ∈ H ∧ x ≠ 1} = Nat.card H - 1 := by
  have e : {x : G | x ∈ H ∧ x ≠ 1} = (H : Set G) \ {1} := by
    ext x
    simp
  change Nat.card ↥{x : G | x ∈ H ∧ x ≠ 1} = _
  rw [e, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (H.one_mem),
    ← Nat.card_coe_set_eq]
  rfl

theorem eq_of_mul_sub_one_eq {q s : ℕ} (hq : 2 ≤ q) (h : s * (q - 1) = q ^ 3 - 1) :
    s = q ^ 2 + q + 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr : 0 < r := by omega
  rw [Nat.add_sub_cancel] at h
  have h3 : (r + 1) ^ 3 - 1 = ((r + 1) ^ 2 + (r + 1) + 1) * r :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [h3] at h
  exact Nat.eq_of_mul_eq_mul_right hr h

include hR hiso hA hB hC hline in
theorem card_points :
    Nat.card {D : Subgroup G // D ∈ R ∧ D ≤ A ⊔ B ⊔ C} = Nat.card A ^ 2 + Nat.card A + 1 := by
  classical
  set S := {D : Subgroup G // D ∈ R ∧ D ≤ A ⊔ B ⊔ C} with hS
  have hcov := coveredBy_sup_sup hA hB hC hline
  let f : (Σ D : S, {x : G // x ∈ D.1 ∧ x ≠ 1}) → {x : G // x ∈ A ⊔ B ⊔ C ∧ x ≠ 1} :=
    fun p => ⟨p.2.1, p.1.2.2 p.2.2.1, p.2.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨D, x, hx, hx1⟩ ⟨D', x', hx', hx'1⟩ h
      have hxx : x = x' := congrArg Subtype.val h
      subst hxx
      have hDD : D = D' := Subtype.ext (Sec3.eq_of_mem_of_mem hR hiso D.2.1 D'.2.1 hx hx' hx1)
      subst hDD
      rfl
    · rintro ⟨x, hx, hx1⟩
      obtain ⟨D, hD, hDle, hxD⟩ := hcov x hx hx1
      exact ⟨⟨⟨D, hD, hDle⟩, x, hxD, hx1⟩, rfl⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  have : Fintype S := Fintype.ofFinite S
  rw [Nat.card_sigma, card_subtype_mem_ne_one, card_sup_sup hR hiso hA hB hC hline] at hcard
  have hsum : ∑ D : S, Nat.card {x : G // x ∈ D.1 ∧ x ≠ 1} = Nat.card S * (Nat.card A - 1) := by
    calc ∑ D : S, Nat.card {x : G // x ∈ D.1 ∧ x ≠ 1} = ∑ _D : S, (Nat.card A - 1) :=
          Finset.sum_congr rfl fun D _ => by rw [card_subtype_mem_ne_one, hR.card_eq D.2.1 hA]
      _ = Nat.card S * (Nat.card A - 1) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [hsum] at hcard
  exact eq_of_mul_sub_one_eq ((Subgroup.one_lt_card_iff_ne_bot A).2 (hR.ne_bot A hA)) hcard

include hR hiso hA hB hC hline in
theorem exists_le_sup_le_sup {P₁ Q₁ P₂ Q₂ : Subgroup G} (hP₁ : P₁ ∈ R)
    (hP₁le : P₁ ≤ A ⊔ B ⊔ C) (hQ₁ : Q₁ ∈ R) (hQ₁le : Q₁ ≤ A ⊔ B ⊔ C) (h₁ : P₁ ≠ Q₁)
    (hP₂ : P₂ ∈ R) (hP₂le : P₂ ≤ A ⊔ B ⊔ C) (hQ₂ : Q₂ ∈ R) (hQ₂le : Q₂ ≤ A ⊔ B ⊔ C)
    (h₂ : P₂ ≠ Q₂) : ∃ D ∈ R, D ≤ P₁ ⊔ Q₁ ∧ D ≤ P₂ ⊔ Q₂ := by
  have hl₁ := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hP₁ hP₁le hQ₁ hQ₁le h₁
  have hl₂ := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hP₂ hP₂le hQ₂ hQ₂le h₂
  by_contra! h
  have hbot : (P₁ ⊔ Q₁) ⊓ (P₂ ⊔ Q₂) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    by_contra hx1
    obtain ⟨D, hD, hDle, hxD⟩ := hl₁.2 x hx.1 hx1
    obtain ⟨D', hD', hD'le, hxD'⟩ := hl₂.2 x hx.2 hx1
    exact h D hD hDle (Sec3.eq_of_mem_of_mem hR hiso hD hD' hxD hxD' hx1 ▸ hD'le)
  have h1 := card_mul_card_le_card_sup hbot
  have h2 := Subgroup.card_le_of_le (sup_le (sup_le hP₁le hQ₁le) (sup_le hP₂le hQ₂le))
  rw [card_sup hR hiso hP₁ hl₁, card_sup hR hiso hP₂ hl₂, hR.card_eq hP₁ hA,
    hR.card_eq hP₂ hA] at h1
  rw [card_sup_sup hR hiso hA hB hC hline] at h2
  have hq : 2 ≤ Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 (hR.ne_bot A hA)
  have h3 : Nat.card A ^ 2 * Nat.card A ^ 2 ≤ Nat.card A ^ 3 := h1.trans h2
  have h4 : Nat.card A ^ 3 < Nat.card A ^ 2 * Nat.card A ^ 2 := by
    rw [← pow_add]
    exact Nat.pow_lt_pow_right hq (by norm_num)
  omega

include hR hiso hA hB hC hline in
theorem sup_sup_eq_of_le {A' B' C' : Subgroup G} (hA' : A' ∈ R) (hA'le : A' ≤ A ⊔ B ⊔ C)
    (hB' : B' ∈ R) (hB'le : B' ≤ A ⊔ B ⊔ C) (hC' : C' ∈ R) (hC'le : C' ≤ A ⊔ B ⊔ C)
    (hBC' : B' ≠ C') (hA'BC : ¬ A' ≤ B' ⊔ C') :
    C' ∈ lambdaSet R B' ∧ (∀ D ∈ R, D ≤ B' ⊔ C' → D ∈ lambdaSet R A') ∧
      A' ⊔ B' ⊔ C' = A ⊔ B ⊔ C := by
  have hC'l := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hB' hB'le hC' hC'le hBC'
  have hline' : ∀ D ∈ R, D ≤ B' ⊔ C' → D ∈ lambdaSet R A' := fun D hD hDle =>
    mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hA' hA'le hD
      (hDle.trans (sup_le hB'le hC'le)) fun e => hA'BC (e ▸ hDle)
  refine ⟨hC'l, hline', Subgroup.eq_of_le_of_card_ge (sup_le (sup_le hA'le hB'le) hC'le) ?_⟩
  rw [card_sup_sup hR hiso hA' hB' hC'l hline', card_sup_sup hR hiso hA hB hC hline,
    hR.card_eq hA' hA]

include hR hiso hA hB hC hline in
theorem exists_mem_iSup_conjSub_eq {P : Subgroup G} (hP : P ∈ R) (hPle : P ≤ A ⊔ B ⊔ C) :
    ∃ g ∈ ⨆ E ∈ {E : Subgroup G | E ∈ R ∧ ∀ x ∈ E, conjSub (A ⊔ B ⊔ C) x = A ⊔ B ⊔ C}, E,
      conjSub A g = P := by
  by_cases hPBC : P ≤ B ⊔ C
  swap
  · exact exists_mem_iSup_conjSub_eq_of_not_le hR hiso hA hB hC hline hP hPle hPBC
  have hBCN : B ⊔ C ≤ A ⊔ B ⊔ C := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hAN : A ≤ A ⊔ B ⊔ C := le_sup_left.trans le_sup_left
  have hPAl : P ∈ lambdaSet R A := hline P hP hPBC
  obtain ⟨P₁, hP₁, hP₁le, hP₁A, hP₁P⟩ := exists_mem_le_sup_ne_ne hR hiso hA hPAl A P
  have hP₁N : P₁ ≤ A ⊔ B ⊔ C := hP₁le.trans (sup_le hAN (hPBC.trans hBCN))
  obtain ⟨-, hsupAP₁⟩ :=
    mem_lambdaSet_of_le_sup hR hiso hA hPAl hA le_sup_left hP₁ hP₁le hP₁A.symm
  have hP₁BC : ¬ P₁ ≤ B ⊔ C := by
    intro h
    obtain ⟨-, hsup⟩ :=
      mem_lambdaSet_of_le_sup hR hiso hA hPAl hP₁ hP₁le hP le_sup_right hP₁P
    exact not_le_sup hA hline (le_sup_left.trans (hsup.symm.le.trans (sup_le h hPBC)))
  obtain ⟨g₁, hg₁, hg₁P⟩ :=
    exists_mem_iSup_conjSub_eq_of_not_le hR hiso hA hB hC hline hP₁ hP₁N hP₁BC
  obtain ⟨W, hW, hWle, hWP, -⟩ := exists_mem_le_sup_ne_ne hR hiso hB hC P P
  have hWA := hline W hW hWle
  have hPAW : ¬ P ≤ A ⊔ W := by
    intro h
    obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hA hWA hP h hW le_sup_right hWP.symm
    exact not_le_sup hA hline (le_sup_left.trans (hsup.symm.le.trans (sup_le hPBC hWle)))
  have hP₁AW : ¬ P₁ ≤ A ⊔ W := by
    intro h
    obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hA hWA hA le_sup_left hP₁ h hP₁A.symm
    exact hPAW (le_sup_right.trans (hsupAP₁.symm.le.trans hsup.le))
  have hAW : A ≠ W := fun e => not_le_sup hA hline (e ▸ hWle)
  obtain ⟨hWl, hline', hNeq⟩ := sup_sup_eq_of_le hR hiso hA hB hC hline hP₁ hP₁N hA hAN hW
    (hWle.trans hBCN) hAW hP₁AW
  obtain ⟨g₂, hg₂, hg₂P⟩ :=
    exists_mem_iSup_conjSub_eq_of_not_le hR hiso hP₁ hA hWl hline' hP (hNeq ▸ hPle) hPAW
  rw [hNeq] at hg₂
  refine ⟨g₂ * g₁, Subgroup.mul_mem _ hg₂ hg₁, ?_⟩
  rw [conjSub_mul, hg₁P, hg₂P]

end Configuration

end Plane

open Plane

theorem plane [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {A B C : Subgroup G}
    (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ lambdaSet R B)
    (hline : ∀ D ∈ R, D ≤ B ⊔ C → D ∈ lambdaSet R A) :
    Commuting (A ⊔ B ⊔ C) (A ⊔ B ⊔ C) ∧ Nat.card ↥(A ⊔ B ⊔ C) = Nat.card A ^ 3 ∧
      CoveredBy R (A ⊔ B ⊔ C) ∧
      Nat.card {D : Subgroup G // D ∈ R ∧ D ≤ A ⊔ B ⊔ C} = Nat.card A ^ 2 + Nat.card A + 1 ∧
      (∀ P ∈ R, P ≤ A ⊔ B ⊔ C → ∀ Q ∈ R, Q ≤ A ⊔ B ⊔ C → P ≠ Q → Q ∈ lambdaSet R P) ∧
      ∀ D ∈ R, D ≤ A ⊔ B ⊔ C → ∃ g ∈ ⨆ E ∈ {E : Subgroup G | E ∈ R ∧
        ∀ x ∈ E, conjSub (A ⊔ B ⊔ C) x = A ⊔ B ⊔ C}, E, conjSub A g = D :=
  ⟨commuting_sup_sup hR hA hB hC hline, card_sup_sup hR hiso hA hB hC hline,
    coveredBy_sup_sup hA hB hC hline, card_points hR hiso hA hB hC hline,
    fun _ hP hPle _ hQ hQle hPQ =>
      mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hP hPle hQ hQle hPQ,
    fun _ hD hDle => exists_mem_iSup_conjSub_eq hR hiso hA hB hC hline hD hDle⟩

end CFSG.Timmesfeld.ARS
