module

public import CFSG.Timmesfeld.ARS.CaseBHidden
public import CFSG.Timmesfeld.ARS.Sec12Frame

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem commuting_of_two_commuting {D Y₀ Y₁ X X' Z : Subgroup G} (hD : D ∈ lambdaStar R A A₀)
    (hY₀ : Y₀ ∈ leviSet R A A₀) (hY₁ : Y₁ ∈ leviSet R A A₀) (hs₀ : Special R D Y₀)
    (hs₁ : Special R D Y₁) (hX : X ∈ deltaSet R A A₀ D) (hX' : X' ∈ deltaSet R A A₀ D)
    (hXX' : X ≠ X') (hX₀ : Commuting X Y₀) (hX₁ : Commuting X Y₁) (hX'₀ : Commuting X' Y₀)
    (hX'₁ : Commuting X' Y₁) (hZ : Z ∈ deltaSet R A A₀ D) (hZ₁ : Commuting Z Y₁) :
    Commuting Z Y₀ := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  obtain ⟨hD₀, hD₀D, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hD hY₀ hs₀
  obtain ⟨hD₁, hD₁D, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hD hY₁ hs₁
  have iff₀ := fun {W : Subgroup G} (hW : W ∈ deltaSet R A A₀ D) =>
    hS.commuting_iff_mem_deltaSet_commutator hD hY₀ hs₀ hW
  have iff₁ := fun {W : Subgroup G} (hW : W ∈ deltaSet R A A₀ D) =>
    hS.commuting_iff_mem_deltaSet_commutator hD hY₁ hs₁ hW
  have hZD₁ := (iff₁ hZ).1 hZ₁
  refine (iff₀ hZ).2 ?_
  by_cases h01 : ⁅D, Y₀⁆ = ⁅D, Y₁⁆
  · rw [h01]
    exact hZD₁
  have hD₁D₀ : ⁅D, Y₁⁆ ∈ lambdaSet R ⁅D, Y₀⁆ := hS.mem_lambdaSet_of_mem_deltaSet_inter hD₀ hD₁
    h01 ⟨(iff₀ hX).1 hX₀, (iff₁ hX).1 hX₁⟩ ⟨(iff₀ hX').1 hX'₀, (iff₁ hX').1 hX'₁⟩ hXX'
  have hle : ⁅D, Y₁⁆ ≤ D ⊔ ⁅D, Y₀⁆ := hS.le_sup_of_mem_lambdaSet hD hD₀ hD₁ hD₀D hD₁D hD₁D₀
  have hDD₁ : D ≠ ⁅D, Y₁⁆ := hD₁D.1.2.1.symm
  have hsup : D ⊔ ⁅D, Y₁⁆ = D ⊔ ⁅D, Y₀⁆ :=
    (mem_lambdaSet_of_le_sup hR hiso hD.1.1.1 hD₀D hD.1.1.1 le_sup_left hD₁.1.1.1 hle hDD₁).2
  have hc : Commuting (D ⊔ ⁅D, Y₁⁆) Z := hZ.2.1.2.2.sup_left hZD₁.2.1.2.2
  rw [hsup] at hc
  exact hS.mem_deltaSet_of_commuting hD₀ hZ.1 (hc.mono le_sup_right le_rfl)


theorem ncard_perp_le {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : IsSubframe R A A₀ E C P Q) {f : ℕ} (hcard : Nat.card A = 2 ^ f) :
    {X | X ∈ leviSet R A A₀ ∧ Commuting X (P 0) ∧ Commuting X (Q 0) ∧ Commuting X (P 1) ∧
      Commuting X (Q 1)}.ncard ≤ 2 ^ f + 1 := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  set S := {X | X ∈ leviSet R A A₀ ∧ Commuting X (P 0) ∧ Commuting X (Q 0) ∧
    Commuting X (P 1) ∧ Commuting X (Q 1)} with hSdef
  have hE := hfr.memE
  have hER : E ∈ R := hE.1.1.1
  have hPQ : ∀ i, ¬ Commuting (P i) (Q i) := fun i =>
    (hfr.opposite i).not_commuting (hR.ne_bot _ (hfr.memP i).1.1.1)
  have hcomm : ∀ i j, i ≠ j → Commuting (P i) (P j) ∧ Commuting (P i) (Q j) ∧
      Commuting (Q i) (P j) ∧ Commuting (Q i) (Q j) := fun i j hij =>
    ⟨(hfr.commuting i j hij).mono le_sup_left le_sup_left,
      (hfr.commuting i j hij).mono le_sup_left le_sup_right,
      (hfr.commuting i j hij).mono le_sup_right le_sup_left,
      (hfr.commuting i j hij).mono le_sup_right le_sup_right⟩
  have hspecial : ∀ {D : Subgroup G}, D ∈ lambdaStar R A A₀ → ∀ i,
      Q i ∈ deltaSet R A A₀ D → Special R D (P i) := by
    intro D hD i hQi
    rcases hS.mem_deltaSet_or_special hD (hfr.memP i).1 with h | h
    · exact absurd (hS.commuting_of_mem_deltaSet' hD h hQi) (hPQ i)
    · exact h
  have hunique : ∀ {D : Subgroup G}, D ∈ lambdaStar R A A₀ → Q 0 ∈ deltaSet R A A₀ D →
      Q 1 ∈ deltaSet R A A₀ D → ∀ X X', X ∈ deltaSet R A A₀ D → X' ∈ deltaSet R A A₀ D →
        Commuting X (P 0) → Commuting X (P 1) → Commuting X' (P 0) → Commuting X' (P 1) →
          X = X' := by
    intro D hD hQ0 hQ1 X X' hX hX' hX0 hX1 hX'0 hX'1
    by_contra hne
    exact hPQ 0 (hS.commuting_of_two_commuting hD (hfr.memP 0).1 (hfr.memP 1).1
      (hspecial hD 0 hQ0) (hspecial hD 1 hQ1) hX hX' hne hX0 hX1 hX'0 hX'1 hQ0
      (hcomm 0 1 (by decide)).2.2.1).symm
  have hspE : ∀ X ∈ S, X ≠ Q 2 → Special R E X := by
    intro X hX hXQ
    rcases hS.mem_deltaSet_or_special hE hX.1 with h | h
    · exact absurd (hunique hE (hfr.memQ 0) (hfr.memQ 1) X (Q 2) h (hfr.memQ 2) hX.2.1
        hX.2.2.2.1 (hcomm 2 0 (by decide)).2.2.1 (hcomm 2 1 (by decide)).2.2.1) hXQ
    · exact h
  have hD : ∀ X ∈ S, X ≠ Q 2 → ⁅E, X⁆ ∈ lambdaStar R A A₀ ∧ ⁅E, X⁆ ∈ lambdaSet R E ∧
      X ∈ deltaSet R A A₀ ⁅E, X⁆ ∧ Q 0 ∈ deltaSet R A A₀ ⁅E, X⁆ ∧
        Q 1 ∈ deltaSet R A A₀ ⁅E, X⁆ := by
    intro X hX hXQ
    obtain ⟨h1, h2, h3⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hE hX.1
      (hspE X hX hXQ)
    have iff := fun {W : Subgroup G} (hW : W ∈ deltaSet R A A₀ E) =>
      hS.commuting_iff_mem_deltaSet_commutator hE hX.1 (hspE X hX hXQ) hW
    exact ⟨h1, h2, hS.mem_deltaSet_of_commuting h1 hX.1 h3.1.2.2.symm,
      (iff (hfr.memQ 0)).1 hX.2.2.1.symm, (iff (hfr.memQ 1)).1 hX.2.2.2.2.symm⟩
  have hinj : ∀ X ∈ S, ∀ X' ∈ S, X ≠ Q 2 → X' ≠ Q 2 → ⁅E, X⁆ = ⁅E, X'⁆ → X = X' := by
    intro X hX X' hX' hXQ hX'Q he
    obtain ⟨hD1, -, hXD, hQ0D, hQ1D⟩ := hD X hX hXQ
    obtain ⟨-, -, hX'D, -, -⟩ := hD X' hX' hX'Q
    rw [← he] at hX'D
    exact hunique hD1 hQ0D hQ1D X X' hXD hX'D hX.2.1 hX.2.2.2.1 hX'.2.1 hX'.2.2.2.1
  by_cases hex : ∃ X₀ ∈ S, X₀ ≠ Q 2
  · obtain ⟨X₀, hX₀, hX₀Q⟩ := hex
    obtain ⟨hD₀, hD₀E, -, hQ0D₀, hQ1D₀⟩ := hD X₀ hX₀ hX₀Q
    have hQ01 : Q 0 ≠ Q 1 := fun h => hPQ 0 (by rw [h]; exact (hcomm 0 1 (by decide)).2.1)
    have hy : ∀ X ∈ S, X ≠ Q 2 → X ≠ X₀ → ∃ y ∈ X₀, y ≠ 1 ∧ conjSub E y = ⁅E, X⁆ := by
      intro X hX hXQ hXX₀
      obtain ⟨hD1, hD1E, -, hQ0D, hQ1D⟩ := hD X hX hXQ
      have hne : ⁅E, X⁆ ≠ ⁅E, X₀⁆ := fun h => hXX₀ (hinj X hX X₀ hX₀ hXQ hX₀Q h)
      have hcol : ⁅E, X⁆ ∈ lambdaSet R ⁅E, X₀⁆ := hS.mem_lambdaSet_of_mem_deltaSet_inter hD₀ hD1
        hne.symm ⟨hQ0D₀, hQ0D⟩ ⟨hQ1D₀, hQ1D⟩ hQ01
      have hle : ⁅E, X⁆ ≤ E ⊔ ⁅E, X₀⁆ := hS.le_sup_of_mem_lambdaSet hE hD₀ hD1 hD₀E hD1E hcol
      obtain ⟨y, hyX₀, hyE⟩ := CaseB.exists_conjSub_eq_of_le_sup hR hiso hER hX₀.1.1.1
        hD1.1.1.1 (hspE X₀ hX₀ hX₀Q) hle hne
      refine ⟨y, hyX₀, fun h1 => ?_, hyE⟩
      rw [h1, conjSub_one] at hyE
      exact hD1E.1.2.1 hyE.symm
    choose! yf hyf using hy
    have hmaps : ∀ X ∈ S \ {Q 2, X₀}, yf X ∈ (X₀ : Set G) \ {1} := by
      intro X hX
      have hX' : X ≠ Q 2 ∧ X ≠ X₀ := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hX.2
      obtain ⟨h1, h2, -⟩ := hyf X hX.1 hX'.1 hX'.2
      exact ⟨h1, h2⟩
    have hinj' : Set.InjOn yf (S \ {Q 2, X₀}) := by
      intro X hX X' hX' he
      have hXn : X ≠ Q 2 ∧ X ≠ X₀ := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hX.2
      have hX'n : X' ≠ Q 2 ∧ X' ≠ X₀ := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hX'.2
      have h1 := (hyf X hX.1 hXn.1 hXn.2).2.2
      have h2 := (hyf X' hX'.1 hX'n.1 hX'n.2).2.2
      rw [he] at h1
      exact hinj X hX.1 X' hX'.1 hXn.1 hX'n.1 (h1.symm.trans h2)
    have hle1 : (S \ {Q 2, X₀}).ncard ≤ ((X₀ : Set G) \ {1}).ncard :=
      Set.ncard_le_ncard_of_injOn yf hmaps hinj'
    have hX₀card : ((X₀ : Set G) \ {1}).ncard = 2 ^ f - 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem (one_mem X₀), ← Nat.card_coe_set_eq,
        SetLike.coe_sort_coe, hR.card_eq hX₀.1.1.1 hA, hcard]
    have hle2 := Set.ncard_le_ncard_sdiff_add_ncard S {Q 2, X₀}
    have hle3 : ({Q 2, X₀} : Set (Subgroup G)).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  · push Not at hex
    calc S.ncard ≤ ({Q 2} : Set (Subgroup G)).ncard := Set.ncard_le_ncard fun X hX => hex X hX
      _ = 1 := Set.ncard_singleton _
      _ ≤ 2 ^ f + 1 := by omega

end Sec12

end CFSG.Timmesfeld.ARS
