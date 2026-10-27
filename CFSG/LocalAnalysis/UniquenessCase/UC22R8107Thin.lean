module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Pair
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

@[expose] def R8107Thin (D : Data G) : Prop :=
  ∀ L₁ ∈ calC D.M, ∀ L₂ ∈ calC D.M, L₁ ≠ L₂ → CFSG.Open.pRank 3 L₁ = 1 →
    CFSG.Open.pRank 3 L₂ = 1 → F08.Thin8 L₁ → F08.Thin8 L₂ →
    ∀ A₁ A₂ : Subgroup G, A₁ ≤ L₁ → Nat.card A₁ = 3 → A₂ ≤ L₂ → Nat.card A₂ = 3 →
      A₁ ∈ uniqueSet D.M ∧ A₂ ∈ uniqueSet D.M

@[expose] def R8107U3 (D : Data G) : Prop :=
  ∀ L₁ ∈ calC D.M, ∀ L₂ ∈ calC D.M, L₁ ≠ L₂ → CFSG.Open.pRank 3 L₁ = 1 →
    CFSG.Open.pRank 3 L₂ = 1 →
    (F08.Thin8 L₁ ∨ ∃ n : ℕ, IsU3 (Bar2 L₁) n) → (F08.Thin8 L₂ ∨ ∃ n : ℕ, IsU3 (Bar2 L₂) n) →
    ((∃ n : ℕ, IsU3 (Bar2 L₁) n) ∨ ∃ n : ℕ, IsU3 (Bar2 L₂) n) →
    ∀ A₁ A₂ : Subgroup G, A₁ ≤ L₁ → Nat.card A₁ = 3 → A₂ ≤ L₂ → Nat.card A₂ = 3 →
      A₁ ∈ uniqueSet D.M ∧ A₂ ∈ uniqueSet D.M

theorem r8107_of_thin_and_u3 {D : Data G} (hT : R8107Thin D) (hU : R8107U3 D) : F08.R8107 D := by
  intro L₁ hL₁ L₂ hL₂ h12 r₁ r₂ s₁ s₂
  by_cases hu : (∃ n : ℕ, IsU3 (Bar2 L₁) n) ∨ ∃ n : ℕ, IsU3 (Bar2 L₂) n
  · exact hU L₁ hL₁ L₂ hL₂ h12 r₁ r₂ s₁ s₂ hu
  · push Not at hu
    exact hT L₁ hL₁ L₂ hL₂ h12 r₁ r₂ (s₁.resolve_right (not_exists.2 hu.1))
      (s₂.resolve_right (not_exists.2 hu.2))

namespace R8107Thin

theorem mem_uniqueSet_of_card_three {D : Data G} (hsp : IsStronglyPEmbedded 3 D.M)
    {L A : Subgroup G} (hL : L ∈ calC D.M) (hAL : A ≤ L) (hA : Nat.card A = 3) :
    A ∈ uniqueSet D.M :=
  uc22p22r_mem_uniqueSet_of_sp D Nat.prime_three hsp (hAL.trans hL.1.le)
    (IsPGroup.of_card (n := 1) (by rw [hA, pow_one]))
    (fun h => by rw [h, Subgroup.card_bot] at hA; omega)

theorem false_of_loss (D : Data G) (hx : DataExt D) (he : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h82 : F08.R82 D)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L₁ L₂ : Subgroup G} (hL₁ : L₁ ∈ calC D.M)
    (hL₂ : L₂ ∈ calC D.M) (h12 : L₁ ≠ L₂) (r₁ : CFSG.Open.pRank 3 L₁ = 1)
    (r₂ : CFSG.Open.pRank 3 L₂ = 1) (hZ₁ : center (Bar2 L₁) = ⊥)
    (hloss₁ : ∀ p : ℕ, p.Prime → 5 ≤ p → R8107Loss.LossAt (Bar2 L₁) p)
    (hloss₂ : ∀ p : ℕ, p.Prime → 5 ≤ p → R8107Loss.LossAt (Bar2 L₂) p) : False := by
  have hns := UC6S846.not_solvable_of_mem_calC hL₁
  have h3σ : 3 ∉ D.sig := fun h => hnsp (UC6S846.sp_of_mem_sig hSg hns h)
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp5 : 5 ≤ p := by
    have h2 := hpp.two_le
    have hp3 : p ≠ 3 := fun h => h3σ (h ▸ hp)
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hpp
    omega
  obtain ⟨R, E, A, hR, hEZ, hEel, hEc, hA, hAel, hAc⟩ :=
    R8107Pair.exists_elemAbelian_of_lossAt_pair hL₁ hL₂ h12
      (fun _ hHM hH => R8107Odd.le_normalizer_of_odd h82 hnsp hL₁ r₁ hHM hH)
      (fun _ hHM hH => R8107Odd.le_normalizer_of_odd h82 hnsp hL₂ r₂ hHM hH) hZ₁
      (fun _ hB hBp => R8107Shape.isCyclic_of_isPGroup_of_pRank_eq_one r₁ hB hBp)
      (fun _ hB hBp => R8107Shape.isCyclic_of_isPGroup_of_pRank_eq_one r₂ hB hBp) hpp hp2
      (hx.four_le he p hp) (hloss₁ p hpp hp5) (hloss₂ p hpp hp5)
  have hΓ := h76 p hp hp2 (UC6S846.sp_of_mem_sig hSg hns hp) 3 Nat.prime_three E
    (hEZ.trans (inf_le_left.trans hR.le)) hEel hEc
    (lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp hA hAel hAc))
    (fun X hXE _ => lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp
      (hA.trans (inf_le_inf_left _ ((centralizer_le hXE).trans (centralizer_le_normalizer _))))
      hAel hAc))
  exact hnsp (h614 (UC6S846.sig_subset_sig1 hSg hns) 3 Nat.prime_three (by norm_num) h3σ R hR E
    hEZ hEel hEc hΓ)

theorem lossAt_of_thin8 (D : Data G) (hKThin : KThinSimple) {L : Subgroup G} (hL : L ∈ calC D.M)
    (r : CFSG.Open.pRank 3 L = 1) (s : F08.Thin8 L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    R8107Loss.LossAt (Bar2 L) p :=
  R8107Loss.lossAt_of_thinShape
    (R8107Shape.thinShape_of_thin8 D hKThin hL s (R8107Shape.three_dvd_card_bar2 r))
    (R8107Shape.center_eq_bot_of_thin8 hL s) (R8107Shape.three_dvd_card_bar2 r) hp (by omega)
    fun _ hB => R8107Shape.isCyclic_of_isPGroup_of_thin8 s hp (by omega) hB

end R8107Thin

theorem r8107_of_loss (D : Data G) (hx : DataExt D) (he : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h82 : F08.R82 D)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D)
    {L₁ L₂ : Subgroup G} (hL₁ : L₁ ∈ calC D.M) (hL₂ : L₂ ∈ calC D.M) (h12 : L₁ ≠ L₂)
    (r₁ : CFSG.Open.pRank 3 L₁ = 1) (r₂ : CFSG.Open.pRank 3 L₂ = 1)
    (hZ₁ : center (Bar2 L₁) = ⊥)
    (hloss₁ : ∀ p : ℕ, p.Prime → 5 ≤ p → R8107Loss.LossAt (Bar2 L₁) p)
    (hloss₂ : ∀ p : ℕ, p.Prime → 5 ≤ p → R8107Loss.LossAt (Bar2 L₂) p)
    {A₁ A₂ : Subgroup G} (hA₁ : A₁ ≤ L₁) (hc₁ : Nat.card A₁ = 3) (hA₂ : A₂ ≤ L₂)
    (hc₂ : Nat.card A₂ = 3) : A₁ ∈ uniqueSet D.M ∧ A₂ ∈ uniqueSet D.M := by
  by_cases hsp : IsStronglyPEmbedded 3 D.M
  · exact ⟨R8107Thin.mem_uniqueSet_of_card_three hsp hL₁ hA₁ hc₁,
      R8107Thin.mem_uniqueSet_of_card_three hsp hL₂ hA₂ hc₂⟩
  · exact (R8107Thin.false_of_loss D hx he hSg h82 h76 h614 hsp hL₁ hL₂ h12 r₁ r₂ hZ₁ hloss₁
      hloss₂).elim

theorem r8107_thin_of_inputs (D : Data G) (hx : DataExt D) (he : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h82 : F08.R82 D)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D)
    (hKThin : KThinSimple) : R8107Thin D := by
  intro L₁ hL₁ L₂ hL₂ h12 r₁ r₂ s₁ s₂ A₁ A₂ hA₁ hc₁ hA₂ hc₂
  exact r8107_of_loss D hx he hSg h82 h76 h614 hL₁ hL₂ h12 r₁ r₂
    (R8107Shape.center_eq_bot_of_thin8 hL₁ s₁)
    (fun _ hp hp5 => R8107Thin.lossAt_of_thin8 D hKThin hL₁ r₁ s₁ hp hp5)
    (fun _ hp hp5 => R8107Thin.lossAt_of_thin8 D hKThin hL₂ r₂ s₂ hp hp5) hA₁ hc₁ hA₂ hc₂

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
