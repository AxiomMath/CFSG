module

public import CFSG.Quasithin.Background.B15P4LayerQuad
public import CFSG.Quasithin.Background.B15P4Repl
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.D2Offenders
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Quasithin.Background.A3ComponentsQuotient
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1MoreSeven
public import CFSG.Quasithin.Background.B1Solvable

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Open

variable {V : Type} [CommGroup V] [Finite V]

theorem isFFStarOffender_of_rPlus (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : A ∈ RPlus X) (hr : rAV A ≤ 1) : IsFFStarOffender X A := by
  refine ⟨hA.1.1, hA.1.2.1, hA.1.2.2, fun B hBA => ?_⟩
  by_cases hB : B = ⊥
  · subst hB
    rw [Subgroup.card_bot, one_mul, B1.fixV_bot, Subgroup.card_top]
    exact (rAV_le_one_iff hV hA.1).1 hr
  · have hB2 : IsA2 X B := hA.1.mono hBA hB
    have hrB : rAV A ≤ rAV B := hA.2 B hB hBA
    have hA' : Nat.card A = 2 ^ rk A := B1.card_elemAbelian hA.1.2.2
    have hB' : Nat.card B = 2 ^ rk B := B1.card_elemAbelian hB2.2.2
    have hfA : Nat.card (fixV A) = 2 ^ rk (fixV A) := card_eq_two_pow hV _
    have hfB : Nat.card (fixV B) = 2 ^ rk (fixV B) := card_eq_two_pow hV _
    have h2 := rk_add_rkIdx (fixV A)
    have h3 := rk_add_rkIdx (fixV B)
    have h4 : rk B ≤ rk A := rk_mono hBA
    have h5 : rkIdx (fixV A) ≤ rk A :=
      (B1.card_le_iff hV hA.1.2.2).1 ((rAV_le_one_iff hV hA.1).1 hr)
    have hkA : 0 < rk A := hA.1.rk_pos
    have hkB : 0 < rk B := hB2.rk_pos
    have h6 : rkIdx (fixV A) * rk B ≤ rkIdx (fixV B) * rk A := by
      unfold rAV at hrB
      rw [div_le_div_iff₀ (by exact_mod_cast hkA) (by exact_mod_cast hkB)] at hrB
      exact_mod_cast hrB
    have h7 : rk B + rkIdx (fixV A) ≤ rk A + rkIdx (fixV B) := by
      by_contra hcon
      push Not at hcon
      have e1 : ((rk A : ℤ) - rk B) * ((rk A : ℤ) - rkIdx (fixV A)) ≥ 0 :=
        mul_nonneg (by omega) (by omega)
      have e2 : (rkIdx (fixV A) : ℤ) * rk B ≤ (rkIdx (fixV B) : ℤ) * rk A := by exact_mod_cast h6
      have e3 : (rk A : ℤ) + rkIdx (fixV B) < rk B + rkIdx (fixV A) := by exact_mod_cast hcon
      have e4 : (0 : ℤ) < rk A := by exact_mod_cast hkA
      nlinarith
    rw [hA', hfA, hB', hfB, ← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem qhatStar_le_normalizer_of_qhatOf_le_one (hV : ∀ v : V, v ^ 2 = 1)
    {X A K : Subgroup (MulAut V)} (hq : qhatOf X ≤ ((1 : ℚ) : WithTop ℚ)) (hA : A ∈ QhatStar X)
    (hK : IsComponentOf K X) : A ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
  obtain ⟨r, hr, -, ⟨⟨hA2, hAr⟩, hcub⟩, hmin⟩ := QhatStar_spec hA
  have hr1 : r ≤ 1 := by
    rw [hr] at hq
    exact_mod_cast hq
  have hplus : A ∈ RPlus X := D2_3_2 hA2 hcub (by rw [hAr]; exact hr.symm)
  have hP := isFFStarOffender_of_rPlus hV hplus (hAr ▸ hr1)
  obtain ⟨F, hFA, hF, hFq, hFcard, -, -⟩ := exists_quadratic_offender_le hV hP
  have hFr : rAV F ≤ r := by
    have h1 := rAV_le_of_card_le hV hA2 hF.isA2 hFA (hAr ▸ hr1) hFcard.ge
    rwa [hAr] at h1
  have hFcub : commSeries F 3 = ⊥ :=
    commSeries_eq_bot_of_le (by norm_num) ((isQuadratic_iff_commSeries_two F).1 hFq)
  have hFeq : F = A := hmin F ⟨⟨hF.isA2, hFr⟩, hFcub⟩ hFA
  rw [← hFeq]
  exact B15P4.normalizes_of_isQuadratic hV hF hFq hK

theorem exists_isFFStarOffender_le {X A₀ : Subgroup (MulAut V)} (hA₀ : IsA2 X A₀)
    (hff : Nat.card V ≤ Nat.card A₀ * Nat.card (fixV A₀)) :
    ∃ A ≤ A₀, IsFFStarOffender X A := by
  suffices H : ∀ n : ℕ, ∀ A₀ : Subgroup (MulAut V), Nat.card A₀ = n → IsA2 X A₀ →
      Nat.card V ≤ Nat.card A₀ * Nat.card (fixV A₀) → ∃ A ≤ A₀, IsFFStarOffender X A from
    H _ A₀ rfl hA₀ hff
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A₀ h hA₀ hff
    by_cases hP : ∀ B ≤ A₀, Nat.card B * Nat.card (fixV B) ≤ Nat.card A₀ * Nat.card (fixV A₀)
    · exact ⟨A₀, le_rfl, hA₀.1, hA₀.2.1, hA₀.2.2, hP⟩
    · push Not at hP
      obtain ⟨B, hBA, hBgt⟩ := hP
      have hBne : B ≠ ⊥ := by
        rintro rfl
        rw [Subgroup.card_bot, one_mul, B1.fixV_bot, Subgroup.card_top] at hBgt
        omega
      have hBlt : Nat.card B < n := by
        rw [← h]
        refine lt_of_le_of_ne (Subgroup.card_le_of_le hBA) fun heq => ?_
        have hBA' : B = A₀ := Subgroup.eq_of_le_of_card_ge hBA heq.ge
        subst hBA'
        omega
      obtain ⟨A, hAB, hA⟩ := ih (Nat.card B) hBlt B rfl (hA₀.mono hBA hBne) (hff.trans hBgt.le)
      exact ⟨A, hAB.trans hBA, hA⟩

theorem qhatOf_le_one_of_isFFModule (hV : ∀ v : V, v ^ 2 = 1) {X Y : Subgroup (MulAut V)}
    (hYX : Y ≤ X) (hff : IsFFModule Y) : qhatOf X ≤ ((1 : ℚ) : WithTop ℚ) := by
  obtain ⟨A₀, hA₀Y, hne, he, hle⟩ := hff
  obtain ⟨A, -, hA⟩ := exists_isFFStarOffender_le ⟨hA₀Y, hne, he⟩ hle
  obtain ⟨F, -, hF, hFq, hFcard, -, -⟩ := exists_quadratic_offender_le hV hA
  have hFle : Nat.card V ≤ Nat.card F * Nat.card (fixV F) := by
    rw [hFcard]
    simpa [B1.fixV_bot] using hA.2.2.2 ⊥ bot_le
  have hF2 : IsA2 X F := ⟨hF.1.trans hYX, hF.2.1, hF.2.2.1⟩
  have hFr : rAV F ≤ 1 := (rAV_le_one_iff hV hF2).2 hFle
  have hFcub : commSeries F 3 = ⊥ :=
    commSeries_eq_bot_of_le (by norm_num) ((isQuadratic_iff_commSeries_two F).1 hFq)
  unfold qhatOf
  exact kq_le_iff.2 ⟨F, hF2, hFcub, hFr⟩

theorem isComponentOf_of_mem_cComp {G : Type*} [Group G] {K X : Subgroup G} (hK : K ∈ cComp X)
    (hq : CFSG.IsQuasisimple ↥K) : IsComponentOf K X :=
  ⟨A3.subnormal_le hK.2.2.1, hK.2.2.1, A3.isQuasisimple_iff_open.mp hq⟩

end CFSG.Quasithin.H13.T326
