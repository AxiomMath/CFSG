module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RJ2Lat
public import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2Lat
public import CFSG.Quasithin.Background.RonanE114C5J2

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A312J2
  CFSG.ComponentClassification.J2Cover

theorem J2Y.eq_of_card
    {j : ℕ} (hj : j = 2 ∨ j = 3)
    {Z : Subgroup ↥CFSG.Sporadic.J2.J} (hSZ : j2CtxA.S ≤ Z)
    (hc : Nat.card Z = Nat.card (j2CtxA.Y j)) : Z = j2CtxA.Y j := by
  rcases hj with rfl | rfl
  · exact CFSG.Quasithin.RonanE114.C5.J2.unique_Y2 Z hSZ hc
  · exact CFSG.Quasithin.RonanE114.C5.J2.unique_Y3 Z hSZ hc

theorem J2Y.normalizer_le
    {j : ℕ}
    (hj : j = 2 ∨ j = 3) :
    Subgroup.normalizer (j2CtxA.S : Set ↥CFSG.Sporadic.J2.J) ≤ j2CtxA.Y j := by
  intro n hn
  have hmapS : j2CtxA.S.map (MulAut.conj n).toMonoidHom = j2CtxA.S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hmapY : (j2CtxA.Y j).map (MulAut.conj n).toMonoidHom = j2CtxA.Y j := by
    refine J2Y.eq_of_card hj ?_ ?_
    · rw [← hmapS]
      exact Subgroup.map_mono (j2CtxA.S_le_Y j)
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have hnY : n ∈ Subgroup.normalizer (j2CtxA.Y j : Set ↥CFSG.Sporadic.J2.J) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapY
  have hnO : n ∈ Subgroup.normalizer (pCoreOf 2 (j2CtxA.Y j) : Set ↥CFSG.Sporadic.J2.J) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) (H := j2CtxA.Y j)) hnY
  have hYN : j2CtxA.Y j = Subgroup.normalizer
      (pCoreOf 2 (j2CtxA.Y j) : Set ↥CFSG.Sporadic.J2.J) := by
    refine J2L.eq_normalizer_of_card (j := j) (by omega) ?_ ?_
    · rcases hj with rfl | rfl
      · intro i _ hd
        rw [J2L.card_Y2] at hd
        interval_cases i <;> simp_all
      · intro i _ hd
        rw [J2L.card_Y3] at hd
        interval_cases i <;> simp_all
    · rcases hj with rfl | rfl
      · intro hbot
        have hcard := J2L.card_pCoreOf_Y2
        rw [hbot, Subgroup.card_bot] at hcard
        norm_num at hcard
      · intro hbot
        have hcard := J2L.card_pCoreOf_Y3
        rw [hbot, Subgroup.card_bot] at hcard
        norm_num at hcard
  rwa [← hYN] at hnO

theorem J2Y.isMaximalTwoLocal
    {j : ℕ}
    (hj : j = 2 ∨ j = 3) : IsMaximalTwoLocal (j2CtxA.Y j) := by
  constructor
  · rcases hj with rfl | rfl
    · exact J2L.isTwoLocal_Y2
    · exact J2L.isTwoLocal_Y3
  · intro H hH hHY
    rcases J2L.overgroup ((j2CtxA.S_le_Y j).trans hHY) with htop | ⟨i, hi, hYi, hcard⟩
    · subst htop
      exact absurd hH J2L.not_isTwoLocal_top
    · rw [hYi] at hHY hcard ⊢
      have hd : Nat.card (j2CtxA.Y j) ∣ Nat.card (j2CtxA.Y i) := Subgroup.card_dvd_of_le hHY
      rw [hcard] at hd
      rcases hj with rfl | rfl
      · rw [J2L.card_Y2] at hd
        interval_cases i <;> simp_all
      · rw [J2L.card_Y3] at hd
        interval_cases i <;> simp_all

theorem J2Y.isYAmalgamPair :
    IsYAmalgamPair j2CtxA.S (j2CtxA.Y 3) (j2CtxA.Y 2) := by
  refine ⟨j2A_sylow, ?_, ?_⟩
  · intro h
    have hcard := congrArg (fun X : Subgroup ↥CFSG.Sporadic.J2.J => Nat.card ↥X) h
    rw [J2L.card_Y3, J2L.card_Y2] at hcard
    norm_num at hcard
  · intro M
    constructor
    · rintro ⟨hM, hNM⟩
      have hSM : j2CtxA.S ≤ M := fun x hx => hNM (Subgroup.le_normalizer hx)
      rcases J2L.eq_Y2_or_Y3 hM hSM with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (rfl | rfl)
      · exact ⟨J2Y.isMaximalTwoLocal (Or.inr rfl), J2Y.normalizer_le (Or.inr rfl)⟩
      · exact ⟨J2Y.isMaximalTwoLocal (Or.inl rfl), J2Y.normalizer_le (Or.inl rfl)⟩

theorem J2Y.card_inf_dvd :
    Nat.card ↥(j2CtxA.Y 3 ⊓ j2CtxA.Y 2) ∣ 384 := by
  have h1 : Nat.card ↥(j2CtxA.Y 3 ⊓ j2CtxA.Y 2) ∣ 1920 := by
    simpa only [J2L.card_Y3] using
      Subgroup.card_dvd_of_le (inf_le_left : j2CtxA.Y 3 ⊓ j2CtxA.Y 2 ≤ j2CtxA.Y 3)
  have h2 : Nat.card ↥(j2CtxA.Y 3 ⊓ j2CtxA.Y 2) ∣ 1152 := by
    simpa only [J2L.card_Y2] using
      Subgroup.card_dvd_of_le (inf_le_right : j2CtxA.Y 3 ⊓ j2CtxA.Y 2 ≤ j2CtxA.Y 2)
  have h := Nat.dvd_gcd h1 h2
  norm_num at h
  exact h

theorem AJ2Y.eq_of_card
    {j : ℕ} (hj : j = 1 ∨ j = 2) {Z : Subgroup R} (hSZ : AJ2L.rCtx.S ≤ Z)
    (hc : Nat.card Z = Nat.card (AJ2L.rCtx.Y j)) : Z = AJ2L.rCtx.Y j := by
  rcases AJ2L.overgroup hSZ with htop | ⟨i, hi, hYi, hcard⟩
  · rw [htop, Subgroup.card_top, card_R] at hc
    rcases hj with rfl | rfl
    · rw [AJ2L.card_Y1] at hc
      norm_num at hc
    · rw [AJ2L.card_Y2] at hc
      norm_num at hc
  · rw [hYi] at hcard
    have hd : Nat.card (AJ2L.rCtx.Y i) = Nat.card (AJ2L.rCtx.Y j) := by
      rw [← hYi]
      exact hc
    rw [hcard] at hd
    rcases hj with rfl | rfl
    · rw [AJ2L.card_Y1] at hd
      interval_cases i <;> simp_all
    · rw [AJ2L.card_Y2] at hd
      interval_cases i <;> simp_all

theorem AJ2Y.normalizer_le
    {j : ℕ} (hj : j = 1 ∨ j = 2) :
    Subgroup.normalizer (AJ2L.rCtx.S : Set R) ≤ AJ2L.rCtx.Y j := by
  intro n hn
  have hmapS : AJ2L.rCtx.S.map (MulAut.conj n).toMonoidHom = AJ2L.rCtx.S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hmapY : (AJ2L.rCtx.Y j).map (MulAut.conj n).toMonoidHom = AJ2L.rCtx.Y j := by
    refine AJ2Y.eq_of_card hj ?_ ?_
    · rw [← hmapS]
      exact Subgroup.map_mono (AJ2L.rCtx.S_le_Y j)
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have hnY : n ∈ Subgroup.normalizer (AJ2L.rCtx.Y j : Set R) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapY
  have hnO : n ∈ Subgroup.normalizer (pCoreOf 2 (AJ2L.rCtx.Y j) : Set R) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) (H := AJ2L.rCtx.Y j)) hnY
  have hYN : AJ2L.rCtx.Y j = Subgroup.normalizer (pCoreOf 2 (AJ2L.rCtx.Y j) : Set R) := by
    refine AJ2L.eq_normalizer_of_card (j := j) (by omega) ?_ ?_
    · rcases hj with rfl | rfl
      · intro i _ hd
        rw [AJ2L.card_Y1] at hd
        interval_cases i <;> simp_all
      · intro i _ hd
        rw [AJ2L.card_Y2] at hd
        interval_cases i <;> simp_all
    · rcases hj with rfl | rfl
      · intro hbot
        have hcard := AJ2L.card_pCoreOf_Y1
        rw [hbot, Subgroup.card_bot] at hcard
        norm_num at hcard
      · intro hbot
        have hcard := AJ2L.card_pCoreOf_Y2
        rw [hbot, Subgroup.card_bot] at hcard
        norm_num at hcard
  rwa [← hYN] at hnO

theorem AJ2Y.isMaximalTwoLocal
    {j : ℕ} (hj : j = 1 ∨ j = 2) :
    IsMaximalTwoLocal (AJ2L.rCtx.Y j) := by
  constructor
  · rcases hj with rfl | rfl
    · exact AJ2L.isTwoLocal_Y1
    · exact AJ2L.isTwoLocal_Y2
  · intro H hH hHY
    rcases AJ2L.overgroup ((AJ2L.rCtx.S_le_Y j).trans hHY) with htop | ⟨i, hi, hYi, hcard⟩
    · subst htop
      exact absurd hH AJ2L.not_isTwoLocal_top
    · rw [hYi] at hHY hcard ⊢
      have hd : Nat.card (AJ2L.rCtx.Y j) ∣ Nat.card (AJ2L.rCtx.Y i) :=
        Subgroup.card_dvd_of_le hHY
      rw [hcard] at hd
      rcases hj with rfl | rfl
      · rw [AJ2L.card_Y1] at hd
        interval_cases i <;> simp_all
      · rw [AJ2L.card_Y2] at hd
        interval_cases i <;> simp_all

theorem AJ2Y.isYAmalgamPair :
    IsYAmalgamPair AJ2L.rCtx.S (AJ2L.rCtx.Y 2) (AJ2L.rCtx.Y 1) := by
  refine ⟨AJ2L.rCtx_sylow, ?_, ?_⟩
  · intro h
    have hcard := congrArg (fun X : Subgroup R => Nat.card ↥X) h
    rw [AJ2L.card_Y2, AJ2L.card_Y1] at hcard
    norm_num at hcard
  · intro M
    constructor
    · rintro ⟨hM, hNM⟩
      have hSM : AJ2L.rCtx.S ≤ M := fun x hx => hNM (Subgroup.le_normalizer hx)
      rcases AJ2L.eq_Y1_or_Y2 hM hSM with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (rfl | rfl)
      · exact ⟨AJ2Y.isMaximalTwoLocal (Or.inr rfl), AJ2Y.normalizer_le (Or.inr rfl)⟩
      · exact ⟨AJ2Y.isMaximalTwoLocal (Or.inl rfl), AJ2Y.normalizer_le (Or.inl rfl)⟩

theorem AJ2Y.card_inf_dvd :
    Nat.card ↥(AJ2L.rCtx.Y 2 ⊓ AJ2L.rCtx.Y 1) ∣ 768 := by
  have h1 : Nat.card ↥(AJ2L.rCtx.Y 2 ⊓ AJ2L.rCtx.Y 1) ∣ 3840 := by
    simpa only [AJ2L.card_Y2] using
      Subgroup.card_dvd_of_le (inf_le_left : AJ2L.rCtx.Y 2 ⊓ AJ2L.rCtx.Y 1 ≤ AJ2L.rCtx.Y 2)
  have h2 : Nat.card ↥(AJ2L.rCtx.Y 2 ⊓ AJ2L.rCtx.Y 1) ∣ 2304 := by
    simpa only [AJ2L.card_Y1] using
      Subgroup.card_dvd_of_le (inf_le_right : AJ2L.rCtx.Y 2 ⊓ AJ2L.rCtx.Y 1 ≤ AJ2L.rCtx.Y 1)
  have h := Nat.dvd_gcd h1 h2
  norm_num at h
  exact h

theorem AJ2Y.inf_eq :
    AJ2L.rCtx.Y 2 ⊓ AJ2L.rCtx.Y 1 = AJ2L.rCtx.Y 4 := by
  rw [eq_comm]
  refine Subgroup.eq_of_le_of_card_ge (le_inf AJ2L.Y4_le_Y2 AJ2L.Y4_le_Y1) ?_
  have h4 : Nat.card (AJ2L.rCtx.Y 4) = 768 := by
    rw [AJ2L.rCtx_card (by norm_num)]
    norm_num
  rw [h4]
  exact Nat.le_of_dvd (by norm_num) AJ2Y.card_inf_dvd

end CFSG.Quasithin.F112R.St84
