module

public import CFSG.RankThree.PartOne.D4RC.GeoBorel
public import CFSG.Timmesfeld.ARS.CaseHFlag

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7 CFSG.Timmesfeld.ARS
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open scoped commutatorElement

variable {K : Type} [Field K] {σ : K →+* K}

section Flags

variable [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) [Finite (twistedGroup σ)]
  [IsSimpleGroup (twistedGroup σ)]
include hσ

theorem rcg_lineN_mem_lines : lineN σ ∈ linesThrough (longClass σ) (Xh σ) := by
  refine (CaseH.mem_linesThrough_iff (rcg_hyp hσ) rcg_Xh_mem).2
    ⟨twistedRootGroup σ (rt 3), ?_, rfl⟩
  refine CaseH.mem_lambdaSet_of_commuting (rcg_sigmaEqLambda hσ) rcg_Xh_mem
    (rcg_long_mem hσ (t := 3) (by simp [longPos])) ?_
    (rcg_commuting_pos hσ (t := 3) (Or.inr rfl))
  intro h3
  have hc : Commuting (twistedRootGroup σ (rt 0)) (twistedRootGroup σ (rt 3)) := by
    rw [h3]
    exact (rcg_commuting_pos hσ (t := 0) (Or.inl rfl)).symm
  exact Special.not_commuting (rcg_isRootClass hσ) (rcg_special_base hσ) hc

theorem rcg_lineB_mem_lines : lineB σ ∈ linesThrough (longClass σ) (Xh σ) := by
  refine (CaseH.mem_linesThrough_iff (rcg_hyp hσ) rcg_Xh_mem).2
    ⟨twistedRootGroup σ (rt 0), ?_, rfl⟩
  refine CaseH.mem_lambdaSet_of_commuting (rcg_sigmaEqLambda hσ) rcg_Xh_mem
    (rcg_long_mem hσ (t := 0) (by simp [longPos])) ?_
    (rcg_commuting_pos hσ (t := 0) (Or.inl rfl))
  intro h0
  have hc : Commuting (twistedRootGroup σ (rt 0)) (twistedRootGroup σ (rt 3)) := by
    rw [h0]
    exact rcg_commuting_pos hσ (t := 3) (Or.inr rfl)
  exact Special.not_commuting (rcg_isRootClass hσ) (rcg_special_base hσ) hc

theorem rcg_exists_conj_line {W W' : Subgroup (twistedGroup σ)}
    (hW : W ∈ linesThrough (longClass σ) (Xh σ)) (hW' : W' ∈ linesThrough (longClass σ) (Xh σ)) :
    ∃ g : twistedGroup σ, conjSub (Xh σ) g = Xh σ ∧ conjSub W g = W' := by
  have h := rcg_hyp hσ
  have hH := rcg_sigmaEqLambda hσ
  have hN := rcg_lineN_mem_lines hσ
  have hB := rcg_lineB_mem_lines hσ
  have hne := rcg_lineN_ne_lineB hσ
  let T : Subgroup (twistedGroup σ) → Subgroup (twistedGroup σ) → Prop := fun X Y =>
    ∃ g : twistedGroup σ, conjSub (Xh σ) g = Xh σ ∧ conjSub X g = Y
  have Tsymm : ∀ X Y, T X Y → T Y X := by
    rintro X Y ⟨g, hg, hgXY⟩
    refine ⟨g⁻¹, ?_, ?_⟩
    · conv_lhs => rw [← hg]
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    · rw [← hgXY]
      exact conjSub_conjSub_inv' X g
  have Ttrans : ∀ X Y Z, T X Y → T Y Z → T X Z := by
    rintro X Y Z ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
    refine ⟨g₂ * g₁, ?_, ?_⟩
    · rw [conjSub_mul, hg₁, hg₂]
    · rw [conjSub_mul, h₁, h₂]
  have ha : ∀ X ∈ linesThrough (longClass σ) (Xh σ), ∀ Y ∈ linesThrough (longClass σ) (Xh σ),
      X ≠ lineN σ → Y ≠ lineN σ → T X Y := by
    intro X hX Y hY hXN hYN
    obtain ⟨g, hg, -, hgXY⟩ := CaseH.exists_conj_line h hH rcg_Xh_mem hN hX hY hXN hYN
    exact ⟨g, hg, hgXY⟩
  have hb : ∀ X ∈ linesThrough (longClass σ) (Xh σ), ∀ Y ∈ linesThrough (longClass σ) (Xh σ),
      X ≠ lineB σ → Y ≠ lineB σ → T X Y := by
    intro X hX Y hY hXB hYB
    obtain ⟨g, hg, -, hgXY⟩ := CaseH.exists_conj_line h hH rcg_Xh_mem hB hX hY hXB hYB
    exact ⟨g, hg, hgXY⟩
  have hc : T (lineN σ) (lineB σ) :=
    ⟨nHat σ (ng 1), (rcg_conj_nHat_lines hσ).1, (rcg_conj_nHat_lines hσ).2.1⟩
  by_cases hXY : W = W'
  · subst hXY
    exact ⟨1, conjSub_one _, conjSub_one _⟩
  by_cases hN1 : W = lineN σ
  · subst hN1
    by_cases hY1 : W' = lineB σ
    · subst hY1
      exact hc
    · exact hb _ hW _ hW' hne hY1
  · by_cases hN2 : W' = lineN σ
    · subst hN2
      by_cases hX1 : W = lineB σ
      · subst hX1
        exact Tsymm _ _ hc
      · exact hb _ hW _ hW' hX1 hne
    · exact ha _ hW _ hW' hN1 hN2

theorem rcg_exists_conj_flag {B V : Subgroup (twistedGroup σ)} (hB : B ∈ longClass σ)
    (hV : V ∈ linesThrough (longClass σ) B) :
    ∃ k : twistedGroup σ, conjSub B k = Xh σ ∧ conjSub V k = lineN σ := by
  obtain ⟨g, rfl⟩ := hB
  have hV₀ : conjSub V g⁻¹ ∈ linesThrough (longClass σ) (Xh σ) := by
    refine ⟨CaseH.IsLine.conjSub (rcg_isRootClass hσ) hV.1 g⁻¹, ?_⟩
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hV.2
    change conjSub (conjSub (Xh σ) g) g⁻¹ ≤ conjSub V g⁻¹ at this
    rwa [conjSub_conjSub_inv'] at this
  obtain ⟨h, hh, hhV⟩ := rcg_exists_conj_line hσ hV₀ (rcg_lineN_mem_lines hσ)
  refine ⟨h * g⁻¹, ?_, ?_⟩
  · rw [conjSub_mul, conjSub_conjSub_inv', hh]
  · rw [conjSub_mul, hhV]

end Flags

theorem rcg_odd_coprime {q p : ℕ} (hq : 1 ≤ q) (hp : p.Prime) (hpq : p ∣ q ^ 2 - q + 1) :
    p ≠ 2 ∧ Nat.Coprime p (q ^ 3 - 1) := by
  have e : q ^ 2 - q = q * (q - 1) := by rw [Nat.mul_sub_one, pow_two]
  have hodd : Odd (q ^ 2 - q + 1) := by
    rw [e]
    exact (Nat.even_mul_pred_self q).add_one
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hodd.not_two_dvd_nat hpq
  refine ⟨hp2, (Nat.Prime.coprime_iff_not_dvd hp).2 fun h1 => hp2 ?_⟩
  have h3 : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    obtain ⟨r, hr⟩ : ∃ r, q ^ 2 = q + r := ⟨q ^ 2 - q, by
      have := Nat.le_self_pow (by norm_num : 2 ≠ 0) q
      omega⟩
    have hr' : q ^ 2 - q = r := by omega
    rw [hr']
    have : q ^ 3 = q * q ^ 2 := by ring
    rw [this, hr]
    nlinarith [hr]
  have h2 : p ∣ q ^ 3 + 1 := by
    rw [h3]
    exact Dvd.dvd.mul_left hpq _
  have h4 : q ^ 3 + 1 = (q ^ 3 - 1) + 2 := by
    have := Nat.one_le_pow 3 q hq
    omega
  rw [h4] at h2
  exact ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((Nat.dvd_add_right h1).1 h2))

theorem rcg_lfpf_gen [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c)
    [Finite (twistedGroup σ)] [IsSimpleGroup (twistedGroup σ)] {q : ℕ} (hK : Nat.card K = q ^ 3)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q ^ 3 - 1) {y : twistedGroup σ}
    (hy : orderOf y = p) {B : Subgroup (twistedGroup σ)} (hB : B ∈ longClass σ)
    (hyB : conjSub B y = B) {D : Subgroup (twistedGroup σ)}
    (hD : D ∈ lambdaSet (longClass σ) B) : conjSub (B ⊔ D) y ≠ B ⊔ D := by
  intro hV
  have hVl : B ⊔ D ∈ linesThrough (longClass σ) B :=
    (CaseH.mem_linesThrough_iff (rcg_hyp hσ) hB).2 ⟨D, hD, rfl⟩
  obtain ⟨k, hkB, hkV⟩ := rcg_exists_conj_flag hσ hB hVl
  have hstab : ∀ {A A' : Subgroup (twistedGroup σ)}, conjSub A k = A' → conjSub A y = A →
      conjSub A' (k * y * k⁻¹) = A' := by
    intro A A' hk hy'
    subst hk
    rw [conjSub_mul, conjSub_mul, conjSub_conjSub_inv', hy']
  have hzb := rcg_stab_le_borel hσ (hstab hkB hyB) (hstab hkV hV)
  have hzo : orderOf (k * y * k⁻¹) = p := by
    rw [← hy]
    exact orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective y
  exact rcg_no_order_borel hσ (m := Nat.card K - 1) rcg_units_pow_card hp hp2
    (by rw [hK]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpq) hzb hzo

theorem rcg_lfpf [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) [Finite (twistedGroup σ)]
    [IsSimpleGroup (twistedGroup σ)] {q : ℕ} (hK : Nat.card K = q ^ 3) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ q ^ 2 - q + 1) {y : twistedGroup σ} (hy : orderOf y = p)
    {B : Subgroup (twistedGroup σ)} (hB : B ∈ longClass σ) (hyB : conjSub B y = B)
    {D : Subgroup (twistedGroup σ)} (hD : D ∈ lambdaSet (longClass σ) B) :
    conjSub (B ⊔ D) y ≠ B ⊔ D := by
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0] at hK
      have : 0 < Nat.card K := Nat.card_pos
      simp [hK] at this
    · exact h0
  obtain ⟨hp2, hcop⟩ := rcg_odd_coprime hq1 hp hpq
  exact rcg_lfpf_gen hσ hK hp hp2 ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop) hy hB hyB hD

end CFSG.RankThree.PartOne.D4RC
