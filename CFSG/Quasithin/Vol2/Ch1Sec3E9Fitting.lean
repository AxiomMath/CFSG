module

public import CFSG.Quasithin.Vol2.Ch1Sec3Solvable
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin.P134

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Ch1Sec3

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem normal_or_centralizes_fitting (hO2 : CFSG.pCore 2 Γ = ⊥)
    (hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → Open.pRank r (⊤ : Subgroup Γ) ≤ 2)
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {P S : Subgroup Γ} (hPp : IsPGroup p P)
    (hexp : ∀ x ∈ P, x ^ p = 1) (hc2 : p ^ 2 ≤ Nat.card P) (hc3 : Nat.card P ≤ p ^ 3)
    (hSP : S ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → S ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hPc : P ≤ commutator Γ) :
    P.Normal ∨ (P ≤ Subgroup.centralizer (CFSG.fittingSubgroup Γ : Set Γ) ∧
      Open.pRank p (CFSG.pCore p Γ) ≤ 1) := by
  by_cases hN : P.Normal
  · exact Or.inl hN
  right
  have hp1 := hp.out.one_lt
  have hPΩ : Subgroup.closure {x | x ∈ P ∧ x ^ p = 1} = P := closure_pow_eq hexp
  have hPcl : ClassLeTwo P := classLeTwo_of_card_le hPp hc3
  have hPrk2 : 2 ≤ Open.pRank p P := two_le_pRank_of_pow_eq_one hexp hc2
  have hPrk : Open.pRank p P = 2 := le_antisymm
    ((CFSG.SectionRank.pRank_mono hp1 le_top).trans (hrank p hp.out hp2)) hPrk2
  have hΦ : frattiniIn P = ⁅P, P⁆ := frattiniIn_eq_commutator hPp hexp
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hc2
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp1
    omega
  have hirrN : A1c.IsNormalizerIrreducible P := by
    refine ⟨frattiniIn_ne_of_ne_bot hPne, fun U hU1 hU2 hU3 => ?_⟩
    rw [hΦ] at hU1 ⊢
    exact hirr U hU1 hU2 (hSP.trans hU3)
  have hA : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p →
      P ≤ Subgroup.centralizer (CFSG.pCore r Γ : Set Γ) := by
    intro r hr hr2 hrp
    have : Fact r.Prime := ⟨hr⟩
    set R₀ := CFSG.pCore r Γ with hR₀
    have hR₀p : IsPGroup r R₀ := CFSG.pCore_isPGroup
    obtain ⟨Y, hY, hYf⟩ := exists_isSupercritical_faithful hr2 hR₀p
    have : Y.Characteristic := hY.characteristic
    have : (Y.map R₀.subtype).Normal := normal_map_of_characteristic Y
    obtain ⟨hRr, hRexp, hRcl⟩ := isSupercritical_map hR₀p hY
    have hRrk : Open.pRank r (Y.map R₀.subtype) ≤ 2 :=
      (CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans (hrank r hr hr2)
    rcases A1c.commutator_eq_bot_or_isPOnePlusTwo hr2 hp2 hRr (closure_pow_eq hRexp) hRcl hRrk
      hPp hPΩ hPcl hPrk hirrN with h | ⟨hpr, -⟩
    · intro x hx
      have hxY : ∀ y : R₀, y ∈ Y → x * (y : Γ) = y * x := fun y hy => by
        have hyR : (y : Γ) ∈ Y.map R₀.subtype := ⟨y, hy, rfl⟩
        have h1 := Subgroup.commutator_mem_commutator hyR hx
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1.symm
      have hα : (MulAut.conjNormal x : MulAut R₀) = 1 := by
        refine hYf _ ?_ fun y hy => ?_
        · have h1 : (MulAut.conjNormal x : MulAut R₀) ^ p = 1 := by
            rw [← map_pow, hexp x hx, map_one]
          exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)
            ((Nat.coprime_primes hp.out hr).2 (Ne.symm hrp))
        · have h2 : (MulAut.conjNormal x : MulAut R₀) y = y := by
            apply Subtype.ext
            rw [MulAut.conjNormal_apply, hxY y hy, mul_inv_cancel_right]
          rw [h2, inv_mul_cancel]
          exact Subgroup.one_mem _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (A1c.mul_comm_of_conjNormal_eq_one hα hy).symm
    · exact absurd hpr (Ne.symm hrp)
  have hB : P ≤ Subgroup.centralizer (CFSG.pCore p Γ : Set Γ) ∧
      Open.pRank p (CFSG.pCore p Γ) ≤ 1 := by
    set R₀ := CFSG.pCore p Γ with hR₀
    have hR₀p : IsPGroup p R₀ := CFSG.pCore_isPGroup
    by_cases hbot : R₀ = ⊥
    · refine ⟨fun x _ => ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [hbot, Subgroup.coe_bot, Set.mem_singleton_iff] at hy
        rw [hy, one_mul, mul_one]
      · rw [hbot]
        refine CFSG.SectionRank.pRank_le hp1 fun E hE _ => ?_
        rw [le_bot_iff.1 hE, Subgroup.card_bot, pow_one]
        exact hp1.le
    · have : Nontrivial R₀ := (Subgroup.nontrivial_iff_ne_bot R₀).2 hbot
      obtain ⟨Y, hY⟩ := exists_isSupercritical hp2 hR₀p
      have : Y.Characteristic := hY.characteristic
      have : (Y.map R₀.subtype).Normal := normal_map_of_characteristic Y
      obtain ⟨hRp, hRexp, hRcl⟩ := isSupercritical_map hR₀p hY
      have hRrk : Open.pRank p (Y.map R₀.subtype) ≤ 2 :=
        (CFSG.SectionRank.pRank_mono hp1 le_top).trans (hrank p hp.out hp2)
      have hR1 : Y.map R₀.subtype ≠ ⊥ := fun h =>
        hY.ne_bot hR₀p ((Subgroup.map_eq_bot_iff_of_injective _ R₀.subtype_injective).1 h)
      have hG : Open.pRank p (⊤ : Subgroup Γ) = 2 :=
        le_antisymm (hrank p hp.out hp2) (hPrk2.trans (CFSG.SectionRank.pRank_mono hp1 le_top))
      rcases A1c.eq_or_eq_centerOf_of_pRank_eq_two hp2 hp2 rfl hR1 hRp (closure_pow_eq hRexp)
        hRcl hRrk hPp hPΩ hPcl hPrk hirrN hG with hRP | ⟨⟨e⟩, -, -⟩
      · exact (hN (hRP ▸ (inferInstance : (Y.map R₀.subtype).Normal))).elim
      · have hcardR : Nat.card (Y.map R₀.subtype) = p := by
          rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
          simp
        have hcardY : Nat.card Y = p := by
          rw [← hcardR, Subgroup.card_map_of_injective R₀.subtype_injective]
        have hYrk : Open.pRank p Y ≤ 1 := CFSG.SectionRank.pRank_le hp1 fun E hE _ => by
          rw [pow_one, ← hcardY]
          exact Subgroup.card_le_of_le hE
        have hR₀rk : Open.pRank p (⊤ : Subgroup R₀) ≤ 1 := by
          by_contra h
          push Not at h
          have := hY.one_lt_pRank hR₀p h
          omega
        refine ⟨hPc.trans (commutator_le_centralizer_of_isCyclic
          (isCyclic_of_pRank_le_one hp2 hR₀p hR₀rk)), ?_⟩
        rw [← pRank_top_subtype]
        exact hR₀rk
  have hC : P ≤ Subgroup.centralizer (CFSG.fittingSubgroup Γ : Set Γ) := by
    refine CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores fun q => ?_
    have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.1.2
    by_cases hq2 : (q : ℕ) = 2
    · rw [hq2, hO2]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      rw [hy, one_mul, mul_one]
    · by_cases hqp : (q : ℕ) = p
      · rw [hqp]
        exact hB.1
      · exact hA q hq hq2 hqp
  exact ⟨hC, hB.2⟩

theorem exists_component_not_le_centralizer {p : ℕ} [hp : Fact p.Prime] {P : Subgroup Γ}
    (hPp : IsPGroup p P) (hrkP : 2 ≤ Open.pRank p P)
    (hF : P ≤ Subgroup.centralizer (CFSG.fittingSubgroup Γ : Set Γ))
    (hrk : Open.pRank p (CFSG.pCore p Γ) ≤ 1) :
    ∃ L : Subgroup Γ, CFSG.IsComponent L ∧ ¬ P ≤ Subgroup.centralizer (L : Set Γ) := by
  by_contra hall
  push Not at hall
  have hE : CFSG.layer Γ ≤ Subgroup.centralizer (P : Set Γ) := by
    apply sSup_le
    intro K hK
    exact Subgroup.le_centralizer_iff.mp (hall K hK)
  have hF' : CFSG.fittingSubgroup Γ ≤ Subgroup.centralizer (P : Set Γ) :=
    Subgroup.le_centralizer_iff.mp hF
  have hFS : P ≤ Subgroup.centralizer (CFSG.generalizedFitting Γ : Set Γ) :=
    Subgroup.le_centralizer_iff.mpr (sup_le hF' hE)
  have hPF : P ≤ CFSG.fittingSubgroup Γ := by
    have h := ComponentClassification.GeneralizedFitting.centralizer_le_fitting Γ
    rw [← CFSG.generalizedFitting_eq_componentClassification] at h
    exact hFS.trans h
  have hPO : P ≤ CFSG.pCore p Γ := le_pCore_of_le_fittingSubgroup hPp hPF
  have := hrkP.trans (CFSG.SectionRank.pRank_mono hp.out.one_lt hPO)
  omega

end CFSG.Quasithin.P134
