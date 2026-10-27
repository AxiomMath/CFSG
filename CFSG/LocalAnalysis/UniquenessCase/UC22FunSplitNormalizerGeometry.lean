module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitAmbient
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationAction
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSymplecticGeometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitDegreeThreeGeometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitLinearGeometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitUnitaryGeometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalGeometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalAction
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitExceptionalGeometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitF4Geometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSimplyLacedGeometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitTwistedE6Geometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitExceptionalAction
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain
public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieE
public import CFSG.ClassicalInvolution.Asc77.WP3L54Thm54
public import CFSG.ClassicalInvolution.Q3.Q3T6FaField
public import CFSG.ClassicalInvolution.RouteD.TriageP1Rows
public import CFSG.GH74.GLS.IVK.Lifted.GroupAux
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Prop46d
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.After
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_7
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129b
public import CFSG.LocalAnalysis.ComponentInitial.FixedLayerNormalizes
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitLinearInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.Blueprint CFSG.ClassicalInvolution.Generic
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ComponentClassification.AS81.Sec2


theorem centralizingLayer_funSet_rankOne_or_degree_three_remaining
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) (ht : t ≠ .PSp)
    (hnotThree : ¬ ((t = .PSL ∨ t = .PSU) ∧ n = 3))
    (hnotLinear : t ≠ .PSL)
    (hnotUnitary : t ≠ .PSU)
    (hnotG2D4 : t ≠ .G2 ∧ t ≠ .trialityD4)
    (hnotSmallOrth : ¬ ((t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4)))
    (hnotOrth : t ≠ .POmegaOdd ∧ t ≠ .POmegaPlus ∧ t ≠ .POmegaMinus)
    (hnotF4 : t ≠ .F4)
    (hnotSimplyLaced : t ≠ .E6 ∧ t ≠ .E7 ∧ t ≠ .E8) :
    let Ω := {J : Subgroup X | IsFundamentalOver (p ^ e) J}
    let Γ := {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      J ≠ K ∧ x ∈ J}
    let A := centralizingLayer Ω Γ
    A = K ∨ LieModel (A ⧸ center A) .PSL 3 p e ∨
      LieModel (A ⧸ center A) .PSU 3 p e := by
  have htw : t = .twistedE6 := by
    cases t <;> first
      | rfl
      | exact (hnotLinear rfl).elim
      | exact (hnotUnitary rfl).elim
      | exact (ht rfl).elim
      | exact (hnotOrth.1 rfl).elim
      | exact (hnotOrth.2.1 rfl).elim
      | exact (hnotOrth.2.2 rfl).elim
      | exact (hnotG2D4.1 rfl).elim
      | exact (hnotF4 rfl).elim
      | exact (hnotSimplyLaced.1 rfl).elim
      | exact (hnotSimplyLaced.2.1 rfl).elim
      | exact (hnotSimplyLaced.2.2 rfl).elim
      | exact (hnotG2D4.2 rfl).elim
      | exact (hRee rfl).elim
      | exact (hp2 hadm.2.2.2.1).elim
  subst t
  have hn : n = 0 := hadm.2.2
  subst n
  let : Fact p.Prime := ⟨hp⟩
  exact Or.inl (centralizingLayer_funSet_eq_of_twistedE6 hp2 hadm hX P hK)

theorem centralizingLayer_funSet_rankOne_or_degree_three_nonpsp
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) (ht : t ≠ .PSp) :
    let Ω := {J : Subgroup X | IsFundamentalOver (p ^ e) J}
    let Γ := {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      J ≠ K ∧ x ∈ J}
    let A := centralizingLayer Ω Γ
    A = K ∨ LieModel (A ⧸ center A) .PSL 3 p e ∨
      LieModel (A ⧸ center A) .PSU 3 p e := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hthree : (t = .PSL ∨ t = .PSU) ∧ n = 3
  · obtain ⟨htt, rfl⟩ := hthree
    have hmodel := lieModel_centralizingLayer_quotient_of_degree_three hp2 htt hadm hX P hK
    rcases htt with rfl | rfl
    · exact Or.inr (Or.inl hmodel)
    · exact Or.inr (Or.inr hmodel)
  · by_cases hlinear : t = .PSL
    · subst t
      by_cases hnEven : Even n
      · obtain ⟨d, hd⟩ := hnEven
        have hn2 : n ≠ 2 := fun h => hA1 ⟨rfl, h⟩
        have hd2 : 2 ≤ d := by have := hadm.2.2.1; omega
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 1 := ⟨d - 1, by omega⟩
        have hn : n = 2 * m + 1 + 1 := by omega
        rw [hn] at hadm hX
        exact Or.inl (centralizingLayer_funSet_eq_of_psl_even hp2 (by omega : 1 ≤ m) hadm hX P hK)
      · have hnOdd : Odd n := (Nat.even_or_odd n).resolve_left hnEven
        obtain ⟨d, hd⟩ := hnOdd
        have hn3 : n ≠ 3 := fun h => hthree ⟨Or.inl rfl, h⟩
        have hd2 : 2 ≤ d := by have := hadm.2.2.1; omega
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 1 := ⟨d - 1, by omega⟩
        have hn : n = 2 * m + 1 + 1 + 1 := by omega
        rw [hn] at hadm hX
        exact Or.inr (Or.inl (lieModel_centralizingLayer_quotient_of_psl_odd
          hp2 (by omega : 1 ≤ m) hadm hX P hK))
    · by_cases hunitary : t = .PSU
      · subst t
        by_cases hnEven : Even n
        · obtain ⟨d, hd⟩ := hnEven
          have hd2 : 2 ≤ d := by have := hadm.2.2.1; omega
          obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 1 := ⟨d - 1, by omega⟩
          have hn : n = 2 * m + 1 + 1 := by omega
          rw [hn] at hadm hX
          exact Or.inl (centralizingLayer_funSet_eq_of_psu_even hp2 (by omega : 1 ≤ m) hadm hX P hK)
        · have hnOdd : Odd n := (Nat.even_or_odd n).resolve_left hnEven
          obtain ⟨d, hd⟩ := hnOdd
          have hn3 : n ≠ 3 := fun h => hthree ⟨Or.inr rfl, h⟩
          have hd2 : 2 ≤ d := by have := hadm.2.2.1; omega
          obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 1 := ⟨d - 1, by omega⟩
          have hn : n = 2 * m + 1 + 1 + 1 := by omega
          rw [hn] at hadm hX
          exact Or.inr (Or.inr (lieModel_centralizingLayer_quotient_of_psu_odd
            hp2 (by omega : 1 ≤ m) hadm hX P hK))
      · by_cases hg2d4 : t = .G2 ∨ t = .trialityD4
        · exact Or.inl (centralizingLayer_funSet_eq_of_g2d4 hp2 hadm hX hg2d4 P hK)
        · by_cases hsmall : (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4)
          · exact Or.inl (centralizingLayer_funSet_eq_of_small_orthogonal hp2 hadm hX hsmall P hK)
          · by_cases horth : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus
            · exact Or.inl (centralizingLayer_funSet_eq_of_orthogonal hp2 horth hadm hX P hK)
            · by_cases hf4 : t = .F4
              · subst t
                have hn : n = 0 := hadm.2.2
                subst n
                exact Or.inl (centralizingLayer_funSet_eq_of_f4 hp2 hadm hX P hK)
              · by_cases hE : t = .E6 ∨ t = .E7 ∨ t = .E8
                · rcases hE with rfl | rfl | rfl
                  all_goals
                    have hn : n = 0 := hadm.2.2
                    subst n
                  · exact Or.inl (centralizingLayer_funSet_eq_of_e6 hp2 hadm hX P hK)
                  · exact Or.inl (centralizingLayer_funSet_eq_of_e7 hp2 hadm hX P hK)
                  · exact Or.inl (centralizingLayer_funSet_eq_of_e8 hp2 hadm hX P hK)
                · exact centralizingLayer_funSet_rankOne_or_degree_three_remaining
                    hp hp2 hadm hX hA1 hRee P hK ht hthree hlinear hunitary
                    (by simpa only [not_or] using hg2d4) hsmall (by simpa only [not_or] using horth) hf4
                    (by simpa only [not_or] using hE)

theorem centralizingLayer_funSet_rankOne_or_degree_three
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    let Ω := {J : Subgroup X | IsFundamentalOver (p ^ e) J}
    let Γ := {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      J ≠ K ∧ x ∈ J}
    let A := centralizingLayer Ω Γ
    A = K ∨ LieModel (A ⧸ center A) .PSL 3 p e ∨
      LieModel (A ⧸ center A) .PSU 3 p e := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases ht : t = .PSp
  · subst t
    exact Or.inl (centralizingLayer_funSet_eq_of_psp hp2 hadm hX P hK)
  · exact centralizingLayer_funSet_rankOne_or_degree_three_nonpsp
      hp hp2 hadm hX hA1 hRee P hK ht

theorem funSet_action_eq_bot_of_ncard_le_four
    {X : Type} [Group X] [Finite X]
    (Δ : Set (Subgroup X)) (B : Subgroup X)
    (hB : B ≤ conjSetStab Δ)
    (hBo : Odd (Nat.card B)) (hB3 : ¬ 3 ∣ Nat.card B)
    (hΔ4 : Δ.ncard ≤ 4) :
    (B.subgroupOf (conjSetStab Δ)).map
      (conjPermHom (le_refl (conjSetStab Δ))) = ⊥ := by
  let T := conjSetStab Δ
  let ρ : T →* Equiv.Perm Δ := conjPermHom (le_refl T)
  let H : Subgroup (Equiv.Perm Δ) := (B.subgroupOf T).map ρ
  have hHcard : Nat.card H ∣ Nat.card (Equiv.Perm Δ) :=
    Subgroup.card_subgroup_dvd_card H
  rw [Nat.card_perm] at hHcard
  have hΔcard : Nat.card Δ ≤ 4 := by
    rw [Nat.card_coe_set_eq]
    exact hΔ4
  have hfac : (Nat.card Δ).factorial ∣ Nat.factorial 4 :=
    Nat.factorial_dvd_factorial hΔcard
  have h24 : Nat.card H ∣ 24 := by
    have h := hHcard.trans hfac
    rw [show Nat.factorial 4 = 24 by norm_num] at h
    exact h
  have hmapdvd : Nat.card H ∣ Nat.card (B.subgroupOf T) := by
    simpa [H, ρ] using Subgroup.card_map_dvd (B.subgroupOf T) ρ
  have hBcard : Nat.card (B.subgroupOf T) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  have hHodd : Odd (Nat.card H) :=
    hBo.of_dvd_nat (hmapdvd.trans (by rw [hBcard]))
  have hH3 : ¬ 3 ∣ Nat.card H := by
    intro h3
    exact hB3 (h3.trans (hmapdvd.trans (by rw [hBcard])))
  have hHone : Nat.card H = 1 := by
    have hcop2 : Nat.Coprime (Nat.card H) (2 ^ 3) :=
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hHodd)
    have hcop3 : Nat.Coprime (Nat.card H) 3 :=
      ((Nat.prime_three.coprime_iff_not_dvd).mpr hH3).symm
    have hcop : Nat.Coprime (Nat.card H) 24 := by
      have h := Nat.Coprime.mul_right hcop2 hcop3
      norm_num at h ⊢
      exact h
    exact Nat.Coprime.eq_one_of_dvd hcop h24
  change H = ⊥
  exact Subgroup.card_eq_one.mp hHone

theorem funSet_action_twoKernel_quotient_of_four_lt_remaining
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X))
    (hnotTwo : ¬ FunTwoType t n)
    (hlarge : 4 < (F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)).ncard)
    (ht : t ≠ .PSp)
    (hnotThree : ¬ ((t = .PSL ∨ t = .PSU) ∧ n = 3))
    (hnotLinear : t ≠ .PSL)
    (hnotUnitary : t ≠ .PSU)
    (hnotF4 : t ≠ .F4)
    (hnotE6 : t ≠ .E6)
    (hnotTwistedE6 : t ≠ .twistedE6)
    (hnotOrthogonal : t ≠ .POmegaOdd ∧ t ≠ .POmegaPlus ∧ t ≠ .POmegaMinus) :
    let Δ := F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)
    let ρ := conjPermHom (le_refl (conjSetStab Δ))
    (∃ (m : ℕ) (N : Subgroup ρ.range) (_ : N.Normal),
      IsPGroup 2 N ∧ Nonempty (ρ.range ⧸ N ≃* Equiv.Perm (Fin m))) ∨
      (∃ (N : Subgroup ρ.range) (_ : N.Normal),
        IsPGroup 2 N ∧ IsSimpleGroup (ρ.range ⧸ N) ∧ Nat.card (ρ.range ⧸ N) = 168) := by
  have hex : t = .E7 ∨ t = .E8 := by
    cases t <;> first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | exact (hnotLinear rfl).elim
      | exact (hnotUnitary rfl).elim
      | exact (ht rfl).elim
      | exact (hnotOrthogonal.1 rfl).elim
      | exact (hnotOrthogonal.2.1 rfl).elim
      | exact (hnotOrthogonal.2.2 rfl).elim
      | exact (hnotF4 rfl).elim
      | exact (hnotE6 rfl).elim
      | exact (hnotTwistedE6 rfl).elim
      | exact (hRee rfl).elim
      | exact (hnotTwo trivial).elim
      | exact (hp2 hadm.2.2.2.1).elim
  exact funSet_action_twoKernel_quotient_of_four_lt_exceptional
    hp hp2 hex hadm hX hA1 hRee P hK hnotTwo hlarge

theorem funSet_action_twoKernel_quotient_of_four_lt_nonpsp
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X))
    (hnotTwo : ¬ FunTwoType t n)
    (hlarge : 4 < (F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)).ncard)
    (ht : t ≠ .PSp) :
    let Δ := F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)
    let ρ := conjPermHom (le_refl (conjSetStab Δ))
    (∃ (m : ℕ) (N : Subgroup ρ.range) (_ : N.Normal),
      IsPGroup 2 N ∧ Nonempty (ρ.range ⧸ N ≃* Equiv.Perm (Fin m))) ∨
      (∃ (N : Subgroup ρ.range) (_ : N.Normal),
        IsPGroup 2 N ∧ IsSimpleGroup (ρ.range ⧸ N) ∧ Nat.card (ρ.range ⧸ N) = 168) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hthree : (t = .PSL ∨ t = .PSU) ∧ n = 3
  · obtain ⟨htt, rfl⟩ := hthree
    have hsingle := funSet_eq_singleton_of_degree_three hp2 htt hadm hX P hK
    rw [hsingle, Set.ncard_singleton] at hlarge
    omega
  · by_cases hlinear : t = .PSL
    · subst t
      by_cases hnEven : Even n
      · obtain ⟨d, hd⟩ := hnEven
        have hn2 : n ≠ 2 := fun h => hA1 ⟨rfl, h⟩
        have hd2 : 2 ≤ d := by have := hadm.2.2.1; omega
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 1 := ⟨d - 1, by omega⟩
        have hn : n = 2 * m + 1 + 1 := by omega
        rw [hn] at hadm hX
        obtain ⟨eρ⟩ := nonempty_equiv_perm_funSet_psl_even hp2 (by omega : 1 ≤ m) hadm hX P
        exact Or.inl ⟨m + 1, ⊥, inferInstance, IsPGroup.of_bot,
          ⟨QuotientGroup.quotientBot.trans eρ⟩⟩
      · have hnOdd : Odd n := (Nat.even_or_odd n).resolve_left hnEven
        obtain ⟨d, hd⟩ := hnOdd
        have hn3 : n ≠ 3 := fun h => hthree ⟨Or.inl rfl, h⟩
        have hd2 : 2 ≤ d := by have := hadm.2.2.1; omega
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 1 := ⟨d - 1, by omega⟩
        have hn : n = 2 * m + 1 + 1 + 1 := by omega
        rw [hn] at hadm hX
        obtain ⟨eρ⟩ := nonempty_equiv_perm_funSet_psl_odd hp2 (by omega : 1 ≤ m) hadm hX P
        exact Or.inl ⟨m + 1, ⊥, inferInstance, IsPGroup.of_bot,
          ⟨QuotientGroup.quotientBot.trans eρ⟩⟩
    · by_cases hunitary : t = .PSU
      · subst t
        by_cases hnEven : Even n
        · obtain ⟨d, hd⟩ := hnEven
          have hd2 : 2 ≤ d := by have := hadm.2.2.1; omega
          obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 1 := ⟨d - 1, by omega⟩
          have hn : n = 2 * m + 1 + 1 := by omega
          rw [hn] at hadm hX
          obtain ⟨eρ⟩ := nonempty_equiv_perm_funSet_psu_even hp2 (by omega : 1 ≤ m) hadm hX P
          exact Or.inl ⟨m + 1, ⊥, inferInstance, IsPGroup.of_bot,
            ⟨QuotientGroup.quotientBot.trans eρ⟩⟩
        · have hnOdd : Odd n := (Nat.even_or_odd n).resolve_left hnEven
          obtain ⟨d, hd⟩ := hnOdd
          have hn3 : n ≠ 3 := fun h => hthree ⟨Or.inr rfl, h⟩
          have hd2 : 2 ≤ d := by have := hadm.2.2.1; omega
          obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 1 := ⟨d - 1, by omega⟩
          have hn : n = 2 * m + 1 + 1 + 1 := by omega
          rw [hn] at hadm hX
          obtain ⟨eρ⟩ := nonempty_equiv_perm_funSet_psu_odd hp2 (by omega : 1 ≤ m) hadm hX P
          exact Or.inl ⟨m + 1, ⊥, inferInstance, IsPGroup.of_bot,
            ⟨QuotientGroup.quotientBot.trans eρ⟩⟩
      · by_cases hf4 : t = .F4
        · subst t
          have hn : n = 0 := hadm.2.2
          subst n
          have hsmall := ncard_funSet_le_four_of_f4 hp2 hadm hX P
          omega
        · by_cases he6 : t = .E6
          · subst t
            have hn : n = 0 := hadm.2.2
            subst n
            have hsmall := ncard_funSet_le_four_of_e6 hp2 hadm hX P hK
            omega
          · by_cases htw : t = .twistedE6
            · subst t
              have hn : n = 0 := hadm.2.2
              subst n
              have hsmall := ncard_funSet_le_four_of_twistedE6 hp2 hadm hX P hK
              omega
            · by_cases horth : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus
              · exact funSet_action_twoKernel_quotient_of_four_lt_orthogonal
                  hp hp2 horth hadm hX hA1 hRee P hK hnotTwo hlarge
              · exact funSet_action_twoKernel_quotient_of_four_lt_remaining
                  hp hp2 hadm hX hA1 hRee P hK hnotTwo hlarge ht hthree hlinear hunitary hf4 he6 htw
                  (by simpa only [not_or] using horth)

theorem funSet_action_twoKernel_quotient_of_four_lt
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X))
    (hnotTwo : ¬ FunTwoType t n)
    (hlarge : 4 < (F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)).ncard) :
    let Δ := F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)
    let ρ := conjPermHom (le_refl (conjSetStab Δ))
    (∃ (m : ℕ) (N : Subgroup ρ.range) (_ : N.Normal),
      IsPGroup 2 N ∧ Nonempty (ρ.range ⧸ N ≃* Equiv.Perm (Fin m))) ∨
      (∃ (N : Subgroup ρ.range) (_ : N.Normal),
        IsPGroup 2 N ∧ IsSimpleGroup (ρ.range ⧸ N) ∧ Nat.card (ρ.range ⧸ N) = 168) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases ht : t = .PSp
  · subst t
    obtain ⟨eρ⟩ := nonempty_equiv_perm_funSet_psp hp2 hadm hX P
    exact Or.inl ⟨n, ⊥, inferInstance, IsPGroup.of_bot,
      ⟨QuotientGroup.quotientBot.trans eρ⟩⟩
  · exact funSet_action_twoKernel_quotient_of_four_lt_nonpsp
      hp hp2 hadm hX hA1 hRee P hK hnotTwo hlarge ht

end CFSG.LocalAnalysis.UniquenessCase.UC22
