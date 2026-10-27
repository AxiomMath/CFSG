module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreOrth
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreE6
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreTypeA
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestExc

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGIOneMoreFieldLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1 ∧ p ∣ lab.n) ∨
    (lab.tag = .twD ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.n) ∨
    (lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1 ∧ p ≠ 3 ∧ p ∣ lab.n) ∨
    ((lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.n)

@[expose] def GGIOneMoreFieldCorFourTwoInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
    GGIOneMoreFieldLabel p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I

namespace IOneMore

open TypeA CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem recipeLinear_normAbove_dvd {d m p : ℕ} (hp : p.Prime) (hpN : p ∣ 2 ^ m - 1)
    (hd : 2 ≤ d) (hpd : p ∣ d) {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear d (2 ^ m) Q) :
    LargeEvenRecipeLinear d (2 ^ m) fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hd3 : 3 ≤ d := hp3.trans (Nat.le_of_dvd (by omega) hpd)
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (TypeA.recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    TypeA.congr_recipeEquiv_mem hφ
  rcases (show d = 3 ∨ d = 4 ∨ 5 ≤ d by omega) with h3 | h4 | h5
  · subst h3
    have hlift : GGTorusLift p 0 (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) :=
      TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv 3 K)
        (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (by norm_num)))
    exact ⟨0, hlift, ggINormAbove_of_mulEquiv (TypeA.recipeEquiv 3 K) hI
      (ggINormAbove_dvd hp hp2 hpK hpd (by norm_num) (by norm_num))⟩
  · subst h4
    exfalso
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact hpd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  · have hsec : TypeA.SLHasSections d K := TypeA.slHasSections_of_five_le h5
    exact ⟨d - 2, TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
      (TypeA.ggTorusLift_sub_two hp hpK hd hsec), ggINormAbove_of_mulEquiv
        (TypeA.recipeEquiv d K) hI (ggINormAbove_dvd hp hp2 hpK hpd hd (by omega))⟩

theorem ne_two_of_field {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGIOneMoreFieldLabel p lab) : p ≠ 2 := by
  rintro rfl
  have hn : 1 ≤ lab.n := hlab.1
  have h2 : 2 ∣ 2 ^ lab.n := dvd_pow_self 2 (by omega)
  have hpos : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
  have hm : ¬ 2 ∣ 2 ^ lab.n - 1 := fun hd => by
    have := Nat.dvd_sub h2 hd
    rw [show 2 ^ lab.n - (2 ^ lab.n - 1) = 1 by omega] at this
    norm_num at this
  have hp' : ¬ 2 ∣ 2 ^ lab.n + 1 := fun hd => by
    have := (Nat.dvd_add_right h2).mp hd
    norm_num at this
  rcases h with ⟨-, h1, -⟩ | ⟨-, -, -, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩
  · exact hm h1
  · exact hp' h1
  · exact hm h1
  · exact hm h1

section Certs


theorem recipeOmegaMinus_normAbove {m n p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (hm : 3 ≤ m) (hmo : Odd m) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hlift := ggOrthRestTorusLiftInput_holds.1 K n m p b c hK hm hp hpn hbc
  have hZ := (ggOrthRestCenterInput_holds.1 K n m p b c hK hm hp hpn hbc).1
  refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, m, hlift,
    ggINormAbove_of_iRankLe hp.one_lt (ggIRankLe_of_card_le fun X hXI hX => ?_)⟩
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn hZ hXI hX
  exact hAc ▸ ggOrthRestMinusRankInput_holds K n m p b c hK hm hmo hp hpn hbc A hA

theorem largeEvenLabelAll_normAbove_field {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGIOneMoreFieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I := by
  have hp2 := ne_two_of_field hlab h
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨ht, hpn, hpl, -⟩ | ⟨ht, hl, hle, hpn, -⟩ | ⟨ht, hpn, hp3, -⟩ |
    ⟨ht, hpn, -⟩
  · dsimp only at ht hpn hpl
    subst ht
    have hl1 : 1 ≤ l := hlab.2.1
    exact recipeLinear_normAbove_dvd hp hpn (by omega) hpl hQ
  · dsimp only at ht hl hle hpn
    subst ht
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · have hmo : Odd (l - 1) := by
        obtain ⟨k, hk⟩ := hle
        exact ⟨k - 1, by omega⟩
      exact recipeOmegaMinus_normAbove hp hpn (by omega) hmo hQ
  · dsimp only at ht hpn hp3
    subst ht
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ⟨K, i1, i2, hK, hq, 6, TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq,
      ggINormAbove_of_iRankLe hp.one_lt (ggIRankLe_E6 hp hp2 hp3 hpq)⟩
  · dsimp only at ht hpn
    rcases ht with rfl | rfl | rfl <;> dsimp only [LargeEvenRawDatum] at hQ ⊢ <;>
      obtain ⟨K, i1, i2, hK, hq⟩ := hQ <;>
      have : CharP K 2 := charP_two_of_card hK <;>
      have hpq : p ∣ Nat.card K - 1 := (by rw [hK]; exact hpn)
    · exact ⟨K, i1, i2, hK, hq, _, TableBExc.ggTorusLift_E7 hp hp2 hpq,
        ggINormAbove_of_iRankLe hp.one_lt (IOneRest.ggIRankLe_E7E8 (Or.inl rfl) hp hpq
          (IOneRest.ggExcToralRankInput_E7E8 (Or.inl rfl) hp hp2 hpq))⟩
    · exact ⟨K, i1, i2, hK, hq, _, TableBExc.ggTorusLift_E8 hp hp2 hpq,
        ggINormAbove_of_iRankLe hp.one_lt (IOneRest.ggIRankLe_E7E8 (Or.inr rfl) hp hpq
          (IOneRest.ggExcToralRankInput_E7E8 (Or.inr rfl) hp hp2 hpq))⟩
    · have hT : GGF4ToralRankInput K p := by
        by_cases hp3 : p = 3
        · subst hp3
          exact TableBF4.ggF4ToralRankInput_three hpq
        · have h5 : 5 ≤ p := by
            have := hp.two_le
            rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
            · exact absurd h hp2
            · exact absurd h hp3
            · subst h
              exact absurd hp (by decide)
            · exact h
          exact TableBF4.ggF4ToralRankInput_of_five_le hp h5 hpq
      exact ⟨K, i1, i2, hK, hq, 4, TableBF4.ggTorusLift_F4 hp hp2 hpq,
        ggINormAbove_of_iRankLe hp.one_lt (IOneRest.ggIRankLe_F4 hp hpq hT)⟩

end Certs

end IOneMore

open IOneMore

theorem ggStdSubIOneProperInputOn_field
    (ha₀ : GGLNoncyclicInput) (hC : GGIOneMoreFieldCorFourTwoInput) :
    GGStdSubIOneProperInputOn GGIOneMoreFieldLabel :=
  ggStdSubIOneProperInputOn_of_bstarEqNorm ha₀ fun p lab hp hlab h _ =>
    largeEvenLabelAll_and_iOne (hC p lab hp hlab h) (largeEvenLabelAll_normAbove_field hp hlab h)

end CFSG.StandardType
