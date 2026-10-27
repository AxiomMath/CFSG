module

public import CFSG.Quasithin.EmptyFaithful.SBc2SzCore
public import CFSG.Quasithin.Vol2.GoldschmidtCor332Bender
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45SzFix
public import CFSG.RankThree.PartTwo.Sec16.KS16ProofSzFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan.Sz

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def SzBorel : Prop :=
  ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    CFSG.Blueprint.SuzukiModel S 2 f →
    ∀ R : Subgroup S, IsPGroup 2 R → R ≠ ⊥ →
      ∃ T : Sylow 2 S,
        Subgroup.normalizer (R : Set S) ≤
          Subgroup.normalizer ((T : Subgroup S) : Set S) ∧
        Group.IsSolvable ↥(Subgroup.normalizer ((T : Subgroup S) : Set S))

@[expose] def SzOutOdd : Prop :=
  ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    CFSG.Blueprint.SuzukiModel S 2 f →
      Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S))

@[expose] def SzFix : Prop :=
  ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    CFSG.Blueprint.SuzukiModel S 2 f → 3 < f →
    ∀ σ : MulAut S, orderOf σ = 3 →
      Group.IsPerfect ↥(fixedSubgroup σ) ∧
      2 ∣ Nat.card (fixedSubgroup σ) ∧
      ∃ b : ℕ, f = 3 * (2 * b + 1) ∧
        Nat.card (fixedSubgroup σ) =
          (2 ^ (2 * b + 1)) ^ 2 * (2 ^ (2 * b + 1) - 1) * ((2 ^ (2 * b + 1)) ^ 2 + 1)

theorem szBorel_holds : SzBorel := by
  intro S _ _ f hS R hR2 hRne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hRT⟩ := hR2.exists_le_sylow
  obtain ⟨-, -, D, hD, -⟩ := CFSG.Quasithin.SBc2.exists_data hS T
  exact ⟨T, CFSG.Quasithin.H13.Cor332.normalizer_le_of_stronglyEmbedded hD.se hRne hRT,
    CFSG.Quasithin.H13.Cor332.isSolvable_normalizer_of_cyclic T.isPGroup' hD.cyc hD.sup⟩

theorem szOutOdd_holds : SzOutOdd := by
  intro S _ _ f hS
  exact (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} S 2 f hS).1.2.2

theorem szFix_holds : SzFix := by
  intro S _ _ f hS h3f σ hσ
  obtain ⟨b, hfb, -, hcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.SzFix.card_fixed_of_orderOf_three hS hσ
  have hperf : Group.IsPerfect ↥(fixedSubgroup σ) ∧
      2 ∣ Nat.card (fixedSubgroup σ) := by
    obtain ⟨-, a, ha, K, hKF, hKfin, hf, hK, ⟨e⟩⟩ := hS
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hf] at hK; exact hK
    have h3 : 3 < 2 * a + 1 := by rw [hf] at h3f; exact h3f
    have hβo : orderOf (MulAut.congr e σ) = 3 := by
      rw [MulEquiv.orderOf_eq (MulAut.congr e) σ, hσ]
    have hβ3 : (MulAut.congr e σ) ^ 3 = 1 :=
      hβo ▸ pow_orderOf_eq_one (MulAut.congr e σ)
    have hβ1 : MulAut.congr e σ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hβo
      omega
    exact CFSG.RankThree.PartTwo.Sec16.KS1619SzFixProof.isPerfect_and_two_dvd_of_mulEquiv
      (CFSG.RankThree.PartTwo.Sec16.KS1619SzFixProof.fixEquiv e σ)
      (CFSG.RankThree.PartTwo.Sec16.KS1619SzFixProof.fix_perfect_even ha hK' h3 hβ3 hβ1)
  exact ⟨hperf.1, hperf.2, b, hfb, hcard⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan.Sz
