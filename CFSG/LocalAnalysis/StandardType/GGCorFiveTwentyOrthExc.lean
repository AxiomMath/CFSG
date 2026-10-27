module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted OrthNs

namespace OrthExc

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem center_data_omegaMinus {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.center (OrthRest.RMinus K m b c) = ⊥ ∧
      GGCenterPrime p (OrthRest.RMinus K m b c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbij, hZ⟩ := OrthRest.spinMinus_bij (K := K) (n := m + 1) (by omega) hbc
  have : Finite (spinGroup (quadMinus (m + 1) K b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hbc)
  exact OrthRest.center_data
    ((MulEquiv.ofBijective _ hbij).trans (omegaMinusProjEquiv (m + 1) b c).symm) hZ
    (fun E _ _ π hπ hcen hC =>
      CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_coprime hbc
        (by omega) hπ hcen hC) hp hp2

end OrthExc

@[expose] def GGOrthSignedTorusInput : Prop :=
  (∀ (K : Type) [Field K] [Finite K] [CharP K 2] (m p : ℕ), 5 ≤ m → Odd m → p.Prime →
      p ∣ Nat.card K + 1 → GGTorusSignedEltSC p (OrthRest.RPlus K m)) ∧
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (m p : ℕ) (b c : K), 3 ≤ m →
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → p.Prime →
      (p ∣ Nat.card K - 1 ∨ (Odd m ∧ p ∣ Nat.card K + 1)) →
        GGTorusSignedEltSC p (OrthRest.RMinus K m b c)

namespace OrthExc

theorem ne_two_of_dvd_two_pow_sub_one {n p : ℕ} (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n - 1) : p ≠ 2 := by
  rintro rfl
  have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

theorem recipeOmegaMinus_weylInputsSC (hin : GGOrthSignedTorusInput) {m n p : ℕ} (hp : p.Prime)
    (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n - 1 ∨ (Odd m ∧ p ∣ 2 ^ n + 1)) (hm : 3 ≤ m)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F => Q R I F ∧
      (GGTorusPseudoReflGenSC p R I ∧ GGTorusSchurSC p R I ∧ GGTorusWeylNormInnerSC p R I) := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 ∨ (Odd m ∧ p ∣ Nat.card K + 1) := by
    rw [hK]
    exact hpn
  have hp2 : p ≠ 2 := by
    rcases hpn with h1 | ⟨-, h1⟩
    · exact ne_two_of_dvd_two_pow_sub_one hn h1
    · exact TableBU.ne_two_of_dvd_two_pow_add_one hn h1
  obtain ⟨hZ, hcp⟩ := center_data_omegaMinus (K := K) hp hp2 hm hbc
  have hT := hin.2 K m p b c hm hbc hp hpK
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ,
    ggTorusPseudoReflGenSC_of_signedEltSC hp hp2 (fun _ h => h) hZ hcp hT,
    ggTorusSchurSC_of_signedEltSC hp hp2 (fun _ h => h) hZ hcp hT,
    ggTorusWeylNormInnerSC_of_signedEltSC hp hp2 (fun _ h => h) hZ hcp hT⟩

end OrthExc

open OrthExc

@[expose] def GGOrthSignedLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .twD ∧ 4 ≤ lab.rank ∧
      (p ∣ 2 ^ lab.n - 1 ∨ (Even lab.rank ∧ p ∣ 2 ^ lab.n + 1)))

end CFSG.StandardType

end
