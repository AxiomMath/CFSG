module

public import CFSG.RankThree.PartOne.KF.ClassifyTags
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartOne.Census3.OpenCases
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartOne.KF.ClsBasic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank

@[expose] def OmegaEightMinusNotTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K), (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∀ p : ℕ, p.Prime → 5 ≤ p →
      localRank p (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) ≠ 2

namespace KFU

theorem card_multiplier_pOmegaMinus {n f : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n) :
    Nat.card (Blueprint.Multiplier.generic .POmegaMinus n 2 f ×
      Blueprint.Multiplier.exceptional .POmegaMinus n 2 f) = 1 := by
  have hodd : (2 ^ f) ^ n % 2 = 0 := by
    have : 2 ∣ (2 ^ f) ^ n := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
    omega
  have hgen : Blueprint.Multiplier.genericOrders .POmegaMinus n 2 f = (1, 1) := by
    simp only [Blueprint.Multiplier.genericOrders]
    have h1 : Nat.gcd 4 ((2 ^ f) ^ n + 1) = 1 := by
      have h2 : ((2 ^ f) ^ n + 1) % 2 = 1 := by omega
      have : Nat.Coprime 4 ((2 ^ f) ^ n + 1) := by
        have h3 : Nat.Coprime 2 ((2 ^ f) ^ n + 1) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
        simpa using Nat.Coprime.pow_left 2 h3
      exact this
    simp [h1]
  have hexc : Blueprint.Multiplier.exceptionalOrders .POmegaMinus n 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

end KFU

theorem kf123ClassifyTag_POmegaMinus
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpin : Census3.SpinRankFour) (hΩ8 : OmegaEightMinusNotTwo) :
    KF123ClassifyTag .POmegaMinus := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hcl : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  exfalso
  have hcl' := hcl
  obtain ⟨hadm', K, hKf, hKfin, hK, b, c, hbc, ⟨e⟩⟩ := hcl'
  have hn4 : 4 ≤ n := hadm'.2.2
  have hf1 : 1 ≤ f := hadm'.2.1
  have hp := h.prime
  have hp5 := h.five_le
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [Fintype.card_eq_nat_card]; exact hK)
  by_cases h4 : n = 4
  ·
    subst h4
    exact hΩ8 K b c hbc p hp hp5 (h.localRank_eq_two_of_mulEquiv e)
  ·
    have hm : Models.LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 f :=
      ⟨hadm', Or.inl hcl⟩
    have hdvd := h.card_center_dvd_multiplier hGA hm
    have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L) := by
      intro r hr hr2 hrZ
      have h2 := (hrZ.trans hdvd).trans (dvd_of_eq (KFU.card_multiplier_pOmegaMinus (n := n) hf1
        (by omega)))
      exact hr.one_lt.ne' (Nat.dvd_one.mp h2)
    have hev := h.evenRank_quot_le hZ
    let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
    have hv : (TauCeti.LieTypeIndex.twistedD n q).Valid :=
      (TauCeti.LieTypeIndex.valid_iff _).2 ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 hn4,
        by
          rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
          exact id⟩
    have hY : StatedClassicalModel (TauCeti.ValidLieTypeIndex.Group ⟨.twistedD n q, hv⟩)
        .POmegaMinus n q.p q.exponent :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even n q hv rfl
        (MulEquiv.refl _)
    obtain ⟨φ⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hcl hY
    have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.twistedD n q, hv⟩) :=
      Finite.of_equiv _ φ.toEquiv
    have h5 := hSpin.typeTwistedD n q hv (fun h' => h4 h'.1)
    rw [← Census3.twoLocalOddRank_eq_of_mulEquiv φ,
      ← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h5
    omega

end CFSG.RankThree.PartOne
