module

public import CFSG.RankThree.PartOne.KF.ClassifyTags
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.RankThree.PartOne.Census3.OpenCases
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KFU

namespace KFU

theorem card_multiplier_pOmegaPlus {n f : ℕ} (hf : 1 ≤ f) :
    Nat.card (Blueprint.Multiplier.generic .POmegaPlus n 2 f ×
      Blueprint.Multiplier.exceptional .POmegaPlus n 2 f) ∣ 4 := by
  have hq : Even (2 ^ f) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hgen : Blueprint.Multiplier.genericOrders .POmegaPlus n 2 f = (1, 1) := by
    simp [Blueprint.Multiplier.genericOrders, hq]
  have hexc : Blueprint.Multiplier.exceptionalOrders .POmegaPlus n 2 f = (2, 2) ∨
      Blueprint.Multiplier.exceptionalOrders .POmegaPlus n 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen]
  rcases hexc with h | h <;> rw [h] <;> simp

end KFU

theorem kf123ClassifyTag_POmegaPlus
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpin : Census3.SpinRankFour) : KF123ClassifyTag .POmegaPlus := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hcl : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus n 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  exfalso
  have hcl' := hcl
  obtain ⟨hadm', K, hKf, hKfin, hK, ⟨e⟩⟩ := hcl'
  have hn4 : 4 ≤ n := hadm'.2.2
  have hf1 : 1 ≤ f := hadm'.2.1
  have hp := h.prime
  have hp5 := h.five_le
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [Fintype.card_eq_nat_card]; exact hK)
  by_cases h42 : n = 4 ∧ f = 1
  ·
    obtain ⟨rfl, rfl⟩ := h42
    have hrank := h.localRank_eq_two_of_mulEquiv e
    have h1 := localRank_statedProj_statedOmega_quadPlus_le (K := K) (by norm_num : 1 ≤ 4) hp
    have h2 := localRank_statedSp_four_le_one (K := K) (by simpa using hK) hp hp5
    omega
  ·
    have hm : Models.LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus n 2 f := ⟨hadm', Or.inl hcl⟩
    have hdvd := h.card_center_dvd_multiplier hGA hm
    have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L) := by
      intro r hr hr2 hrZ
      have h2 := (hrZ.trans hdvd).trans (KFU.card_multiplier_pOmegaPlus (n := n) hf1)
      have h3 : r ∣ 2 ^ 2 := by simpa using h2
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h3))
    have hev := h.evenRank_quot_le hZ
    let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
    have hv : (TauCeti.LieTypeIndex.D n q).Valid :=
      (TauCeti.LieTypeIndex.valid_iff _).2 ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 hn4,
        by
          rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
          exact id⟩
    have hY : StatedClassicalModel (TauCeti.ValidLieTypeIndex.Group ⟨.D n q, hv⟩) .POmegaPlus n
        q.p q.exponent :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even n q hv rfl (MulEquiv.refl _)
    obtain ⟨φ⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hcl hY
    have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.D n q, hv⟩) := Finite.of_equiv _ φ.toEquiv
    have h4 := hSpin.typeD n q hv (fun h' => h42 ⟨h'.1, h'.2.2⟩)
    rw [← Census3.twoLocalOddRank_eq_of_mulEquiv φ,
      ← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h4
    omega

end CFSG.RankThree.PartOne
