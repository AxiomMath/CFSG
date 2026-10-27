module

public import CFSG.RankThree.PartOne.Q1327C.BDefs
public import CFSG.RankThree.PartOne.KF.ClsPOmegaPlus
public import CFSG.RankThree.PartOne.KF.ClsOmegaMinusUpper
public import CFSG.RankThree.PartOne.KF.ClsPOmegaMinus
public import CFSG.RankThree.PartOne.Q1327C.BBase

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

variable {G : Type} [Group G] [Finite G] {p : ℕ} {X A₀ F : Subgroup G}

theorem false_of_POmegaPlus
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpin : Census3.SpinRankFour) (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .POmegaPlus n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .POmegaPlus n 2 f) : False := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hcl : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .POmegaPlus n 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
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
  · obtain ⟨rfl, rfl⟩ := h42
    have hrank := T123Base.two_le_localRank_of_mulEquiv h e
    have h1 := localRank_statedProj_statedOmega_quadPlus_le (K := K) (by norm_num : 1 ≤ 4) hp
    have h2 := localRank_statedSp_four_le_one (K := K) (by simpa using hK) hp hp5
    omega
  · have hm : Models.LieModel (↥X ⧸ Subgroup.center ↥X) .POmegaPlus n 2 f :=
      ⟨hadm', Or.inl hcl⟩
    have hdvd := T123Base.card_center_dvd_multiplier h hGA hm
    have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥X) := by
      intro r hr hr2 hrZ
      have h2 := (hrZ.trans hdvd).trans (KFU.card_multiplier_pOmegaPlus (n := n) hf1)
      have h3 : r ∣ 2 ^ 2 := by simpa using h2
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h3))
    have hev := T123Base.evenRank_quot_le h hZ
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

theorem bTag_POmegaMinus
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpin : Census3.SpinRankFour) (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .POmegaMinus n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .POmegaMinus n 2 f) : BOutcome p X := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hcl : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .POmegaMinus n 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hcl' := hcl
  obtain ⟨hadm', K, hKf, hKfin, hK, b, c, hbc, ⟨e⟩⟩ := hcl'
  have hn4 : 4 ≤ n := hadm'.2.2
  have hf1 : 1 ≤ f := hadm'.2.1
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [Fintype.card_eq_nat_card]; exact hK)
  by_cases h4 : n = 4
  · subst h4
    by_cases h1 : p ∣ 2 ^ f - 1
    · exact BOutcome.of_Om8 ⟨f, hf1, Or.inl h1, hcl⟩
    by_cases h2 : p ∣ 2 ^ f + 1
    · exact BOutcome.of_Om8 ⟨f, hf1, Or.inr h2, hcl⟩
    exfalso
    have hrank := T123Base.two_le_localRank_of_mulEquiv h e
    have hle := KFU.localRank_statedProj_statedOmegaMinus_four_le_one hbc hp hp2
      (by rw [hK]; exact h1) (by rw [hK]; exact h2)
    omega
  · exfalso
    have hm : Models.LieModel (↥X ⧸ Subgroup.center ↥X) .POmegaMinus n 2 f :=
      ⟨hadm', Or.inl hcl⟩
    have hdvd := T123Base.card_center_dvd_multiplier h hGA hm
    have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥X) := by
      intro r hr hr2 hrZ
      have h2 := (hrZ.trans hdvd).trans (dvd_of_eq (KFU.card_multiplier_pOmegaMinus (n := n) hf1
        (by omega)))
      exact hr.one_lt.ne' (Nat.dvd_one.mp h2)
    have hev := T123Base.evenRank_quot_le h hZ
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

end CFSG.RankThree.PartOne.Q1327C
