module

public import CFSG.RankThree.PartOne.S11d.LowRank
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.KF.ClsPSp
public import CFSG.RankThree.PartOne.KF.ClsPOmegaPlus
public import CFSG.RankThree.PartOne.KF.ClsPOmegaMinus
public import CFSG.RankThree.PartOne.CTP.SpinRankFour

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KFU

section Common

variable {J : Type} [Group J] [Finite J]

theorem card_center_dvd_multiplier_J
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hJ : Group.IsPerfect J) {t : StatedLieTag} {n f : ℕ}
    (hm : Models.LieModel (J ⧸ Subgroup.center J) t n 2 f) :
    Nat.card (Subgroup.center J) ∣ Nat.card (Blueprint.Multiplier.generic t n 2 f ×
      Blueprint.Multiplier.exceptional t n 2 f) := by
  obtain ⟨hperf, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  have hd := card_ker_dvd_card_hopfMultiplier hperf hJ
    (QuotientGroup.mk' (Subgroup.center J)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
  rwa [QuotientGroup.ker_mk', hcard] at hd

theorem localRank_quot_le_evenRank_J
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center J)) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) : localRank r (J ⧸ Subgroup.center J) ≤ evenRank J :=
  (CFSG.RankThree.Classical2.localRank_quotient_le hr hr2 (Subgroup.center J) (hZ r hr hr2)).trans
    (CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2)

theorem evenRank_quot_le_three_J (he : evenRank J ≤ 3)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center J)) :
    evenRank (J ⧸ Subgroup.center J) ≤ 3 :=
  CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le (m := 3) fun _ hr hr2 =>
    (localRank_quot_le_evenRank_J hZ hr hr2).trans he

theorem false_of_four_le_twoLocalOddRank_J (he : evenRank J ≤ 3)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center J)) {Y : Type} [Group Y]
    [Finite Y] (φ : J ⧸ Subgroup.center J ≃* Y) (h4 : 4 ≤ CFSG.twoLocalOddRank Y) : False := by
  have hev := evenRank_quot_le_three_J he hZ
  rw [← Census3.twoLocalOddRank_eq_of_mulEquiv φ,
    ← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h4
  omega

end Common

theorem TCX.highRankFalse_PSp : TCX.HighRankFalse .PSp := by
  intro hGA J _ _ p n f₀ hq hp hp5 hf₀ hZ2 hZ he hM hnl
  have hn4 : 4 ≤ n := by
    simp only [TCX.LowRank, not_le] at hnl
    omega
  have hcl := (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mp hM
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hcl
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := p * f₀)
      (by rw [Fintype.card_eq_nat_card]; exact hK)
  have hm : Models.LieModel (J ⧸ Subgroup.center J) .PSp n 2 (p * f₀) :=
    ⟨hadm, Or.inl ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩⟩
  have hdvd := card_center_dvd_multiplier_J hGA hq.1 hm
  have hZ' : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center J) := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (card_multiplier_psp_dvd_two (n := n) (by omega))
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  obtain ⟨r, hr, hr2, -, hrd⟩ :=
    exists_odd_prime_dvd_two_pow_sub_one_ne_five (by omega : 2 ≤ p * f₀)
  have hrK : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hrd
  have h4 := le_localRank_statedSp_torus (K := K) hr hr2 hrK (by omega : 1 ≤ n)
  have h3 : localRank r (StatedProj (StatedSp n K)) ≤ 3 := by
    rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr]
    exact (localRank_quot_le_evenRank_J hZ' hr hr2).trans he
  omega

theorem TCX.highRankFalse_POmegaPlus : TCX.HighRankFalse .POmegaPlus := by
  intro hGA J _ _ p n f₀ hq hp hp5 hf₀ hZ2 hZ he hM hnl
  have hcl := (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mp hM
  have hcl' := hcl
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hcl'
  have hn4 : 4 ≤ n := hadm.2.2
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  have hf1 : 1 ≤ p * f₀ := by omega
  have hm : Models.LieModel (J ⧸ Subgroup.center J) .POmegaPlus n 2 (p * f₀) :=
    ⟨hadm, Or.inl hcl⟩
  have hdvd := card_center_dvd_multiplier_J hGA hq.1 hm
  have hZ' : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center J) := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (KFU.card_multiplier_pOmegaPlus (n := n) hf1)
    have h3 : r ∣ 2 ^ 2 := by simpa using h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h3))
  let q : TauCeti.PrimePower := ⟨2, p * f₀, Nat.prime_two, hf1⟩
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
  have h4 := CFSG.RankThree.PartOne.CTP.spinRankFour.typeD n q hv
    (fun h' => absurd h'.2.2 (by simp only [q]; omega))
  exact false_of_four_le_twoLocalOddRank_J he hZ' φ h4

theorem TCX.highRankFalse_POmegaMinus : TCX.HighRankFalse .POmegaMinus := by
  intro hGA J _ _ p n f₀ hq hp hp5 hf₀ hZ2 hZ he hM hnl
  have hn5 : 5 ≤ n := by
    simp only [TCX.LowRank, not_le] at hnl
    omega
  have hcl := (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mp hM
  have hcl' := hcl
  obtain ⟨hadm, K, hKf, hKfin, hK, b, c, hbc, ⟨e⟩⟩ := hcl'
  have hn4 : 4 ≤ n := by omega
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  have hf1 : 1 ≤ p * f₀ := by omega
  have hm : Models.LieModel (J ⧸ Subgroup.center J) .POmegaMinus n 2 (p * f₀) :=
    ⟨hadm, Or.inl hcl⟩
  have hdvd := card_center_dvd_multiplier_J hGA hq.1 hm
  have hZ' : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center J) := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (dvd_of_eq (KFU.card_multiplier_pOmegaMinus (n := n) hf1
      (by omega)))
    exact hr.one_lt.ne' (Nat.dvd_one.mp h2)
  let q : TauCeti.PrimePower := ⟨2, p * f₀, Nat.prime_two, hf1⟩
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
  have h4 := CFSG.RankThree.PartOne.CTP.spinRankFour.typeTwistedD n q hv
    (fun h' => absurd h'.1 (by omega))
  exact false_of_four_le_twoLocalOddRank_J he hZ' φ h4

end CFSG.RankThree.PartOne
