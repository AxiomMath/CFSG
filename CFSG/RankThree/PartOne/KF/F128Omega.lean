module

public import CFSG.RankThree.PartOne.KF.F128OmegaRank
public import CFSG.RankThree.PartOne.KF.ClsPOmegaPlus
public import CFSG.RankThree.PartOne.KF.ClsOmegaMinusQPlus
public import CFSG.RankThree.PartOne.K128.ExclExc

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.KFU

theorem kf128SylTag_POmegaOdd : KF128SylTag .POmegaOdd := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 hkerp hLR2 n f₀ hf₀ hM
  exfalso
  have hadm := statedLieAdmissible_of_lieModel hM
  exact hadm.2.2.2 rfl

theorem kf128SylTag_POmegaPlus
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpin : Census3.SpinRankFour) : KF128SylTag .POmegaPlus := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 hkerp hLR2 n f₀ hf₀ hM
  exfalso
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  have hf1 : 1 ≤ p * f₀ := by omega
  have hcl : StatedClassicalModel T .POmegaPlus n 2 (p * f₀) :=
    statedClassicalModel_of_lieModel_tags (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hM
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := id hcl
  have hn4 : 4 ≤ n := hadm.2.2
  have hm : Models.LieModel T .POmegaPlus n 2 (p * f₀) := ⟨hadm, Or.inl hcl⟩
  have hdvd := card_ker_dvd_multiplier_cls hq π hπ hker hGA hm
  have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card π.ker := by
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
  have h4 := hSpin.typeD n q hv (fun h' => by
    have := h'.2.2
    simp only [q] at this
    omega)
  exact K128.false_of_four_le_quot π hπ hZ he φ h4

theorem kf128SylTag_POmegaMinus
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpin : Census3.SpinRankFour) : KF128SylTag .POmegaMinus := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 hkerp hLR2 n f₀ hf₀ hM α hαp hαinn hLRA hX hF hrk
  exfalso
  have hp2 : p ≠ 2 := by omega
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  have hf1 : 1 ≤ p * f₀ := by omega
  have hcl : StatedClassicalModel T .POmegaMinus n 2 (p * f₀) :=
    statedClassicalModel_of_lieModel_tags (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hM
  obtain ⟨hadm, K, hKf, hKfin, hK, b, c, hbc, ⟨e⟩⟩ := id hcl
  have hn4 : 4 ≤ n := hadm.2.2
  have : CharP K 2 := K128.charP_two_of_card_eq_two_pow hK
  by_cases hn : n = 4
  ·
    subst hn
    have hlr : ∀ r : ℕ, r.Prime →
        localRank r T = localRank r (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) :=
      fun r hr => CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr
    by_cases h1 : p ∣ Nat.card K - 1
    · have hKu : p ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact h1
      have h3 := PartTwo.KFacts.KS21LocalRank.le_localRank_statedOmegaMinus_torus hp hp2 hKu b c
      rw [← hlr p hp] at h3
      exact false_of_three_le_localRank hp hLR2 h3
    · by_cases h2 : p ∣ Nat.card K + 1
      · have h3 := KFU.QPlus.three_le_localRank_statedProj_statedOmegaMinus b c hbc hp hp2 h2
        rw [← hlr p hp] at h3
        exact false_of_three_le_localRank hp hLR2 h3
      · have h4 := pRank_statedProj_statedOmegaMinus_four_le_one hbc hp hp5 h1 h2
        rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e] at hrk
        omega
  ·
    have hm : Models.LieModel T .POmegaMinus n 2 (p * f₀) := ⟨hadm, Or.inl hcl⟩
    have hdvd := card_ker_dvd_multiplier_cls hq π hπ hker hGA hm
    have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card π.ker := by
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
    have h5 := hSpin.typeTwistedD n q hv (fun h' => hn h'.1)
    exact K128.false_of_four_le_quot π hπ hZ he φ h5

end CFSG.RankThree.PartOne
