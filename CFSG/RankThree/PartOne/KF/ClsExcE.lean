module

public import CFSG.RankThree.PartOne.KF.ClassifyTags
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartOne.Census3.OpenCases
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.RankThree.PartOne.KF.ClsBasic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
open CFSG.Blueprint (AdjointQuotient UntwistedChevalleyModel)

@[expose] def KF123ExcF4TwoNoRankTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [Finite (AdjointQuotient .F4 K)], Nat.card K = 2 →
    ∀ p : ℕ, p.Prime → 5 ≤ p → localRank p (AdjointQuotient .F4 K) ≠ 2

theorem chevalleyModel_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (h1 : t ∉ Blueprint.classicalTags) (h2 : t ∉ Blueprint.reeTitsTags) (h3 : t ≠ .twistedB2)
    (h : Blueprint.LieModel X t n 2 f) : Blueprint.ChevalleyExceptionalModel X t 2 f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by revert h1 h2 h3; cases t <;> decide)

theorem false_of_four_le_twoLocalOddRank {G : Type} [Group G] [Finite G] {p : ℕ}
    {L A₀ F : Subgroup G} (h : Table123Generic p L A₀ F)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L)) {Y : Type} [Group Y]
    [Finite Y] (φ : ↥L ⧸ Subgroup.center ↥L ≃* Y) (h4 : 4 ≤ CFSG.twoLocalOddRank Y) : False := by
  have hev := h.evenRank_quot_le hZ
  rw [← Census3.twoLocalOddRank_eq_of_mulEquiv φ,
    ← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h4
  omega

namespace KFU

theorem card_multiplier_E7 {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (Blueprint.Multiplier.generic .E7 0 2 f ×
      Blueprint.Multiplier.exceptional .E7 0 2 f) = 1 := by
  have hodd : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hm : (2 ^ f - 1) % 2 = 1 := by omega
    rw [Nat.gcd_rec, hm]
    rfl
  have hgen : Blueprint.Multiplier.genericOrders .E7 0 2 f = (1, 1) := by
    show (Nat.gcd 2 (2 ^ f - 1), 1) = (1, 1)
    rw [hodd]
  have hexc : Blueprint.Multiplier.exceptionalOrders .E7 0 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem card_multiplier_E8 {f : ℕ} :
    Nat.card (Blueprint.Multiplier.generic .E8 0 2 f ×
      Blueprint.Multiplier.exceptional .E8 0 2 f) = 1 := by
  have hgen : Blueprint.Multiplier.genericOrders .E8 0 2 f = (1, 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .E8 0 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem card_multiplier_F4 {f : ℕ} :
    Nat.card (Blueprint.Multiplier.generic .F4 0 2 f ×
      Blueprint.Multiplier.exceptional .F4 0 2 f) ∣ 2 := by
  have hgen : Blueprint.Multiplier.genericOrders .F4 0 2 f = (1, 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .F4 0 2 f = (2, 1) ∨
      Blueprint.Multiplier.exceptionalOrders .F4 0 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen]
  rcases hexc with h | h <;> rw [h] <;> simp

end KFU


theorem kf123ClassifyTag_E7
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) : KF123ClassifyTag .E7 := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  have hU : UntwistedChevalleyModel (↥L ⧸ Subgroup.center ↥L) .E7 (2 ^ f) := hch.2
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hU
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  have hKq : Nat.card K = q.card := by rw [TauCeti.PrimePower.card_def]; exact hK
  have hv : (TauCeti.LieTypeIndex.E7 q).Valid :=
    (TauCeti.LieTypeIndex.valid_iff _).2 ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 trivial,
      by
        rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact id⟩
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).e7 q hv rfl K hKq
  let φ := e.trans b
  have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.E7 q, hv⟩) := Finite.of_equiv _ φ.toEquiv
  have hm : Models.LieModel (↥L ⧸ Subgroup.center ↥L) .E7 0 2 f :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.E7 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := h.card_center_dvd_multiplier hGA hm
  have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L) := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (dvd_of_eq (KFU.card_multiplier_E7 hf1))
    exact hr.one_lt.ne' (Nat.dvd_one.mp h2)
  exact (false_of_four_le_twoLocalOddRank h hZ φ (hExc.e7 q hv)).elim

theorem kf123ClassifyTag_E8
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) : KF123ClassifyTag .E8 := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  have hU : UntwistedChevalleyModel (↥L ⧸ Subgroup.center ↥L) .E8 (2 ^ f) := hch.2
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hU
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  have hKq : Nat.card K = q.card := by rw [TauCeti.PrimePower.card_def]; exact hK
  have hv : (TauCeti.LieTypeIndex.E8 q).Valid :=
    (TauCeti.LieTypeIndex.valid_iff _).2 ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 trivial,
      by
        rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact id⟩
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).e8 q hv rfl K hKq
  let φ := e.trans b
  have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.E8 q, hv⟩) := Finite.of_equiv _ φ.toEquiv
  have hm : Models.LieModel (↥L ⧸ Subgroup.center ↥L) .E8 0 2 f :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.E8 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := h.card_center_dvd_multiplier hGA hm
  have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L) := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (dvd_of_eq (KFU.card_multiplier_E8 (f := f)))
    exact hr.one_lt.ne' (Nat.dvd_one.mp h2)
  exact (false_of_four_le_twoLocalOddRank h hZ φ (hExc.e8 q hv)).elim

theorem kf123ClassifyTag_F4
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) (hF42 : KF123ExcF4TwoNoRankTwo) :
    KF123ClassifyTag .F4 := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  have hU : UntwistedChevalleyModel (↥L ⧸ Subgroup.center ↥L) .F4 (2 ^ f) := hch.2
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hU
  have hp := h.prime
  have hp5 := h.five_le
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  have hKq : Nat.card K = q.card := by rw [TauCeti.PrimePower.card_def]; exact hK
  have hv : (TauCeti.LieTypeIndex.F4 q).Valid :=
    (TauCeti.LieTypeIndex.valid_iff _).2 ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 trivial,
      by
        rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact id⟩
  by_cases hf : f = 1
  ·
    subst hf
    have : Finite (AdjointQuotient .F4 K) := Finite.of_equiv _ e.toEquiv
    exact (hF42 K (by simpa using hK) p hp hp5 (h.localRank_eq_two_of_mulEquiv e)).elim
  · obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).f4 q hv rfl K hKq
    let φ := e.trans b
    have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.F4 q, hv⟩) := Finite.of_equiv _ φ.toEquiv
    have hm : Models.LieModel (↥L ⧸ Subgroup.center ↥L) .F4 0 2 f :=
      ⟨hadm, Or.inr ⟨rfl, ⟨.F4 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
    have hdvd := h.card_center_dvd_multiplier hGA hm
    have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L) := by
      intro r hr hr2 hrZ
      have h2 := (hrZ.trans hdvd).trans (KFU.card_multiplier_F4 (f := f))
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
    exact (false_of_four_le_twoLocalOddRank h hZ φ
      (hExc.f4 q hv (fun h' => hf h'.2))).elim

end CFSG.RankThree.PartOne
