module

public import CFSG.RankThree.PartOne.KF.ClsExcE
public import CFSG.RankThree.PartOne.KF.ClsExcE6Data
public import CFSG.RankThree.PartOne.KF.ClsExcE6Two
public import CFSG.RankThree.PartOne.KF.ClsLiftSL2

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
open CFSG.Blueprint (AdjointQuotient UntwistedChevalleyModel TwistedChevalleyModel)
open scoped MatrixGroups

namespace KFU

theorem card_multiplicative_zmod (n : ℕ) : Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod n) ≃ ZMod n), Nat.card_zmod]

theorem card_multiplier_E6 {f : ℕ} :
    Nat.card (Blueprint.Multiplier.generic .E6 0 2 f ×
      Blueprint.Multiplier.exceptional .E6 0 2 f) = Nat.gcd 3 (2 ^ f - 1) := by
  have hgen : Blueprint.Multiplier.genericOrders .E6 0 2 f = (Nat.gcd 3 (2 ^ f - 1), 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .E6 0 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp [card_multiplicative_zmod]

theorem card_multiplier_twistedE6 {f : ℕ} (hf : f ≠ 1) :
    Nat.card (Blueprint.Multiplier.generic .twistedE6 0 2 f ×
      Blueprint.Multiplier.exceptional .twistedE6 0 2 f) = Nat.gcd 3 (2 ^ f + 1) := by
  have hgen : Blueprint.Multiplier.genericOrders .twistedE6 0 2 f = (Nat.gcd 3 (2 ^ f + 1), 1) :=
    rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .twistedE6 0 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp [card_multiplicative_zmod]

theorem card_multiplier_twistedE6_one :
    Nat.card (Blueprint.Multiplier.generic .twistedE6 0 2 1 ×
      Blueprint.Multiplier.exceptional .twistedE6 0 2 1) = 12 := by
  have hgen : Blueprint.Multiplier.genericOrders .twistedE6 0 2 1 = (3, 1) := by
    show (Nat.gcd 3 (2 ^ 1 + 1), 1) = (3, 1)
    norm_num
  have hexc : Blueprint.Multiplier.exceptionalOrders .twistedE6 0 2 1 = (2, 2) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    rfl
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem false_of_commuting_sl2 {G : Type} [Group G] [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Table123Generic p L A₀ F) (hodd : Nat.Coprime 2 (Nat.card (Subgroup.center ↥L)))
    {Y : Type} [Group Y] (ε : ↥L ⧸ Subgroup.center ↥L ≃* Y) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (φ : Fin 4 → SL(2, K) →* Y)
    (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, φ i A * φ j B = φ j B * φ i A) : False := by
  have hπ : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥L)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center ↥L)).ker ≤ Subgroup.center ↥L :=
    (QuotientGroup.ker_mk' _).le
  have hodd' : Nat.Coprime 2 (Nat.card (QuotientGroup.mk' (Subgroup.center ↥L)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact hodd
  obtain ⟨φ', hφ'1, hφ'2⟩ := exists_lift_four_commuting_sl2 hGA hf hK
    (QuotientGroup.mk' (Subgroup.center ↥L)) hπ hker hodd'
    (fun i => ε.symm.toMonoidHom.comp (φ i)) (fun i => ε.symm.injective.comp (hφ i))
    (fun i j hij A B => by simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B])
  have : Fintype K := Fintype.ofFinite K
  have hK2 : Fintype.card K ≠ 2 := by
    rw [← Nat.card_eq_fintype_card, hK]
    have : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have h4 : 4 ≤ CFSG.twoLocalOddRank ↥L :=
    PartTwo.Census.Exceptional.four_le_twoLocalOddRank_of_four_commuting_SL2 (K := K) hK2 φ'
      hφ'1 hφ'2
  have h3 := h.evenRank_le
  rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h3
  omega

end KFU

theorem kf123ClassifyTag_E6
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) : KF123ClassifyTag .E6 := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  have hU : UntwistedChevalleyModel (↥L ⧸ Subgroup.center ↥L) .E6 (2 ^ f) := hch.2
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hU
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  have hq : q.card = 2 ^ f := TauCeti.PrimePower.card_def q
  have hKq : Nat.card K = q.card := by rw [hq]; exact hK
  have hv : (TauCeti.LieTypeIndex.E6 q).Valid := by simp
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).e6 q hv rfl K hKq
  let φ := e.trans b
  have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) := Finite.of_equiv _ φ.toEquiv
  have hm : Models.LieModel (↥L ⧸ Subgroup.center ↥L) .E6 0 2 f :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.E6 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := h.card_center_dvd_multiplier hGA hm
  rw [KFU.card_multiplier_E6] at hdvd
  by_cases hf2 : 2 ≤ f
  · have hodd : Nat.Coprime 2 (Nat.card (Subgroup.center ↥L)) :=
      Nat.Coprime.coprime_dvd_right (hdvd.trans (Nat.gcd_dvd_left 3 _)) (by norm_num)
    obtain ⟨K', hK'f, hK'fin, hK'q, ψ, hψ, hψc⟩ := KFU.exists_four_commuting_SL2_E6 q hv
    exact (KFU.false_of_commuting_sl2 hGA h hodd φ hf2 (hK'q.trans hq) ψ hψ hψc).elim
  · have hf : f = 1 := by omega
    subst hf
    have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L) := by
      intro r hr hr2 hrZ
      have h1 : Nat.card (Subgroup.center ↥L) ∣ 1 := by simpa using hdvd
      exact hr.one_lt.ne' (Nat.dvd_one.mp (hrZ.trans h1))
    exact (false_of_four_le_twoLocalOddRank h hZ φ (hExc.e6 q hv)).elim

theorem kf123ClassifyTag_twistedE6
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) : KF123ClassifyTag .twistedE6 := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  have hU : TwistedChevalleyModel (↥L ⧸ Subgroup.center ↥L) .E6 (2 ^ f) := hch.2
  obtain ⟨K, hKf, hKfin, hK, σ, hσ, ⟨e⟩⟩ := hU
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  have hq : q.card = 2 ^ f := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := by simp
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).twistedE6 q hv rfl K
    (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
  let φ := e.trans b
  have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :=
    Finite.of_equiv _ φ.toEquiv
  have hm : Models.LieModel (↥L ⧸ Subgroup.center ↥L) .twistedE6 0 2 f :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.twistedE6 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := h.card_center_dvd_multiplier hGA hm
  by_cases hf2 : 2 ≤ f
  · rw [KFU.card_multiplier_twistedE6 (by omega)] at hdvd
    have hodd : Nat.Coprime 2 (Nat.card (Subgroup.center ↥L)) :=
      Nat.Coprime.coprime_dvd_right (hdvd.trans (Nat.gcd_dvd_left 3 _)) (by norm_num)
    obtain ⟨K', hK'f, hK'fin, hK'q, ψ, hψ, hψc⟩ := KFU.exists_four_commuting_SL2_twistedE6 q hv
    exact (KFU.false_of_commuting_sl2 hGA h hodd φ hf2 (hK'q.trans hq) ψ hψ hψc).elim
  · have hf : f = 1 := by omega
    subst hf
    rw [KFU.card_multiplier_twistedE6_one] at hdvd
    by_cases h3 : 3 ∣ Nat.card (Subgroup.center ↥L)
    · obtain ⟨K', hK'f, hK'fin, hK'q, ψ, hψ, hψc⟩ :=
        KFU.exists_four_commuting_SL2_twistedE6 q hv
      have hK'2 : Nat.card K' = 2 := by rw [hK'q, hq]; norm_num
      have h4 := KFU.four_le_localRank_three_of_commuting_sl2_two hdvd h3 φ hK'2 ψ hψ hψc
      have h5 := PartTwo.Census.Exceptional.four_le_twoLocalOddRank_of_localRank Nat.prime_three
        (by norm_num) h4
      have h6 := h.evenRank_le
      rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h6
      omega
    · have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L) := by
        intro r hr hr2 hrZ
        have h12 : r ∣ 2 ^ 2 * 3 := by simpa using hrZ.trans hdvd
        rcases (Nat.Prime.dvd_mul hr).1 h12 with h2 | h3'
        · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
        · exact h3 (by rw [(Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3'] at hrZ; exact hrZ)
      exact (false_of_four_le_twoLocalOddRank h hZ φ (hExc.twistedE6 q hv)).elim

end CFSG.RankThree.PartOne
