module

public import CFSG.RankThree.PartOne.KF.F128Syl
public import CFSG.RankThree.PartOne.KF.ClsExcE6

public section

namespace CFSG.RankThree.PartOne.K128

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.Blueprint (AdjointQuotient UntwistedChevalleyModel TwistedChevalleyModel)
open scoped MatrixGroups

theorem false_of_four_le_quot {J T Y : Type} [Group J] [Finite J] [Group T] [Finite T] [Group Y]
    [Finite Y] (π : J →* T) (hπ : Function.Surjective π)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card π.ker) (he : evenRank J ≤ 3)
    (φ : T ≃* Y) (h4 : 4 ≤ CFSG.twoLocalOddRank Y) : False := by
  have eT : evenRank T ≤ 3 :=
    CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le (m := 3) fun r hr hr2 => by
      calc localRank r T = localRank r (J ⧸ π.ker) :=
            (CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
              (QuotientGroup.quotientKerEquivOfSurjective π hπ) hr).symm
        _ ≤ localRank r J :=
            CFSG.RankThree.Classical2.localRank_quotient_le hr hr2 π.ker (hZ r hr hr2)
        _ ≤ evenRank J := CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2
        _ ≤ 3 := he
  rw [← Census3.twoLocalOddRank_eq_of_mulEquiv φ,
    ← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h4
  omega

theorem card_ker_dvd_multiplier {J T : Type} [Group J] [Finite J] [Group T] [Finite T]
    (hq : CFSG.IsQuasisimple J) (π : J →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center J)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {t : StatedLieTag} {n f : ℕ} (hm : Models.LieModel T t n 2 f) :
    Nat.card π.ker ∣ Nat.card (Blueprint.Multiplier.generic t n 2 f ×
      Blueprint.Multiplier.exceptional t n 2 f) := by
  obtain ⟨hperf, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  have hd := card_ker_dvd_card_hopfMultiplier hperf hq.1 π hπ hker
  rwa [hcard] at hd

theorem false_of_commuting_sl2_quot
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {J T Y : Type} [Group J] [Finite J] [Group T] [Finite T] [Group Y] [Finite Y]
    (π : J →* T) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center J)
    (hodd : Nat.Coprime 2 (Nat.card π.ker)) (he : evenRank J ≤ 3) (ε : T ≃* Y)
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (φ : Fin 4 → SL(2, K) →* Y) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, φ i A * φ j B = φ j B * φ i A) : False := by
  obtain ⟨φ', hφ'1, hφ'2⟩ := KFU.exists_lift_four_commuting_sl2 hGA hf hK π hπ hker hodd
    (fun i => ε.symm.toMonoidHom.comp (φ i)) (fun i => ε.symm.injective.comp (hφ i))
    (fun i j hij A B => by simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B])
  have : Fintype K := Fintype.ofFinite K
  have hK2 : Fintype.card K ≠ 2 := by
    rw [← Nat.card_eq_fintype_card, hK]
    have : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have h4 : 4 ≤ CFSG.twoLocalOddRank J :=
    PartTwo.Census.Exceptional.four_le_twoLocalOddRank_of_four_commuting_SL2 (K := K) hK2 φ'
      hφ'1 hφ'2
  rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at he
  omega

set_option linter.unusedSectionVars false


theorem kf128SylTag_E7
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) : KF128SylTag .E7 := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 _ _ n f₀ _ hM
  exfalso
  have hadm := statedLieAdmissible_of_lieModel hM
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ p * f₀ := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hM
  have hU : UntwistedChevalleyModel T .E7 (2 ^ (p * f₀)) := hch.2
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hU
  let q : TauCeti.PrimePower := ⟨2, p * f₀, Nat.prime_two, hf1⟩
  have hKq : Nat.card K = q.card := by rw [TauCeti.PrimePower.card_def]; exact hK
  have hv : (TauCeti.LieTypeIndex.E7 q).Valid :=
    (TauCeti.LieTypeIndex.valid_iff _).2 ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 trivial,
      by
        rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact id⟩
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).e7 q hv rfl K hKq
  let φ := e.trans b
  have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.E7 q, hv⟩) := Finite.of_equiv _ φ.toEquiv
  have hm : Models.LieModel T .E7 0 2 (p * f₀) :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.E7 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := card_ker_dvd_multiplier hq π hπ hker hGA hm
  have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card π.ker := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (dvd_of_eq (KFU.card_multiplier_E7 hf1))
    exact hr.one_lt.ne' (Nat.dvd_one.mp h2)
  exact false_of_four_le_quot π hπ hZ he φ (hExc.e7 q hv)

theorem kf128SylTag_E8
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) : KF128SylTag .E8 := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 _ _ n f₀ _ hM
  exfalso
  have hadm := statedLieAdmissible_of_lieModel hM
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ p * f₀ := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hM
  have hU : UntwistedChevalleyModel T .E8 (2 ^ (p * f₀)) := hch.2
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hU
  let q : TauCeti.PrimePower := ⟨2, p * f₀, Nat.prime_two, hf1⟩
  have hKq : Nat.card K = q.card := by rw [TauCeti.PrimePower.card_def]; exact hK
  have hv : (TauCeti.LieTypeIndex.E8 q).Valid :=
    (TauCeti.LieTypeIndex.valid_iff _).2 ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 trivial,
      by
        rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact id⟩
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).e8 q hv rfl K hKq
  let φ := e.trans b
  have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.E8 q, hv⟩) := Finite.of_equiv _ φ.toEquiv
  have hm : Models.LieModel T .E8 0 2 (p * f₀) :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.E8 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := card_ker_dvd_multiplier hq π hπ hker hGA hm
  have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card π.ker := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (dvd_of_eq (KFU.card_multiplier_E8 (f := p * f₀)))
    exact hr.one_lt.ne' (Nat.dvd_one.mp h2)
  exact false_of_four_le_quot π hπ hZ he φ (hExc.e8 q hv)

theorem kf128SylTag_F4
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) : KF128SylTag .F4 := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 _ _ n f₀ hf₀ hM
  exfalso
  have hadm := statedLieAdmissible_of_lieModel hM
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ p * f₀ := hadm.2.1
  have hfne : p * f₀ ≠ 1 := by
    intro h
    have : p ∣ 1 := ⟨f₀, h.symm⟩
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hM
  have hU : UntwistedChevalleyModel T .F4 (2 ^ (p * f₀)) := hch.2
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hU
  let q : TauCeti.PrimePower := ⟨2, p * f₀, Nat.prime_two, hf1⟩
  have hKq : Nat.card K = q.card := by rw [TauCeti.PrimePower.card_def]; exact hK
  have hv : (TauCeti.LieTypeIndex.F4 q).Valid :=
    (TauCeti.LieTypeIndex.valid_iff _).2 ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 trivial,
      by
        rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact id⟩
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).f4 q hv rfl K hKq
  let φ := e.trans b
  have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.F4 q, hv⟩) := Finite.of_equiv _ φ.toEquiv
  have hm : Models.LieModel T .F4 0 2 (p * f₀) :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.F4 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := card_ker_dvd_multiplier hq π hπ hker hGA hm
  have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card π.ker := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (KFU.card_multiplier_F4 (f := p * f₀))
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  exact false_of_four_le_quot π hπ hZ he φ (hExc.f4 q hv (fun h' => hfne h'.2))

theorem kf128SylTag_E6
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF128SylTag .E6 := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 _ _ n f₀ hf₀ hM
  exfalso
  have hadm := statedLieAdmissible_of_lieModel hM
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ p * f₀ := hadm.2.1
  have hf2 : 2 ≤ p * f₀ := by nlinarith [hp.two_le]
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hM
  have hU : UntwistedChevalleyModel T .E6 (2 ^ (p * f₀)) := hch.2
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hU
  let q : TauCeti.PrimePower := ⟨2, p * f₀, Nat.prime_two, hf1⟩
  have hq' : q.card = 2 ^ (p * f₀) := TauCeti.PrimePower.card_def q
  have hKq : Nat.card K = q.card := by rw [hq']; exact hK
  have hv : (TauCeti.LieTypeIndex.E6 q).Valid := by simp
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).e6 q hv rfl K hKq
  let φ := e.trans b
  have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) := Finite.of_equiv _ φ.toEquiv
  have hm : Models.LieModel T .E6 0 2 (p * f₀) :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.E6 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := card_ker_dvd_multiplier hq π hπ hker hGA hm
  rw [KFU.card_multiplier_E6] at hdvd
  have hodd : Nat.Coprime 2 (Nat.card π.ker) :=
    Nat.Coprime.coprime_dvd_right (hdvd.trans (Nat.gcd_dvd_left 3 _)) (by norm_num)
  obtain ⟨K', hK'f, hK'fin, hK'q, ψ, hψ, hψc⟩ := KFU.exists_four_commuting_SL2_E6 q hv
  exact false_of_commuting_sl2_quot hGA π hπ hker hodd he φ hf2 (hK'q.trans hq') ψ hψ hψc

theorem kf128SylTag_twistedE6
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF128SylTag .twistedE6 := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 _ _ n f₀ hf₀ hM
  exfalso
  have hadm := statedLieAdmissible_of_lieModel hM
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ p * f₀ := hadm.2.1
  have hf2 : 2 ≤ p * f₀ := by nlinarith [hp.two_le]
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hM
  have hU : TwistedChevalleyModel T .E6 (2 ^ (p * f₀)) := hch.2
  obtain ⟨K, hKf, hKfin, hK, σ, hσ, ⟨e⟩⟩ := hU
  let q : TauCeti.PrimePower := ⟨2, p * f₀, Nat.prime_two, hf1⟩
  have hq' : q.card = 2 ^ (p * f₀) := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := by simp
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).twistedE6 q hv rfl K
    (by rw [hK, hq']) σ (fun x => by rw [hq']; exact hσ x)
  let φ := e.trans b
  have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :=
    Finite.of_equiv _ φ.toEquiv
  have hm : Models.LieModel T .twistedE6 0 2 (p * f₀) :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.twistedE6 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := card_ker_dvd_multiplier hq π hπ hker hGA hm
  rw [KFU.card_multiplier_twistedE6 (by omega)] at hdvd
  have hodd : Nat.Coprime 2 (Nat.card π.ker) :=
    Nat.Coprime.coprime_dvd_right (hdvd.trans (Nat.gcd_dvd_left 3 _)) (by norm_num)
  obtain ⟨K', hK'f, hK'fin, hK'q, ψ, hψ, hψc⟩ := KFU.exists_four_commuting_SL2_twistedE6 q hv
  exact false_of_commuting_sl2_quot hGA π hπ hker hodd he φ hf2 (hK'q.trans hq') ψ hψ hψc

end CFSG.RankThree.PartOne.K128
