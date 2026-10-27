module

public import CFSG.RankThree.PartOne.Q1327C.BDefs
public import CFSG.RankThree.PartOne.Q1327C.BNoCube
public import CFSG.RankThree.PartOne.KF.ClsExcE6
public import CFSG.RankThree.PartOne.KF.ClsSz
public import CFSG.RankThree.PartOne.Q1327C.BBase
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
open CFSG.Blueprint (AdjointQuotient UntwistedChevalleyModel TwistedChevalleyModel)
open CFSG.RankThree.PartOne CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {G : Type} [Group G] [Finite G] {p : ℕ} {X A₀ F : Subgroup G}

theorem false_of_four_le_twoLocalOddRank_B (h : Q1327.T123Base p X A₀ F)
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥X)) {Y : Type} [Group Y]
    [Finite Y] (φ : ↥X ⧸ Subgroup.center ↥X ≃* Y) (h4 : 4 ≤ CFSG.twoLocalOddRank Y) : False := by
  have hev := T123Base.evenRank_quot_le h hZ
  rw [← Census3.twoLocalOddRank_eq_of_mulEquiv φ,
    ← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h4
  omega

theorem not_dvd_two_pow_of_five_le {f : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ∣ 2 ^ f := by
  intro hd
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
  omega

theorem false_of_G2
    (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .G2 n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .G2 n 2 f) : False := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := (show n = 0 ∧ 3 ≤ 2 ^ f from hadm.2.2).1
  subst hn0
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hch
  have hC : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  let e : (↥X ⧸ Subgroup.center ↥X) ≃* adjointGroup .G2 K :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot)
  have hpq : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_two_pow_of_five_le h.prime h.five_le
  refine false_of_pow_three_G2_five K h.prime h.five_le hpq
    (E := (bar X F).map (e : (↥X ⧸ Subgroup.center ↥X) →* _)) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    change (e x) ^ p = 1
    rw [← map_pow, barF_exp h x hx, map_one]
  · rw [← Nat.card_congr (e.subgroupMap (bar X F)).toEquiv]
    exact barF_card h

theorem false_of_trialityD4
    (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .trialityD4 n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .trialityD4 n 2 f) : False := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  exact false_of_pow_three_triality_five hch h.prime h.five_le (E := bar X F) (barF_exp h)
    (barF_card h)

theorem false_of_twistedF4
    (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .twistedF4 n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .twistedF4 n 2 f) : False := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hR : Blueprint.ReeTitsModel (↥X ⧸ Subgroup.center ↥X) .twistedF4 2 f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hR⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hR
    · exact absurd ht (by decide)
  exact false_of_pow_three_ree_five hR h.prime h.five_le (E := bar X F) (barF_exp h)
    (barF_card h)

theorem false_of_twistedB2 (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .twistedB2 n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .twistedB2 n 2 f) : False := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hS : Blueprint.SuzukiModel (↥X ⧸ Subgroup.center ↥X) 2 f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hS
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := hS
  let e' : (↥X ⧸ Subgroup.center ↥X) ≃* Sz a :=
    e.trans ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  have : Finite (Sz a) := Finite.of_equiv _ e'.toEquiv
  have hrank := T123Base.two_le_localRank_of_mulEquiv h e'
  have hle := KFU.localRank_le_one_of_fusionBenderBorel (bender_suzuki_borel_full a ha) h.prime
    (by have := h.five_le; omega)
  omega

theorem not_pow_three_dvd_card_titsD (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ^ 3 ∣ 17971200 := by
  intro h
  have e : (17971200 : ℕ) = 2 ^ 11 * (3 ^ 3 * (5 ^ 2 * 13)) := by norm_num
  rw [e] at h
  have hpd : p ∣ 2 ^ 11 * (3 ^ 3 * (5 ^ 2 * 13)) := (dvd_pow_self p three_ne_zero).trans h
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
    omega
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)
      omega
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h3)
        norm_num at h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 h3
        norm_num at h

theorem false_of_Tits
    (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .Tits n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .Tits n 2 f) : False := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hR : Blueprint.ReeTitsModel (↥X ⧸ Subgroup.center ↥X) .Tits 2 f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hR⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hR
    · exact absurd ht (by decide)
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv (↥X ⧸ Subgroup.center ↥X) 2 f hR
  have hd := pow_three_dvd_card_quot h
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD] at hd
  exact not_pow_three_dvd_card_titsD h.prime h.five_le hd

theorem not_pow_three_dvd_ordF4_two (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 3 ∣ CFSG.Open.ordF4 2 := by
  intro h
  have e : CFSG.Open.ordF4 2 = 2 ^ 24 * (3 ^ 6 * (5 ^ 2 * (7 ^ 2 * (13 * 17)))) := by
    simp [CFSG.Open.ordF4]
  rw [e] at h
  have hpd : p ∣ 2 ^ 24 * (3 ^ 6 * (5 ^ 2 * (7 ^ 2 * (13 * 17)))) :=
    (dvd_pow_self p three_ne_zero).trans h
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
    omega
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)
      omega
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h3)
        norm_num at h
      · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
        · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1
            (hp.dvd_of_dvd_pow h4)
          norm_num at h
        · rcases (Nat.Prime.dvd_mul hp).1 h4 with h5 | h5
          · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 h5
            norm_num at h
          · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).1 h5
            norm_num at h

theorem false_of_E7
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .E7 n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .E7 n 2 f) : False := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  have hU : UntwistedChevalleyModel (↥X ⧸ Subgroup.center ↥X) .E7 (2 ^ f) := hch.2
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
  have hm : Models.LieModel (↥X ⧸ Subgroup.center ↥X) .E7 0 2 f :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.E7 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := T123Base.card_center_dvd_multiplier h hGA hm
  have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥X) := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (dvd_of_eq (KFU.card_multiplier_E7 hf1))
    exact hr.one_lt.ne' (Nat.dvd_one.mp h2)
  exact false_of_four_le_twoLocalOddRank_B h hZ φ (hExc.e7 q hv)

theorem false_of_E8
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .E8 n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .E8 n 2 f) : False := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  have hU : UntwistedChevalleyModel (↥X ⧸ Subgroup.center ↥X) .E8 (2 ^ f) := hch.2
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
  have hm : Models.LieModel (↥X ⧸ Subgroup.center ↥X) .E8 0 2 f :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.E8 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := T123Base.card_center_dvd_multiplier h hGA hm
  have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥X) := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (dvd_of_eq (KFU.card_multiplier_E8 (f := f)))
    exact hr.one_lt.ne' (Nat.dvd_one.mp h2)
  exact false_of_four_le_twoLocalOddRank_B h hZ φ (hExc.e8 q hv)

theorem false_of_F4
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .F4 n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .F4 n 2 f) : False := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  have hU : UntwistedChevalleyModel (↥X ⧸ Subgroup.center ↥X) .F4 (2 ^ f) := hch.2
  have hp := h.prime
  have hp5 := h.five_le
  by_cases hf : f = 1
  · subst hf
    have hT := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4
      (by simpa using hU : UntwistedChevalleyModel (↥X ⧸ Subgroup.center ↥X) .F4 2)
    have hd := pow_three_dvd_card_quot h
    rw [hT] at hd
    exact not_pow_three_dvd_ordF4_two hp hp5 hd
  · obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hU
    let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
    have hKq : Nat.card K = q.card := by rw [TauCeti.PrimePower.card_def]; exact hK
    have hv : (TauCeti.LieTypeIndex.F4 q).Valid :=
      (TauCeti.LieTypeIndex.valid_iff _).2 ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 trivial,
        by
          rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
          exact id⟩
    obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).f4 q hv rfl K hKq
    let φ := e.trans b
    have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.F4 q, hv⟩) := Finite.of_equiv _ φ.toEquiv
    have hm : Models.LieModel (↥X ⧸ Subgroup.center ↥X) .F4 0 2 f :=
      ⟨hadm, Or.inr ⟨rfl, ⟨.F4 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
    have hdvd := T123Base.card_center_dvd_multiplier h hGA hm
    have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥X) := by
      intro r hr hr2 hrZ
      have h2 := (hrZ.trans hdvd).trans (KFU.card_multiplier_F4 (f := f))
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
    exact false_of_four_le_twoLocalOddRank_B h hZ φ (hExc.f4 q hv (fun h' => hf h'.2))

theorem false_of_commuting_sl2_B
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Q1327.T123Base p X A₀ F) (hodd : Nat.Coprime 2 (Nat.card (Subgroup.center ↥X)))
    {Y : Type} [Group Y] (ε : ↥X ⧸ Subgroup.center ↥X ≃* Y) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (φ : Fin 4 → Matrix.SpecialLinearGroup (Fin 2) K →* Y) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, φ i A * φ j B = φ j B * φ i A) : False := by
  have hπ : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥X)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center ↥X)).ker ≤ Subgroup.center ↥X :=
    (QuotientGroup.ker_mk' _).le
  have hodd' : Nat.Coprime 2 (Nat.card (QuotientGroup.mk' (Subgroup.center ↥X)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact hodd
  obtain ⟨φ', hφ'1, hφ'2⟩ := KFU.exists_lift_four_commuting_sl2 hGA hf hK
    (QuotientGroup.mk' (Subgroup.center ↥X)) hπ hker hodd'
    (fun i => ε.symm.toMonoidHom.comp (φ i)) (fun i => ε.symm.injective.comp (hφ i))
    (fun i j hij A B => by simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B])
  have : Fintype K := Fintype.ofFinite K
  have hK2 : Fintype.card K ≠ 2 := by
    rw [← Nat.card_eq_fintype_card, hK]
    have : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have h4 : 4 ≤ CFSG.twoLocalOddRank ↥X :=
    PartTwo.Census.Exceptional.four_le_twoLocalOddRank_of_four_commuting_SL2 (K := K) hK2 φ'
      hφ'1 hφ'2
  have h3 := h.evenRank_le
  rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h3
  omega

theorem false_of_E6
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .E6 n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .E6 n 2 f) : False := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  have hU : UntwistedChevalleyModel (↥X ⧸ Subgroup.center ↥X) .E6 (2 ^ f) := hch.2
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hU
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  have hq : q.card = 2 ^ f := TauCeti.PrimePower.card_def q
  have hKq : Nat.card K = q.card := by rw [hq]; exact hK
  have hv : (TauCeti.LieTypeIndex.E6 q).Valid := by simp
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).e6 q hv rfl K hKq
  let φ := e.trans b
  have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) := Finite.of_equiv _ φ.toEquiv
  have hm : Models.LieModel (↥X ⧸ Subgroup.center ↥X) .E6 0 2 f :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.E6 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := T123Base.card_center_dvd_multiplier h hGA hm
  rw [KFU.card_multiplier_E6] at hdvd
  by_cases hf2 : 2 ≤ f
  · have hodd : Nat.Coprime 2 (Nat.card (Subgroup.center ↥X)) :=
      Nat.Coprime.coprime_dvd_right (hdvd.trans (Nat.gcd_dvd_left 3 _)) (by norm_num)
    obtain ⟨K', hK'f, hK'fin, hK'q, ψ, hψ, hψc⟩ := KFU.exists_four_commuting_SL2_E6 q hv
    exact false_of_commuting_sl2_B hGA h hodd φ hf2 (hK'q.trans hq) ψ hψ hψc
  · have hf : f = 1 := by omega
    subst hf
    have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥X) := by
      intro r hr hr2 hrZ
      have h1 : Nat.card (Subgroup.center ↥X) ∣ 1 := by simpa using hdvd
      exact hr.one_lt.ne' (Nat.dvd_one.mp (hrZ.trans h1))
    exact false_of_four_le_twoLocalOddRank_B h hZ φ (hExc.e6 q hv)

theorem false_of_twistedE6
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .twistedE6 n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .twistedE6 n 2 f) : False := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hf1 : 1 ≤ f := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hmodel
  have hU : TwistedChevalleyModel (↥X ⧸ Subgroup.center ↥X) .E6 (2 ^ f) := hch.2
  obtain ⟨K, hKf, hKfin, hK, σ, hσ, ⟨e⟩⟩ := hU
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  have hq : q.card = 2 ^ f := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := by simp
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).twistedE6 q hv rfl K
    (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
  let φ := e.trans b
  have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :=
    Finite.of_equiv _ φ.toEquiv
  have hm : Models.LieModel (↥X ⧸ Subgroup.center ↥X) .twistedE6 0 2 f :=
    ⟨hadm, Or.inr ⟨rfl, ⟨.twistedE6 q, hv⟩, ⟨rfl, rfl⟩, ⟨φ⟩⟩⟩
  have hdvd := T123Base.card_center_dvd_multiplier h hGA hm
  by_cases hf2 : 2 ≤ f
  · rw [KFU.card_multiplier_twistedE6 (by omega)] at hdvd
    have hodd : Nat.Coprime 2 (Nat.card (Subgroup.center ↥X)) :=
      Nat.Coprime.coprime_dvd_right (hdvd.trans (Nat.gcd_dvd_left 3 _)) (by norm_num)
    obtain ⟨K', hK'f, hK'fin, hK'q, ψ, hψ, hψc⟩ := KFU.exists_four_commuting_SL2_twistedE6 q hv
    exact false_of_commuting_sl2_B hGA h hodd φ hf2 (hK'q.trans hq) ψ hψ hψc
  · have hf : f = 1 := by omega
    subst hf
    rw [KFU.card_multiplier_twistedE6_one] at hdvd
    by_cases h3 : 3 ∣ Nat.card (Subgroup.center ↥X)
    · obtain ⟨K', hK'f, hK'fin, hK'q, ψ, hψ, hψc⟩ :=
        KFU.exists_four_commuting_SL2_twistedE6 q hv
      have hK'2 : Nat.card K' = 2 := by rw [hK'q, hq]; norm_num
      have h4 := KFU.four_le_localRank_three_of_commuting_sl2_two hdvd h3 φ hK'2 ψ hψ hψc
      have h5 := PartTwo.Census.Exceptional.four_le_twoLocalOddRank_of_localRank Nat.prime_three
        (by norm_num) h4
      have h6 := h.evenRank_le
      rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h6
      omega
    · have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥X) := by
        intro r hr hr2 hrZ
        have h12 : r ∣ 2 ^ 2 * 3 := by simpa using hrZ.trans hdvd
        rcases (Nat.Prime.dvd_mul hr).1 h12 with h2 | h3'
        · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
        · exact h3 (by rw [(Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3'] at hrZ; exact hrZ)
      exact false_of_four_le_twoLocalOddRank_B h hZ φ (hExc.twistedE6 q hv)

end CFSG.RankThree.PartOne.Q1327C
