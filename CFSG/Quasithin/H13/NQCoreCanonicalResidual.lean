module

public import CFSG.Quasithin.H13.NQCoreCanonicalAmbient
public import CFSG.Quasithin.SteinbergCDPrimePlaneSylowNormalizer
public import CFSG.Quasithin.H13.NQRigidConjugate
public import CFSG.Quasithin.Vol2.Ch1Unique

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)

variable {G : Type} [Group G] [Finite G]

structure SNCanonical (T D X : Subgroup G) (p : ℕ) : Prop where
  le : X ≤ D
  characteristic : (X.subgroupOf D).Characteristic
  normal : (X.subgroupOf (normalizer (D : Set G))).Normal
  solvable : Group.IsSolvable ↥X
  le_rad : X ≤ (CFSG.solvableRadical ↥D).map D.subtype
  noTwoQuotient : NoPQuotient 2 X
  pCore_ne_bot : CFSG.pCore 2 ↥X ≠ ⊥
  genFitting : quasithinGenFitting X = pCoreOf 2 X
  normalizer_eq : normalizer (D : Set G) = normalizer (X : Set G)
  normalizer_eq_core : normalizer (D : Set G) = normalizer (pCoreOf 2 X : Set G)
  inf_pCore : X ⊓ pCoreOf 2 D = pCoreOf 2 X
  image : (X.subgroupOf D).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D)) =
    closure {c | c ∈ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) ∧ c ^ p = 1}
  shape : (IsMulCommutative (X ⧸ CFSG.pCore 2 X) ∧ Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2) ∨
    (¬ IsMulCommutative (X ⧸ CFSG.pCore 2 X) ∧ Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 3)
  isPGroup : IsPGroup p (X ⧸ CFSG.pCore 2 X)
  exponent : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p
  pRank : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2
  card_W : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2
  nontrivial : ∃ d : normalizer (X : Set G), (d : G) ∈ D ∧ normalizerFrattiniConj X d ≠ 1
  irreducible_D : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
    (∀ d : normalizer (X : Set G), (d : G) ∈ D → ∀ w ∈ V, normalizerFrattiniConj X d w ∈ V) →
      V = ⊥ ∨ V = ⊤
  irreducible_TD : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
    (∀ d : normalizer (X : Set G), (d : G) ∈ T ⊓ D →
      ∀ w ∈ V, normalizerFrattiniConj X d w ∈ V) → V = ⊥ ∨ V = ⊤
  irreducible_T : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
    (∀ d : normalizer (X : Set G), (d : G) ∈ T → ∀ w ∈ V, normalizerFrattiniConj X d w ∈ V) →
      V = ⊥ ∨ V = ⊤

theorem mem_primeFactors_fitting {K : Type*} [Group K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    (h : CFSG.pCore p K ≠ ⊥) : p ∈ (Nat.card (CFSG.fittingSubgroup K)).primeFactors := by
  have hpc : p ∣ Nat.card (CFSG.pCore p K) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := p) (G := K))
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact h (Subgroup.card_eq_one.mp hk)
    rw [hk]
    exact dvd_pow_self p hk0
  have hdvd : Nat.card (CFSG.pCore p K) ∣ Nat.card (CFSG.fittingSubgroup K) :=
    Subgroup.card_dvd_of_le (CFSG.pCore_le_fitting K p)
  exact Nat.mem_primeFactors.mpr ⟨hp.out, hpc.trans hdvd, Nat.card_pos.ne'⟩

theorem snCanonical {T D : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTD : T ≤ normalizer (D : Set G)) (hDq : ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D))
    (hA : SNAmbient T D) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hCp : CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) ≠ ⊥) :
    SNCanonical T D (nqPrimeResidualX D p) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp1 : 1 < p := hp.one_lt
  set Q : Subgroup (↥D ⧸ CFSG.pCore 2 ↥D) := CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) with hQdef
  set B : Subgroup (↥D ⧸ CFSG.pCore 2 ↥D) := closure {a | a ∈ Q ∧ a ^ p = 1} with hBdef
  set E : Subgroup ↥D := B.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥D)) with hEdef
  set X' : Subgroup ↥D := closure {e | e ∈ E ∧ Odd (orderOf e)} with hX'def
  obtain ⟨-, hXc, hW', hsolv', hE, hO2', ⟨-, φ, -, hφ, -, -, -⟩, hshape, -⟩ :=
    NQBlock.canonical_prime_witness hA.sqt hA.isCComponent_top hDq (mem_primeFactors_fitting hCp)
      Q B E X' rfl rfl rfl rfl
  have hXeq : nqPrimeResidualX D p = X'.map D.subtype := rfl
  rw [hXeq]
  set X : Subgroup G := X'.map D.subtype with hXdef
  have hXD : X ≤ D := map_subtype_le _
  have hXsub : X.subgroupOf D = X' := comap_map_eq_self_of_injective D.subtype_injective X'
  have hXchar : (X.subgroupOf D).Characteristic := hXsub ▸ hXc
  set eX : X' ≃* X := X'.equivMapOfInjective D.subtype D.subtype_injective with heX
  have hpc : (CFSG.pCore 2 X').map (eX : X' →* X) = CFSG.pCore 2 X := CFSG.pCore_map_iso 2 eX
  set eQ : (X' ⧸ CFSG.pCore 2 X') ≃* (X ⧸ CFSG.pCore 2 X) :=
    QuotientGroup.congr _ _ eX hpc with heQ
  set eW : ((X' ⧸ CFSG.pCore 2 X') ⧸ frattini (X' ⧸ CFSG.pCore 2 X')) ≃*
      ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    QuotientGroup.congr _ _ eQ (NQBlock.map_frattini_mulEquiv eQ) with heW
  have hX2 : NoPQuotient 2 X := NoPQuotient.of_surjective eX.toMonoidHom eX.surjective
    hW'.noTwoQuotient
  have hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p := by
    rw [← Monoid.exponent_eq_of_mulEquiv eQ, hW'.exponent]
  have hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 := by
    rw [← NQRigid.pRank_congr hp1 eQ, hW'.pRank]
  have hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 := by
    rw [← Nat.card_congr eW.toEquiv, hW'.card_W]
  have hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X) := hW'.isPGroup.of_equiv eQ
  set J := normalizer (D : Set G) with hJdef
  have hJX : J ≤ normalizer (X : Set G) :=
    NQSetup.normalizer_le_normalizer_of_characteristic hXD hXchar
  have hDJ : D ≤ J := le_normalizer
  have hXJ : X ≤ J := hXD.trans hDJ
  have hXn : (X.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hXJ).mpr hJX
  have hXsubn : IsSubnormal X J := A4.subnormal_of_normal hXJ hXn
  have hcharX : CharTwo X := A4.charTwo_of_subnormal hXsubn hA.charTwo_normalizer
  have hX1 : X ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥X = 1 := by rw [hbot]; exact Subgroup.card_bot
    have h2 : Nat.card (X ⧸ CFSG.pCore 2 X) ≤ Nat.card ↥X :=
      Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    have h3 : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) ≤
        Nat.card (X ⧸ CFSG.pCore 2 X) :=
      Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    rw [hW] at h3
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp1
    omega
  have hO2X : pCoreOf 2 X ≠ ⊥ := pCoreOf_ne_bot_of_charTwo hcharX hX1
  have hO2X' : CFSG.pCore 2 ↥X ≠ ⊥ := by
    intro h
    apply hO2X
    rw [pCoreOf, h, Subgroup.map_bot]
  have hNcore : IsTwoLocal (normalizer (pCoreOf 2 X : Set G)) :=
    ⟨pCoreOf 2 X, hO2X, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X, rfl⟩
  have hXcore : normalizer (X : Set G) ≤ normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  have hJcore : J = normalizer (pCoreOf 2 X : Set G) :=
    (hA.unique.1.2 _ hNcore (hJX.trans hXcore)).symm
  have hJN : J = normalizer (X : Set G) :=
    le_antisymm hJX (hXcore.trans hJcore.ge)
  have hinf : X ⊓ pCoreOf 2 D = pCoreOf 2 X := by
    have e1 : pCoreOf 2 X = ((CFSG.pCore 2 X').map X'.subtype).map D.subtype := by
      rw [pCoreOf, ← hpc, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [e1, ← hO2', Subgroup.subgroupOf_map_subtype, pCoreOf, hXdef,
      ← Subgroup.map_inf_eq _ _ _ D.subtype_injective, inf_comm]
  have himage : (X.subgroupOf D).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D)) = B := by
    rw [hXsub]
    have h1 : E.map (QuotientGroup.mk' (CFSG.pCore 2 ↥D)) = B :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) B
    rw [hE, Subgroup.map_sup] at h1
    have h2 : (CFSG.pCore 2 ↥D).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rwa [h2, bot_sup_eq] at h1
  set e : (X ⧸ CFSG.pCore 2 X) ≃* B := eQ.symm.trans φ with he
  have hcardB : Nat.card (X ⧸ CFSG.pCore 2 X) = Nat.card B := Nat.card_congr e.toEquiv
  have hshapeX : (IsMulCommutative (X ⧸ CFSG.pCore 2 X) ∧ Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2) ∨
      (¬ IsMulCommutative (X ⧸ CFSG.pCore 2 X) ∧ Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 3) := by
    rcases hshape with ⟨-, -, -, hB2⟩ | ⟨hQB, hQnc, hQ3, -⟩
    · left
      have h2 : Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2 := hcardB.trans hB2
      exact ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq h2, h2⟩
    · right
      have h3 : Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 3 := by rw [hcardB, ← hQB]; exact hQ3
      refine ⟨fun hc => hQnc ?_, h3⟩
      have hB : IsMulCommutative ↥B := ⟨⟨fun a b => by
        have h := hc.is_comm.comm (e.symm a) (e.symm b)
        apply e.symm.injective
        rw [map_mul, map_mul, h]⟩⟩
      rw [hQB]
      exact hB
  have hDN : D ≤ normalizer (X : Set G) := hDJ.trans hJX
  have hcompat : ∀ (l : ↥D) (w : (X' ⧸ CFSG.pCore 2 X') ⧸ frattini (X' ⧸ CFSG.pCore 2 X')),
      eW (NQBlock.residualAction X' l w) =
        normalizerFrattiniConj X ⟨(l : G), hDN l.2⟩ (eW w) := by
    intro l w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rfl
  have hnt : ∃ d : normalizer (X : Set G), (d : G) ∈ D ∧ normalizerFrattiniConj X d ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hW'.nontrivial
    refine MonoidHom.ext fun l => MulEquiv.ext fun w => ?_
    apply eW.injective
    rw [hcompat, hall ⟨(l : G), hDN l.2⟩ l.2]
    rfl
  have hirrD : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ d : normalizer (X : Set G), (d : G) ∈ D → ∀ w ∈ V, normalizerFrattiniConj X d w ∈ V) →
        V = ⊥ ∨ V = ⊤ := by
    intro V hV
    by_contra hne
    push Not at hne
    obtain ⟨hV0, hVT⟩ := hne
    have hVcard : Nat.card V = p := by
      have hdvd : Nat.card V ∣ p ^ 2 := hW ▸ V.card_subgroup_dvd_card
      obtain ⟨k, hk, hVk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      interval_cases k
      · exact absurd (Subgroup.eq_bot_of_card_eq V (by rw [hVk, pow_zero])) hV0
      · rw [hVk, pow_one]
      · exact absurd (Subgroup.eq_top_of_card_eq V (by rw [hVk, hW])) hVT
    obtain ⟨l, u, hu, hlu⟩ := hW'.irreducible (V.map eW.symm.toMonoidHom) (by
      rw [card_map_of_injective (f := eW.symm.toMonoidHom) eW.symm.injective, hVcard])
    obtain ⟨y, hy, rfl⟩ := hu
    apply hlu
    refine ⟨normalizerFrattiniConj X ⟨(l : G), hDN l.2⟩ y, hV _ l.2 y hy, ?_⟩
    apply eW.injective
    rw [hcompat]
    simp
  have hTJs : IsSylowTwoOf T J := isSylowTwoOf_of_quasithinIsSylowTwo hT hTD
  have hTDs : IsSylowTwoOf (T ⊓ D) D := A4.isSylowTwoOf_inf_normal hTJs hDJ le_rfl
  have hTDp : IsPGroup 2 ((T ⊓ D).subgroupOf D) :=
    hTDs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTDs.1).symm
  have hTDi : ¬ 2 ∣ ((T ⊓ D).subgroupOf D).index := hTDs.2.2
  set S' : Sylow 2 ↥D := hTDp.toSylow hTDi with hS'
  have hS'c : (S' : Subgroup ↥D) = (T ⊓ D).subgroupOf D := IsPGroup.toSylow_coe hTDp hTDi
  have : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hA.cComp_self)
  have hWc : IsMulCommutative ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hW
  have hWp : ∀ w : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X), w ^ p = 1 := by
    intro w
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_pow, ← hexp, Monoid.pow_exponent_eq_one, QuotientGroup.mk_one]
  set β : ↥D →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    (normalizerFrattiniConj X).comp (Subgroup.inclusion hDN) with hβdef
  have hβ : β ≠ 1 := by
    intro h1
    obtain ⟨d, hdD, hd⟩ := hnt
    apply hd
    have h2 := congrArg (fun f => f ⟨(d : G), hdD⟩) h1
    have hinc : Subgroup.inclusion hDN ⟨(d : G), hdD⟩ = d := Subtype.ext rfl
    simp only [hβdef, MonoidHom.comp_apply, MonoidHom.one_apply, hinc] at h2
    exact h2
  have hirrTD : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ d : normalizer (X : Set G), (d : G) ∈ T ⊓ D →
        ∀ w ∈ V, normalizerFrattiniConj X d w ∈ V) → V = ⊥ ∨ V = ⊤ := by
    intro V hV
    refine SteinbergCD.perfect_sylow_two_irreducible_of_card_eq_sq hp5 hWp hW β hβ S' V ?_
    intro s hs w hw
    rw [hS'c] at hs
    exact hV _ (Subgroup.mem_subgroupOf.mp hs) w hw
  have hirrT : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ d : normalizer (X : Set G), (d : G) ∈ T → ∀ w ∈ V, normalizerFrattiniConj X d w ∈ V) →
        V = ⊥ ∨ V = ⊤ :=
    fun V hV => hirrTD V fun d hd w hw => hV d hd.1 w hw
  exact
    { le := hXD
      characteristic := hXchar
      normal := hXn
      solvable := Group.isSolvable_of_surjective (f := eX.toMonoidHom) eX.surjective
      le_rad := map_mono hW'.le_rad
      noTwoQuotient := hX2
      pCore_ne_bot := hO2X'
      genFitting := (quasithinGenFitting_eq_pCoreOf_iff X 2).mpr hcharX
      normalizer_eq := hJN
      normalizer_eq_core := hJcore
      inf_pCore := hinf
      image := himage
      shape := hshapeX
      isPGroup := hXp
      exponent := hexp
      pRank := hrk
      card_W := hW
      nontrivial := hnt
      irreducible_D := hirrD
      irreducible_TD := hirrTD
      irreducible_T := hirrT }

theorem sylow_normalized_maximal_nonquasisimple_canonical_residual_structure
    (hA7u : U3.SylowNormalizedMaximalLocalUniqueNormalizer)
    (hA7n : NQBlock.SylowNormalizedLocalNormalComponent) [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G) {T D : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hDmax : quasithinIsMaximalLocal T D)
    (hDf : quasithinIsFaithfulLocal T D) (hTD : T ≤ normalizer (D : Set G))
    (hDq : ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D)) :
    (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) ≠ ⊥) ∧ SNAmbient T D ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) ≠ ⊥ →
        SNCanonical T D (nqPrimeResidualX D p) p := by
  have hA := snAmbient hA7u hA7n hnab hQ hT hDmax hDf hTD
  refine ⟨?_, hA, fun p hp hp5 hCp => snCanonical hT hTD hDq hA hp hp5 hCp⟩
  obtain ⟨p, hp, hp5, D₀, -, hD₀, hshape, -⟩ :=
    NQBlock.nq_characteristic_radical_odd_residual_witness hA.sqt hA.isCComponent_top hDq
  refine ⟨p, hp, hp5, fun hbot => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hD₀b : D₀ = ⊥ := le_bot_iff.mp (hbot ▸ hD₀)
  have hcard : Nat.card D₀ = 1 := by rw [hD₀b, Subgroup.card_bot]
  rcases hshape with ⟨-, h2⟩ | ⟨-, h3, -⟩
  · rw [hcard] at h2
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  · rw [hcard] at h3
    have : 1 < p ^ 3 := Nat.one_lt_pow three_ne_zero hp.one_lt
    omega

theorem SNCanonical.of_qtTMaxNQPrime
    (hA7u : U3.SylowNormalizedMaximalLocalUniqueNormalizer)
    (hA7n : NQBlock.SylowNormalizedLocalNormalComponent) {T L M D X : Subgroup G} {p : ℕ}
    (h : QTTMaxNQPrime T L M D p X) : SNAmbient T D ∧ SNCanonical T D X p := by
  have := h.qtnq.simple
  obtain ⟨-, hA, hall⟩ := sylow_normalized_maximal_nonquasisimple_canonical_residual_structure
    hA7u hA7n h.qtnq.nonabelian h.qtnq.qtke h.qtnq.sylow h.maximal_local h.faithful_local
    h.le_normalizer h.not_quasisimple
  rw [h.eq_residual]
  exact ⟨hA, hall p h.prime h.five_le h.core_ne_bot⟩

end CFSG.Quasithin.H13.NQCore
