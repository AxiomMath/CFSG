module

public import CFSG.Quasithin.H13.NQRigidWitness
public import CFSG.Quasithin.H13.NQRigidFacts

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem witness_map_props (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) {X₀ : Subgroup ↥L}
    (hX : NQBlock.IsOddResidualWitness p X₀) :
    X₀.map L.subtype ≤ (CFSG.solvableRadical L).map L.subtype ∧
      ((X₀.map L.subtype).subgroupOf L).Characteristic ∧ CFSG.pCore 2 ↥(X₀.map L.subtype) ≠ ⊥ ∧
      NoPQuotient 2 ↥(X₀.map L.subtype) ∧
      IsPGroup p (↥(X₀.map L.subtype) ⧸ CFSG.pCore 2 ↥(X₀.map L.subtype)) ∧
      Monoid.exponent (↥(X₀.map L.subtype) ⧸ CFSG.pCore 2 ↥(X₀.map L.subtype)) = p ∧
      CFSG.pRank p (↥(X₀.map L.subtype) ⧸ CFSG.pCore 2 ↥(X₀.map L.subtype)) = 2 ∧
      Nat.card ((↥(X₀.map L.subtype) ⧸ CFSG.pCore 2 ↥(X₀.map L.subtype)) ⧸
        frattini (↥(X₀.map L.subtype) ⧸ CFSG.pCore 2 ↥(X₀.map L.subtype))) = p ^ 2 ∧
      (∃ l : normalizer ((X₀.map L.subtype : Subgroup G) : Set G), (l : G) ∈ L ∧
        normalizerFrattiniConj (X₀.map L.subtype) l ≠ 1) ∧
      IsFrattiniIrreducible (X₀.map L.subtype) L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨hcharM, -, -, -, -, -⟩ := NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hXc₀ := hX.characteristic
  set X : Subgroup G := X₀.map L.subtype with hXdef
  have hXL : X ≤ L := map_subtype_le _
  have hXsub : X.subgroupOf L = X₀ := comap_map_eq_self_of_injective L.subtype_injective X₀
  have hXchar : (X.subgroupOf L).Characteristic := hXsub ▸ hXc₀
  have hXRad : X ≤ (CFSG.solvableRadical L).map L.subtype := map_mono hX.le_rad
  set eX : X₀ ≃* X := X₀.equivMapOfInjective L.subtype L.subtype_injective with heX
  have hpc : (CFSG.pCore 2 X₀).map (eX : X₀ →* X) = CFSG.pCore 2 X := CFSG.pCore_map_iso 2 eX
  set eQ : (X₀ ⧸ CFSG.pCore 2 X₀) ≃* (X ⧸ CFSG.pCore 2 X) :=
    QuotientGroup.congr _ _ eX hpc with heQ
  set eW : ((X₀ ⧸ CFSG.pCore 2 X₀) ⧸ frattini (X₀ ⧸ CFSG.pCore 2 X₀)) ≃*
      ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    QuotientGroup.congr _ _ eQ (map_frattini_mulEquiv eQ) with heW
  have hX2 : NoPQuotient 2 X := NoPQuotient.of_surjective eX.toMonoidHom eX.surjective
    hX.noTwoQuotient
  have hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p := by
    rw [← Monoid.exponent_eq_of_mulEquiv eQ, hX.exponent]
  have hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 := by
    rw [← pRank_congr hp1 eQ, hX.pRank]
  have hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 := by
    rw [← Nat.card_congr eW.toEquiv, hX.card_W]
  have hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X) := hX.isPGroup.of_equiv eQ
  have hMX : M ≤ normalizer (X : Set G) := by
    rw [h.eq_normalizer]
    exact NQSetup.normalizer_le_normalizer_of_characteristic hXL hXchar
  have hXM : X ≤ M := hXL.trans h.l_le
  have hO2 : CFSG.pCore 2 X ≠ ⊥ := by
    intro hbot
    have hle := le_pCore_map_of_pCore_eq_bot hXM hMX hbot hcharM
    have hX2' : IsPGroup 2 X := by
      have h2 : IsPGroup 2 ((CFSG.pCore 2 M).map M.subtype) := CFSG.pCore_isPGroup.map _
      exact h2.to_le hle
    have htop : CFSG.pCore 2 X = ⊤ := by
      rw [eq_top_iff]
      exact SteinbergCC.le_pCore_of_normal_of_isPGroup normal_top
        (hX2'.of_equiv Subgroup.topEquiv.symm)
    have hsub : Subsingleton (X ⧸ CFSG.pCore 2 X) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have h1 : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = 1 := Monoid.exp_eq_one_iff.mpr hsub
    rw [hexp] at h1
    exact hp1.ne' h1
  have hLN : L ≤ normalizer (X : Set G) := h.l_le.trans hMX
  have hcompat : ∀ (l : L) (w : (X₀ ⧸ CFSG.pCore 2 X₀) ⧸ frattini (X₀ ⧸ CFSG.pCore 2 X₀)),
      eW (NQBlock.residualAction X₀ l w) =
        normalizerFrattiniConj X ⟨(l : G), hLN l.2⟩ (eW w) := by
    intro l w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rfl
  have hnt : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hX.nontrivial
    refine MonoidHom.ext fun l => MulEquiv.ext fun w => ?_
    apply eW.injective
    rw [hcompat, hall ⟨(l : G), hLN l.2⟩ l.2]
    rfl
  have hirrL : IsFrattiniIrreducible X L := by
    intro Y hY
    by_contra hne
    push Not at hne
    obtain ⟨hY0, hYT⟩ := hne
    have hYcard : Nat.card Y = p := by
      have hdvd : Nat.card Y ∣ p ^ 2 := hW ▸ Y.card_subgroup_dvd_card
      obtain ⟨k, hk, hYk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      interval_cases k
      · exact absurd (Subgroup.eq_bot_of_card_eq Y (by rw [hYk, pow_zero])) hY0
      · rw [hYk, pow_one]
      · exact absurd (Subgroup.eq_top_of_card_eq Y (by rw [hYk, hW])) hYT
    obtain ⟨l, u, hu, hlu⟩ := hX.irreducible (Y.map eW.symm.toMonoidHom) (by
      rw [card_map_of_injective (f := eW.symm.toMonoidHom) eW.symm.injective, hYcard])
    obtain ⟨y, hy, rfl⟩ := hu
    apply hlu
    refine ⟨normalizerFrattiniConj X ⟨(l : G), hLN l.2⟩ y, hY _ l.2 y hy, ?_⟩
    apply eW.injective
    rw [hcompat]
    simp
  exact ⟨hXRad, hXchar, hO2, hX2, hXp, hexp, hrk, hW, hnt, hirrL⟩

theorem not_le_of_witness (hWS : FactWitnessSingleton) (h : QTNQ T L M) {H : Subgroup G}
    (hTH : T ≤ H) (hH2 : pCoreOf 2 H ≠ ⊥) (hHM : ¬ H ≤ M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X₀ : Subgroup ↥L} (hX : NQBlock.IsOddResidualWitness p X₀) : ¬ X₀.map L.subtype ≤ H := by
  intro hXH
  obtain ⟨hXR, hXc, hO2, hX2, hXp, hexp, hrk, hW, hnt, hirr⟩ := witness_map_props h hp hX
  have hS := hWS G T L M h p hp hp5 _ hXR hXc hO2 hX2 hXp hexp hrk hW hnt hirr
  have hloc : IsTwoLocal (normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, hH2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, rfl⟩
  have hHN : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)
  obtain ⟨M', hM', hNM'⟩ := QuasithinUnique.exists_quasithinIsMaxTwoLocal_ge hloc
  have hmem : M' ∈ CFSG.maximalTwoLocalsContaining ((X₀.map L.subtype ⊔ T : Subgroup G) : Set G) :=
    ⟨isMaximalTwoLocal_iff_quasithinIsMaxTwoLocal.mpr hM',
      SetLike.coe_subset_coe.mpr ((sup_le hXH hTH).trans (hHN.trans hNM'))⟩
  rw [hS, Set.mem_singleton_iff] at hmem
  exact hHM (hmem ▸ hHN.trans hNM')

end CFSG.Quasithin.H13.NQRigid
