module

public import CFSG.Quasithin.H13.NQCatExcludesSmallMatrix
public import CFSG.Quasithin.H13.QTESylowStmt
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore
public import CFSG.RankThree.PartOne.S11c.J4Plane
public import CFSG.LieType.SteinbergBRLieModelRankOneClassifier

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped Pointwise

@[expose] def PrimeLinearThreeAmbientPrime : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (K : Type) [Group K] [Finite K] (q : ℕ) [Fact q.Prime],
    Nat.card F = q → 5 ≤ q →
    ∀ (D : Subgroup (CFSG.Wreathed.OddLinearThreeCentralizerCore.SL3 F)) [D.Normal],
      D ≤ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F →
      ∀ (_ : K ⧸ CFSG.pCore 2 K ≃* CFSG.Wreathed.OddLinearThreeCentralizerCore.SL3 F ⧸ D)
        (S : Sylow 2 K) (A : Subgroup K), A ∈ cComp (A ⊔ (S : Subgroup K)) →
        ¬ CFSG.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A) →
        ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : Subgroup K, X ≤ A → (X.subgroupOf A).Normal →
          (∀ (Y : Subgroup ↥X) [Y.Normal], IsPGroup 2 (↥X ⧸ Y) → Y = ⊤) →
          IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X) → CFSG.pRank p (↥X ⧸ CFSG.pCore 2 ↥X) = 2 → p = q

section Tools

theorem sq_dvd_card_of_not_isCyclic' {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) : p ^ 2 ∣ Nat.card P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk]
  apply pow_dvd_pow
  by_contra hlt
  have hk1 : k = 0 ∨ k = 1 := by omega
  rcases hk1 with rfl | rfl
  · rw [pow_zero] at hk
    have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hk).1
    exact hnc isCyclic_of_subsingleton
  · rw [pow_one] at hk
    exact hnc (isCyclic_of_prime_card hk)

theorem pCore_two_eq_bot_of_simple {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : CFSG.pCore 2 S = ⊥ := by
  have hN : (CFSG.pCore 2 S).Normal := CFSG.pCore_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 S) with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 S := by
      have h1 : IsPGroup 2 (CFSG.pCore 2 S) := CFSG.pCore_isPGroup
      rw [h] at h1
      exact IsPGroup.of_equiv h1 Subgroup.topEquiv
    obtain ⟨a, b, hab⟩ := hnab
    have hnil := hp.isNilpotent
    have hsolv : Group.IsSolvable S := inferInstance
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv a b)

theorem sup_lt_top_of_not_quasisimple {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) {B T : Subgroup S} (hB : B ∈ cComp (B ⊔ T))
    (hBq : ¬ CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B)) : B ⊔ T < ⊤ := by
  have hBnq : ¬ CFSG.IsQuasisimple ↥B := fun h =>
    hBq (NQCat.isQuasisimple_quotient_pCore_of_isQuasisimple h)
  refine lt_top_iff_ne_top.mpr fun htop => hBnq ?_
  have hBc : B ∈ cComp (⊤ : Subgroup S) := htop ▸ hB
  have hsub : B.IsSubnormal :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_top_iff_mathlib B).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open B ⊤).2
        (subnormal_of_mem_cComp hBc))
  obtain ⟨hSq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hSq hsub with
    hBtop | hcen
  · rw [hBtop]
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).2 hSq
  · exfalso
    apply ne_bot_of_mem_cComp hB
    rw [← le_bot_iff, ← hZ]
    exact hcen

theorem isCyclic_of_proper_sylow_overgroup_transport {S X : Type*} [Group S] [Finite S]
    [Group X] {Γ : Subgroup X} (e : S ≃* Γ)
    (hΓ : ∀ T B : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 T Γ → B ≤ Γ → Group.IsPerfect B →
      B ⊔ T < Γ → ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ E : Subgroup X, E ≤ B → IsPGroup r E →
        IsCyclic E)
    {T B : Subgroup S} (hT : quasithinIsSylowTwo T) (hB : Group.IsPerfect B) (hBT : B ⊔ T < ⊤)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup S} (hEB : E ≤ B) (hE : IsPGroup r E) :
    IsCyclic E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : S →* X := Γ.subtype.comp e.toMonoidHom with hφ
  have hφi : Function.Injective φ := Γ.subtype_injective.comp e.injective
  have hrange : (⊤ : Subgroup S).map φ = Γ := by
    rw [← MonoidHom.range_eq_map, hφ, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hTm : quasithinIsSylowTwo (T.map e.toMonoidHom) :=
    ⟨hT.1.map _, by
      rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
      exact hT.2⟩
  have hTs : CFSG.ABGLocalTools.IsSylowOf 2 (T.map φ) Γ :=
    ⟨hTm.1.toSylow hTm.2, by
      change (T.map e.toMonoidHom).map Γ.subtype = T.map φ
      rw [Subgroup.map_map]⟩
  have hBΓ : B.map φ ≤ Γ := hrange ▸ Subgroup.map_mono le_top
  have hBp : Group.IsPerfect (B.map φ) := by
    have := hB
    exact Group.IsPerfect.map (H := B) (f := φ)
  have hBT' : B.map φ ⊔ T.map φ < Γ := by
    rw [← Subgroup.map_sup, ← hrange]
    exact (Subgroup.map_lt_map_iff_of_injective hφi).mpr hBT
  have hcyc := hΓ _ _ hTs hBΓ hBp hBT' r hr hr2 (E.map φ) (Subgroup.map_mono hEB) (hE.map φ)
  exact isCyclic_of_surjective (E.equivMapOfInjective φ hφi).symm.toMonoidHom
    (E.equivMapOfInjective φ hφi).symm.surjective

end Tools

section Exclusions

variable {S : Type} [Group S] [Finite S] [IsSimpleGroup S]

omit [Finite S] in
theorem isQuasisimple_quotient_bot (hnab : ∃ a b : S, a * b ≠ b * a) :
    CFSG.IsQuasisimple (S ⧸ (⊥ : Subgroup S)) :=
  (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr QuotientGroup.quotientBot).2
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1

theorem not_statedPSU_three (hnab : ∃ a b : S, a * b ≠ b * a) (Ts : Sylow 2 S) {B : Subgroup S}
    (hB : B ∈ cComp (B ⊔ (Ts : Subgroup S))) (hBq : ¬ CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B))
    {ℓ : ℕ} (hU : StatedClassicalModel S .PSU 3 ℓ 1) : False := by
  obtain ⟨⟨hℓ, -⟩, F, _, _, hF, ⟨e⟩⟩ := hU
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ 1 F :=
    ⟨hℓ, le_rfl, by rw [hF]; ring⟩
  have hexcl :=
    (NQCat.nonquasisimple_local_two_core_quotient_excludes_small_matrix_ambient_quotients
      (⊥ : Subgroup S) IsPGroup.of_bot Ts hB (isQuasisimple_quotient_bot hnab) hBq).2.1 ℓ 1 F h
      ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (ℓ ^ 1) F))
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq h (by norm_num)).ge
  exact hexcl.false (QuotientGroup.quotientBot.trans e)

theorem not_statedPSL_three_two (hnab : ∃ a b : S, a * b ≠ b * a) (Ts : Sylow 2 S)
    {B : Subgroup S} (hB : B ∈ cComp (B ⊔ (Ts : Subgroup S)))
    (hBq : ¬ CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B)) {f : ℕ} (hf : 1 ≤ f)
    (hL : StatedClassicalModel S .PSL 3 2 f) : False := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hL
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hF
  have hexcl :=
    (NQCat.nonquasisimple_local_two_core_quotient_excludes_small_matrix_ambient_quotients
      (⊥ : Subgroup S) IsPGroup.of_bot Ts hB (isQuasisimple_quotient_bot hnab) hBq).2.2.1 F
      (StatedSL 3 F) ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) (fun d hd => by
        obtain ⟨c, hc⟩ := (mem_subgroupOf.mp hd)
        exact ⟨c, hc.symm⟩)
  exact hexcl.false (QuotientGroup.quotientBot.trans e)

theorem not_statedPSp_four_two (hnab : ∃ a b : S, a * b ≠ b * a) (Ts : Sylow 2 S)
    {B : Subgroup S} (hB : B ∈ cComp (B ⊔ (Ts : Subgroup S)))
    (hBq : ¬ CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B)) {f : ℕ} (hf : 1 ≤ f)
    (hSp : StatedClassicalModel S .PSp 2 2 f) : False := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hSp
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hF
  have hexcl :=
    (NQCat.nonquasisimple_local_two_core_quotient_excludes_small_matrix_ambient_quotients
      (⊥ : Subgroup S) IsPGroup.of_bot Ts hB (isQuasisimple_quotient_bot hnab) hBq).2.2.2 F
  exact hexcl.false (QuotientGroup.quotientBot.trans
    (e.trans (CFSG.LieType.SteinbergBR.EvenSp.projEquiv (by norm_num))))

theorem eq_of_statedPSL_three (hPL3 : PrimeLinearThreeAmbientPrime)
    (hnab : ∃ a b : S, a * b ≠ b * a) (Ts : Sylow 2 S) {B : Subgroup S}
    (hB : B ∈ cComp (B ⊔ (Ts : Subgroup S))) (hBq : ¬ CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B))
    {ℓ : ℕ} (hℓ5 : 5 ≤ ℓ) (hL : StatedClassicalModel S .PSL 3 ℓ 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup S} (hXB : X ≤ B) (hXn : (X.subgroupOf B).Normal)
    (hX2 : ∀ (Y : Subgroup ↥X) [Y.Normal], IsPGroup 2 (↥X ⧸ Y) → Y = ⊤)
    (hXp : IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X)) (hXr : CFSG.pRank p (↥X ⧸ CFSG.pCore 2 ↥X) = 2) :
    p = ℓ := by
  obtain ⟨⟨hℓ, -⟩, F, _, _, hF, ⟨e⟩⟩ := hL
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hF' : Nat.card F = ℓ := by rw [hF, pow_one]
  let D : Subgroup (CFSG.Wreathed.OddLinearThreeCentralizerCore.SL3 F) :=
    center (Matrix.SpecialLinearGroup (Fin 3) F)
  have hD : D ≤ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F := by
    intro d hd
    obtain ⟨r, hr, hrd⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hd
    have hr3 : r ^ 3 = 1 := by simpa using hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      norm_num at hr3
    refine ⟨Units.mk0 r hr0, Units.ext (by simpa using hr3), ?_⟩
    rw [← hrd]
    rfl
  have hO2 := pCore_two_eq_bot_of_simple hnab
  let α : S ⧸ CFSG.pCore 2 S ≃* CFSG.Wreathed.OddLinearThreeCentralizerCore.SL3 F ⧸ D :=
    ((QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot).trans
      (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm)
  exact hPL3 F S ℓ hF' hℓ5 D hD α Ts B hB hBq p hp2 X hXB hXn hX2 hXp hXr

end Exclusions

section Main

variable {K : Type} [Group K] [Finite K]

theorem ambient_witness_data
    (hK : CFSG.SectionRank.IsSQTKCat K) (hQ : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    {T A : Subgroup K} (hT : quasithinIsSylowTwo T) (hA : A ∈ cComp (A ⊔ T))
    (hAq : ¬ CFSG.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup K} (hXA : X ≤ A) (hXn : (X.subgroupOf A).Normal)
    (hTX : T ≤ normalizer (X : Set K))
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hXr : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) :
    let Q := K ⧸ CFSG.pCore 2 K
    let η : K →* Q ⧸ center Q :=
      (QuotientGroup.mk' (center Q)).comp (QuotientGroup.mk' (CFSG.pCore 2 K))
    X.map η ≤ A.map η ∧ ((X.map η).subgroupOf (A.map η)).Normal ∧
      (∀ (N : Subgroup (X.map η)) [N.Normal], IsPGroup 2 ((X.map η) ⧸ N) → N = ⊤) ∧
      IsPGroup p ((X.map η) ⧸ CFSG.pCore 2 (X.map η)) ∧
      CFSG.pRank p ((X.map η) ⧸ CFSG.pCore 2 (X.map η)) = 2 ∧
      ∃ U : Subgroup (Q ⧸ center Q), U ≤ X.map η ∧ IsPGroup p U ∧ ¬ IsCyclic U ∧
        (U : Set (Q ⧸ center Q)) * (T.map η : Set (Q ⧸ center Q)) =
          (T.map η : Set (Q ⧸ center Q)) * (U : Set (Q ⧸ center Q)) := by
  intro Q η
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, -, -, -, -, hwit⟩ :=
    NQTerm.quasisimple_two_core_ambient_simple_quotient_retains_original_local_witnesses hK hQ hT
      hA hAq
  obtain ⟨hXbn, -, hXb2, ⟨e, -⟩, hP⟩ := hwit p hp hp5 X hXA hXn hTX hX2 hXp hXr
  obtain ⟨S0⟩ : Nonempty (Sylow p X) := inferInstance
  have hS0 : CFSG.ABGLocalTools.IsSylowOf p ((S0 : Subgroup X).map X.subtype) X := ⟨S0, rfl⟩
  obtain ⟨-, hUp, hUnc, hUT, -, -⟩ := hP _ hS0
  refine ⟨Subgroup.map_mono hXA, hXbn, hXb2, IsPGroup.of_equiv hXp e, ?_,
    _, Subgroup.map_mono (map_subtype_le _), hUp, hUnc, hUT⟩
  rw [← CFSG.LieType.SteinbergBR.RankOneClassifier.pRank_eq_of_mulEquiv e p]
  exact hXr

theorem two_original_prime_witnesses_force_exceptional_simple_ambient_quotient_of
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct) (hPL3 : PrimeLinearThreeAmbientPrime)
    (hK : CFSG.SectionRank.IsSQTKCat K) (hQ : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    {T A : Subgroup K} (hT : quasithinIsSylowTwo T) (hA : A ∈ cComp (A ⊔ T))
    (hAq : ¬ CFSG.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hpq : p ≠ q) {Xp Xq : Subgroup K}
    (hXpA : Xp ≤ A) (hXpn : (Xp.subgroupOf A).Normal) (hTXp : T ≤ normalizer (Xp : Set K))
    (hXp2 : ∀ (N : Subgroup Xp) [N.Normal], IsPGroup 2 (Xp ⧸ N) → N = ⊤)
    (hXpp : IsPGroup p (Xp ⧸ CFSG.pCore 2 Xp)) (hXpr : CFSG.pRank p (Xp ⧸ CFSG.pCore 2 Xp) = 2)
    (hXqA : Xq ≤ A) (hXqn : (Xq.subgroupOf A).Normal) (hTXq : T ≤ normalizer (Xq : Set K))
    (hXq2 : ∀ (N : Subgroup Xq) [N.Normal], IsPGroup 2 (Xq ⧸ N) → N = ⊤)
    (hXqp : IsPGroup q (Xq ⧸ CFSG.pCore 2 Xq)) (hXqr : CFSG.pRank q (Xq ⧸ CFSG.pCore 2 Xq) = 2) :
    let Q := K ⧸ CFSG.pCore 2 K
    (∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel (Q ⧸ center Q) .G2 2 f) ∨
      (∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel (Q ⧸ center Q) .trialityD4 2 f) ∨
      (∃ a : ℕ, 1 ≤ a ∧ ReeTitsModel (Q ⧸ center Q) .twistedF4 2 (2 * a + 1)) ∨
      ReeTitsModel (Q ⧸ center Q) .Tits 2 1 := by
  intro Q
  obtain ⟨⟨hsimple, hnab⟩, hcat, hsqt, -, hTb, hAb, hAbq, -⟩ :=
    NQTerm.quasisimple_two_core_ambient_simple_quotient_retains_original_local_witnesses hK hQ hT
      hA hAq
  have := hsimple
  set η : K →* Q ⧸ center Q :=
    (QuotientGroup.mk' (center Q)).comp (QuotientGroup.mk' (CFSG.pCore 2 K)) with hη
  let Ts : Sylow 2 (Q ⧸ center Q) := hTb.1.toSylow hTb.2
  have hBS : A.map η ∈ cComp (A.map η ⊔ (Ts : Subgroup (Q ⧸ center Q))) := hAb
  obtain ⟨hXpB, hXpbn, hXpb2, hXpbp, hXpbr, Up, -, hUp, hUpnc, hUpT⟩ :=
    ambient_witness_data hK hQ hT hA hAq hp hp5 hXpA hXpn hTXp hXp2 hXpp hXpr
  obtain ⟨hXqB, hXqbn, hXqb2, hXqbp, hXqbr, Uq, -, hUq, hUqnc, hUqT⟩ :=
    ambient_witness_data hK hQ hT hA hAq hq hq5 hXqA hXqn hTXq hXq2 hXqp hXqr
  rcases hCat (Q ⧸ center Q) hnab hcat hsqt p hp hp5 Ts Up hUp hUpnc hUpT with
    ⟨ℓ, -, hℓ5, hPSL | hPSU⟩ | ⟨f, hf3, hPSL2⟩ | ⟨f, hf2, hSp⟩ | hexc | hree | ⟨⟨eJ⟩, hp11⟩
  · exfalso
    have h1 := eq_of_statedPSL_three hPL3 hnab Ts hBS hAbq hℓ5 hPSL hp (by omega) hXpB hXpbn
      hXpb2 hXpbp hXpbr
    have h2 := eq_of_statedPSL_three hPL3 hnab Ts hBS hAbq hℓ5 hPSL hq (by omega) hXqB hXqbn
      hXqb2 hXqbp hXqbr
    exact hpq (h1.trans h2.symm)
  · exact (not_statedPSU_three hnab Ts hBS hAbq hPSU).elim
  · exact (not_statedPSL_three_two hnab Ts hBS hAbq (by omega) hPSL2).elim
  · exact (not_statedPSp_four_two hnab Ts hBS hAbq (by omega) hSp).elim
  · rcases hexc with hG2 | hD4
    · exact Or.inl hG2
    · exact Or.inr (Or.inl hD4)
  · rcases hree with hF4 | hTits
    · exact Or.inr (Or.inr (Or.inl hF4))
    · exact Or.inr (Or.inr (Or.inr hTits))
  · exfalso
    have hsq := (sq_dvd_card_of_not_isCyclic' hq hUq hUqnc).trans
      (Subgroup.card_subgroup_dvd_card Uq)
    rw [Nat.card_congr eJ.toEquiv, CFSG.Sporadic.J4.card_J4] at hsq
    exact hpq (hp11.trans (CFSG.RankThree.PartOne.eq_eleven_of_sq_dvd_card_J4 hq hq5 hsq).symm)

@[expose] def StmtQuasisimpleAmbientOneRankTwoPrime : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.SectionRank.IsSQTKCat K →
    CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) → ∀ T A : Subgroup K, quasithinIsSylowTwo T →
    A ∈ cComp (A ⊔ T) → ¬ CFSG.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A) → ∀ p q : ℕ, p.Prime →
    q.Prime → 5 ≤ p → 5 ≤ q → ∀ Xp Xq : Subgroup K,
    Xp ≤ A → (Xp.subgroupOf A).Normal → T ≤ normalizer (Xp : Set K) →
    (∀ (N : Subgroup Xp) [N.Normal], IsPGroup 2 (Xp ⧸ N) → N = ⊤) →
    IsPGroup p (Xp ⧸ CFSG.pCore 2 Xp) → CFSG.pRank p (Xp ⧸ CFSG.pCore 2 Xp) = 2 →
    Xq ≤ A → (Xq.subgroupOf A).Normal → T ≤ normalizer (Xq : Set K) →
    (∀ (N : Subgroup Xq) [N.Normal], IsPGroup 2 (Xq ⧸ N) → N = ⊤) →
    IsPGroup q (Xq ⧸ CFSG.pCore 2 Xq) → CFSG.pRank q (Xq ⧸ CFSG.pCore 2 Xq) = 2 → p = q

end Main

end CFSG.Quasithin.H13.NQBlock
