module

public import CFSG.RankThree.PartTwo.Sec16.Item16Statements
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec16.Item162Proof
import CFSG.RankThree.PartTwo.Sec16.Item163ProofY4
import CFSG.RankThree.PartTwo.Sec16.Item164Proof
import CFSG.RankThree.PartTwo.Sec16.Item169HJ
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
public import CFSG.RankThree.PartTwo.Sec15.Item1512
public import CFSG.RankThree.PartTwo.Sec15.Item153
public import CFSG.Sporadic.J2
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

section Vocabulary

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Case1514Three (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L Y : Subgroup G) : Prop :=
  (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSU 3 5 1)) ∧
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∧
    Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ omegaA A = {Subgroup.zpowers c} ∧
    (∀ Y₀ ∈ scriptY0Star A LB, ¬ L ≤ Y₀) ∧ IsSimpleGroup ↥L ∧
    Odd (Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer (L : Set G)))

@[expose] def IsL3TwoPow (L : Subgroup G) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n

@[expose] def QTwoNe (A : Subgroup G) (Y₁ Y₂ : Subgroup G) : Prop :=
  ∃ Q ∈ scriptQPi A (lB A)
    (Subgroup.normalizer (Y₁ : Set G) ⊓ Subgroup.normalizer (Y₂ : Set G)) (piOf 2), Q ≠ ⊥

@[expose] def GoodR163 (A L R : Subgroup G) : Prop :=
  R ∈ scriptQPi A (lB A) ⊤ (piOf 2) ∧ xA A ≤ Subgroup.normalizer (R : Set G) ∧
    CFSG.Open.pCoreOf 2 (R ⊔ L) ≠ ⊥

end Vocabulary

@[expose] def Step163U35 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      ¬ Case1514Three A (lB A) c L Y

@[expose] def Step163Pt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    (∀ (a : G) (La Y : Subgroup G), Subgroup.zpowers a ∈ omegaA A → La ∈ lA A a →
      Y ∈ scriptY0Star A (lB A) → MeetsY4 A (lB A) La Y → ¬ Case1514Three A (lB A) a La Y) →
    ∀ Y ∈ scriptY0Star A (lB A), ∃ (a : G) (La : Subgroup G), Subgroup.zpowers a ∈ omegaA A ∧
      La ∈ lA A a ∧ La = (Y ⊓ La) ⊔ CFSG.Open.pCoreOf 2 La

@[expose] def Step163Ya : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), ∀ (a : G) (La : Subgroup G),
      Subgroup.zpowers a ∈ omegaA A → La ∈ lA A a →
      La = (Y ⊓ La) ⊔ CFSG.Open.pCoreOf 2 La → CFSG.Open.pCoreOf 2 La ≠ ⊥ →
        ∃ Ya ∈ scriptY0Star A (lB A), La ≤ Ya ∧ (Ya ≠ Y → QTwoNe A Ya Y)

@[expose] def Step163Meets : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), L ≤ Y → MeetsY4 A (lB A) L Y

@[expose] def Step163A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → omegaA A ≠ {Subgroup.zpowers c} →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    WStarS4 A → TransOmegaThree A c →
    ∀ Y ∈ scriptY0Star A (lB A),
      (∃ (a : G) (La : Subgroup G), Subgroup.zpowers a ∈ omegaA A ∧ La ∈ lA A a ∧ La ≤ Y) →
        IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))

@[expose] def Step163A10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → omegaA A ≠ {Subgroup.zpowers c} →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    WStarS4 A → TransOmegaThree A c →
    ∀ Y ∈ scriptY0Star A (lB A),
      (∃ (a : G) (La : Subgroup G), Subgroup.zpowers a ∈ omegaA A ∧ La ∈ lA A a ∧ La ≤ Y) →
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) →
        ∀ F ∈ omegaA A, ∀ F' ∈ omegaA A,
          ∃ y ∈ Y ⊓ Subgroup.normalizer (A : Set G), F' = F.map (MulAut.conj y).toMonoidHom

@[expose] def Step163Q2TwoPow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → (∀ Y ∈ scriptY0Star A (lB A), L ≤ Y) → CFSG.Open.pCoreOf 2 L = ⊥ →
      IsL3TwoPow L → ∀ Y₁ ∈ scriptY0Star A (lB A), ∀ Y₂ ∈ scriptY0Star A (lB A), Y₁ ≠ Y₂ →
        QTwoNe A Y₁ Y₂

@[expose] def Step163Delta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → (∀ Y ∈ scriptY0Star A (lB A), L ≤ Y) →
    ∀ Y ∈ scriptY0Star A (lB A), ∀ R : Subgroup G, GoodR163 A L R →
      R ≤ Subgroup.normalizer (Y : Set G) →
        delta A (lB A) (Subgroup.normalizer (CFSG.Open.pCoreOf 2 (R ⊔ L) : Set G)) ≤
          Subgroup.normalizer (Y : Set G)

section Tools

variable {G : Type} [Group G] [Finite G]

theorem xA_mem_scriptQ {A : Subgroup G} (hA : IsMulCommutative A) :
    xA A ∈ scriptQ A (lB A) := by
  have h := pPrimeCoreOf_centralizer_inf_mem_scriptQ (LB := lB A) hA (Y := ⊤) (fun a _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp)
  rwa [inf_top_eq] at h

omit [Finite G] in
theorem map_conj_xA {A : Subgroup G} {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G)) :
    (xA A).map (MulAut.conj w).toMonoidHom = xA A := by
  change (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))).map (MulAut.conj w).toMonoidHom =
    pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  rw [map_pPrimeCoreOf, map_conj_centralizer, Late.map_conj_eq_of_mem_normalizer hw]

theorem three_dvd_card_of_mem_lA {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    {a : G} {La : Subgroup G} (ha : Subgroup.zpowers a ∈ omegaA A) (hLa : La ∈ lA A a) :
    3 ∣ Nat.card La := by
  have hq : 3 ∣ Nat.card (↥La ⧸ aschbacherSolvableCore 3 ↥La) → 3 ∣ Nat.card La :=
    fun h3 => h3.trans (Subgroup.card_quotient_dvd_card _)
  rcases (h.chosen136.2 a ha La hLa).1 with hJ | ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact three_dvd_card_of_j2 hJ
  · rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · exact hq (KFacts.three_dvd_card_of_mulEquiv_projSL φ)
    · exact hq (KFacts.three_dvd_card_of_mulEquiv_projSU (by omega) φ)
  · apply hq
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    norm_num
  · apply hq
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22]
    norm_num
  · apply hq
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12]
    norm_num

theorem xA_le_normalizer_of_mem_lA {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) {a : G} {La : Subgroup G} (ha : Subgroup.zpowers a ∈ omegaA A)
    (hLa : La ∈ lA A a) : xA A ≤ Subgroup.normalizer (La : Set G) := by
  have ha' : Sec15R G A a La := sec15R_of_point h ha hLa
  exact (xA_le_normalizer_zpowers ha'.mem_A).trans
    (normalizer_zpowers_le_normalizer_L ha' (three_dvd_card_of_mem_lA h ha hLa))

theorem map_conj_eq_of_zpowers {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    {a : G} {La : Subgroup G} (ha : Subgroup.zpowers a ∈ omegaA A) (hLa : La ∈ lA A a) {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G))
    (hcw : Subgroup.zpowers c = (Subgroup.zpowers a).map (MulAut.conj w).toMonoidHom) :
    La.map (MulAut.conj w).toMonoidHom = L := by
  have hLw : La.map (MulAut.conj w).toMonoidHom ∈ lA A (w * a * w⁻¹) :=
    (map_conj_mem_lA_iff hw).mpr hLa
  have hz : Subgroup.zpowers (w * a * w⁻¹) = Subgroup.zpowers c := by
    rw [hcw, MonoidHom.map_zpowers]
    rfl
  have hLc : La.map (MulAut.conj w).toMonoidHom ∈ thetaComponentsAt 3 c := by
    have := hLw.1
    rwa [thetaComponentsAt_eq_thetaComponentsIn, centralizer_singleton_eq_of_zpowers_eq hz,
      ← thetaComponentsAt_eq_thetaComponentsIn] at this
  have h3 : 3 ∣ Nat.card (La.map (MulAut.conj w).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact three_dvd_card_of_mem_lA h ha hLa
  exact (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 _ hLc h3

theorem eq_of_zpowers_eq {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    {a : G} {La : Subgroup G} (ha : Subgroup.zpowers a ∈ omegaA A) (hLa : La ∈ lA A a)
    (hac : Subgroup.zpowers a = Subgroup.zpowers c) : La = L := by
  have h1 := map_conj_eq_of_zpowers h ha hLa (one_mem _)
    (by rw [Late.map_conj_one, hac])
  rwa [Late.map_conj_one] at h1

omit [Finite G] in
theorem le_of_eq_map_conj {La Y Ya : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (La : Set G)) (hYa : Ya = Y.map (MulAut.conj x).toMonoidHom)
    (hLa : La ≤ Ya) : La ≤ Y := by
  have h1 : La.map (MulAut.conj x).toMonoidHom ≤ Y.map (MulAut.conj x).toMonoidHom := by
    rw [Late.map_conj_eq_of_mem_normalizer hx, ← hYa]
    exact hLa
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj x).injective).mp h1

theorem map_conj_mem_scriptY4 {A : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) {Y : Subgroup G}
    (hY : Y ∈ scriptY4 A (lB A)) : Y.map (MulAut.conj w).toMonoidHom ∈ scriptY4 A (lB A) := by
  obtain ⟨hYY, h3, hΔ, hq⟩ := hY
  refine ⟨Sec17.HeadProof.map_conj_mem_scriptY hw hYY, ?_, ?_, ?_⟩
  · rw [← Sec17.HeadProof.map_oPrimeResidualOf, ← h3]
  · rw [← Sec17.HeadProof.map_conj_delta hw, ← hΔ]
  · set e : ↥Y ≃* ↥(Y.map (MulAut.conj w).toMonoidHom) :=
      Y.equivMapOfInjective _ (MulAut.conj w).injective
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)) hq

theorem map_conj_mem_scriptY0 {A : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0 A (lB A)) : Y.map (MulAut.conj w).toMonoidHom ∈ scriptY0 A (lB A) := by
  refine ⟨map_conj_mem_scriptY4 hw hY.1, Sec17.HeadProof.map_conj_mem_scriptY hw hY.2.1, ?_⟩
  rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
  exact fun h0 => hY.2.2 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj w).injective).mp h0)

theorem map_conj_mem_scriptY0Star {A : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) :
    Y.map (MulAut.conj w).toMonoidHom ∈ scriptY0Star A (lB A) :=
  Late.maximal_map_conj (W := Subgroup.normalizer (A : Set G))
    (fun _ hS _ hv => map_conj_mem_scriptY0 hv hS) hY hw

theorem exists_qStar_le_normalizer {A : Subgroup G} (h153 : Item153Main A (lB A))
    (hobs : Claim153Obs A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) :
    ∃ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), S ≤ Subgroup.normalizer (Y : Set G) := by
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  have hbot : (⊥ : Subgroup G) ∈ scriptQPi A (lB A) (Subgroup.normalizer (X : Set G))
      (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2))) hbot
  exact ⟨S, ((h153 Y hY).2.1 S hS).1, hobs Y hY S hS⟩

theorem exists_conj_le_normalizer {A : Subgroup G} (h1411 : Item1411_1 A (lB A))
    {Y S₀ : Subgroup G} (hS₀ : S₀ ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hS₀Y : S₀ ≤ Subgroup.normalizer (Y : Set G)) {R : Subgroup G}
    (hR : R ∈ scriptQPi A (lB A) ⊤ (piOf 2)) :
    ∃ w ∈ Subgroup.normalizer (A : Set G),
      R ≤ Subgroup.normalizer ((Y.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) := by
  obtain ⟨T, hRT, hT⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) hR
  obtain ⟨w, hw, rfl⟩ := h1411 S₀ hS₀ T hT
  refine ⟨w, (Subgroup.mem_inf.mp hw).1, hRT.trans ?_⟩
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hS₀Y

theorem xA_le_delta_normalizer {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    {R : Subgroup G} (hXR : xA A ≤ Subgroup.normalizer (R : Set G)) :
    xA A ≤ delta A (lB A) (Subgroup.normalizer (CFSG.Open.pCoreOf 2 (R ⊔ L) : Set G)) := by
  have hXL : xA A ≤ Subgroup.normalizer (L : Set G) :=
    xA_le_normalizer_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA
  refine le_delta (xA_mem_scriptQ h.isElemAbelian.1) ?_
  exact (le_normalizer_sup hXR hXL).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem qTwoNe_of_scriptQPi {A L Y₁ Y₂ : Subgroup G}
    (hQ : ∃ Q ∈ scriptQPi A (lB A) L (piOf 2), Q ≠ ⊥) (h₁ : L ≤ Y₁) (h₂ : L ≤ Y₂) :
    QTwoNe A Y₁ Y₂ := by
  obtain ⟨Q, hQ, hQ1⟩ := hQ
  exact ⟨Q, ⟨⟨hQ.1.1, le_inf (hQ.1.2.trans (h₁.trans Subgroup.le_normalizer))
    (hQ.1.2.trans (h₂.trans Subgroup.le_normalizer))⟩, hQ.2⟩, hQ1⟩

theorem goodR163_bot {A L : Subgroup G} (hO : CFSG.Open.pCoreOf 2 L ≠ ⊥) :
    GoodR163 A L ⊥ := by
  refine ⟨⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
    (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩,
    (bot_mem_invariantPiSubgroups ⊤ (xA A) (piOf 2)).2.2, ?_⟩
  · rw [bot_inf_eq]
    exact bot_le
  · rwa [bot_sup_eq]

theorem pCoreOf_mem_scriptQPi {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hQ : ∀ Q ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), Q ∈ scriptQ A (lB A)) :
    CFSG.Open.pCoreOf 2 L ∈ scriptQPi A (lB A) L (piOf 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L
  have hOL : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hAO : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    h.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have h3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 L) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hmem : CFSG.Open.pCoreOf 2 L ∈
      invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piCompl 3) :=
    ⟨hOL.trans (h.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)),
      (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr h3, hAO⟩
  exact ⟨⟨hQ _ hmem, hOL⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr h2⟩

theorem mem_scriptQ_of_concl142 {A : Subgroup G} (h142 : Concl142 A (lB A)) {c : G}
    (hc : Subgroup.zpowers c ∈ omegaA A) {Q : Subgroup G}
    (hQ : Q ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) : Q ∈ scriptQ A (lB A) := by
  obtain ⟨Q', hQ', hQQ'⟩ := exists_le_mem_maxInvariantPiSubgroups hQ
  exact mem_scriptQ_of_le (h142 c hc Q' hQ').1 hQQ' hQ.2.2

theorem exists_scriptQPi_two_of_j2
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ Q ∈ scriptQPi A (lB A) L (piOf 2), Q ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨-, h9, hAeq⟩ := j2_point_facts hD hJ
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  have hT3 : IsPGroup 3 (A.subgroupOf L) :=
    hA3.comap_of_ker_isPGroup L.subtype (IsPGroup.ker_isPGroup_of_injective L.subtype_injective)
  obtain ⟨S, hAS⟩ := hT3.exists_le_sylow
  set P := S.mapSurjective hπs with hP
  set Ab := (A.subgroupOf L).map π with hAb
  have hEP : Ab ≤ (P : Subgroup (↥L ⧸ θ)) := by
    rw [hP, Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hAS
  have hE9 : Nat.card Ab = 9 := by
    rw [hAb, hπ, card_map_mk_subgroupOf hD.isElemAbelian, h9]
  obtain ⟨-, -, -, -, h5⟩ := h415 (↥L ⧸ θ) hJ P _ rfl _ rfl
  obtain ⟨Sb, hSb, -, -, ⟨T, ⟨e⟩⟩, -⟩ := h5 Ab ⟨hEP, hE9⟩
  have hL34c : Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) = 20160 := by
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 2)
    rw [GaloisField.card 2 2 (by norm_num)] at hc
    norm_num at hc
    omega
  have : Finite (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hL34c]; norm_num)
  have hL34 : 2 ∣ Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
    rw [hL34c]
    norm_num
  have h2Sb : 2 ∣ Nat.card Sb := by
    rw [Nat.card_congr e.toEquiv]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T.isPGroup'
    have h1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr (T.ne_bot_of_dvd_card hL34)
    rw [hk] at h1 ⊢
    rcases k with _ | k
    · simp at h1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  have hSb2 : IsPGroup 2 Sb := (isPiSubgroup_piOf_iff Nat.prime_two Sb).mp hSb.prop.2.1
  set K := Sb.comap π with hK
  have h2K : 2 ∣ Nat.card K := by
    refine h2Sb.trans ?_
    have hmap : K.map π = Sb := Subgroup.map_comap_eq_self_of_surjective hπs Sb
    rw [← hmap]
    exact Subgroup.card_map_dvd K π
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro h3
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hπk : π k ∈ Sb := k.2
    have hk3 : (k : ↥L) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hk, pow_orderOf_eq_one, Subgroup.coe_one]
    have hπ1 : π (k : ↥L) = 1 := by
      obtain ⟨n, hn⟩ := hSb2 ⟨π k, hπk⟩
      have hn' : (π (k : ↥L)) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have ho1 : orderOf (π (k : ↥L)) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
      have ho2 : orderOf (π (k : ↥L)) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk3, map_one])
      exact orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left n (by norm_num)) ho1 ho2)
    have hkθ : (k : ↥L) ∈ θ := by
      rw [← QuotientGroup.eq_one_iff]
      exact hπ1
    have hk1 : (k : ↥L) = 1 := eq_one_of_mem_aschbacherSolvableCore hkθ hk3
    have : orderOf k = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext hk1
    omega
  set KG := K.map L.subtype with hKG
  have hKGL : KG ≤ L := Subgroup.map_subtype_le K
  have hcKG : Nat.card KG = Nat.card K := Subgroup.card_map_of_injective L.subtype_injective
  have hAKG : A ≤ Subgroup.normalizer (KG : Set G) := by
    rw [hAeq]
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
      exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer (hKGL hx))
    · intro b hb
      obtain ⟨hbA, hbL⟩ := Subgroup.mem_inf.mp hb
      have hbAb : π ⟨b, hbL⟩ ∈ Ab :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hbA)
      have hbN : (⟨b, hbL⟩ : ↥L) ∈ Subgroup.normalizer (K : Set ↥L) :=
        Subgroup.le_normalizer_comap π (show π ⟨b, hbL⟩ ∈ _ from hSb.prop.2.2 hbAb)
      exact Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype hbN)
  obtain ⟨R, hRKG, hR2, hAR, hRcard⟩ := Sec17.HeadProof.exists_invariant_sylow hA3
    (by rwa [hcKG]) hAKG Nat.prime_two
  have hR1 : R ≠ ⊥ := by
    intro h0
    have hpos : 0 < (Nat.card KG).factorization 2 :=
      Nat.prime_two.factorization_pos_of_dvd Nat.card_pos.ne' (by rwa [hcKG])
    rw [h0, Subgroup.card_bot] at hRcard
    have : 2 ≤ 2 ^ (Nat.card KG).factorization 2 :=
      Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hpos) 2
    omega
  have hRL : R ≤ L := hRKG.trans hKGL
  have hR3 : ¬ 3 ∣ Nat.card R := fun h3 =>
    hK3 (by rw [← hcKG]; exact h3.trans (Subgroup.card_dvd_of_le hRKG))
  have hRH : R ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3) :=
    ⟨hRL.trans (hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)),
      (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩
  exact ⟨R, ⟨⟨(mem_scriptQ_of_hj_point h.toSec14Std hJ hRH).1, hRL⟩,
    (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2⟩, hR1⟩

end Tools

section Cover

variable {G : Type} [Group G] [Finite G]

theorem le_of_cover {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h162 : Item162 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) {a : G}
    {La : Subgroup G} (ha : Subgroup.zpowers a ∈ omegaA A) (hLa : La ∈ lA A a)
    (hcov : La = (Y ⊓ La) ⊔ CFSG.Open.pCoreOf 2 La)
    (hYa : CFSG.Open.pCoreOf 2 La ≠ ⊥ →
      ∃ Ya ∈ scriptY0Star A (lB A), La ≤ Ya ∧ (Ya ≠ Y → QTwoNe A Ya Y)) : La ≤ Y := by
  by_cases hO : CFSG.Open.pCoreOf 2 La = ⊥
  · rw [hcov, hO, sup_bot_eq]
    exact inf_le_left
  · obtain ⟨Ya, hYa', hLYa, hQ⟩ := hYa hO
    by_cases hYY : Ya = Y
    · exact hYY ▸ hLYa
    · obtain ⟨x, hx, hxY⟩ := h162 Ya hYa' Y hY (hQ hYY)
      exact le_of_eq_map_conj (xA_le_normalizer_of_mem_lA h ha hLa hx) hxY hLYa

end Cover

section FourFive

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem transOmegaThree_of_conj {A : Subgroup G} {a c w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) (hT : TransOmegaThree A a)
    (hcw : Subgroup.zpowers c = (Subgroup.zpowers a).map (MulAut.conj w).toMonoidHom) :
    TransOmegaThree A c := by
  refine ⟨hT.1, fun F hF => ?_⟩
  obtain ⟨v, hv, rfl⟩ := hT.2 F hF
  refine ⟨v * w⁻¹, mul_mem hv (inv_mem hw), ?_⟩
  rw [hcw, Late.map_conj_map_conj, mul_assoc, inv_mul_cancel, mul_one]

theorem nonempty_a7_of_map_conj {La L : Subgroup G} {w : G}
    (hw : La.map (MulAut.conj w).toMonoidHom = L)
    (h7 : Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* alternatingGroup (Fin 7))) :
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨φ⟩ := h7
  have h : Nonempty (↥(La.map (MulAut.conj w).toMonoidHom) ⧸
      aschbacherSolvableCore 3 ↥(La.map (MulAut.conj w).toMonoidHom) ≃*
        alternatingGroup (Fin 7)) := ⟨(thetaQuotEquiv (MulAut.conj w) La).symm.trans φ⟩
  rwa [hw] at h

theorem le_and_a10_of_ne {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h1514 : ∀ (c' : G) (L' : Subgroup G), Sec15R G A c' L' → Item1514 A (lB A) c' L')
    (hMeets : Step163Meets) (hA7 : Step163A7) (hA10 : Step163A10) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) {a : G} {La : Subgroup G}
    (ha : Subgroup.zpowers a ∈ omegaA A) (hLa : La ∈ lA A a) (hLaY : La ≤ Y)
    (hac : Subgroup.zpowers a ≠ Subgroup.zpowers c) :
    L ≤ Y ∧ Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) := by
  have hΩ : omegaA A ≠ {Subgroup.zpowers c} := fun hΩ => hac (by
    have := hΩ ▸ ha
    exact this)
  have ha' : Sec15R G A a La := sec15R_of_point h ha hLa
  have hm : MeetsY4 A (lB A) La Y := hMeets G A a La ha' Y hY hLaY
  have hpt : ∃ (a' : G) (La' : Subgroup G), Subgroup.zpowers a' ∈ omegaA A ∧ La' ∈ lA A a' ∧
      La' ≤ Y := ⟨a, La, ha, hLa, hLaY⟩
  have hne : omegaA A ≠ {Subgroup.zpowers a} := fun hΩa => hac (by
    have := hΩa ▸ h.zpowers_mem_omegaA
    exact (Set.mem_singleton_iff.mp this).symm)
  rcases h1514 a La ha' Y hY hm with ⟨-, -, hΩa, -⟩ | ⟨h7, hW, hT, hY'⟩ | ⟨-, -, -, hΩa, -⟩
  · exact absurd hΩa hne
  · obtain ⟨w, hw, hcw⟩ := hT.2 (Subgroup.zpowers c) h.zpowers_mem_omegaA
    have hLw : La.map (MulAut.conj w).toMonoidHom = L := map_conj_eq_of_zpowers h ha hLa hw hcw
    have h7L := nonempty_a7_of_map_conj hLw h7
    have hTc : TransOmegaThree A c := transOmegaThree_of_conj hw hT hcw
    rcases hY' with ⟨⟨φ⟩⟩ | hY10
    · exact ((hA7 G A c L h hΩ h7L hW hTc Y hY hpt).false φ).elim
    · obtain ⟨y, hy, hcy⟩ := hA10 G A c L h hΩ h7L hW hTc Y hY hpt hY10 _ ha _
        h.zpowers_mem_omegaA
      have hLy : La.map (MulAut.conj y).toMonoidHom = L :=
        map_conj_eq_of_zpowers h ha hLa (Subgroup.mem_inf.mp hy).2 hcy
      refine ⟨?_, hY10⟩
      rw [← hLy, ← Late.map_conj_eq_of_mem_normalizer
        (Subgroup.le_normalizer (Subgroup.mem_inf.mp hy).1)]
      exact Subgroup.map_mono hLaY
  · exact absurd hΩa hne

theorem a10_or_of_le {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h1514 : Item1514 A (lB A) c L) (hMeets : Step163Meets) (hA7 : Step163A7)
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hLY : L ≤ Y) :
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) ∨
      omegaA A = {Subgroup.zpowers c} := by
  by_cases hΩ : omegaA A = {Subgroup.zpowers c}
  · exact Or.inr hΩ
  have hm : MeetsY4 A (lB A) L Y := hMeets G A c L h Y hY hLY
  rcases h1514 Y hY hm with ⟨-, -, hΩ', -⟩ | ⟨h7, hW, hT, hY'⟩ | ⟨-, -, -, hΩ', -⟩
  · exact absurd hΩ' hΩ
  · rcases hY' with ⟨⟨φ⟩⟩ | hY10
    · exact ((hA7 G A c L h hΩ h7 hW hT Y hY
        ⟨c, L, h.zpowers_mem_omegaA, h.mem_lA, hLY⟩).false φ).elim
    · exact Or.inl hY10
  · exact absurd hΩ' hΩ

theorem rank3II_16_3_four_five_of {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L)
    (h1514 : ∀ (c' : G) (L' : Subgroup G), Sec15R G A c' L' → Item1514 A (lB A) c' L')
    (h162 : Item162 A (lB A)) (hU35 : Step163U35) (hPt : Step163Pt) (hYa : Step163Ya)
    (hMeets : Step163Meets) (hA7 : Step163A7) (hA10 : Step163A10) :
    ∀ Y ∈ scriptY0Star A (lB A), L ≤ Y ∧
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) ∨
        omegaA A = {Subgroup.zpowers c}) := by
  intro Y hY
  have hP1 : ∀ (a : G) (La Y' : Subgroup G), Subgroup.zpowers a ∈ omegaA A → La ∈ lA A a →
      Y' ∈ scriptY0Star A (lB A) → MeetsY4 A (lB A) La Y' →
        ¬ Case1514Three A (lB A) a La Y' :=
    fun a La Y' ha hLa hY' hm => hU35 G A a La (sec15R_of_point h ha hLa) Y' hY' hm
  obtain ⟨a, La, ha, hLa, hcov⟩ := hPt G A c L h hP1 Y hY
  have hLaY : La ≤ Y := le_of_cover h h162 hY ha hLa hcov (hYa G A c L h Y hY a La ha hLa hcov)
  by_cases hac : Subgroup.zpowers a = Subgroup.zpowers c
  · have hLaL : La = L := eq_of_zpowers_eq h ha hLa hac
    subst hLaL
    exact ⟨hLaY, a10_or_of_le h (h1514 c La h) hMeets hA7 hY hLaY⟩
  · obtain ⟨hLY, h10⟩ := le_and_a10_of_ne h h1514 hMeets hA7 hA10 hY ha hLa hLaY hac
    exact ⟨hLY, Or.inl h10⟩

theorem le_of_j2
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1514 : ∀ (c' : G) (L' : Subgroup G), Sec15R G A c' L' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Item1514 A (lB A) c' L')
    (h1523 : Item1523 A (lB A) L) (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (h1411 : Item1411_1 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) :
    L ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  obtain ⟨φJ⟩ := hJ
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set O := CFSG.Open.pCoreOf 2 L with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L
  have hOL : O ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLH : L ≤ H := hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hHO : H ≤ Subgroup.normalizer (O : Set G) :=
    (normalizer_zpowers_le_normalizer_L h (three_dvd_card_of_j2 ⟨φJ⟩)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hD.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hbot : (⊥ : Subgroup G) ∈ scriptQPi A (lB A) H (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨T₀, -, hT₀⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) H (piOf 2))) hbot
  have hT₀2 : IsPGroup 2 T₀ := isPGroup_of_mem_scriptQPi Nat.prime_two hT₀.prop
  have hT₀H : T₀ ≤ H := hT₀.prop.1.2
  have hs2 : IsPGroup 2 ↥(T₀ ⊔ O) := IsPGroup.to_sup_of_normal_right' hT₀2 hO2 (hT₀H.trans hHO)
  have hs3 : ¬ 3 ∣ Nat.card ↥(T₀ ⊔ O) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hs2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hsH : T₀ ⊔ O ≤ H := sup_le hT₀H (hOL.trans hLH)
  have hsQ : T₀ ⊔ O ∈ scriptQPi A (lB A) H (piOf 2) :=
    ⟨⟨(mem_scriptQ_of_hj_point h.toSec14Std ⟨φJ⟩ ⟨hsH,
      (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr hs3,
      le_normalizer_sup hT₀.prop.1.1.1.2.2 hAO⟩).1, hsH⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hs2⟩
  have hOT : O ≤ T₀ := le_sup_right.trans (hT₀.2 hsQ le_sup_left)
  obtain ⟨S', hT₀S', hS'⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) (a := T₀) ⟨⟨hT₀.prop.1.1, le_top⟩, hT₀.prop.2⟩
  obtain ⟨S₀, hS₀, hS₀Y⟩ := exists_qStar_le_normalizer h153 hobs hY
  obtain ⟨w, hw, rfl⟩ := h1411 S₀ hS₀ S' hS'
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
  set Y' := Y.map (MulAut.conj w).toMonoidHom with hY'def
  have hY' : Y' ∈ scriptY0Star A (lB A) := map_conj_mem_scriptY0Star hwA hY
  have hT₀Y' : T₀ ≤ Subgroup.normalizer (Y' : Set G) := by
    refine hT₀S'.trans ?_
    rw [hY'def, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hS₀Y
  obtain ⟨-, hcov⟩ := h1523 ⟨φJ⟩ Y' hY'
  have hLN : L ≤ Subgroup.normalizer (Y' : Set G) :=
    calc L = (Y' ⊓ L) ⊔ O := hcov
      _ ≤ Subgroup.normalizer (Y' : Set G) :=
        sup_le (inf_le_left.trans Subgroup.le_normalizer) (hOT.trans hT₀Y')
  have h3 : 3 ∣ Nat.card ↥(L ⊓ Y') := by
    have hdvd : Nat.card L ∣ Nat.card ↥(Y' ⊓ L) * Nat.card O := by
      conv_lhs => rw [hcov]
      exact card_sup_dvd_card_mul (inf_le_right.trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
    have hcop : Nat.Coprime 3 (Nat.card O) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
      rw [hn]
      exact Nat.Coprime.pow_right _ (by norm_num)
    rw [inf_comm]
    exact hcop.dvd_of_dvd_mul_right ((three_dvd_card_of_j2 ⟨φJ⟩).trans hdvd)
  have hsimp : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    exact φJ.isSimpleGroup
  have hLY' : L ≤ Y' := le_of_le_normalizer_of_theta
    (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) hsimp hLN h3
  have hLaY : L.map (MulAut.conj w⁻¹).toMonoidHom ≤ Y := by
    have := Subgroup.map_mono (f := (MulAut.conj w⁻¹).toMonoidHom) hLY'
    rwa [hY'def, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one] at this
  have ha : Subgroup.zpowers (w⁻¹ * c * w⁻¹⁻¹) ∈ omegaA A := by
    have := (map_conj_mem_omegaA_iff (inv_mem hwA)).mpr h.zpowers_mem_omegaA
    rwa [MonoidHom.map_zpowers] at this
  have hLa : L.map (MulAut.conj w⁻¹).toMonoidHom ∈ lA A (w⁻¹ * c * w⁻¹⁻¹) :=
    (map_conj_mem_lA_iff (inv_mem hwA)).mpr h.mem_lA
  by_cases hac : Subgroup.zpowers (w⁻¹ * c * w⁻¹⁻¹) = Subgroup.zpowers c
  · rw [← eq_of_zpowers_eq h ha hLa hac]
    exact hLaY
  · exfalso
    have hJa : Nonempty (↥(L.map (MulAut.conj w⁻¹).toMonoidHom) ⧸
        aschbacherSolvableCore 3 ↥(L.map (MulAut.conj w⁻¹).toMonoidHom) ≃*
          CFSG.Blueprint.NativeSporadic.J2) :=
      ⟨(thetaQuotEquiv (MulAut.conj w⁻¹) L).symm.trans φJ⟩
    have ha' := sec15R_of_point h ha hLa
    have hm : MeetsY4 A (lB A) (L.map (MulAut.conj w⁻¹).toMonoidHom) Y :=
      ⟨_, map_conj_mem_scriptY4 (inv_mem hwA) (mem_scriptY4_of_j2 h ⟨φJ⟩ h1523 hY' hLY'),
        le_inf le_rfl hLaY⟩
    have hne : omegaA A ≠ {Subgroup.zpowers (w⁻¹ * c * w⁻¹⁻¹)} := fun hΩ => hac (by
      have := hΩ ▸ h.zpowers_mem_omegaA
      exact (Set.mem_singleton_iff.mp this).symm)
    obtain ⟨φa⟩ := hJa
    rcases h1514 _ _ ha' ⟨φa⟩ Y hY hm with ⟨-, -, hΩ, -⟩ | ⟨⟨φ7⟩, -⟩ | ⟨-, -, -, hΩ, -⟩
    · exact hne hΩ
    · exact KFacts.KS14.isEmpty_mulEquiv_j2_alternating.2.1.false (φa.symm.trans φ7)
    · exact hne hΩ

end FourFive

section Core

variable {G : Type} [Group G] [Finite G]

theorem item163_of_core {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h162 : Item162 A (lB A)) (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (h1411 : Item1411_1 A (lB A))
    (h45 : ∀ Y ∈ scriptY0Star A (lB A), L ≤ Y ∧
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) ∨
        omegaA A = {Subgroup.zpowers c}))
    (hQ2 : ∀ Y₁ ∈ scriptY0Star A (lB A), ∀ Y₂ ∈ scriptY0Star A (lB A), Y₁ ≠ Y₂ →
      QTwoNe A Y₁ Y₂)
    {R : Subgroup G} (hRgood : GoodR163 A L R)
    (hΔ : ∀ Y ∈ scriptY0Star A (lB A), R ≤ Subgroup.normalizer (Y : Set G) →
      delta A (lB A) (Subgroup.normalizer (CFSG.Open.pCoreOf 2 (R ⊔ L) : Set G)) ≤
        Subgroup.normalizer (Y : Set G)) :
    Item163 A (lB A) c L := by
  have hRQ : R ∈ scriptQPi A (lB A) ⊤ (piOf 2) := hRgood.1
  have hXP := xA_le_delta_normalizer h hRgood.2.1
  have hXY : ∀ Y ∈ scriptY0Star A (lB A), xA A ≤ Subgroup.normalizer (Y : Set G) := by
    intro Y hY
    obtain ⟨S₀, hS₀, hS₀Y⟩ := exists_qStar_le_normalizer h153 hobs hY
    obtain ⟨w, hw, hRw⟩ := exists_conj_le_normalizer h1411 hS₀ hS₀Y hRQ
    have hYw := map_conj_mem_scriptY0Star hw hY
    have h1 : xA A ≤ Subgroup.normalizer
        ((Y.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) :=
      hXP.trans (hΔ _ hYw hRw)
    have h2 : (xA A).map (MulAut.conj w).toMonoidHom ≤
        (Subgroup.normalizer (Y : Set G)).map (MulAut.conj w).toMonoidHom := by
      rw [map_conj_xA hw, Subgroup.map_equiv_normalizer_eq]
      exact h1
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj w).injective).mp h2
  have hone : ∀ Y ∈ scriptY0Star A (lB A), ∀ Y' ∈ scriptY0Star A (lB A), Y' = Y := by
    intro Y hY Y' hY'
    by_contra hne
    obtain ⟨x, hx, hxY⟩ := h162 Y' hY' Y hY (hQ2 Y' hY' Y hY hne)
    apply hne
    rw [hxY]
    exact Late.map_conj_eq_of_mem_normalizer (hXY Y hY hx)
  intro Y hY
  have hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Y : Set G) := fun w hw =>
    mem_normalizer_of_map_conj_eq (hone Y hY _ (map_conj_mem_scriptY0Star hw hY))
  refine ⟨hW, fun S hS => ?_, Set.eq_singleton_iff_unique_mem.mpr ⟨hY, fun Y' hY' =>
    hone Y hY Y' hY'⟩, (h45 Y hY).1, (h45 Y hY).2⟩
  obtain ⟨S₀, hS₀, hS₀Y⟩ := exists_qStar_le_normalizer h153 hobs hY
  obtain ⟨w, hw, rfl⟩ := h1411 S₀ hS₀ S hS
  have hwY : w ∈ Subgroup.normalizer (Y : Set G) := hW (Subgroup.mem_inf.mp hw).1
  rw [← Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hwY)]
  exact Subgroup.map_mono hS₀Y

end Core

end CFSG.RankThree.PartTwo.Sec16
