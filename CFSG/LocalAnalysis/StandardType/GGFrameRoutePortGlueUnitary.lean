module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoinDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
import CFSG.LocalAnalysis.StandardType.GGFrameFSxEndsCardJoin
import CFSG.LocalAnalysis.StandardType.GGFrameRouteEndNormal
import CFSG.LocalAnalysis.StandardType.GGFrameRouteLower
import CFSG.LocalAnalysis.StandardType.GGHdRo7LNC
import CFSG.LocalAnalysis.StandardType.GGQTwoLMMult
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSU
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalUInner
import CFSG.RankThree.PartOne.KF.R9Plane
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOutUnitary
import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
import CFSG.Holt.Centralizer
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockCensus
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
import CFSG.RankThree.PartOne.N143.SectionCenter
import CFSG.RankThree.PartOne.N143.SectionRankBound
import CFSG.RankThree.PartOne.N143.SectionRankProof
import CFSG.RankThree.PartOne.N143.SectionRankSplit
import CFSG.RankThree.PartTwo.Sec19.Item194Used
import Certificates.Certificate19800
import Certificates.Certificate9591
import Certificates.Certificate9594
import Certificates.Certificate9595
import Certificates.Certificate9597
import Certificates.Certificate9602

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)
open CFSG.ComponentClassification.OuterAutomorphisms

theorem nonempty_mulEquiv_unitarySeven_of_marking
    {X : Type} [Group X] [Finite X]
    (hm : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 6 ∧ lab.n = 1)) :
    Subgroup.center X = ⊥ ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (X ≃* StatedProj (StatedSU 7 (2 ^ 1) K)) := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hm
  obtain ⟨R₀, hR₀, I₀, F₀, hSimple₀, hNa₀, θ₀, hP⟩ := largeEvenRawDatum_exists hraw
  have hlab' : lab = ⟨.twA, 6, 1⟩ := by
    obtain ⟨hTag, hRank, hN⟩ := hP
    rw [← hTag, ← hRank, ← hN]
  rw [hlab'] at hraw
  simp only at hraw
  obtain ⟨K, hK_field, hK_fin, hKcard, hQ⟩ := hraw
  obtain ⟨hSimple, hNa, θ, hP'⟩ := hQ
  let R := LargeEvenProj (LargeEvenSUGroup (Fin 7) K 2)
  have hLieR : LieModel R .PSU 7 2 1 := by
    refine Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by norm_num, ?_⟩, K, hK_field, hK_fin,
      ?_, ?_⟩
    · intro h
      exact absurd (congrArg Prod.fst h) (by norm_num)
    · norm_num at hKcard ⊢
      exact hKcard
    · exact ⟨MulEquiv.refl _⟩
  have hLieX : LieModel (X ⧸ Subgroup.center X) .PSU 7 2 1 :=
    LieModel.of_mulEquiv θ.symm hLieR
  have hCenterCard : Nat.card (Subgroup.center X) = 1 :=
    CFSG.StandardType.QTwo.qTwo_psuTrivialMultiplier (m := 7) (by norm_num) (by norm_num) X hperf
      hLieX
  have hCenterBot : Subgroup.center X = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    simpa using hCenterCard
  refine ⟨hCenterBot, K, hK_field, hK_fin, ?_, ?_⟩
  · norm_num at hKcard ⊢
    exact hKcard
  · have e : X ≃* R :=
      QuotientGroup.quotientBot.symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hCenterBot.symm).trans θ)
    exact ⟨e⟩

theorem autThreePowInner_of_mulEquiv_unitarySeven {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {X : Type} [Group X] (e : X ≃* StatedProj (StatedSU 7 (2 ^ 1) K)) :
    AutThreePowInner X := by
  have hf : 0 < 2 := by norm_num
  have hK' : Nat.card K = 2 ^ (2 * 1) := by simpa using hK
  let φ : K ≃+* GaloisField 2 2 := CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 2 hf hK'
  have eSU : X ≃* CFSG.Assembly.RankThreeEven.projSU 7 2 1 :=
    e.trans ((CFSG.Open.StatedSUFieldChange.statedProjSUEquiv φ 7 2).trans
      (CFSG.PGLModel.projSUEquivStatedProj 7 2 1).symm)
  have hOut : Nat.card (Outer (CFSG.Assembly.RankThreeEven.projSU 7 2 1)) = 2 := by
    have h := CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.card_outer_projSU_eq 7 2 1
      le_rfl (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have h3 : ¬ 3 ∣ Nat.card (Outer (CFSG.Assembly.RankThreeEven.projSU 7 2 1)) := by
    rw [hOut]
    norm_num
  exact CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.autThreePowInner_of_mulEquiv eSU
   (CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.autThreePowInner_of_not_three_dvd_outer
     h3)

section UnitarySevenTorus

open CFSG.SectionRank.OddCover (diagHom)

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def suSevenDiag (K : Type) [Field K] : Subgroup ↥(StatedSU 7 (2 ^ 1) K) :=
  (diagHom 7).range.comap (StatedSU 7 (2 ^ 1) K).subtype

omit [Finite K] in
theorem statedSU_seven_scalars_eq_bot (hK : Nat.card K = 4) :
    (StatedScalars (Fin 7) K).subgroupOf (StatedSU 7 (2 ^ 1) K) = ⊥ := by
  refine CFSG.RankThree.PartOne.KFU.scalars_subgroupOf_eq_bot (f := 1) (n := 7) ?_ (by norm_num) ?_
  · rw [hK]
    norm_num
  · norm_num

omit [Finite K] in
theorem center_statedSU_seven_eq_bot (hK : Nat.card K = 4) :
    Subgroup.center ↥(StatedSU 7 (2 ^ 1) K) = ⊥ := by
  have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  rw [CFSG.SeitzReduction.UnitaryPilot.center_unitarySU_eq_unitaryScalars h 7,
    CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq h (n := 7) (by norm_num)]
  exact statedSU_seven_scalars_eq_bot hK

private theorem glue5aAux_exists_zeta (hK : Nat.card K = 4) :
    ∃ ζ : Kˣ, ζ ^ 3 = 1 ∧ ζ ^ 2 ≠ 1 := by
  have hunits3 : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]
  obtain ⟨ζ, hζord⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hunits3])
  refine ⟨ζ, by rw [← hζord]; exact pow_orderOf_eq_one ζ, ?_⟩
  intro h
  have h2 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one h
  rw [hζord] at h2
  omega

omit [Finite K] in
private theorem glue5aAux_torusElt_mem_suSevenDiag (hK : Nat.card K = 4) {ζ : Kˣ}
    (hζ3 : ζ ^ 3 = 1) {i j : Fin 7} (hij : i ≠ j) :
    ∃ d ∈ suSevenDiag K, ((d : ↥(StatedSU 7 (2 ^ 1) K)) : GL (Fin 7) K) =
      CFSG.RankThree.PartOne.KFU.diagU
        (CFSG.RankThree.PartOne.KFU.torusElt i j ζ) := by
  have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  have hvec := CFSG.RankThree.PartOne.KFU.torusElt_mem (K := K) (n := 7) (p := 3) hij hζ3
  have hSU : CFSG.RankThree.PartOne.KFU.diagU
      (CFSG.RankThree.PartOne.KFU.torusElt i j ζ) ∈
      CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 7 :=
    CFSG.RankThree.PartOne.KFU.torusSU_le_unitarySU h (p := 3) (n := 7)
      (by norm_num : 3 ∣ 2 ^ 1 + 1)
      (CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.mpr
        ⟨_, hvec.1, hvec.2, rfl⟩)
  let d₀ : ↥(StatedSU 7 (2 ^ 1) K) := ⟨CFSG.RankThree.PartOne.KFU.diagU
    (CFSG.RankThree.PartOne.KFU.torusElt i j ζ), hSU⟩
  have hd0 : (d₀ : GL (Fin 7) K) = CFSG.RankThree.PartOne.KFU.diagU
      (CFSG.RankThree.PartOne.KFU.torusElt i j ζ) := rfl
  refine ⟨d₀, ?_, hd0⟩
  rw [suSevenDiag, Subgroup.mem_comap]
  refine ⟨CFSG.RankThree.PartOne.KFU.torusElt i j ζ, ?_⟩
  change CFSG.SectionRank.OddCover.diagHom 7
    (CFSG.RankThree.PartOne.KFU.torusElt i j ζ) = (d₀ : GL (Fin 7) K)
  rw [hd0]
  exact Units.ext (by
    rw [CFSG.RankThree.PartOne.KFU.diagU_val, CFSG.SectionRank.OddCover.coe_diagHom])

theorem exists_conj_eq_suSevenDiag (hK : Nat.card K = 4) {E : Subgroup ↥(StatedSU 7 (2 ^ 1) K)}
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 6 ≤ Nat.card E) :
    ∃ P : ↥(StatedSU 7 (2 ^ 1) K), E.map (MulAut.conj P⁻¹).toMonoidHom = suSevenDiag K := by
  classical
  have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  obtain ⟨P, hP⟩ := CFSG.StandardType.OrdPInnerSU.exists_su_conj_diag (f := 1) (n := 7) h
    (by norm_num) (p := 3) Nat.prime_three (by norm_num : 3 ∣ 2 ^ 1 + 1) hE
  have hTSU : CFSG.RankThree.PartOne.KFU.torusSU 3 7 K ≤ StatedSU 7 (2 ^ 1) K :=
    CFSG.RankThree.PartOne.KFU.torusSU_le_unitarySU h (p := 3) (n := 7)
      (by norm_num : 3 ∣ 2 ^ 1 + 1)
  have hcardT : Nat.card ↥(CFSG.RankThree.PartOne.KFU.torusSU 3 7 K) ≤ 3 ^ 6 := by
    rw [CFSG.RankThree.PartOne.KFU.torusSU,
      Subgroup.card_map_of_injective CFSG.RankThree.PartOne.KFU.diagU_injective]
    exact CFSG.RankThree.PartOne.KFU.card_torusVec_le (K := K) (p := 3) (by norm_num) 6
  have hleT : suSevenDiag K ≤
      (CFSG.RankThree.PartOne.KFU.torusSU 3 7 K).subgroupOf (StatedSU 7 (2 ^ 1) K) := by
    intro d hd
    rw [suSevenDiag, Subgroup.mem_comap] at hd
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨e, he⟩ := hd
    have hmem : CFSG.SectionRank.OddCover.diagHom 7 e ∈
        CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 7 := by
      rw [he]
      exact d.2
    have hu := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mp hmem
    refine CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.mpr ⟨e, fun i => ?_, ?_, ?_⟩
    · have hdiag := hu.2
      rw [CFSG.SectionRank.OddCover.coe_diagHom,
        Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal] at hdiag
      have h1 : h.bar ((e i : K)) * (e i : K) = 1 := by
        have h2 := congrFun (congrFun hdiag i) i
        simpa using h2
      have hbar : h.bar (e i) = (e i : K) ^ 2 := by
        rw [h.bar_apply]
        norm_num
      rw [hbar] at h1
      have h3 : ((e i : K)) ^ 3 = 1 := by
        calc ((e i : K)) ^ 3 = (e i : K) ^ 2 * (e i : K) := by ring
          _ = 1 := h1
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h3)
    · have hdet := hu.1
      rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.det_diagonal] at hdet
      exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact hdet)
    · have h1 : CFSG.RankThree.PartOne.KFU.diagU e =
          CFSG.SectionRank.OddCover.diagHom 7 e := by
        apply Units.ext
        rw [CFSG.RankThree.PartOne.KFU.diagU_val, CFSG.SectionRank.OddCover.coe_diagHom]
      exact h1.trans he
  have hcardS : Nat.card ↥(suSevenDiag K) ≤ 3 ^ 6 := by
    calc Nat.card ↥(suSevenDiag K)
        ≤ Nat.card ↥((CFSG.RankThree.PartOne.KFU.torusSU 3 7 K).subgroupOf
            (StatedSU 7 (2 ^ 1) K)) :=
          Nat.card_le_card_of_injective
            (fun x => (⟨x.1, hleT x.2⟩ :
              ↥((CFSG.RankThree.PartOne.KFU.torusSU 3 7 K).subgroupOf
                (StatedSU 7 (2 ^ 1) K))))
            (by
              intro a b hab
              exact Subtype.ext (congrArg
                (fun y : ↥((CFSG.RankThree.PartOne.KFU.torusSU 3 7 K).subgroupOf
                  (StatedSU 7 (2 ^ 1) K)) => (y : ↥(StatedSU 7 (2 ^ 1) K))) hab))
      _ = Nat.card ↥(CFSG.RankThree.PartOne.KFU.torusSU 3 7 K) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTSU).toEquiv
      _ ≤ 3 ^ 6 := hcardT
  refine ⟨P, ?_⟩
  have hcardE : Nat.card ↥(E.map (MulAut.conj P⁻¹).toMonoidHom) = Nat.card ↥E :=
    Subgroup.card_map_of_injective (MulAut.conj P⁻¹).injective
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨σ, hσ⟩ := hP x hx
    rw [suSevenDiag, Subgroup.mem_comap]
    refine ⟨σ, ?_⟩
    change (CFSG.SectionRank.OddCover.diagHom 7) σ =
      (StatedSU 7 (2 ^ 1) K).subtype ((MulAut.conj P⁻¹) x)
    rw [MulAut.conj_apply]
    simpa using hσ.symm
  · rw [hcardE]
    exact le_trans hcardS hcard

theorem eq_bot_of_two_group_suSevenDiag (hK : Nat.card K = 4)
    {S : Subgroup ↥(StatedSU 7 (2 ^ 1) K)} (hS : IsPGroup 2 S)
    (hN : suSevenDiag K ≤ Subgroup.normalizer (S : Set ↥(StatedSU 7 (2 ^ 1) K))) : S = ⊥ := by
  classical
  have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  obtain ⟨ζ, hζ3, hζ2⟩ := glue5aAux_exists_zeta (K := K) hK
  have hsep : ∀ i j : Fin 7, i ≠ j →
      ∃ g ∈ (suSevenDiag K).map (StatedSU 7 (2 ^ 1) K).subtype,
        CFSG.RankThree.PartOne.KFU.ent g i i ≠ CFSG.RankThree.PartOne.KFU.ent g j j := by
    intro i j hij
    obtain ⟨d, hd, hdval⟩ := glue5aAux_torusElt_mem_suSevenDiag (K := K) hK hζ3 hij
    refine ⟨((d : ↥(StatedSU 7 (2 ^ 1) K)) : GL (Fin 7) K),
      Subgroup.mem_map.mpr ⟨d, hd, rfl⟩, ?_⟩
    rw [hdval]
    have hii : CFSG.RankThree.PartOne.KFU.ent
        (CFSG.RankThree.PartOne.KFU.diagU (CFSG.RankThree.PartOne.KFU.torusElt i j ζ)) i i
        = (ζ : K) := by
      change (((CFSG.RankThree.PartOne.KFU.diagU
        (CFSG.RankThree.PartOne.KFU.torusElt i j ζ) : GL (Fin 7) K) :
          Matrix (Fin 7) (Fin 7) K)) i i = (ζ : K)
      rw [CFSG.RankThree.PartOne.KFU.diagU_apply_same,
        CFSG.RankThree.PartOne.KFU.torusElt_apply_left hij]
    have hjj : CFSG.RankThree.PartOne.KFU.ent
        (CFSG.RankThree.PartOne.KFU.diagU (CFSG.RankThree.PartOne.KFU.torusElt i j ζ)) j j
        = ((ζ⁻¹ : Kˣ) : K) := by
      change (((CFSG.RankThree.PartOne.KFU.diagU
        (CFSG.RankThree.PartOne.KFU.torusElt i j ζ) : GL (Fin 7) K) :
          Matrix (Fin 7) (Fin 7) K)) j j = ((ζ⁻¹ : Kˣ) : K)
      rw [CFSG.RankThree.PartOne.KFU.diagU_apply_same,
        CFSG.RankThree.PartOne.KFU.torusElt_apply_right hij]
    rw [hii, hjj]
    intro hcon
    exact hζ2 (by
      have h1 : ζ = ζ⁻¹ := Units.ext hcon
      calc ζ ^ 2 = ζ * ζ := sq ζ
        _ = ζ * ζ⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel ζ)
  have hbot := CFSG.RankThree.PartOne.KFU.eq_bot_of_two_group_separated (f := 1) h
    (S.map (StatedSU 7 (2 ^ 1) K).subtype)
    (by rintro _ ⟨s, -, rfl⟩; exact s.2) (hS.map _)
    ((suSevenDiag K).map (StatedSU 7 (2 ^ 1) K).subtype)
    (by
      rintro g hg
      obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hg
      rw [suSevenDiag, Subgroup.mem_comap] at hx
      obtain ⟨d, hd⟩ := hx
      refine ⟨d, ?_⟩
      rw [← hxval]
      apply Units.ext
      rw [CFSG.RankThree.PartOne.KFU.diagU_val, ← hd,
        CFSG.SectionRank.OddCover.coe_diagHom])
    (by
      rintro g hg s hs
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hs
      exact Subgroup.mem_map.mpr ⟨a * b * a⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hN ha) b).mp hb, by simp⟩)
    hsep
  rwa [Subgroup.map_eq_bot_iff_of_injective _ (StatedSU 7 (2 ^ 1) K).subtype_injective] at hbot

omit [Finite K] in
private theorem glue5aAux_diagU_eq_diagHom (d : Fin 7 → Kˣ) :
    CFSG.RankThree.PartOne.KFU.diagU d = CFSG.SectionRank.OddCover.diagHom 7 d := by
  apply Units.ext
  rw [CFSG.RankThree.PartOne.KFU.diagU_val, CFSG.SectionRank.OddCover.coe_diagHom]

private theorem glue5aAux_units_trichotomy (hK : Nat.card K = 4) {ζ : Kˣ}
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) : ∀ x : Kˣ, x = 1 ∨ x = ζ ∨ x = ζ ^ 2 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hunits3 : Fintype.card Kˣ = 3 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hK]
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h2
    have hd : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hd3 : orderOf ζ ∣ 3 := orderOf_dvd_of_pow_eq_one hζ3
    have h1 : orderOf ζ = 1 := by
      have := Nat.dvd_gcd hd hd3
      simpa using this
    exact hζ1 (orderOf_eq_one_iff.mp h1)
  have hζ21 : ζ ^ 2 ≠ ζ := by
    intro h
    apply hζ1
    have h' : ζ * ζ = ζ * 1 := by rw [← sq, h, mul_one]
    exact mul_left_cancel h'
  have hset : ({1, ζ, ζ ^ 2} : Finset Kˣ) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hunits3]
    have h1 : (1 : Kˣ) ∉ ({ζ, ζ ^ 2} : Finset Kˣ) := by
      simp [Ne.symm hζ1, Ne.symm hζ2]
    have h2 : ζ ∉ ({ζ ^ 2} : Finset Kˣ) := by
      simpa using hζ21.symm
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_singleton]
  intro x
  have hx : x ∈ ({1, ζ, ζ ^ 2} : Finset Kˣ) := by rw [hset]; exact Finset.mem_univ x
  simpa using hx

private theorem glue5aAux_exists_third (i j : Fin 7) : ∃ m : Fin 7, m ≠ i ∧ m ≠ j := by
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset (Fin 7)) ⊆ ({i, j} : Finset (Fin 7)) := by
    intro k _
    by_cases hk : k = i
    · rw [hk]; exact Finset.mem_insert_self i {j}
    · have hkj : k = j := hcon k hk
      rw [hkj]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ({i, j} : Finset (Fin 7)).card ≤ 2 := by
    have := Finset.card_insert_le i ({j} : Finset (Fin 7))
    simpa using this
  omega

theorem eq_one_of_two_pow_fix_suSevenDiag (hK : Nat.card K = 4)
    (γ : MulAut (StatedProj (StatedSU 7 (2 ^ 1) K))) {k : ℕ} (hγ : γ ^ 2 ^ k = 1)
    (hfix : ∀ d ∈ suSevenDiag K, γ (QuotientGroup.mk d) = QuotientGroup.mk d) : γ = 1 := by
  classical
  have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨σ, B, hB, hrep⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.l212in_aut_su (n := 7) (r := 2) (f := 1)
      (by norm_num) hcard γ
  rw [CFSG.LocalAnalysis.RankFourTheoremC.AutSU.conjTr_unitaryInvolution h] at hB
  have hmkinj : Function.Injective
      (QuotientGroup.mk' ((StatedScalars (Fin 7) K).subgroupOf (StatedSU 7 (2 ^ 1) K))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact statedSU_seven_scalars_eq_bot hK
  have hmk : ∀ a b : ↥(StatedSU 7 (2 ^ 1) K),
      QuotientGroup.mk' ((StatedScalars (Fin 7) K).subgroupOf (StatedSU 7 (2 ^ 1) K)) a =
        QuotientGroup.mk' ((StatedScalars (Fin 7) K).subgroupOf (StatedSU 7 (2 ^ 1) K)) b → a = b :=
    fun a b hab => hmkinj hab
  have hconj : ∀ d ∈ suSevenDiag K,
      B * (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ) (d : GL (Fin 7) K) * B⁻¹ =
        (d : GL (Fin 7) K) := by
    intro d hd
    obtain ⟨hgd, hgd'⟩ := hrep d
    have h1 : γ (QuotientGroup.mk d) = QuotientGroup.mk (⟨_, hgd⟩ :
        ↥(StatedSU 7 (2 ^ 1) K)) := hgd'
    have h2 : (⟨_, hgd⟩ : ↥(StatedSU 7 (2 ^ 1) K)) = d := by
      apply hmk
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← h1, hfix d hd]
    have h2' := congrArg (Subtype.val : ↥(StatedSU 7 (2 ^ 1) K) → GL (Fin 7) K) h2
    simpa using h2'
  obtain ⟨ζ, hζ3, hζ2u⟩ := glue5aAux_exists_zeta (K := K) hK
  have hζ1 : ζ ≠ 1 := fun h1 => hζ2u (by rw [h1]; exact one_pow 2)
  have hunits := glue5aAux_units_trichotomy (K := K) hK hζ3 hζ1
  have hζ3K : ((ζ : K)) ^ 3 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hζ3
    simpa using this
  have hζ2K : ((ζ : K)) ^ 2 ≠ 1 := by
    intro h1
    exact hζ2u (Units.ext (by simpa using h1))
  have hζinv : ((ζ : K))⁻¹ = (ζ : K) ^ 2 := by
    have h1 : (ζ : K) * (ζ : K)⁻¹ = (ζ : K) * (ζ : K) ^ 2 := by
      rw [mul_inv_cancel₀ ζ.ne_zero]
      rw [show (ζ : K) * (ζ : K) ^ 2 = (ζ : K) ^ 3 from by ring, hζ3K]
    exact mul_left_cancel₀ ζ.ne_zero h1
  by_cases hσζ : σ (ζ : K) = (ζ : K)
  ·
    have hσid : ∀ x : K, σ x = x := by
      intro x
      rcases eq_or_ne x 0 with h0 | hx
      · subst h0; exact map_zero σ
      · obtain ⟨y, hy⟩ : ∃ y : Kˣ, (y : K) = x := ⟨Units.mk0 x hx, rfl⟩
        rw [← hy]
        rcases hunits y with h1 | h1 | h1
        · rw [h1]; simp
        · rw [h1]; exact hσζ
        · rw [h1, Units.val_pow_eq_pow_val, map_pow, hσζ]
    have hσrefl : σ = RingEquiv.refl K := RingEquiv.ext hσid
    have hglAut : (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut
        (ι := Fin 7) σ) = 1 := by
      rw [hσrefl]
      exact map_one _
    have hBcomm : ∀ d ∈ suSevenDiag K,
        B * (d : GL (Fin 7) K) = (d : GL (Fin 7) K) * B := by
      intro d hd
      have h1 := hconj d hd
      rw [hglAut] at h1
      have h2 : B * (d : GL (Fin 7) K) * B⁻¹ = (d : GL (Fin 7) K) := by simpa using h1
      calc B * (d : GL (Fin 7) K) = (B * (d : GL (Fin 7) K) * B⁻¹) * B := by group
        _ = (d : GL (Fin 7) K) * B := by rw [h2]
    have hdiag : ∀ i j : Fin 7, i ≠ j →
        (B : Matrix (Fin 7) (Fin 7) K) i j = 0 := by
      intro i j hij
      obtain ⟨d, hd, hdval⟩ := glue5aAux_torusElt_mem_suSevenDiag (K := K) hK hζ3 hij
      have hcomm := hBcomm d hd
      have h1 : (B : Matrix (Fin 7) (Fin 7) K) *
          ((d : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) =
          ((d : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
            (B : Matrix (Fin 7) (Fin 7) K) := by
        rw [← Units.val_mul, hcomm, Units.val_mul]
      have h2 := congrFun (congrFun h1 i) j
      rw [hdval, CFSG.RankThree.PartOne.KFU.diagU_val, Matrix.mul_diagonal,
        Matrix.diagonal_mul] at h2
      rw [CFSG.RankThree.PartOne.KFU.torusElt_apply_left hij,
        CFSG.RankThree.PartOne.KFU.torusElt_apply_right hij] at h2
      have h3 : (B : Matrix (Fin 7) (Fin 7) K) i j * (((ζ⁻¹ : Kˣ) : K) - (ζ : K)) = 0 := by
        rw [mul_sub, sub_eq_zero]
        exact h2.trans (mul_comm _ _)
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · exfalso
        apply hζ2u
        have h5 : ζ⁻¹ = ζ := Units.ext (sub_eq_zero.mp h4)
        calc ζ ^ 2 = ζ * ζ := sq ζ
          _ = ζ⁻¹ * ζ := by rw [h5]
          _ = 1 := inv_mul_cancel ζ
    have hBdiag : (B : Matrix (Fin 7) (Fin 7) K) =
        Matrix.diagonal (fun i => (B : Matrix (Fin 7) (Fin 7) K) i i) := by
      ext i j
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ hij, hdiag i j hij]
    have hcube : ∀ i, (B : Matrix (Fin 7) (Fin 7) K) i i ^ 3 = 1 := by
      intro i
      have h2 := congrFun (congrFun hB i) i
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
        Matrix.one_apply_eq] at h2
      rw [Finset.sum_eq_single i] at h2
      · have hbar : h.bar ((B : Matrix (Fin 7) (Fin 7) K) i i) =
            ((B : Matrix (Fin 7) (Fin 7) K) i i) ^ 2 := by
          rw [h.bar_apply]
          norm_num
        rw [hbar] at h2
        calc (B : Matrix (Fin 7) (Fin 7) K) i i ^ 3 =
            (B : Matrix (Fin 7) (Fin 7) K) i i ^ 2 * (B : Matrix (Fin 7) (Fin 7) K) i i := by
              ring
          _ = 1 := h2
      · intro x _ hx
        rw [hdiag x i hx, map_zero, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ i) hmem
    have hB3 : B ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, hBdiag]
      have hdiagpow : ∀ n : ℕ,
          (Matrix.diagonal (fun i => (B : Matrix (Fin 7) (Fin 7) K) i i)) ^ n =
            Matrix.diagonal ((fun i => (B : Matrix (Fin 7) (Fin 7) K) i i) ^ n) := by
        intro n
        induction n with
        | zero => rw [pow_zero, pow_zero]; exact (Matrix.diagonal_one).symm
        | succ n ih =>
            rw [pow_succ, ih, pow_succ, Matrix.diagonal_mul_diagonal]
            rfl
      rw [hdiagpow 3]
      have hf3 : (fun i => (B : Matrix (Fin 7) (Fin 7) K) i i) ^ 3 = 1 := by
        funext i
        show (B : Matrix (Fin 7) (Fin 7) K) i i ^ 3 = 1
        exact hcube i
      rw [hf3]
      exact Matrix.diagonal_one
    have hγ3 : γ ^ 3 = 1 := by
      have hstep : ∀ g : ↥(StatedSU 7 (2 ^ 1) K),
          ∃ hg : B * (g : GL (Fin 7) K) * B⁻¹ ∈ StatedSU 7 (2 ^ 1) K,
            γ (QuotientGroup.mk g) =
              QuotientGroup.mk (⟨B * (g : GL (Fin 7) K) * B⁻¹, hg⟩ :
                ↥(StatedSU 7 (2 ^ 1) K)) := by
        intro g
        obtain ⟨hg, hgm⟩ := hrep g
        exact ⟨by simpa [hglAut] using hg, by simpa [hglAut] using hgm⟩
      ext x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨hg1, h1⟩ := hstep g
      obtain ⟨hg2, h2⟩ := hstep ⟨B * (g : GL (Fin 7) K) * B⁻¹, hg1⟩
      obtain ⟨hg3, h3⟩ := hstep ⟨B * (B * (g : GL (Fin 7) K) * B⁻¹) * B⁻¹, hg2⟩
      calc (γ ^ 3) (QuotientGroup.mk g)
          = γ (γ (γ (QuotientGroup.mk g))) := rfl
        _ = γ (γ (QuotientGroup.mk (⟨B * (g : GL (Fin 7) K) * B⁻¹, hg1⟩ :
              ↥(StatedSU 7 (2 ^ 1) K)))) := by rw [h1]
        _ = γ (QuotientGroup.mk (⟨B * (B * (g : GL (Fin 7) K) * B⁻¹) * B⁻¹, hg2⟩ :
              ↥(StatedSU 7 (2 ^ 1) K))) := by rw [h2]
        _ = QuotientGroup.mk (⟨B * (B * (B * (g : GL (Fin 7) K) * B⁻¹) * B⁻¹) * B⁻¹,
              hg3⟩ : ↥(StatedSU 7 (2 ^ 1) K)) := h3
        _ = QuotientGroup.mk g := by
            congr 1
            apply Subtype.ext
            have hBBB : (B : GL (Fin 7) K) * (B * B) = 1 := by
              rw [← pow_three]
              exact hB3
            calc (B : GL (Fin 7) K) * (B * (B * (g : GL (Fin 7) K) * B⁻¹) * B⁻¹) * B⁻¹
                = ((B : GL (Fin 7) K) * (B * B)) * (g : GL (Fin 7) K) *
                  ((B : GL (Fin 7) K) * (B * B))⁻¹ := by group
              _ = (g : GL (Fin 7) K) := by rw [hBBB]; group
    have hdvd3 : orderOf γ ∣ 3 := orderOf_dvd_of_pow_eq_one hγ3
    have hdvd2 : orderOf γ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hγ
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by decide)
    have hone : orderOf γ = 1 := by
      have h := Nat.dvd_gcd hdvd3 hdvd2
      have h1 : Nat.gcd 3 (2 ^ k) = 1 := hcop
      rw [h1] at h
      exact Nat.dvd_one.mp h
    exact orderOf_eq_one_iff.mp hone
  ·
    have hσζinv : σ (ζ : K) = ((ζ : K))⁻¹ := by
      have hne : σ (ζ : K) ≠ 0 := by
        intro h0
        have h1 : σ (ζ : K) = σ 0 := by rw [h0, map_zero]
        exact ζ.ne_zero (σ.injective h1)
      obtain ⟨y, hy⟩ : ∃ y : Kˣ, (y : K) = σ (ζ : K) := ⟨Units.mk0 _ hne, rfl⟩
      have hy3 : y ^ 3 = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one, hy, ← map_pow, hζ3K, map_one]
      rcases hunits y with h | h | h
      · exfalso
        have h1 : σ (ζ : K) = 1 := by rw [← hy, h]; simp
        exact hζ1 (Units.ext (σ.injective (h1.trans (map_one σ).symm)))
      · exact absurd (by rw [← hy, h]) hσζ
      · rw [← hy, h, Units.val_pow_eq_pow_val, ← hζinv]
    obtain ⟨j, hj⟩ :=
      CFSG.RankThree.PartOne.KFU.exists_ent_ne_zero (B : GL (Fin 7) K) 0
    obtain ⟨m, hm0, hmj⟩ := glue5aAux_exists_third 0 j
    obtain ⟨d, hd, hdval⟩ := glue5aAux_torusElt_mem_suSevenDiag (K := K) hK hζ3 hm0.symm
    have hBne : (B : Matrix (Fin 7) (Fin 7) K) j 0 ≠ 0 := by
      simpa [CFSG.RankThree.PartOne.KFU.ent] using hj
    have hentry : σ ((CFSG.RankThree.PartOne.KFU.torusElt 0 m ζ 0 : Kˣ) : K) =
        (((CFSG.RankThree.PartOne.KFU.torusElt 0 m ζ j : Kˣ) : K)) := by
      have hde : (d : GL (Fin 7) K) = CFSG.SectionRank.OddCover.diagHom 7
          (CFSG.RankThree.PartOne.KFU.torusElt 0 m ζ) :=
        hdval.trans (glue5aAux_diagU_eq_diagHom _)
      have hA : ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ)
          (d : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) =
          Matrix.diagonal (fun x => σ ((CFSG.RankThree.PartOne.KFU.torusElt 0 m ζ x : K))) := by
        rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut, hde,
          CFSG.SectionRank.OddCover.coe_diagHom, Matrix.diagonal_map (map_zero σ)]
      have hcommGL : B * (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ)
          (d : GL (Fin 7) K) = (d : GL (Fin 7) K) * B := by
        calc B * (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ) (d : GL (Fin 7) K)
            = (B * (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ)
                (d : GL (Fin 7) K) * B⁻¹) * B := by group
          _ = (d : GL (Fin 7) K) * B := by rw [hconj d hd]
      have h1 : (B : Matrix (Fin 7) (Fin 7) K) *
          ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ) (d : GL (Fin 7) K) :
            Matrix (Fin 7) (Fin 7) K) =
          ((d : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
            (B : Matrix (Fin 7) (Fin 7) K) := by
        rw [← Units.val_mul, hcommGL, Units.val_mul]
      have h2 := congrFun (congrFun h1 j) 0
      rw [hA, Matrix.mul_diagonal, hde, CFSG.SectionRank.OddCover.coe_diagHom,
        Matrix.diagonal_mul] at h2
      have h3 : (B : Matrix (Fin 7) (Fin 7) K) j 0 *
          σ ((CFSG.RankThree.PartOne.KFU.torusElt 0 m ζ 0 : Kˣ) : K) =
          (B : Matrix (Fin 7) (Fin 7) K) j 0 *
            ((CFSG.RankThree.PartOne.KFU.torusElt 0 m ζ j : Kˣ) : K) :=
        h2.trans (mul_comm _ _)
      exact mul_left_cancel₀ hBne h3
    have hei : ((CFSG.RankThree.PartOne.KFU.torusElt 0 m ζ 0 : Kˣ) : K) = (ζ : K) := by
      rw [CFSG.RankThree.PartOne.KFU.torusElt_apply_left hm0.symm]
    by_cases hji : j = 0
    · exfalso
      apply hσζ
      calc σ (ζ : K) = σ ((CFSG.RankThree.PartOne.KFU.torusElt 0 m ζ 0 : Kˣ) : K) := by rw [hei]
        _ = ((CFSG.RankThree.PartOne.KFU.torusElt 0 m ζ j : Kˣ) : K) := hentry
        _ = (ζ : K) := by rw [hji, hei]
    · exfalso
      have hej : ((CFSG.RankThree.PartOne.KFU.torusElt 0 m ζ j : Kˣ) : K) = 1 := by
        rw [CFSG.RankThree.PartOne.KFU.torusElt_apply_other hji hmj.symm]
        simp
      have h1 : σ (ζ : K) = 1 := by
        calc σ (ζ : K) = σ ((CFSG.RankThree.PartOne.KFU.torusElt 0 m ζ 0 : Kˣ) : K) := by
              rw [hei]
          _ = ((CFSG.RankThree.PartOne.KFU.torusElt 0 m ζ j : Kˣ) : K) := hentry
          _ = 1 := hej
      exact hζ1 (Units.ext (σ.injective (h1.trans (map_one σ).symm)))


end UnitarySevenTorus

private theorem glue5aAux_le_normalizer {Γ : Type} [Group Γ] {P Q : Subgroup Γ}
    (h : ∀ x ∈ P, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q) : P ≤ Subgroup.normalizer (Q : Set Γ) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact h x hx y
  · intro hy
    have h1 := h x⁻¹ (P.inv_mem hx) (x * y * x⁻¹) hy
    have h2 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [h2] at h1

private theorem glue5aAux_mulAut_congr_conj {M N : Type} [Group M] [Group N] (e : M ≃* N)
    (a : M) : MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
  ext y
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply]
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

private theorem glue5aAux_conj_apply_mul {M : Type} [Group M] (t : MulAut M) (d : M) :
    MulAut.conj (t d) = t * MulAut.conj d * t⁻¹ := by
  ext y
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply]
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem le_centralizer_of_unitarySeven {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {G : Type} [Group G] [Finite G] {L E T : Subgroup G}
    (φ : ↥L ≃* StatedProj (StatedSU 7 (2 ^ 1) K)) (hEL : E ≤ L) (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 6 ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hET : E ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ Subgroup.centralizer (L : Set G) := by
  classical
  let U := ↥(StatedSU 7 (2 ^ 1) K)
  let X := StatedProj (StatedSU 7 (2 ^ 1) K)
  let π : U →* X :=
    QuotientGroup.mk' ((StatedScalars (Fin 7) K).subgroupOf (StatedSU 7 (2 ^ 1) K))
  have hπker : π.ker = ⊥ := by
    change (QuotientGroup.mk' ((StatedScalars (Fin 7) K).subgroupOf
      (StatedSU 7 (2 ^ 1) K))).ker = ⊥
    rw [QuotientGroup.ker_mk', statedSU_seven_scalars_eq_bot hK]
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hπker
  let πe : U ≃* X := MulEquiv.ofBijective π ⟨hπinj, QuotientGroup.mk'_surjective _⟩
  have hπe : ∀ u : U, πe u = QuotientGroup.mk u := by
    intro u
    show π u = QuotientGroup.mk u
    rw [QuotientGroup.mk'_apply]
  let ι : X →* U := πe.symm.toMonoidHom
  have hι : ∀ x : X, ι x = πe.symm x := fun x => rfl
  have hZX : Subgroup.center X = ⊥ :=
    CFSG.Sporadic.HeldB.center_eq_bot_of_mulEquiv πe.symm (center_statedSU_seven_eq_bot hK)
  have hconjinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.Sporadic.HeldB.conj_injective_of_center hZX
  let E_U : Subgroup U := ((E.subgroupOf L).map φ.toMonoidHom).map πe.symm.toMonoidHom
  have hEU : IsElemAbelian 3 E_U :=
    ((hE.subgroupOf L).map φ.toMonoidHom).map πe.symm.toMonoidHom
  have hcardEsub : Nat.card ↥(E.subgroupOf L) = Nat.card ↥E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  have hcardEU : 3 ^ 6 ≤ Nat.card ↥E_U := by
    have h1 : Nat.card ↥E_U = Nat.card ↥(E.subgroupOf L) := by
      change Nat.card ↥(((E.subgroupOf L).map φ.toMonoidHom).map
        πe.symm.toMonoidHom) = Nat.card ↥(E.subgroupOf L)
      rw [Subgroup.card_map_of_injective πe.symm.injective,
        Subgroup.card_map_of_injective φ.injective]
    rw [h1, hcardEsub]
    exact hcard
  obtain ⟨P, hP⟩ := exists_conj_eq_suSevenDiag (K := K) hK hEU hcardEU
  let φ' : ↥L ≃* X := φ.trans (πe.symm.trans ((MulAut.conj P⁻¹).trans πe))
  have hE'map : (E.subgroupOf L).map φ'.toMonoidHom =
      (suSevenDiag K).map πe.toMonoidHom := by
    show (E.subgroupOf L).map (πe.toMonoidHom.comp ((MulAut.conj P⁻¹).toMonoidHom.comp
      (πe.symm.toMonoidHom.comp φ.toMonoidHom))) = (suSevenDiag K).map πe.toMonoidHom
    rw [← Subgroup.map_map, ← Subgroup.map_map, ← Subgroup.map_map]
    change (E_U.map (MulAut.conj P⁻¹).toMonoidHom).map πe.toMonoidHom =
      (suSevenDiag K).map πe.toMonoidHom
    rw [hP]
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let c : ↥N →* MulAut ↥L := Subgroup.normalizerMonoidHom (H := L)
  let ρ : ↥N →* MulAut X := (MulAut.congr φ').toMonoidHom.comp c
  let D : Subgroup X := (suSevenDiag K).map πe.toMonoidHom
  let T' : Subgroup (MulAut X) := (T.subgroupOf N).map ρ
  have hT'sub : IsPGroup 2 ↥(T.subgroupOf N) :=
    hT.comap_of_injective N.subtype N.subtype_injective
  have hT' : IsPGroup 2 ↥T' := hT'sub.map ρ
  have hDconj : ∀ c ∈ D.map (MulAut.conj : X →* MulAut X), ∀ t ∈ T',
      c * t * c⁻¹ ∈ T' := by
    intro c hc t ht
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hc
    have hd' : d ∈ (E.subgroupOf L).map φ'.toMonoidHom := by
      rwa [hE'map]
    obtain ⟨x, hxE, hxd⟩ := Subgroup.mem_map.mp hd'
    have hxG : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hxE
    have hxN : (x : G) ∈ N := Subgroup.le_normalizer (hEL hxG)
    have hρx : ρ ⟨(x : G), hxN⟩ = MulAut.conj d := by
      have hc : c ⟨(x : G), hxN⟩ = MulAut.conj x := by
        ext y
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        rfl
      have hxd' : φ' x = d := hxd
      rw [show ρ ⟨(x : G), hxN⟩ = MulAut.congr φ' (c ⟨(x : G), hxN⟩) from rfl, hc,
        glue5aAux_mulAut_congr_conj, hxd']
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht
    have hmem : ⟨(x : G), hxN⟩ * t₀ * ⟨(x : G), hxN⟩⁻¹ ∈ T.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      have h1 : (t₀ : G) ∈ T := Subgroup.mem_subgroupOf.mp ht₀
      have h2 := (Subgroup.mem_normalizer_iff.mp (hET hxG) (t₀ : G)).mp h1
      simpa using h2
    have heq : MulAut.conj d * ρ t₀ * (MulAut.conj d)⁻¹ =
        ρ (⟨(x : G), hxN⟩ * t₀ * ⟨(x : G), hxN⟩⁻¹) := by
      rw [← hρx]
      simp only [map_mul, map_inv]
    rw [heq]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  let SX : Subgroup X := T'.comap (MulAut.conj : X →* MulAut X)
  have hSX2 : IsPGroup 2 ↥SX :=
    hT'.comap_of_injective (MulAut.conj : X →* MulAut X) hconjinj
  have hDconjS : ∀ d ∈ D, ∀ x ∈ SX, d * x * d⁻¹ ∈ SX := by
    intro d hd x hx
    have h1 : MulAut.conj x ∈ T' := hx
    have h2 : MulAut.conj d * MulAut.conj x * (MulAut.conj d)⁻¹ ∈ T' :=
      hDconj (MulAut.conj d) (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩) (MulAut.conj x) h1
    have h3 : MulAut.conj (d * x * d⁻¹) =
        MulAut.conj d * MulAut.conj x * (MulAut.conj d)⁻¹ := by
      simp only [map_mul, map_inv]
    change MulAut.conj (d * x * d⁻¹) ∈ T'
    rw [h3]
    exact h2
  have hS : IsPGroup 2 ↥(SX.map πe.symm.toMonoidHom) := hSX2.map πe.symm.toMonoidHom
  have hNs : suSevenDiag K ≤ Subgroup.normalizer
      (↑(SX.map πe.symm.toMonoidHom) : Set U) := by
    refine glue5aAux_le_normalizer ?_
    intro d hd y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hdD : πe d ∈ D := Subgroup.mem_map.mpr ⟨d, hd, rfl⟩
    have h1 : πe d * x * (πe d)⁻¹ ∈ SX := hDconjS (πe d) hdD x hx
    have h2 : d * ι x * d⁻¹ = ι (πe d * x * (πe d)⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      rw [show ι (πe d) = d from by rw [hι]; exact MulEquiv.symm_apply_apply πe d]
    rw [h2]
    exact Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
  have hSbot : SX.map πe.symm.toMonoidHom = ⊥ :=
    eq_bot_of_two_group_suSevenDiag hK hS hNs
  have hSXbot : SX = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective SX πe.symm.injective).mp hSbot
  have hfixT' : ∀ t ∈ T', ∀ d ∈ D, t d = d := by
    intro t ht d hd
    have h1 : MulAut.conj d * t * (MulAut.conj d)⁻¹ ∈ T' :=
      hDconj (MulAut.conj d) (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩) t ht
    have h2 : MulAut.conj d * t * (MulAut.conj d)⁻¹ * t⁻¹ ∈ T' :=
      T'.mul_mem h1 (T'.inv_mem ht)
    have h3 : MulAut.conj d * t * (MulAut.conj d)⁻¹ * t⁻¹ =
        MulAut.conj (d * (t d)⁻¹) := by
      rw [map_mul, map_inv, glue5aAux_conj_apply_mul]
      group
    rw [h3] at h2
    have h4 : d * (t d)⁻¹ ∈ SX := h2
    rw [hSXbot] at h4
    have h5 : d * (t d)⁻¹ = 1 := Subgroup.mem_bot.mp h4
    have h6 : d = t d := by
      have h7 := congrArg (fun z => z * (t d)) h5
      simpa [mul_assoc] using h7
    exact h6.symm
  have hT'bot : T' = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨k, hk⟩ := hT' ⟨t, ht⟩
    have hk' : (t : MulAut X) ^ 2 ^ k = 1 := by
      have h := congrArg (Subtype.val : ↥T' → MulAut X) hk
      simpa using h
    have hfix : ∀ d ∈ suSevenDiag K, t (QuotientGroup.mk d) = QuotientGroup.mk d := by
      intro d hd
      have h1 : t (πe d) = πe d :=
        hfixT' t ht (πe d) (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩)
      rwa [hπe d] at h1
    have h1 : t = 1 := eq_one_of_two_pow_fix_suSevenDiag hK t hk' hfix
    exact Subgroup.mem_bot.mpr h1
  intro t ht
  have htN : t ∈ N := hTN ht
  have h1 : ρ ⟨t, htN⟩ = 1 := by
    have h2 : ρ ⟨t, htN⟩ ∈ T' :=
      Subgroup.mem_map.mpr ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    rw [hT'bot] at h2
    exact Subgroup.mem_bot.mp h2
  have h2 : c ⟨t, htN⟩ = 1 := by
    have h3 : MulAut.congr φ' (c ⟨t, htN⟩) = 1 := h1
    exact (MulEquiv.map_eq_one_iff (MulAut.congr φ')).mp h3
  have hker : ⟨t, htN⟩ ∈ c.ker := by
    rw [MonoidHom.mem_ker]
    exact h2
  change ⟨t, htN⟩ ∈ (Subgroup.normalizerMonoidHom (H := L)).ker at hker
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

theorem ne_bstar_of_unitarySeven
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hAt : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₇)
    (hm : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 6 ∧ lab.n = 1)) :
    B ≠ Bs := by
  obtain ⟨hZ, K, hK_field, hK_fin, hKcard, ⟨e⟩⟩ := nonempty_mulEquiv_unitarySeven_of_marking hm
  obtain ⟨lab, hlab, hhas, hR₂, hR₂grp, I, F, θ, hP⟩ :=
    CFSG.StandardType.largeEvenMarking_exists_hasLabel hm
  obtain ⟨hTag, hRank, hN⟩ := hP
  have hlab_eq : lab = ⟨.twA, 6, 1⟩ := by
    rw [← hTag, ← hRank, ← hN]
  subst hlab_eq
  obtain ⟨S, hSL, hS3, hSnc⟩ :=
    CFSG.StandardType.HdRo7LNC.hdRo7LNCAux_su_noncyclic rfl rfl (by norm_num) hhas
  have hN : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
    subgroupOf_centralizer_normal_of_noncyclic hR ⟨S, hSL, hS3, hSnc⟩
  have hsup := bstar_eq_sup_of_restHyp hR hN hZ (autThreePowInner_of_mulEquiv_unitarySeven hKcard e)
  obtain ⟨𝒦, -, -, hM⟩ := hAt
  have hBscard : 3 ^ 7 ≤ Nat.card Bs :=
    pow_le_card_of_weylOfType_of_two Nat.prime_three (by norm_num) hR.1.2.1.2.1 hM
      exists_elemAbelian_two_coxeterE7
  have hle := card_bstar_le_three_mul_inf hR hsup.2
  have h6 : 3 ^ 6 ≤ Nat.card ↥(Bs ⊓ L) := by
    have hmul : 3 * 3 ^ 6 ≤ 3 * Nat.card ↥(Bs ⊓ L) := by
      calc 3 * 3 ^ 6 = 3 ^ 7 := by norm_num
        _ ≤ Nat.card Bs := hBscard
        _ ≤ 3 * Nat.card ↥(Bs ⊓ L) := hle
    exact Nat.le_of_mul_le_mul_left hmul (by norm_num)
  refine ne_bstar_of_le_centralizer hR hN hsup.2 (fun T hT2 hTN hET => ?_)
  exact le_centralizer_of_unitarySeven hKcard e inf_le_right
    (IsElemAbelian.mono hR.1.2.1.2.1 inf_le_left)
    (by simpa [Fintype.card_sum] using h6)
    hT2 hTN hET

end CFSG.StandardType.FrameRoute
