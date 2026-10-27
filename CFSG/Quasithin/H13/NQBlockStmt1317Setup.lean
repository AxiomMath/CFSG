module

public import CFSG.Quasithin.H13.NQBlockStmt1317
public import CFSG.Quasithin.H13.NQTermInternalModule
public import CFSG.Quasithin.SteinbergBMCentralizerRigidityTI
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin.H13
open CFSG.Quasithin.BlueprintB2 (centerTorsion mem_centerTorsion_iff)

@[expose] def NonquasisimpleRadicalNormalizerWitness : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    (∃ K : Subgroup G, quasithinIsFaithfulLocal T K ∧
      ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) →
    ∃ L X : Subgroup G,
      (quasithinIsMaximalLocal T L ∧ quasithinIsFaithfulLocal T L) ∧
      ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      T ≤ normalizer (L : Set G) ∧
      X ≤ (CFSG.solvableRadical ↥L).map L.subtype ∧
      (quasithinIsMaxTwoLocal (normalizer (L : Set G)) ∧ X ⊔ T ≤ normalizer (L : Set G) ∧
        ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → X ⊔ T ≤ M' →
          M' = normalizer (L : Set G)) ∧
      L ⊓ centralizer (qtnqVc (normalizer (L : Set G)) : Set G) =
        (CFSG.solvableRadical ↥L).map L.subtype

@[expose] def NonquasisimpleInternalCentralizerRigidity : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ u ∈ qtnqU L M, u ≠ 1 → centralizer ({u} : Set G) ≤ M ∧
      ∀ g : G, M ⊓ centralizer ({u} : Set G) ≤ CFSG.conjugate M g → CFSG.conjugate M g = M

theorem nonquasisimpleInternalModuleTI_of_rigidity
    (hR : NonquasisimpleInternalCentralizerRigidity) : NonquasisimpleInternalModuleTI := by
  intro G _ _ T L M h
  obtain ⟨-, -, -, -, ⟨hU1, hUM, hUn, -⟩, hNM⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  exact ⟨hU1, CFSG.Quasithin.SteinbergBM.centralizer_rigidity_implies_TI hNM hUM hUn
    (fun u hu hu1 => (hR G T L M h u hu hu1).1) (fun u hu hu1 => (hR G T L M h u hu hu1).2)⟩

theorem quasithinOmegaOneCenter_le_qtnqVc {G : Type} [Group G] [Finite G] {T M : Subgroup G}
    (hQ : QuasithinUnique.quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) (hTM : T ≤ M) :
    quasithinOmegaOneCenter T ≤ qtnqVc M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hT.1, ?_⟩
    change ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2
  have hchar : QuasithinUnique.CharTwo M :=
    QuasithinUnique.charTwo_of_isTwoLocal_of_isSylowTwoOf_le hQ.2.1 hT' hM.1 hTM
  have hcharP : CFSG.IsCharacteristicP 2 M :=
    QuasithinUnique.EscapingLocal.isCharacteristicP_of_charTwo hchar
  have hTs : IsPGroup 2 (T.subgroupOf M) :=
    hT.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
  have hTi : ¬ 2 ∣ (T.subgroupOf M).index := fun hd =>
    hT.2 (hd.trans (Subgroup.relIndex_dvd_index_of_le hTM))
  set T' : Sylow 2 M := hTs.toSylow hTi
  have hT'c : (T' : Subgroup M) = T.subgroupOf M := IsPGroup.toSylow_coe hTs hTi
  have hZT : (quasithinOmegaOneCenter T).subgroupOf M ≤ centerTorsion 2 (T' : Subgroup M) := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    obtain ⟨hzT, hzc, hz2⟩ :=
      mem_centerTorsion_iff.mp (NQTerm.quasithinOmegaOneCenter_le_centerTorsion T hz)
    rw [mem_centerTorsion_iff, hT'c]
    exact ⟨hzT, fun k hk => Subtype.ext (hzc k hk), Subtype.ext hz2⟩
  obtain ⟨-, -, hZW, hWR⟩ :=
    QuasithinUnique.Setup.qt_characteristic_p_Sylow_center_reduced_closure 2 hcharP T' hZT
  intro z hz
  have hzM : z ∈ M :=
    hTM (mem_centerTorsion_iff.mp (NQTerm.quasithinOmegaOneCenter_le_centerTorsion T hz)).1
  exact ⟨⟨z, hzM⟩, hWR (hZW hz), rfl⟩

theorem sylow_ne_bot_of_twoLocal {G : Type} [Group G] [Finite G] {T M : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hM : IsTwoLocal M) : T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP1, hP2, -⟩ := hM
  intro hT1
  apply hT.2
  rw [hT1, index_bot]
  have hP : 2 ∣ Nat.card P := (hP2.card_eq_or_dvd).resolve_left
    (fun h => hP1 ((card_eq_one).mp h))
  exact hP.trans (card_subgroup_dvd_card P)

theorem nonquasisimpleMaximalNormalizerSetup_of_witness
    (hW : NonquasisimpleRadicalNormalizerWitness) : NonquasisimpleMaximalNormalizerSetup := by
  intro G _ _ T hs hnab hQ hT hexcl hK
  classical
  obtain ⟨L, X, ⟨hLmax, hLf⟩, hLq, hTM, hXR, ⟨hMmax, hXTM, hXTu⟩, hCR⟩ :=
    hW G T hs hnab hQ hT hexcl hK
  have hZV := quasithinOmegaOneCenter_le_qtnqVc hQ hT hMmax hTM
  have hT1 := sylow_ne_bot_of_twoLocal hT hMmax.1
  have hZ1 : quasithinOmegaOneCenter T ≠ ⊥ := QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hT.1 hT1
  have hZT : quasithinOmegaOneCenter T ≤ T := by
    rw [quasithinOmegaOneCenter, closure_le]
    exact fun z hz => (mem_inf.mp hz.1).1
  have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter T) := hT.1.to_le hZT
  have hXT : X ⊔ T ≤ centralizer (quasithinOmegaOneCenter T : Set G) := by
    refine sup_le ?_ ?_
    · refine (hXR.trans (hCR.symm.le.trans inf_le_right)).trans ?_
      exact centralizer_le hZV
    · refine le_centralizer_iff.mp ?_
      rw [quasithinOmegaOneCenter, closure_le]
      exact fun z hz => (mem_inf.mp hz.1).2
  have hMset : {K : Subgroup G | CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal K ∧
      ((X ⊔ T : Subgroup G) : Set G) ⊆ (K : Set G)} = {normalizer (L : Set G)} := by
    ext K
    constructor
    · rintro ⟨hK, hXK⟩
      exact hXTu K hK hXK
    · intro hK
      rw [Set.mem_singleton_iff] at hK
      subst hK
      exact ⟨hMmax, hXTM⟩
  obtain ⟨hCN, hNM, hCset, -⟩ := QuasithinUnique.maxTwoLocal_centralizer_transfer hZ1 hZ2
    (fun x hx => hXT hx) hMset
  have hXL : X ≤ L := hXR.trans (map_subtype_le _)
  refine ⟨L, normalizer (L : Set G),
    { simple := hs
      nonabelian := hnab
      qtke := hQ
      sylow := hT
      not_excluded := hexcl
      maximal_local := hLmax
      faithful_local := hLf
      not_quasisimple := hLq
      t_le := hTM
      eq_normalizer := rfl
      max_two_local := hMmax
      join_le := sup_le le_normalizer hTM
      join_unique := fun M' hM' hLT => hXTu M' hM' ((sup_le_sup_right hXL T).trans hLT)
      centralizer_eq_radical := hCR
      centralizer_le := hCN.trans hNM
      centralizer_unique := fun M' hM' hCM' => by
        have : M' ∈ ({normalizer (L : Set G)} : Set (Subgroup G)) := by
          rw [← hCset]
          exact ⟨hM', hCM'⟩
        exact this }⟩

theorem stmt13_1_7_of_witness_rigidity (hW : NonquasisimpleRadicalNormalizerWitness)
    (hR : NonquasisimpleInternalCentralizerRigidity)
    (hC : NonquasisimpleTITerminalContradiction) : Stmt13_1_7 :=
  stmt13_1_7_of_inputs (nonquasisimpleMaximalNormalizerSetup_of_witness hW)
    (nonquasisimpleInternalModuleTI_of_rigidity hR) hC

end CFSG.Quasithin.H13.NQBlock
