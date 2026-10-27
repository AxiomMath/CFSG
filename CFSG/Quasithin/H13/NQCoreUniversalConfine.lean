module

public import CFSG.Quasithin.H13.NQCoreIntrinsicActionStmt
public import CFSG.Quasithin.H13.NQCoreSChainStmts
public import CFSG.Quasithin.H13.NQCoreRadicalCentralizerProof

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.BlueprintB2 (centerTorsion mem_centerTorsion_iff)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem quasithinOmegaOneCenter_le_reduced {T E : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTE : T ≤ E) (hchar : CharTwo E) :
    quasithinOmegaOneCenter T ≤ (primeReducedAggregate ↥E 2).map E.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcharP : CFSG.IsCharacteristicP 2 E := EscapingLocal.isCharacteristicP_of_charTwo hchar
  have hTs : IsPGroup 2 (T.subgroupOf E) :=
    hT.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTE).symm
  have hTi : ¬ 2 ∣ (T.subgroupOf E).index := fun hd =>
    hT.2 (hd.trans (Subgroup.relIndex_dvd_index_of_le hTE))
  set T' : Sylow 2 E := hTs.toSylow hTi
  have hT'c : (T' : Subgroup E) = T.subgroupOf E := IsPGroup.toSylow_coe hTs hTi
  have hZT : (quasithinOmegaOneCenter T).subgroupOf E ≤ centerTorsion 2 (T' : Subgroup E) := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    obtain ⟨hzT, hzc, hz2⟩ :=
      mem_centerTorsion_iff.mp (NQTerm.quasithinOmegaOneCenter_le_centerTorsion T hz)
    rw [mem_centerTorsion_iff, hT'c]
    exact ⟨hzT, fun k hk => Subtype.ext (hzc k hk), Subtype.ext hz2⟩
  obtain ⟨-, -, hZW, hWR⟩ :=
    QuasithinUnique.Setup.qt_characteristic_p_Sylow_center_reduced_closure 2 hcharP T' hZT
  intro z hz
  have hzE : z ∈ E :=
    hTE (mem_centerTorsion_iff.mp (NQTerm.quasithinOmegaOneCenter_le_centerTorsion T hz)).1
  exact ⟨⟨z, hzE⟩, hWR (hZW hz), rfl⟩

theorem normalizer_eq_of_qtTMaxNQPrime
    (hA7u : U3.SylowNormalizedMaximalLocalUniqueNormalizer)
    (hA7n : NQBlock.SylowNormalizedLocalNormalComponent)
    (hO : StmtSCComponentOrbits) (hN : StmtSCNormalExclusion) (hP : StmtSCPairedExclusion)
    (hI : StmtIntrinsicActionExclusion) {T L M D X : Subgroup G} {p : ℕ}
    (hX : QTTMaxNQPrime T L M D p X) :
    normalizer (D : Set G) = M ∧ U3.UniqueMaxTwoLocal (X ⊔ T) (normalizer (D : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hX.qtnq
  obtain ⟨hA, hC⟩ := SNCanonical.of_qtTMaxNQPrime hA7u hA7n hX
  have hS : SCSetup T D X p := ⟨h.simple, h.nonabelian, h.qtke, h.sylow, hX.maximal_local,
    hX.faithful_local, hX.le_normalizer, hX.not_quasisimple, hX.prime, hX.five_le, hA, hC⟩
  have hU := unique_maximal_overgroup_of hO hN hP hS
  refine ⟨?_, hU⟩
  by_contra hJM
  have hcomm := hI G T L M D X p hX hJM hU
  have hXE : X ≤ X ⊔ T := le_sup_left
  have hEN : X ⊔ T ≤ normalizer (X : Set G) := by
    rw [← hC.normalizer_eq]
    exact sup_le (hC.le.trans le_normalizer) hX.le_normalizer
  have hn : (X.subgroupOf (X ⊔ T)).Normal := (normal_subgroupOf_iff_le_normalizer hXE).mpr hEN
  have hRX : ⁅(primeReducedAggregate ↥(X ⊔ T) 2).map (X ⊔ T).subtype, X⁆ = ⊥ := by
    by_contra hne
    exact (reduced_witness_of_le hXE hn hC.noTwoQuotient).1 hne hcomm
  have hO2X : pCoreOf 2 X ≠ ⊥ := by
    intro hb
    apply hC.pCore_ne_bot
    exact (map_eq_bot_iff_of_injective _ X.subtype_injective).mp hb
  have hO2E : pCoreOf 2 (X ⊔ T) ≠ ⊥ := by
    intro hb
    apply hO2X
    rw [eq_bot_iff, ← hb]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXE)
      (hEN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hT' : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, h.sylow.1, ?_⟩
    change ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h.sylow.2
  have hchar : CharTwo (X ⊔ T) :=
    charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot h.qtke.2.1 hT' le_sup_right hO2E
  have hZ := quasithinOmegaOneCenter_le_reduced h.sylow le_sup_right hchar
  have hXM : X ≤ M := by
    refine le_trans (fun x hx => ?_) h.centralizer_le
    rw [mem_centralizer_iff]
    intro z hz
    have h1 : ⁅z, x⁆ ∈ ⁅(primeReducedAggregate ↥(X ⊔ T) 2).map (X ⊔ T).subtype, X⁆ :=
      commutator_mem_commutator (hZ hz) hx
    rwa [hRX, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact hJM (hU.2.2 M h.max_two_local (sup_le hXM h.t_le)).symm

theorem every_sylow_normalized_maximal_nonquasisimple_local_is_confined
    (hA7u : U3.SylowNormalizedMaximalLocalUniqueNormalizer)
    (hA7n : NQBlock.SylowNormalizedLocalNormalComponent)
    (hO : StmtSCComponentOrbits) (hN : StmtSCNormalExclusion) (hP : StmtSCPairedExclusion)
    (hI : StmtIntrinsicActionExclusion) {T L M D : Subgroup G} (h : QTNQ T L M)
    (hDmax : quasithinIsMaximalLocal T D) (hDf : quasithinIsFaithfulLocal T D)
    (hTD : T ≤ normalizer (D : Set G)) (hDq : ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D)) :
    D ≤ M ∧ normalizer (D : Set G) = M ∧
      ∀ (p : ℕ) (X : Subgroup G), QTTMaxNQPrime T L M D p X →
        U3.UniqueMaxTwoLocal (X ⊔ T) M := by
  have := h.simple
  obtain ⟨⟨p, hp, hp5, hCp⟩, -, -⟩ :=
    sylow_normalized_maximal_nonquasisimple_canonical_residual_structure hA7u hA7n h.nonabelian
      h.qtke h.sylow hDmax hDf hTD hDq
  have hX : QTTMaxNQPrime T L M D p (nqPrimeResidualX D p) :=
    ⟨h, hDmax, hDf, hTD, hDq, hp, hp5, hCp, rfl⟩
  have hJ := (normalizer_eq_of_qtTMaxNQPrime hA7u hA7n hO hN hP hI hX).1
  refine ⟨fun d hd => hJ ▸ le_normalizer hd, hJ, fun p' X' hX' => ?_⟩
  obtain ⟨hJ', hU'⟩ := normalizer_eq_of_qtTMaxNQPrime hA7u hA7n hO hN hP hI hX'
  rwa [hJ'] at hU'

end CFSG.Quasithin.H13.NQCore
