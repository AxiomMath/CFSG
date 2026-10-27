module

public import CFSG.Quasithin.H13.NQCoreT2Gap
public import CFSG.Quasithin.H13.NQCoreAnotherMaxLocal
public import CFSG.Quasithin.H13.NQBlockTerminalInputs
public import CFSG.Quasithin.H13.NQCoreHYSingleModels

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_minimal_escaping {T M H₀ : Subgroup G} (hTH₀ : T ≤ H₀) (hH₀M : ¬ H₀ ≤ M) :
    ∃ H : Subgroup G, T ≤ H ∧ H ≤ H₀ ∧ ¬ H ≤ M ∧
      ∀ K : Subgroup G, T ≤ K → K ≤ H₀ → ¬ K ≤ M → Nat.card H ≤ Nat.card K := by
  classical
  have hex : ∃ n, ∃ K : Subgroup G, T ≤ K ∧ K ≤ H₀ ∧ ¬ K ≤ M ∧ Nat.card K = n :=
    ⟨_, H₀, hTH₀, le_rfl, hH₀M, rfl⟩
  obtain ⟨H, hTH, hHH₀, hHM, hHn⟩ := Nat.find_spec hex
  exact ⟨H, hTH, hHH₀, hHM, fun K hTK hKH₀ hKM =>
    hHn ▸ Nat.find_min' hex ⟨K, hTK, hKH₀, hKM, rfl⟩⟩

theorem nonquasisimpleTIEscapingResidual_of
    (h3 : ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
      fusionIsBenderGroup G ∨ UniqueSmallModel G)
    (hD : LocalDoubleEmbeddingExclusion) (h37 : Vol2Native.A37ForSQTKCat)
    (hA7u : U3.SylowNormalizedMaximalLocalUniqueNormalizer)
    (hA7n : NQBlock.SylowNormalizedLocalNormalComponent)
    (hO : StmtSCComponentOrbits) (hN : StmtSCNormalExclusion) (hP : StmtSCPairedExclusion)
    (hI : StmtIntrinsicActionExclusion) (h1323 : Stmt13_1_2_three)
    (hrig : StmtFiveModelLocalChainRigid) (hpair : StmtEscapingPairExcluded)
    (hrank : StmtEscapingSingleTwoRank) : NQBlock.NonquasisimpleTIEscapingResidual := by
  intro G _ _ T L M h hTI hW
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H₀, hH₀, hTH₀, hH₀M⟩ := nq_original_configuration_has_another_maximal_two_local h3 h
  have hH₀M' : ¬ H₀ ≤ M := fun hle => hH₀M (hH₀.2 M h.max_two_local.1 hle).symm
  obtain ⟨H, hTH, hHH₀, hHM, hmin⟩ := exists_minimal_escaping hTH₀ hH₀M'
  have hsimple := hpair G T L M h hTI hW H₀ H hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨-, hJR, hsimpleE, hnab, hmodels⟩ := minimal_escaping_single_factor_models hD h37 hA7u
    hA7n hO hN hP hI h1323 hrig h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  have hm2 := hrank G T L M h hTI hW H₀ H hH₀ hTH₀ hTH hHH₀ hHM hmin hsimple hJR hmodels
  obtain ⟨⟨-, hYperf, hYchar⟩, ⟨-, hYM, h2grp⟩, -⟩ :=
    minimal_escaping_structure h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  have := hYchar
  refine ⟨H, (CFSG.perfectResidual ↥H).map H.subtype, inferInstance, hTH, map_subtype_le _,
    Subgroup.isPerfect_iff.mpr hYperf, fun q => ?_, hsimpleE, hnab, hYM, hm2⟩
  induction q using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨k, hk⟩ := h2grp x x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    simpa using hk

end CFSG.Quasithin.H13.NQCore
