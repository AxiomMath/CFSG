module

public import CFSG.Quasithin.H13.NQBlockOriginalKSingleton
public import CFSG.Quasithin.H13.NQBlockOriginalReducedModule
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def StmtOverlapNormalizesOriginalK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ H : Subgroup G, T ≤ H → pCoreOf 2 H ≠ ⊥ → ¬ H ≤ M →
      H ⊓ M ≤ normalizer (nqOriginalK T L : Set G) ∧
        oTwoUpper (nqOriginalK T L ⊔ T) = nqOriginalK T L

@[expose] def StmtAnotherMaximalTwoLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∃ H₀ : Subgroup G, quasithinIsMaxTwoLocal H₀ ∧ T ≤ H₀ ∧ H₀ ≠ M

theorem thompson_generation_of_inputs
    (h317 : Theorem317Statement) (hAnother : StmtAnotherMaximalTwoLocal)
    (hS : NQBlock.OriginalKEscapingSourceY) (hE : NQBlock.OriginalNoNormalSourceYEscapes)
    (hNK : StmtOverlapNormalizesOriginalK) {T L M : Subgroup G} (h : QTNQ T L M) :
    ⁅L, (CFSG.elemThompson T 2).map T.subtype⁆ = L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hLJ
  have hTL : T ≤ normalizer (L : Set G) := h.eq_normalizer ▸ h.t_le
  obtain ⟨R, hR⟩ := NQBlock.exists_originalCentralizer hTL
  have hRT : R ≤ T := fun x hx => by
    have hx' : x ∈ nqOriginalCentralizer T L := by
      rw [← hR]
      exact hx
    exact hx'.1
  obtain ⟨-, -, -, -, -, -, -, hfail⟩ :=
    NQBlock.original_radical_normalizer_local_and_Thompson_failure h hR
  obtain ⟨hJR, -, -, -, -⟩ := hfail hLJ
  obtain ⟨hMmax, hKTM, hKTuniq⟩ := NQBlock.original_K_singleton_of_inputs hS hE h
  obtain ⟨H₀, hH₀, hTH₀, hH₀M⟩ := hAnother G T L M h
  obtain ⟨H, hH⟩ := exists_isHStar (T := T) (M := M) ⟨hH₀, hTH₀⟩ ⟨hMmax, h.t_le⟩ hH₀M
  obtain ⟨-, -, -, -, -, hV₀red, -, -, hTV₀, hRO⟩ :=
    NQBlock.original_common_residual_is_faithful_and_has_exact_reduced_action_kernel h hR
  have hV₀ : IsTwoReducedIn (nqOriginalK T L ⊔ T)
      ((primeReducedAggregate ↥(nqOriginalK T L ⊔ T) 2).map (nqOriginalK T L ⊔ T).subtype) := by
    refine isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨map_subtype_le _, ?_⟩
    have hsub : ((primeReducedAggregate ↥(nqOriginalK T L ⊔ T) 2).map
        (nqOriginalK T L ⊔ T).subtype).subgroupOf (nqOriginalK T L ⊔ T) =
        primeReducedAggregate ↥(nqOriginalK T L ⊔ T) 2 :=
      comap_map_eq_self_of_injective (nqOriginalK T L ⊔ T).subtype_injective _
    rw [hsub]
    exact hV₀red
  obtain ⟨hHM, hKodd⟩ := hNK G T L M h H hH.1.1 hH.1.2 hH.2.1
  have hcaseI : Hyp315.CaseI M (nqOriginalK T L ⊔ T) H := by
    show H ⊓ M ≤ normalizer (oTwoUpper (nqOriginalK T L ⊔ T) : Set G)
    rw [hKodd]
    exact hHM
  have hyp : Hyp315 T M (nqOriginalK T L ⊔ T) H
      ((primeReducedAggregate ↥(nqOriginalK T L ⊔ T) 2).map (nqOriginalK T L ⊔ T).subtype) :=
    { T_le := le_sup_right
      le_M := hKTM
      hStar := hH
      reduced := hV₀
      centralizer := hRO.symm.trans hTV₀.symm
      case := Or.inl hcaseI }
  have hJ : thompsonJ T ≤ pCoreOf 2 (nqOriginalK T L ⊔ T) := by
    rw [← elemThompson_map_subtype_eq_thompsonJ, ← hRO]
    exact hJR
  rcases h317 G T h.simple h.nonabelian h.qtke h.sylow M (nqOriginalK T L ⊔ T) H _
      ⟨hMmax, h.t_le⟩ hyp hJ with ⟨hZ, -⟩ | ⟨R₀, hR₀, hR₀O, hR₀N⟩
  ·
    apply hH.2.1
    intro x hx
    apply h.centralizer_le
    rw [mem_centralizer_iff]
    intro z hz
    have hzc : z ∈ centralizer (H : Set G) :=
      (mem_inf.mp (hZ (show z ∈ quasithinOmegaOneCenter T from hz))).2
    exact ((mem_centralizer_iff.mp hzc) x hx).symm
  ·
    have hR₀2 : IsPGroup 2 R₀ := h.sylow.1.to_le (hR₀O.trans (hRO ▸ hRT))
    have hloc : IsTwoLocal (normalizer (R₀ : Set G)) := ⟨R₀, hR₀, hR₀2, rfl⟩
    obtain ⟨M', hM', hle⟩ := NQBlock.exists_maxTwoLocal_ge_of_isTwoLocal hloc
    have hM'M : M' = M := hKTuniq M' hM' ((le_sup_left.trans hR₀N).trans hle)
    apply hH.2.1
    rw [← hM'M]
    exact (le_sup_right.trans hR₀N).trans hle

end CFSG.Quasithin.H13.NQRigid
