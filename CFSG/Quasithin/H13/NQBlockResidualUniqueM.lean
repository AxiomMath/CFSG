module

public import CFSG.Quasithin.H13.NQCoreT2Holds

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem isUniqueM_canonical_residual
    {G : Type} [Group G] [Finite G] {T D : Subgroup G} (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hDm : quasithinIsMaximalLocal T D) (hDf : quasithinIsFaithfulLocal T D)
    (hTD : T ≤ normalizer (D : Set G)) (hDq : ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hCp : CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) ≠ ⊥) :
    IsUniqueM (nqPrimeResidualX D p ⊔ T) (normalizer (nqPrimeResidualX D p : Set G)) := by
  have := hs
  obtain ⟨-, hamb, hcan⟩ :=
    sylow_normalized_maximal_nonquasisimple_canonical_residual_structure
      sylowNormalizedMaximalLocalUniqueNormalizer_holds
      NQBlock.sylowNormalizedLocalNormalComponent_proved hnab hQ hT hDm hDf hTD hDq
  have hcanp := hcan p hp hp5 hCp
  have hSC : SCSetup T D (nqPrimeResidualX D p) p :=
    { simple := hs
      nonabelian := hnab
      qtke := hQ
      sylow := hT
      maximal_local := hDm
      faithful_local := hDf
      le_normalizer := hTD
      not_quasisimple := hDq
      prime := hp
      five_le := hp5
      ambient := hamb
      canonical := hcanp }
  have hUX := unique_maximal_overgroup_of stmtSCComponentOrbits_holds
    stmtSCNormalExclusion_holds stmtSCPairedExclusion_holds hSC
  rw [← hcanp.normalizer_eq]
  exact ⟨⟨hUX.1, hUX.2.1⟩, fun M' hM' => hUX.2.2 M' hM'.1 hM'.2⟩

end CFSG.Quasithin.H13.NQCore
