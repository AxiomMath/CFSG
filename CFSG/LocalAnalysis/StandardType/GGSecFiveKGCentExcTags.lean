module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRoot
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.ChevLink
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreTorus
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentExcTorus
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentExcCore
import CFSG.Adapters.ClassicalCatalogLinearUnitary
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Engine
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadicalSmall
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Background.B1
import CFSG.Quasithin.Background.C1GNC124
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.C31Steps
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E2Three
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.GoldschmidtS146RArith2
import CFSG.Quasithin.Background.InternalSecB56B
import CFSG.Quasithin.EmptyFaithful.R3c20A
import CFSG.Quasithin.EmptyFaithful.R3c21A
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S151YC
import CFSG.Quasithin.EmptyFaithful.S151cA2
import CFSG.Quasithin.EmptyFaithful.S151cCases
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.EmptyFaithful.S153H32
import CFSG.Quasithin.EmptyFaithful.SBc5Aut
import CFSG.Quasithin.EmptyFaithful.SzN17Abs
import CFSG.Quasithin.EmptyFaithful.T1515Top9
import CFSG.Quasithin.EmptyFaithful.T1531Cat
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
import CFSG.Quasithin.H13.J4Classes
import CFSG.Quasithin.H13.J4Core
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Recognition.CertTwoLocalPair
import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11StatementsF
import CFSG.Quasithin.Vol2.Ch11StatementsG
import CFSG.Quasithin.Vol2.Ch11StatementsH
import CFSG.Quasithin.Vol2.Ch11StatementsInputs
import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
import CFSG.Quasithin.Vol2.KGFactC31A7
import CFSG.Quasithin.Vol2.KGFactC31Blk
import CFSG.Quasithin.Vol2.KGFactC31HSCases
import CFSG.Quasithin.Vol2.KGFactC31HSMod
import CFSG.Quasithin.Vol2.KGFactC31Hat
import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Universal CFSG.SeitzReduction

theorem ggKGCentTagStmt_E8
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput) : GGKGCentTagStmt .E8 := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ hJR X hX n f ψ hloc hstd t ht htN htD htJ
  obtain ⟨r, hr, hrefl⟩ := hJR
  have hf : 1 ≤ f := hloc.1.2.2.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hψ : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 (eq_bot_iff.2
    (hloc.2.1.1.trans (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).le))
  have htN' : t ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hloc.2.1.2.1]; exact htN
  have hroot : ∀ β, β ∈ (ggU .E8 n f).D.roots ↔ IsRoot .E8 β := fun β =>
    Adjoint.mem_adjDatum_roots (F := rootOperatorFamily .E8) (K := GaloisField 2 f)
  have hcent := KGCentExc.mem_centralizer_of_kgCent_adj (τ := .E8) (K := GaloisField 2 f)
    (Or.inr rfl) hf hK hloc.1.1 hloc.1.2.1 (by rw [Nat.card_units, hK]; exact hloc.2.1.2.2.2) hψ
    (fun d hd => by
      have hdB := SecFiveL1Odd.le_bstar hcfg hd
      obtain ⟨u, hu, hdu⟩ := jcore_inner_torus _ hψ hstd hdB
        (PsiDiag.Adj.exists_mem_centralizer_E8 (K := GaloisField 2 f) ψ hloc.2.1.1
          (hloc.2.2.2.1 d hdB))
      refine ⟨hloc.2.2.1.1.2 d hdB, u,
        KGCentExc.mem_torusGroup_of_forall_mem_normalizer_rootSubgroup (Subtype.property u)
          fun γ hγ => ?_, hdu⟩
      rw [← HardMathSupport.Cooperstein.Coordinator.LieInput.map_rootGroup_eq_rootSubgroup hγ]
      exact Subgroup.le_normalizer_map _
        ⟨u, Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hu γ) ((hroot γ).2 hγ), rfl⟩)
    (Φ := ggKGCentRoots (ggU .E8 n f).D ψ D)
    (fun β => ⟨fun ⟨hβ, hle⟩ => ⟨(hroot β).1 hβ, fun c => hle
        ((KGCentExc.mem_rootGroup_iff_pinnedElt ((hroot β).1 hβ)).2 ⟨c, rfl⟩)⟩,
      fun ⟨hβ, hc⟩ => ⟨(hroot β).2 hβ, fun z hz => by
        obtain ⟨c, rfl⟩ := (KGCentExc.mem_rootGroup_iff_pinnedElt hβ).1 hz
        exact hc c⟩⟩)
    (fun β hβ c => ggKGCent_rootGroup_le ha₀ hL hcfg hr hrefl hX hloc hstd hβ
      (Subgroup.mem_map_of_mem ψ ((KGCentExc.mem_rootGroup_iff_pinnedElt ((hroot β).1 hβ.1)).2
        ⟨c, rfl⟩)))
    (let ⟨β, hβ, _⟩ := ggKGCent_exists_root_add ha₀ hL hcfg hr hrefl hX hloc hstd; ⟨β, hβ⟩)
    ht htN' htD htJ
  intro g hg h _
  rw [← hloc.2.1.2.1] at hg
  rw [← Subgroup.mem_centralizer_iff.1 hcent g hg, mul_inv_cancel_right, mul_inv_cancel]
  exact Commute.one_left h

theorem ggKGCentTagStmt_E7
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput) : GGKGCentTagStmt .E7 := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ hJR X hX n f ψ hloc hstd t ht htN htD htJ
  obtain ⟨r, hr, hrefl⟩ := hJR
  have hf : 1 ≤ f := hloc.1.2.2.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  set Θ := E8Pilot.e7MinEquivAdjoint (GaloisField 2 f)
  have hψ : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 (eq_bot_iff.2
    (hloc.2.1.1.trans (E8Pilot.center_minGroup_e7_eq_bot (K := GaloisField 2 f)).le))
  have hr' : (ψ.comp Θ.symm.toMonoidHom).range = X := by
    rw [← hloc.2.1.2.1]
    ext y
    exact ⟨fun ⟨k, hk⟩ => ⟨Θ.symm k, hk⟩,
      fun ⟨z, hz⟩ => ⟨Θ z, (congrArg ψ (Θ.symm_apply_apply z)).trans hz⟩⟩
  have htN' : t ∈ Subgroup.normalizer ((ψ.comp Θ.symm.toMonoidHom).range : Set G) := by
    rw [hr']; exact htN
  have hroot : ∀ β, β ∈ (ggU .E7 n f).D.roots ↔ IsRoot .E7 β := fun β =>
    Minuscule.e7Data_valid.mem_minDatum_roots Minuscule.isFiniteType_cartan_E7 _
  have hsymm : ∀ β, IsRoot .E7 β → ∀ c,
      Θ.symm (EPilot.pinnedElt .E7 β c) ∈ (ggU .E7 n f).D.rootGroup β := fun β hβ c =>
    (KGCentExc.mem_e7Datum_rootGroup_iff hβ).2 ⟨c, rfl⟩
  have hcent := KGCentExc.mem_centralizer_of_kgCent_adj (τ := .E7) (K := GaloisField 2 f)
    (ψ := ψ.comp Θ.symm.toMonoidHom) (Or.inl rfl) hf hK hloc.1.1 hloc.1.2.1
    (by rw [Nat.card_units, hK]; exact hloc.2.1.2.2.2) (hψ.comp Θ.symm.injective)
    (fun d hd => by
      have hdB := SecFiveL1Odd.le_bstar hcfg hd
      obtain ⟨u, hu, hdu⟩ := jcore_inner_torus _ hψ hstd hdB
        (PsiDiag.Minu.exists_mem_centralizer_E7 (k := GaloisField 2 f) ψ hloc.2.1.1
          (hloc.2.2.2.1 d hdB))
      refine ⟨hloc.2.2.1.1.2 d hdB, Θ u,
        KGCentExc.mem_torusGroup_of_forall_mem_normalizer_rootSubgroup (Θ u).2 fun γ hγ => ?_,
        KGCentExc.conj_comp_symm Θ hdu⟩
      rw [← KGCentExc.map_e7Datum_rootGroup hγ]
      exact Subgroup.le_normalizer_map _
        ⟨u, Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hu γ) ((hroot γ).2 hγ), rfl⟩)
    (Φ := ggKGCentRoots (ggU .E7 n f).D ψ D)
    (fun β => ⟨fun ⟨hβ, hle⟩ => ⟨(hroot β).1 hβ, fun c => hle (hsymm β ((hroot β).1 hβ) c)⟩,
      fun ⟨hβ, hc⟩ => ⟨(hroot β).2 hβ, fun z hz => by
        obtain ⟨c, rfl⟩ := (KGCentExc.mem_e7Datum_rootGroup_iff hβ).1 hz
        exact hc c⟩⟩)
    (fun β hβ c => ggKGCent_rootGroup_le ha₀ hL hcfg hr hrefl hX hloc hstd hβ
      (Subgroup.mem_map_of_mem ψ (hsymm β ((hroot β).1 hβ.1) c)))
    (let ⟨β, hβ, _⟩ := ggKGCent_exists_root_add ha₀ hL hcfg hr hrefl hX hloc hstd; ⟨β, hβ⟩)
    ht htN' htD htJ
  intro g hg h _
  rw [← hr'] at hg
  rw [← Subgroup.mem_centralizer_iff.1 hcent g hg, mul_inv_cancel_right, mul_inv_cancel]
  exact Commute.one_left h

end CFSG.StandardType

end
