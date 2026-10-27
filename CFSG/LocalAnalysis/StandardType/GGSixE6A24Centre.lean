module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6RootData
import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier
public import CFSG.LieType.Simplicity.Exceptional
import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4Generic
import CFSG.Foundations
import CFSG.LieType.Chevalley.RootCommutatorCertificate
import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint CFSG.Open

@[expose] def GGSixE6A24RootDataRest : Prop :=
  ∀ (E : Type) [Group E] [Finite E], commutator E = ⊤ →
    CFSG.Blueprint.LieModel (E ⧸ Subgroup.center E) .E6 0 2 1 →
    ∀ (x₀ : E) (L' J' : Subgroup E), x₀ ^ 3 = 1 →
      CFSG.Assembly.IsComponentOf L' (Subgroup.centralizer {x₀}) →
      CFSG.Blueprint.LieModel (↥L' ⧸ Subgroup.center ↥L') .PSL 6 2 1 →
      J' ≤ L' → CFSG.Assembly.IsQuasisimple ↥J' →
      CFSG.Blueprint.LieModel (↥J' ⧸ Subgroup.center ↥J') .PSL 3 2 2 →
      ∃ R' J₀' : Subgroup E, R' ≤ J' ∧ R' ≠ ⊥ ∧ IsPGroup 2 R' ∧ J₀' ≤ J' ∧
        pCoreOf 2 (Subgroup.normalizer (R' : Set E)) ⊔ J₀' = ⊤ ∧
        (∀ Q' : Subgroup E, Q' = pCoreOf 2 (Subgroup.normalizer (R' : Set E)) →
          ∀ U : Subgroup E, (Subgroup.center ↥Q').map Q'.subtype ≤ U → U ≤ Q' →
            U ≠ (Subgroup.center ↥Q').map Q'.subtype → U ≠ Q' →
            Subgroup.normalizer (R' : Set E) ≤ Subgroup.normalizer (U : Set E) →
            J' ⊔ U = ⊤) ∧
        GGRootNormInner R' ∧
        ∀ g : E, g ^ 3 = 1 → g ≠ 1 → g ∈ Subgroup.centralizer {x₀} →
          g ∈ Subgroup.centralizer (J' : Set E) →
          ∀ K' : Subgroup E, J' ≤ K' →
            CFSG.Assembly.IsComponentOf K' (Subgroup.centralizer {g}) →
            GGRootNormNoCentral (R'.subgroupOf K') ∧
              (GGRootNormInner (R'.subgroupOf K') ∨
                ∃ δ : ↥(Subgroup.normalizer (K' : Set E)),
                  (δ : E) ∈ Subgroup.centralizer {g} ∧
                    (δ : E) ∈ Subgroup.normalizer (R' : Set E) ∧
                    GGRootNormInnerDiag (R'.subgroupOf K') (K'.normalizerMonoidHom δ))

section Centre

open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds in
theorem ggSixE6A24_center_eq_bot (E : Type) [Group E] [Finite E] (hperf : commutator E = ⊤)
    (hL : LieModel (E ⧸ Subgroup.center E) .E6 0 2 1) : Subgroup.center E = ⊥ := by
  rcases hL with ⟨ht, -⟩ | ⟨-, -, hch⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · have hsimple := (CFSG.LieType.Simplicity.fam_e6_simplicity (E ⧸ Subgroup.center E) 2 1 hch).2
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hch
    have hK2 : Nat.card K = 2 := by simpa using hK
    haveI := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hK2)
    obtain ⟨-, ⟨f⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.FieldTwo.e6_two_hopfMultiplier (K := K) hK2
    have hsub : Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E6 K)) := by
      haveI : Subsingleton (Multiplicative (ZMod (Nat.gcd 3 (Nat.card K - 1)))) := by
        rw [hK2]
        exact inferInstanceAs (Subsingleton (ZMod 1))
      exact f.toEquiv.subsingleton
    have hQ : CFSG.Open.IsQuasisimple E := ⟨hperf, hsimple⟩
    exact center_eq_bot_of_hopf_subsingleton' hQ e hsub
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem ggSixE6A24RootData_of_rest (h : GGSixE6A24RootDataRest) : GGSixE6A24RootData :=
  fun E _ _ hperf hL => ⟨ggSixE6A24_center_eq_bot E hperf hL, h E hperf hL⟩

end Centre

end CFSG.StandardType
