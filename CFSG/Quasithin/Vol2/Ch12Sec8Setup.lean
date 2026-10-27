module

public import CFSG.Quasithin.EmptyFaithful.S142Basic
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.A4Four
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G]

theorem oTwoUpper_oTwoUpper (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun x hx => ?_)
  exact mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2

structure Hyp1281Two (G : Type) [Group G] [Finite G] (T M L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  inM : InM T M
  rank_two : Nat.card (VZ T M) = 4
  residual : oTwoUpper L = L
  le : L ≤ M
  normal : M ≤ Subgroup.normalizer (L : Set G)
  unique : IsUniqueM (L ⊔ T) M
  centralizer : (L ⊔ T) ⊓ Subgroup.centralizer (VZ T M : Set G) = pCoreOf 2 (L ⊔ T)
  sThree : Nonempty (OTwoQuot (L ⊔ T) ≃* Equiv.Perm (Fin 3))
  not_le : ¬ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M

@[expose] def yOfL22 (T M : Subgroup G) : Subgroup G :=
  oTwoUpper (conjClosure
    (pCoreOf 2 (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) M)

theorem yOfL22_le (T M : Subgroup G) : yOfL22 T M ≤ M :=
  (oTwoUpper_le _).trans (conjClosure_le fun _ hh _ hz =>
    M.mul_mem (M.mul_mem hh ((LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left hz))
      (M.inv_mem hh))

theorem le_normalizer_yOfL22 (T M : Subgroup G) :
    M ≤ Subgroup.normalizer (yOfL22 T M : Set G) :=
  (le_normalizer_conjClosure _ M).trans (normalizer_le_normalizer_oTwoUpper _)

theorem oTwoUpper_yOfL22 (T M : Subgroup G) : oTwoUpper (yOfL22 T M) = yOfL22 T M :=
  oTwoUpper_oTwoUpper _

namespace Hyp1421

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem centralizer_not_le (h : Hyp1421 G T M) :
    ¬ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M := fun hle =>
  h.ne_centralizer (h.mc_max.2 M h.m_max.1.1.1 hle)

theorem hyp1281Two (h : Hyp1421 G T M) (hU : IsUniqueM (yOfL22 T M ⊔ T) M)
    (hC : (yOfL22 T M ⊔ T) ⊓ Subgroup.centralizer (VZ T M : Set G) =
      pCoreOf 2 (yOfL22 T M ⊔ T))
    (hS : Nonempty (OTwoQuot (yOfL22 T M ⊔ T) ≃* Equiv.Perm (Fin 3))) :
    Hyp1281Two G T M (yOfL22 T M) where
  simple := h.simple
  nonabelian := h.nonabelian
  qtke := h.qtke
  sylow := h.sylow
  inM := h.m_max.1
  rank_two := h.rank_two
  residual := oTwoUpper_yOfL22 T M
  le := yOfL22_le T M
  normal := le_normalizer_yOfL22 T M
  unique := hU
  centralizer := hC
  sThree := hS
  not_le := h.centralizer_not_le

end Hyp1421

end CFSG.Quasithin
