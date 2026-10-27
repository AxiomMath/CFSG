module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeAxB
public import CFSG.Quasithin.EmptyFaithful.R3c23Glue1

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure GroupPair (H T L : Subgroup G) (t : G) : Prop where
  tT : t ∈ T
  tN : t ∉ Subgroup.normalizer (L : Set G)
  hLt : L.map (MulAut.conj t).toMonoidHom ∈ cComp H
  comm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 H
  dich : ∀ x ∈ H, L.map (MulAut.conj x).toMonoidHom = L ∨
    L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj t).toMonoidHom

@[expose] def QuasiData (V L : Subgroup G) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (φ : ↥L →* Q), Function.Surjective φ ∧
    φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L ∧ CFSG.IsQuasisimple Q


theorem not_thompsonJ_le_centralizer' {H T L V : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hLH : L ≤ H)
    (hnJ : ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (V : Set G)) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := by
  intro hJC
  apply hnJ
  refine Subgroup.commutator_le.2 fun l hl j hj => ?_
  have hlN : l ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer V (hHN (hLH hl))
  have h1 : l * j * l⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    have := (Subgroup.mem_normalizer_iff.mp hlN j).mp (hJC hj)
    exact this
  have h2 : ⁅l, j⁆ = (l * j * l⁻¹) * j⁻¹ := commutatorElement_def l j
  rw [h2]
  exact mul_mem h1 (inv_mem (hJC hj))

end CFSG.Quasithin.C116Three
