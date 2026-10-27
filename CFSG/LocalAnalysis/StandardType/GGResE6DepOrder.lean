module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModule
public import CFSG.LocalAnalysis.StandardType.GGTBRowE6Equiv
public import CFSG.GroupTheory.AutomorphismAction.CommutingPGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nL4o_coxeterMatrix_E6 :
    CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E6) =
      CoxeterMatrix.E₆ :=
  coxeterMatrix_eq_of_ggIntCartan
    (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E6)
    (by
      rw [show CFSG.Blueprint.Chevalley.Tag.cartan CFSG.Blueprint.Chevalley.Tag.E6 =
          CartanMatrix.E 6 from CFSG.LieType.Chevalley.cartanE_eq 6]
      exact ggIntCartan_E₆)

theorem ggResE6DepShape_card_automizer
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    (hS : GGResE6DepShape p Bs L J K) :
    Nat.card ↥(ggAutomizer L Bs) = 51840 ∧ Nat.card ↥(ggAutomizer K Bs) = 51840 := by
  have hS' : p = 3 ∧ Nat.card Bs = 3 ^ 6 ∧ GGResLeviDatum p Bs L J K ggSelDep ggTypLKE6 := hS
  obtain ⟨-, -, hD⟩ := hS'
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -⟩ := hD
  have h5' : GGIsTypeE6 ML ∧ GGIsTypeE6 MK := h5
  obtain ⟨⟨eL, heL⟩, ⟨eK, heK⟩⟩ := h5'
  obtain ⟨fL, -⟩ := h11
  obtain ⟨fK, -⟩ := h12
  have hE6 : Nat.card CoxeterMatrix.E₆.Group = 51840 := by
    rw [← l05nL4o_coxeterMatrix_E6]
    exact NoOffExc.card_weyl_E6
  have cardML : Nat.card ML.Group = 51840 := by
    rw [heL]
    exact (Nat.card_congr (CoxeterMatrix.reindexGroupEquiv CoxeterMatrix.E₆ eL).toEquiv).trans hE6
  have cardMK : Nat.card MK.Group = 51840 := by
    rw [heK]
    exact (Nat.card_congr (CoxeterMatrix.reindexGroupEquiv CoxeterMatrix.E₆ eK).toEquiv).trans hE6
  exact ⟨(Nat.card_congr fL.toEquiv).symm.trans cardML,
    (Nat.card_congr fK.toEquiv).symm.trans cardMK⟩

theorem card_ggAutomizer_of_typeE6
    {G : Type} [Group G] {Bs X : Subgroup G}
    {Λ : Type} {M : CoxeterMatrix Λ} (hM : GGIsTypeE6 M)
    (f : M.Group ≃* ↥(ggAutomizer X Bs)) :
    Nat.card (ggAutomizer X Bs) = 51840 := by
  obtain ⟨e, he⟩ := hM
  have hE6 : Nat.card CoxeterMatrix.E₆.Group = 51840 := by
    rw [← l05nL4o_coxeterMatrix_E6]
    exact NoOffExc.card_weyl_E6
  rw [← Nat.card_congr f.toEquiv, he]
  exact (Nat.card_congr (CoxeterMatrix.reindexGroupEquiv CoxeterMatrix.E₆ e).toEquiv).trans hE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

end CFSG.StandardType
