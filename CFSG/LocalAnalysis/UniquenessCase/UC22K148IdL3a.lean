module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdT
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Graph
public import CFSG.Milestones.ASVolI.B4Ext.GL4
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Bridge
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.QuasithinUnique.Setup.Offender (weight commGL fixGL)
open Module

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem imgGL_congr {H₁ H₂ : Subgroup G} {U : Submodule (ZMod 2) V} (h₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H₁ U)
    (h₂ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H₂ U) {X : Subgroup G} (hX₁ : X ≤ H₁) (hX₂ : X ≤ H₂) :
    imgGL ρ H₁ U h₁ X = imgGL ρ H₂ U h₂ X := by
  ext y
  rw [mem_imgGL, mem_imgGL]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hX₂ hb⟩, hb, LinearEquiv.ext fun u => Subtype.ext rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hX₁ hb⟩, hb, LinearEquiv.ext fun u => Subtype.ext rfl⟩

theorem exists_inner_of_mem_normalizer_imgGL [Finite V] {L B : Subgroup G}
    {hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤)} (hT : TransportGL ρ L B hinv)
    (e : GL (Fin 3) (ZMod 2) ≃* ↥(imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L))
    {g : ↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤)}
    (hg : g ∈ Subgroup.normalizer
      (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L : Set (↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤)))) :
    ∃ x ∈ imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L, ∀ y ∈ imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L,
      g * y * g⁻¹ = x * y * x⁻¹ := by
  by_contra h
  exact hT.comm (CFSG.QuasithinUnique.Setup.Family.commutator_eq_bot_of_graph_normalizer hT.comp e hg
    (fun l hl hall => h ⟨l, hl, hall⟩) hT.le hT.elem hT.ne_bot hT.off hT.strict)

theorem exists_inner_of_mem_normalizer [Finite V] {L B : Subgroup G}
    {hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤)} (hT : TransportGL ρ L B hinv)
    (eL : ↥L ≃* GL (Fin 3) (ZMod 2)) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ∃ l ∈ L, ∀ m ∈ L, g * m * g⁻¹ = l * m * l⁻¹ := by
  obtain ⟨e, he⟩ := hT.iso
  have hUN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (Subgroup.normalizer (L : Set G)) (commOn ρ L ⊤) :=
    isInvariant_commOn_top le_rfl
  have hcongr : imgGL ρ (Subgroup.normalizer (L : Set G)) (commOn ρ L ⊤) hUN L =
      imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L :=
    imgGL_congr hUN hinv Subgroup.le_normalizer le_sup_left
  have hg' : resGL ρ (Subgroup.normalizer (L : Set G)) (commOn ρ L ⊤) hUN ⟨g, hg⟩ ∈
      Subgroup.normalizer (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L :
        Set (↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤))) := by
    rw [← hcongr]
    exact imgGL_le_normalizer le_rfl (resGL_mem_imgGL hg hg)
  obtain ⟨x, hx, hxy⟩ := exists_inner_of_mem_normalizer_imgGL hT (eL.symm.trans e) hg'
  obtain ⟨⟨l, hlH⟩, hlL, rfl⟩ := mem_imgGL.1 hx
  refine ⟨l, hlL, fun m hm => ?_⟩
  have h1 : g * m * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hg m).1 hm
  have h2 : l * m * l⁻¹ ∈ L := mul_mem (mul_mem hlL hm) (inv_mem hlL)
  have h3 := hxy _ (resGL_mem_imgGL (H := L ⊔ B) (hU := hinv) hm (le_sup_left (a := L) hm))
  have h4 : e ⟨g * m * g⁻¹, h1⟩ = e ⟨l * m * l⁻¹, h2⟩ := by
    apply Subtype.ext
    rw [he, he]
    refine LinearEquiv.ext fun u => Subtype.ext ?_
    have h5 := congrArg
      (fun f : ↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤) => ((f u : ↥(commOn ρ L ⊤)) : V)) h3
    calc ρ (g * m * g⁻¹) (u : V) = ρ g (ρ m (ρ g⁻¹ u)) := by rw [glRep_mul_apply, glRep_mul_apply]
      _ = ρ l (ρ m (ρ l⁻¹ u)) := h5
      _ = ρ (l * m * l⁻¹) u := by rw [glRep_mul_apply, glRep_mul_apply]
  exact congrArg Subtype.val (e.injective h4)

section Decomp

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] {𝓛 : Subgroup (E ≃ₗ[ZMod 2] E)}

theorem eq_of_conj_eq (hcen : Subgroup.center ↥𝓛 = ⊥) {t x x' : E ≃ₗ[ZMod 2] E} (hx : x ∈ 𝓛)
    (hx' : x' ∈ 𝓛) (h : ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹)
    (h' : ∀ y ∈ 𝓛, t * y * t⁻¹ = x' * y * x'⁻¹) : x = x' := by
  have hz : (⟨x'⁻¹ * x, mul_mem (inv_mem hx') hx⟩ : ↥𝓛) ∈ Subgroup.center ↥𝓛 := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h1 : x * y * x⁻¹ = x' * y * x'⁻¹ := (h y y.2).symm.trans (h' y y.2)
    show (y : E ≃ₗ[ZMod 2] E) * (x'⁻¹ * x) = x'⁻¹ * x * y
    calc (y : E ≃ₗ[ZMod 2] E) * (x'⁻¹ * x) = x'⁻¹ * (x' * y * x'⁻¹) * x := by group
      _ = x'⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = x'⁻¹ * x * y := by group
  rw [hcen, Subgroup.mem_bot] at hz
  have h2 : x'⁻¹ * x = 1 := congrArg Subtype.val hz
  calc x = x' * (x'⁻¹ * x) := by group
    _ = x' := by rw [h2, mul_one]

@[expose] noncomputable def innerPart {T : Subgroup (E ≃ₗ[ZMod 2] E)}
    (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹) (t : ↥T) : E ≃ₗ[ZMod 2] E :=
  (hT t t.2).choose

variable {T : Subgroup (E ≃ₗ[ZMod 2] E)}

theorem innerPart_mem (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹) (t : ↥T) :
    innerPart hT t ∈ 𝓛 :=
  (hT t t.2).choose_spec.1

theorem innerPart_conj (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹) (t : ↥T) :
    ∀ y ∈ 𝓛, (t : E ≃ₗ[ZMod 2] E) * y * (t : E ≃ₗ[ZMod 2] E)⁻¹ =
      innerPart hT t * y * (innerPart hT t)⁻¹ :=
  (hT t t.2).choose_spec.2

theorem innerPart_eq (hcen : Subgroup.center ↥𝓛 = ⊥)
    (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹) {t : ↥T} {x : E ≃ₗ[ZMod 2] E}
    (hx : x ∈ 𝓛) (h : ∀ y ∈ 𝓛, (t : E ≃ₗ[ZMod 2] E) * y * (t : E ≃ₗ[ZMod 2] E)⁻¹ = x * y * x⁻¹) :
    innerPart hT t = x :=
  eq_of_conj_eq hcen (innerPart_mem hT t) hx (innerPart_conj hT t) h

theorem innerPart_inv_mul_commute (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹)
    (t : ↥T) {y : E ≃ₗ[ZMod 2] E} (hy : y ∈ 𝓛) :
    (innerPart hT t)⁻¹ * t * y = y * ((innerPart hT t)⁻¹ * t) := by
  have h := innerPart_conj hT t y hy
  calc (innerPart hT t)⁻¹ * t * y =
        (innerPart hT t)⁻¹ * ((t : E ≃ₗ[ZMod 2] E) * y * (t : E ≃ₗ[ZMod 2] E)⁻¹) * t := by group
    _ = (innerPart hT t)⁻¹ * (innerPart hT t * y * (innerPart hT t)⁻¹) * t := by rw [h]
    _ = y * ((innerPart hT t)⁻¹ * t) := by group

@[expose] noncomputable def innerHom (hcen : Subgroup.center ↥𝓛 = ⊥)
    (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹) : ↥T →* ↥𝓛 where
  toFun t := ⟨innerPart hT t, innerPart_mem hT t⟩
  map_one' := Subtype.ext (innerPart_eq hcen hT (one_mem 𝓛) fun y _ => by simp)
  map_mul' s t := by
    apply Subtype.ext
    refine innerPart_eq hcen hT (mul_mem (innerPart_mem hT s) (innerPart_mem hT t)) fun y hy => ?_
    have h1 := innerPart_conj hT t y hy
    have h2 := innerPart_conj hT s _
      (mul_mem (mul_mem (innerPart_mem hT t) hy) (inv_mem (innerPart_mem hT t)))
    show (s : E ≃ₗ[ZMod 2] E) * t * y * ((s : E ≃ₗ[ZMod 2] E) * t)⁻¹ =
      innerPart hT s * innerPart hT t * y * (innerPart hT s * innerPart hT t)⁻¹
    calc (s : E ≃ₗ[ZMod 2] E) * t * y * ((s : E ≃ₗ[ZMod 2] E) * t)⁻¹ =
          (s : E ≃ₗ[ZMod 2] E) * ((t : E ≃ₗ[ZMod 2] E) * y * (t : E ≃ₗ[ZMod 2] E)⁻¹) *
            (s : E ≃ₗ[ZMod 2] E)⁻¹ := by group
      _ = (s : E ≃ₗ[ZMod 2] E) * (innerPart hT t * y * (innerPart hT t)⁻¹) *
            (s : E ≃ₗ[ZMod 2] E)⁻¹ := by rw [h1]
      _ = innerPart hT s * (innerPart hT t * y * (innerPart hT t)⁻¹) * (innerPart hT s)⁻¹ := h2
      _ = innerPart hT s * innerPart hT t * y * (innerPart hT s * innerPart hT t)⁻¹ := by group

theorem innerPart_eq_one_iff (hcen : Subgroup.center ↥𝓛 = ⊥)
    (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹) (t : ↥T) :
    innerPart hT t = 1 ↔ ∀ y ∈ 𝓛, (t : E ≃ₗ[ZMod 2] E) * y = y * t := by
  constructor
  · intro h y hy
    have h1 := innerPart_conj hT t y hy
    rw [h] at h1
    calc (t : E ≃ₗ[ZMod 2] E) * y =
          (t : E ≃ₗ[ZMod 2] E) * y * (t : E ≃ₗ[ZMod 2] E)⁻¹ * t := by group
      _ = 1 * y * 1⁻¹ * t := by rw [h1]
      _ = y * t := by group
  · intro h
    exact innerPart_eq hcen hT (one_mem 𝓛) fun y hy => by rw [h y hy]; group

@[expose] noncomputable def cHom (hcen : Subgroup.center ↥𝓛 = ⊥)
    (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹) : ↥T →* (E ≃ₗ[ZMod 2] E) where
  toFun t := (innerPart hT t)⁻¹ * t
  map_one' := by
    show (innerPart hT 1)⁻¹ * ((1 : ↥T) : E ≃ₗ[ZMod 2] E) = 1
    rw [innerPart_eq hcen hT (one_mem 𝓛) fun y _ => by simp]
    simp
  map_mul' s t := by
    show (innerPart hT (s * t))⁻¹ * ((s * t : ↥T) : E ≃ₗ[ZMod 2] E) =
      (innerPart hT s)⁻¹ * s * ((innerPart hT t)⁻¹ * t)
    have hm : innerPart hT (s * t) = innerPart hT s * innerPart hT t :=
      congrArg Subtype.val (map_mul (innerHom hcen hT) s t)
    have hc := innerPart_inv_mul_commute hT s (inv_mem (innerPart_mem hT t))
    rw [hm, Subgroup.coe_mul]
    calc (innerPart hT s * innerPart hT t)⁻¹ * ((s : E ≃ₗ[ZMod 2] E) * t) =
          (innerPart hT t)⁻¹ * ((innerPart hT s)⁻¹ * s) * t := by group
      _ = (innerPart hT s)⁻¹ * s * (innerPart hT t)⁻¹ * t := by rw [← hc]
      _ = (innerPart hT s)⁻¹ * s * ((innerPart hT t)⁻¹ * t) := by group

theorem cHom_apply (hcen : Subgroup.center ↥𝓛 = ⊥)
    (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹) (t : ↥T) :
    cHom hcen hT t = (innerPart hT t)⁻¹ * t :=
  rfl

theorem cHom_commute (hcen : Subgroup.center ↥𝓛 = ⊥)
    (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹) (t : ↥T) {y : E ≃ₗ[ZMod 2] E}
    (hy : y ∈ 𝓛) : cHom hcen hT t * y = y * cHom hcen hT t :=
  innerPart_inv_mul_commute hT t hy

theorem innerPart_mul_cHom (hcen : Subgroup.center ↥𝓛 = ⊥)
    (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹) (t : ↥T) :
    innerPart hT t * cHom hcen hT t = t := by
  rw [cHom_apply, mul_inv_cancel_left]

theorem cHom_eq_one_iff (hcen : Subgroup.center ↥𝓛 = ⊥)
    (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹) (t : ↥T) :
    cHom hcen hT t = 1 ↔ (t : E ≃ₗ[ZMod 2] E) ∈ 𝓛 := by
  rw [cHom_apply, inv_mul_eq_one]
  constructor
  · intro h
    rw [← h]
    exact innerPart_mem hT t
  · intro h
    exact innerPart_eq hcen hT h fun y _ => rfl

theorem card_le_four_of_inner (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛)
    (hcen : Subgroup.center ↥𝓛 = ⊥) (hTe : CFSG.IsElementaryAbelian 2 ↥T)
    (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹)
    (hcT : ∀ t ∈ T, (∀ y ∈ 𝓛, t * y = y * t) → t = 1) : Nat.card ↥T ≤ 4 := by
  haveI := hTe
  set f : ↥T →* ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
    eV.symm.toMonoidHom.comp (innerHom hcen hT) with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    have h1 : innerHom hcen hT t = 1 := by
      have h2 := congrArg eV ht
      rw [map_one] at h2
      simpa [f] using h2
    have h3 : innerPart hT t = 1 := congrArg Subtype.val h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hcT t t.2 ((innerPart_eq_one_iff hcen hT t).1 h3))
  have hc : ∀ a ∈ f.range, ∀ b ∈ f.range, a * b = b * a := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, hTe.toIsMulCommutative.is_comm.comm s t]
  have h2 : ∀ a ∈ f.range, a * a = 1 := by
    rintro _ ⟨s, rfl⟩
    have hs : s * s = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
      exact elemPow_eq_one_of_isElementaryAbelian (s : E ≃ₗ[ZMod 2] E) s.2)
    rw [← map_mul, hs, map_one]
  have hcard : Nat.card ↥f.range = Nat.card ↥T := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  rw [← hcard]
  exact CFSG.ASVolI.burnsideB49x_gl_three (Module.finrank_fin_fun (ZMod 2)) hc h2

end Decomp

theorem card_mul_card_fix_le_sixteen {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 3) {E₀ : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hc : ∀ e ∈ E₀, ∀ e' ∈ E₀, e * e' = e' * e) (h2 : ∀ e ∈ E₀, e * e = 1) :
    Nat.card E₀ * Nat.card (CFSG.ASVolI.burnsideB49x_gl_fix E₀) ≤ 16 := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  have hc1 := CFSG.ASVolI.burnsideB49x_gl_one_le_finrank_fix (by omega) h2
  have hbc := Submodule.finrank_mono (CFSG.ASVolI.burnsideB49x_gl_quad_of_codim hc h2 (by omega))
  have hc3 := Submodule.finrank_le (CFSG.ASVolI.burnsideB49x_gl_fix E₀)
  have hcard := CFSG.ASVolI.burnsideB49x_gl_card_le_fix_comm E₀
  rw [hW] at hcard hc3
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := CFSG.ASVolI.burnsideB49x_gl_fix E₀),
    Nat.card_zmod]
  have hexp : (3 - finrank (ZMod 2) (CFSG.ASVolI.burnsideB49x_gl_fix E₀)) *
      finrank (ZMod 2) (CFSG.ASVolI.burnsideB49x_gl_comm E₀) +
      finrank (ZMod 2) (CFSG.ASVolI.burnsideB49x_gl_fix E₀) ≤ 4 := by
    generalize finrank (ZMod 2) (CFSG.ASVolI.burnsideB49x_gl_fix E₀) = f at hc1 hbc hc3 ⊢
    generalize finrank (ZMod 2) (CFSG.ASVolI.burnsideB49x_gl_comm E₀) = b at hbc ⊢
    interval_cases f <;> omega
  calc Nat.card E₀ * 2 ^ finrank (ZMod 2) (CFSG.ASVolI.burnsideB49x_gl_fix E₀)
      ≤ 2 ^ ((3 - finrank (ZMod 2) (CFSG.ASVolI.burnsideB49x_gl_fix E₀)) *
          finrank (ZMod 2) (CFSG.ASVolI.burnsideB49x_gl_comm E₀)) *
        2 ^ finrank (ZMod 2) (CFSG.ASVolI.burnsideB49x_gl_fix E₀) := Nat.mul_le_mul_right _ hcard
    _ = 2 ^ ((3 - finrank (ZMod 2) (CFSG.ASVolI.burnsideB49x_gl_fix E₀)) *
          finrank (ZMod 2) (CFSG.ASVolI.burnsideB49x_gl_comm E₀) +
          finrank (ZMod 2) (CFSG.ASVolI.burnsideB49x_gl_fix E₀)) := by rw [pow_add]
    _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hexp
    _ = 16 := by norm_num

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
