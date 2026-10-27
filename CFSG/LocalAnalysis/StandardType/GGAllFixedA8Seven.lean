module

public import CFSG.GroupTheory.MinimalBinaryCentralizer
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.FixedCentralQuotientFamily
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.pStability
public import CFSG.LocalAnalysis.StandardType.GGSL9TwoProj
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGQTwoCentralizerLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientSolvable
public import CFSG.LocalAnalysis.StandardType.GGAllFixedSC
public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.GroupTheory.FixedCentralQuotientFamily

theorem ggFixedSubgroup_eq_commonFixed {R : Type} [Group R]
    (E : Subgroup (MulAut R)) :
    ggFixedSubgroup E = commonFixed (fun e : E => (e : MulAut R)) := by
  ext x
  simp only [ggFixedSubgroup, commonFixed, Subgroup.mem_iInf, Subgroup.coe_iInf,
    Set.mem_iInter, SetLike.mem_coe]
  exact ⟨fun h e => h e e.property, fun h e he => h ⟨e, he⟩⟩

theorem ggFixedSubgroup_map_congr {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (E : Subgroup (MulAut G)) :
    ggFixedSubgroup (E.map (MulAut.congr e).toMonoidHom) =
      (ggFixedSubgroup E).map (e : G →* H) := by
  ext x
  constructor
  · intro hx
    simp only [ggFixedSubgroup_eq_commonFixed, commonFixed, Subgroup.mem_iInf, Subgroup.coe_iInf,
      Set.mem_iInter] at hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [ggFixedSubgroup_eq_commonFixed, commonFixed]
    simp only [Subgroup.mem_iInf, Subgroup.coe_iInf, Set.mem_iInter]
    intro a
    let φ : ↥(E.map (MulAut.congr e).toMonoidHom) :=
      ⟨MulAut.congr e a,
        Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom a.property⟩
    have h := hx φ
    have hφx : (MulAut.congr e (a : MulAut G)) x = x := h
    have h2 : e ((a : MulAut G) (e.symm x)) = e (e.symm x) := by
      simpa [MulAut.congr, MulEquiv.trans_apply] using hφx
    exact e.injective h2
  · rintro ⟨y, hy, rfl⟩
    simp only [ggFixedSubgroup_eq_commonFixed, commonFixed, Subgroup.mem_iInf, Subgroup.coe_iInf,
      Set.mem_iInter] at hy
    rw [ggFixedSubgroup_eq_commonFixed, commonFixed]
    simp only [Subgroup.mem_iInf, Subgroup.coe_iInf, Set.mem_iInter]
    intro φ
    obtain ⟨a, ha, hφeq⟩ := φ.property
    rw [← hφeq]
    change e (a (e.symm (e y))) = e y
    have hya : a y = y := hy ⟨a, ha⟩
    simpa using congrArg e hya

theorem ggFixedSubgroup_map_conj_eq_centralizer {G : Type} [Group G]
    (E : Subgroup G) :
    ggFixedSubgroup (E.map (MulAut.conj : G →* MulAut G)) =
      Subgroup.centralizer (E : Set G) := by
  ext x
  constructor
  · intro hx
    simp only [ggFixedSubgroup_eq_commonFixed, commonFixed, Subgroup.mem_iInf, Subgroup.coe_iInf,
      Set.mem_iInter] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    let φ : ↥(E.map (MulAut.conj : G →* MulAut G)) :=
      ⟨MulAut.conj g, Subgroup.mem_map_of_mem (MulAut.conj : G →* MulAut G) hg⟩
    have h := hx φ
    change g * x * g⁻¹ = x at h
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h]
  · intro hx
    rw [ggFixedSubgroup_eq_commonFixed, commonFixed]
    simp only [Subgroup.mem_iInf, Subgroup.coe_iInf, Set.mem_iInter]
    intro φ
    obtain ⟨g, hg, hφeq⟩ := φ.property
    rw [← hφeq]
    change g * x * g⁻¹ = x
    have h := (Subgroup.mem_centralizer_iff.mp hx) g hg
    calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [h]
      _ = x := by group

theorem ggFixedSubgroup_isSolvable_of_recipe_linear_nine_two
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (E : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 9) K))))
    (hEI : (E : Set (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 9) K)))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 9) K)) Set.univ)
    (hE : IsElemAbelian 7 E)
    (hcard : 7 ^ 3 ≤ Nat.card E) :
    Group.IsSolvable (ggFixedSubgroup E) := by
  classical
  let eR : LargeEvenProj (LargeEvenSLGroup (Fin 9) K) ≃*
      (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := ggSL9RecipeEquiv hK
  let E' : Subgroup (MulAut (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) :=
    E.map (MulAut.congr eR).toMonoidHom
  have hE'range : E' ≤ (MulAut.conj :
      (GGSL9V ≃ₗ[ZMod 2] GGSL9V) →* MulAut (GGSL9V ≃ₗ[ZMod 2] GGSL9V)).range := by
    rintro _ ⟨e, he, rfl⟩
    exact congr_ggSL9RecipeEquiv_mem hK (hEI he)
  let E0 : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
    E'.comap (MulAut.conj :
      (GGSL9V ≃ₗ[ZMod 2] GGSL9V) →* MulAut (GGSL9V ≃ₗ[ZMod 2] GGSL9V))
  have hconjinj : Function.Injective (MulAut.conj :
      (GGSL9V ≃ₗ[ZMod 2] GGSL9V) →* MulAut (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot center_ggSL9_eq_bot
  have hE0map : E0.map (MulAut.conj :
      (GGSL9V ≃ₗ[ZMod 2] GGSL9V) →* MulAut (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) = E' :=
    Subgroup.map_comap_eq_self hE'range
  have hE'ab : IsElemAbelian 7 E' := hE.map (MulAut.congr eR).toMonoidHom
  have hE0ab : IsElemAbelian 7 E0 := hE'ab.comap hconjinj
  have hE0card : 7 ^ 3 ≤ Nat.card E0 := by
    have hcard' : Nat.card E' = Nat.card E := by
      exact Subgroup.card_map_of_injective (MulAut.congr eR).injective
    have hcard'' : Nat.card E0 = Nat.card E' := by
      rw [← hE0map]
      exact (Subgroup.card_map_of_injective hconjinj).symm
    rwa [hcard'', hcard']
  let eG : GL (Fin 9) (ZMod 2) ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := ggSL9GLEquiv
  let E1 : Subgroup (GL (Fin 9) (ZMod 2)) :=
    E0.map eG.symm.toMonoidHom
  have hE1ab : IsElemAbelian 7 E1 := hE0ab.map eG.symm.toMonoidHom
  have hE1card : 7 ^ 3 ≤ Nat.card E1 := by
    rw [Subgroup.card_map_of_injective (K := E0) (f := eG.symm.toMonoidHom) eG.symm.injective]
    exact hE0card
  have hsolvE1 : Group.IsSolvable
      (Subgroup.centralizer (E1 : Set (GL (Fin 9) (ZMod 2)))) :=
    CFSG.GroupTheory.centralizer_isSolvable_of_elementaryAbelian_seven E1 hE1ab hE1card
  have hE1map : E1.map eG.toMonoidHom = E0 := by
    ext x
    simp [E1, Subgroup.map_map]
  have hcent : (Subgroup.centralizer (E1 : Set (GL (Fin 9) (ZMod 2)))).map eG.toMonoidHom =
      Subgroup.centralizer (E0 : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := by
    rw [CFSG.Glauberman.map_centralizer_eq_of_equiv eG E1, hE1map]
  have hsolvE0 : Group.IsSolvable
      (Subgroup.centralizer (E0 : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) := by
    letI : Group.IsSolvable
        (Subgroup.centralizer (E1 : Set (GL (Fin 9) (ZMod 2)))) := hsolvE1
    have hsolvImage : Group.IsSolvable
        ((Subgroup.centralizer (E1 : Set (GL (Fin 9) (ZMod 2)))).map eG.toMonoidHom) :=
      Group.isSolvable_of_surjective
        (f := eG.toMonoidHom.subgroupMap
          (Subgroup.centralizer (E1 : Set (GL (Fin 9) (ZMod 2)))))
        (MonoidHom.subgroupMap_surjective eG.toMonoidHom _)
    rwa [hcent] at hsolvImage
  have hfixE' : ggFixedSubgroup E' =
      Subgroup.centralizer (E0 : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := by
    rw [← hE0map, ggFixedSubgroup_map_conj_eq_centralizer]
  have hmapFix : ggFixedSubgroup E' = (ggFixedSubgroup E).map eR.toMonoidHom :=
    ggFixedSubgroup_map_congr eR E
  have hsolvMap : Group.IsSolvable ((ggFixedSubgroup E).map eR.toMonoidHom) := by
    rw [← hmapFix, hfixE']
    exact hsolvE0
  letI : Group.IsSolvable ((ggFixedSubgroup E).map eR.toMonoidHom) := hsolvMap
  exact Group.isSolvable_of_isSolvable_injective
    (f := eR.toMonoidHom.subgroupMap (ggFixedSubgroup E))
    (MonoidHom.subgroupMap_injective eR.toMonoidHom _ eR.injective)

@[expose] def A8SevenActualMarkProp {G : Type} [Group G] (Bs X : Subgroup G) :
    LargeEvenMarkProp X :=
  fun lab R _ I F θ =>
    lab = ⟨.A, 8, 1⟩ ∧
    ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
        (fun l l' : ↥X => (l' : G) = b⁻¹ * l * b) φ) ∧
      IsElemAbelian 7 (ggBeta (G := G) (L := X) θ hN).range ∧
      ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
      7 ^ 3 ≤ Nat.card (ggBeta (G := G) (L := X) θ hN).range

theorem ggFixedSubgroup_range_eq_iInf_fixed {B R : Type} [Group B] [Group R]
    (β : B →* MulAut R) :
    ggFixedSubgroup β.range =
      ⨅ b : B, CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (β b) := by
  ext x
  constructor
  · intro hx
    simp only [ggFixedSubgroup_eq_commonFixed, commonFixed, Subgroup.mem_iInf, Subgroup.coe_iInf,
      Set.mem_iInter] at hx
    rw [Subgroup.mem_iInf]
    intro b
    exact hx ⟨β b, ⟨b, rfl⟩⟩
  · intro hx
    rw [Subgroup.mem_iInf] at hx
    rw [ggFixedSubgroup_eq_commonFixed, commonFixed]
    simp only [Subgroup.mem_iInf, Subgroup.coe_iInf, Set.mem_iInter]
    rintro ⟨φ, b, rfl⟩
    exact hx b

theorem ggFix_eq_fixedSubgroup {H : Type*} [Group H] (a : MulAut H) :
    ggFix a = CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup a := by
  ext x
  rfl

theorem ggFixedSubgroup_range_eq_iInf_ggFix {B R : Type} [Group B] [Group R]
    (β : B →* MulAut R) :
    ggFixedSubgroup β.range = ⨅ b : B, ggFix (β b) := by
  simpa only [ggFix_eq_fixedSubgroup] using ggFixedSubgroup_range_eq_iInf_fixed β

theorem hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {R : Type} [Group R] (θ : ↥X ⧸ Subgroup.center ↥X ≃* R) :
    CFSG.HasNormalPComplement p
      ↥(_root_.commutator ↥(ggFixedSubgroup (ggBeta (G := G) (L := X) θ hN).range)) := by
  classical
  let ψ := QTwoCentralizer.action X Bs hN
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hNPC : CFSG.HasNormalPComplement p ↥(commonFixed ψ) := by
    rw [show ψ = QTwoCentralizer.action X Bs hN from rfl,
      QTwoCentralizer.commonFixed_eq]
    exact CFSG.RankThree.Coprime.hasNormalPComplement_subgroupOf X
      (SecFiveL1Solv.hasNormalPComplement_centralizer_of_ggBstar hp hp2 hcfg.2.1)
  let Q := QTwoCentralizer.quotientCentralizer X Bs hN
  have hNPCQ : CFSG.HasNormalPComplement p ↥(⁅Q, Q⁆) :=
    hasNormalPComplement_commutator_quotientFixed (Subgroup.center ↥X) ψ
      (QTwoCentralizer.centerInvariant X Bs hN) le_rfl hNPC
  let F := ggFixedSubgroup (ggBeta (G := G) (L := X) θ hN).range
  have hQF : Q.map θ.toMonoidHom = F := by
    change (QTwoCentralizer.quotientCentralizer X Bs hN).map θ.toMonoidHom =
      ggFixedSubgroup (ggBeta (G := G) (L := X) θ hN).range
    rw [ggFixedSubgroup_range_eq_iInf_ggFix]
    exact QTwoCav.quotientCentralizer_map hN θ
  let eQ : ↥Q ≃* ↥F :=
    (Q.equivMapOfInjective θ.toMonoidHom θ.injective).trans
      (MulEquiv.subgroupCongr hQF)
  let eD : ↥(_root_.commutator ↥Q) ≃* ↥(⁅Q, Q⁆) :=
    ((_root_.commutator ↥Q).equivMapOfInjective Q.subtype Q.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator Q))
  have hNPCD : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥Q) :=
    CFSG.hasNormalPComplement_of_equiv p eD.symm hNPCQ
  have hmapD : (_root_.commutator ↥Q).map eQ.toMonoidHom = _root_.commutator ↥F := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr eQ.surjective, ← commutator_def]
  have h := CFSG.hasNormalPComplement_of_equiv p
    ((_root_.commutator ↥Q).equivMapOfInjective eQ.toMonoidHom eQ.injective) hNPCD
  rwa [hmapD] at h

theorem isSolvable_inf_centralizer_of_quotientFixed_solvable {G : Type} [Group G]
    {Bs X : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {R : Type} [Group R] (θ : ↥X ⧸ Subgroup.center ↥X ≃* R)
    (hsolv : Group.IsSolvable (ggFixedSubgroup (ggBeta (G := G) (L := X) θ hN).range)) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  classical
  have hsolvFixed : Group.IsSolvable ↥(⨅ b : Bs, ggFix (ggBeta (G := G) (L := X) θ hN b)) := by
    have hEq : ggFixedSubgroup (ggBeta (G := G) (L := X) θ hN).range =
        ⨅ b : Bs, ggFix (ggBeta (G := G) (L := X) θ hN b) :=
      ggFixedSubgroup_range_eq_iInf_ggFix (ggBeta (G := G) (L := X) θ hN)
    exact hEq ▸ hsolv
  have hsolvQ : Group.IsSolvable (QTwoCentralizer.quotientCentralizer X Bs hN) := by
    have hmap := QTwoCav.quotientCentralizer_map hN θ
    have hsolvImage : Group.IsSolvable
        ((QTwoCentralizer.quotientCentralizer X Bs hN).map θ.toMonoidHom) := by
      rw [hmap]
      exact hsolvFixed
    letI : Group.IsSolvable
        ((QTwoCentralizer.quotientCentralizer X Bs hN).map θ.toMonoidHom) := hsolvImage
    exact Group.isSolvable_of_isSolvable_injective
      (f := θ.toMonoidHom.subgroupMap (QTwoCentralizer.quotientCentralizer X Bs hN))
      (MonoidHom.subgroupMap_injective θ.toMonoidHom _ θ.injective)
  have hsolvCommon : Group.IsSolvable
      (commonFixed (QTwoCentralizer.action X Bs hN)) :=
    CFSG.GroupTheory.FixedCentralQuotientFamily.isSolvable_commonFixed_of_quotientFixed
      (Subgroup.center ↥X) (QTwoCentralizer.action X Bs hN)
      (QTwoCentralizer.centerInvariant X Bs hN) (le_refl _) hsolvQ
  have hsolvSub : Group.IsSolvable ↥((Subgroup.centralizer (Bs : Set G)).subgroupOf X) := by
    have h := hsolvCommon
    rw [QTwoCentralizer.commonFixed_eq X Bs hN] at h
    exact h
  haveI : Group.IsSolvable ↥((Subgroup.centralizer (Bs : Set G)).subgroupOf X) := hsolvSub
  let f : ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) →*
      ↥((Subgroup.centralizer (Bs : Set G)).subgroupOf X) :=
    { toFun := fun z => ⟨⟨z, z.property.1⟩, z.property.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact Group.isSolvable_of_isSolvable_injective (f := f) (fun _ _ h => by
    apply Subtype.ext
    exact congrArg
      (fun z : ↥((Subgroup.centralizer (Bs : Set G)).subgroupOf X) => z.val.val) h)

theorem isSolvable_inf_centralizer_of_A8Seven_marking {G : Type} [Group G]
    {Bs X : Subgroup G}
    (hmark : LargeEvenMarking ↥X (A8SevenActualMarkProp Bs X)) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  classical
  obtain ⟨-, lab, -, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  have hlab : lab = ⟨.A, 8, 1⟩ := hP₀.1
  subst lab
  obtain ⟨K, fieldK, finiteK, hK, hQK⟩ := hraw
  letI := fieldK
  letI := finiteK
  obtain ⟨-, -, θ, hP⟩ := hQK
  obtain ⟨-, hN, -, hEab, hEsub, hEcard⟩ := hP
  let E : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 9) K))) :=
    (ggBeta (G := G) (L := X) θ hN).range
  have hsolvE : Group.IsSolvable (ggFixedSubgroup E) :=
    ggFixedSubgroup_isSolvable_of_recipe_linear_nine_two (K := K) hK E hEsub hEab hEcard
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ (by simpa [E] using hsolvE)

end CFSG.StandardType

end
