module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeOrthRegular
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeOrthFree
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSUCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaSplit
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
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
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open QuadraticMap
open CFSG.StandardType.LayerCores CFSG.StandardType.LayerCores.OrthSplit
open CFSG.ClassicalGroups.Orthogonal

private noncomputable def projFstEquiv {G₀ G₁ : Type*} [Group G₀] [Group G₁]
    (J : Subgroup (G₀ × G₁)) (hJ : J ≤ (MonoidHom.snd G₀ G₁).ker) :
    ↥J ≃* ↥(J.map (MonoidHom.fst G₀ G₁)) := by
  classical
  let F : ↥J →* ↥(J.map (MonoidHom.fst G₀ G₁)) :=
    ((MonoidHom.fst G₀ G₁).comp J.subtype).codRestrict (J.map (MonoidHom.fst G₀ G₁))
      (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  exact MulEquiv.ofBijective F ⟨fun x y hxy => by
    apply Subtype.ext
    have h1 : (x : G₀ × G₁).1 = (y : G₀ × G₁).1 := congrArg Subtype.val hxy
    have h2 : (x : G₀ × G₁).2 = 1 := MonoidHom.mem_ker.mp (hJ x.2)
    have h3 : (y : G₀ × G₁).2 = 1 := MonoidHom.mem_ker.mp (hJ y.2)
    exact Prod.ext h1 (by rw [h2, h3]), fun y => by
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

private noncomputable def projSndEquiv {G₀ G₁ : Type*} [Group G₀] [Group G₁]
    (J : Subgroup (G₀ × G₁)) (hJ : J ≤ (MonoidHom.fst G₀ G₁).ker) :
    ↥J ≃* ↥(J.map (MonoidHom.snd G₀ G₁)) := by
  classical
  let F : ↥J →* ↥(J.map (MonoidHom.snd G₀ G₁)) :=
    ((MonoidHom.snd G₀ G₁).comp J.subtype).codRestrict (J.map (MonoidHom.snd G₀ G₁))
      (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  exact MulEquiv.ofBijective F ⟨fun x y hxy => by
    apply Subtype.ext
    have h1 : (x : G₀ × G₁).2 = (y : G₀ × G₁).2 := congrArg Subtype.val hxy
    have h2 : (x : G₀ × G₁).1 = 1 := MonoidHom.mem_ker.mp (hJ x.2)
    have h3 : (y : G₀ × G₁).1 = 1 := MonoidHom.mem_ker.mp (hJ y.2)
    exact Prod.ext (by rw [h2, h3]) h1, fun y => by
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

theorem ggA6_shape_orthCentralizer_abs {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (A : Subgroup (V ≃ₗ[K] V))
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (Nat.card A))
    (hnil : Group.IsNilpotent ↥A) {J : Subgroup (V ≃ₗ[K] V)}
    (hJq : CFSG.Assembly.IsQuasisimple J)
    (hJs : CFSG.Assembly.IsSubnormal J (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      Subgroup.centralizer (A : Set (V ≃ₗ[K] V)))) :
    GGA6CharTwoLie ↥J := by
  classical
  haveI hfin : Finite (V ≃ₗ[K] V) := finite_linearEquiv (K := K) (V := V)
  have : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_card_ne_zero_of_odd hodd
  let G₀ := fixSp A ≃ₗ[K] fixSp A
  let G₁ := freeSp A ≃ₗ[K] freeSp A
  let φ : G₀ × G₁ →* (V ≃ₗ[K] V) := OrthSplit.split hA
  let O₀ : Subgroup G₀ := TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSp A))
  let C₁ : Subgroup G₁ := OrthSplit.freeCent A Q
  let H : Subgroup (G₀ × G₁) := O₀.prod C₁
  haveI hG₀fin : Finite G₀ := by
    dsimp only [G₀]; exact finite_linearEquiv (K := K) (V := fixSp A)
  haveI hG₁fin : Finite G₁ := by
    dsimp only [G₁]; exact finite_linearEquiv (K := K) (V := freeSp A)
  haveI hHfin : Finite ↥H :=
    Finite.of_injective (fun x : ↥H => (x : G₀ × G₁)) Subtype.coe_injective
  have hφinj : Function.Injective φ := OrthSplit.split_injective hA
  have hC : H.map φ = TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) := by
    dsimp only [H, O₀, C₁, φ]
    rw [inf_comm]
    exact (OrthSplit.centralizer_eq_map_split hA hAO).symm
  have hJs' : IsSubnormal J (H.map φ) := by rwa [hC]
  have hJle : J ≤ H.map φ := hJs'.le
  have hJrange : J ≤ φ.range := hJle.trans (Subgroup.map_le_range φ H)
  let J₁ : Subgroup (G₀ × G₁) := J.comap φ
  have hJmap : J₁.map φ = J := Subgroup.map_comap_eq_self hJrange
  have hJ₁H : IsSubnormal J₁ H := by
    have h := hJs'.comap φ
    have hker : φ.ker ≤ H := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx1 : x = 1 := hφinj (by rw [hx, map_one])
      rw [hx1]
      exact H.one_mem
    rw [Subgroup.comap_map_eq_self hker] at h
    exact h
  have eJ₁ : ↥J₁ ≃* ↥J :=
    (Subgroup.equivMapOfInjective J₁ φ hφinj).trans (MulEquiv.subgroupCongr hJmap)
  have hJ₁q : CFSG.Assembly.IsQuasisimple ↥J₁ :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv eJ₁ hJq
  have hK' : IsComponentOf (J₁.subgroupOf H) ⊤ :=
    ⟨le_top, by simpa [Subgroup.subgroupOf_self] using hJ₁H.comap H.subtype,
      CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ₁H.le) hJ₁q⟩
  have hK'open : CFSG.Open.IsComponentOf (J₁.subgroupOf H) ⊤ :=
    CFSG.Assembly.isComponentOf_iff_open.mp hK'
  let N₁ : Subgroup ↥H := ((MonoidHom.snd G₀ G₁).comp H.subtype).ker
  let N₂ : Subgroup ↥H := ((MonoidHom.fst G₀ G₁).comp H.subtype).ker
  haveI hN₁ : N₁.Normal := MonoidHom.normal_ker _
  haveI hN₂ : N₂.Normal := MonoidHom.normal_ker _
  have hsup : N₁ ⊔ N₂ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.mp (show x.val ∈ O₀.prod C₁ from x.2)
    have hx_eq : x = (⟨(x.val.1, 1), Subgroup.mem_prod.mpr ⟨hx1, Subgroup.one_mem C₁⟩⟩ : ↥H) *
        (⟨(1, x.val.2), Subgroup.mem_prod.mpr ⟨Subgroup.one_mem O₀, hx2⟩⟩ : ↥H) := by
      apply Subtype.ext
      exact Prod.ext (by simp) (by simp)
    rw [hx_eq]
    refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
    · exact MonoidHom.mem_ker.mpr (by simp [N₁])
    · exact MonoidHom.mem_ker.mpr (by simp [N₂])
  have hchoice := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_component_le_or_le
    (X := ↥H) (A₁ := N₁) (A₂ := N₂) (K' := J₁.subgroupOf H) hsup hK'open
  have hHfst : H.map (MonoidHom.fst G₀ G₁) = O₀ := by
    dsimp only [H, O₀, C₁]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_prod.mp hy).1
    · intro hx
      exact ⟨(x, 1), Subgroup.mem_prod.mpr ⟨hx, Subgroup.one_mem C₁⟩, rfl⟩
  have hHsnd : H.map (MonoidHom.snd G₀ G₁) = C₁ := by
    dsimp only [H, O₀, C₁]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_prod.mp hy).2
    · intro hx
      exact ⟨(1, x), Subgroup.mem_prod.mpr ⟨Subgroup.one_mem O₀, hx⟩, rfl⟩
  rcases hchoice with hle₁ | hle₂
  ·
    have hJ₁ker : J₁ ≤ (MonoidHom.snd G₀ G₁).ker := by
      intro x hx
      have hxH : x ∈ H := hJ₁H.le hx
      have hm : (⟨x, hxH⟩ : ↥H) ∈ N₁ := hle₁ (Subgroup.mem_subgroupOf.mpr hx)
      have hm' : ((MonoidHom.snd G₀ G₁).comp H.subtype) ⟨x, hxH⟩ = 1 :=
        MonoidHom.mem_ker.mp (show (⟨x, hxH⟩ : ↥H) ∈
          ((MonoidHom.snd G₀ G₁).comp H.subtype).ker from hm)
      exact MonoidHom.mem_ker.mpr (by simpa using hm')
    let J₀ : Subgroup G₀ := J₁.map (MonoidHom.fst G₀ G₁)
    have e₀ : ↥J₁ ≃* ↥J₀ := projFstEquiv J₁ hJ₁ker
    have hJ₀q : CFSG.Assembly.IsQuasisimple ↥J₀ :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv e₀.symm hJ₁q
    have hJ₀s : IsSubnormal J₀ O₀ := by
      have h := IsSubnormal.map (MonoidHom.fst G₀ G₁) hJ₁H
      rwa [hHfst] at h
    have hreg := ggA6_shape_orthRegular (Q.restrict (fixSp A))
      (nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hA hAO)) hJ₀q hJ₀s
    exact GGA6CharTwoLie.of_mulEquiv ((eJ₁.symm.trans e₀).symm) hreg
  ·
    have hJ₁ker : J₁ ≤ (MonoidHom.fst G₀ G₁).ker := by
      intro x hx
      have hxH : x ∈ H := hJ₁H.le hx
      have hm : (⟨x, hxH⟩ : ↥H) ∈ N₂ := hle₂ (Subgroup.mem_subgroupOf.mpr hx)
      have hm' : ((MonoidHom.fst G₀ G₁).comp H.subtype) ⟨x, hxH⟩ = 1 :=
        MonoidHom.mem_ker.mp (show (⟨x, hxH⟩ : ↥H) ∈
          ((MonoidHom.fst G₀ G₁).comp H.subtype).ker from hm)
      exact MonoidHom.mem_ker.mpr (by simpa using hm')
    let J₂ : Subgroup G₁ := J₁.map (MonoidHom.snd G₀ G₁)
    have e₂ : ↥J₁ ≃* ↥J₂ := projSndEquiv J₁ hJ₁ker
    have hJ₂q : CFSG.Assembly.IsQuasisimple ↥J₂ :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv e₂.symm hJ₁q
    have hJ₂s : IsSubnormal J₂ C₁ := by
      have h := IsSubnormal.map (MonoidHom.snd G₀ G₁) hJ₁H
      rwa [hHsnd] at h
    have hJ₂s' : IsSubnormal J₂ (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (freeSp A)) ⊓
        Subgroup.centralizer (freeGroup A : Set (freeSp A ≃ₗ[K] freeSp A))) := by
      rw [inf_comm]
      exact hJ₂s
    have hA₁O : freeGroup A ≤
        TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (freeSp A)) := by
      rintro _ ⟨a, ha, rfl⟩
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun y =>
        map_of_mem (hAO (Subgroup.mem_subgroupOf.mp ha)) (y : V)
    have hA₁odd : Odd (Nat.card (freeGroup A)) := by
      refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe OrthSplit.le_stab).toEquiv]
      exact hodd
    have hA₁free : ∀ w : freeSp A, (∀ a ∈ freeGroup A, a w = w) → w = 0 := by
      intro w hw
      have h1 : (w : V) ∈ fixSp A := (OrthSplit.mem_fixSp_iff hA).mpr fun a ha =>
        congrArg Subtype.val (hw (OrthSplit.restrFree A ⟨a, OrthSplit.le_stab ha⟩)
          ⟨⟨a, OrthSplit.le_stab ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩)
      exact Subtype.ext
        ((Submodule.disjoint_def.mp (OrthSplit.isCompl_fixSp_freeSp hA).disjoint) _ h1 w.2)
    have hA₁nil : Group.IsNilpotent ↥(freeGroup A) := by
      let f : ↥A →* ↥(freeGroup A) :=
        ((OrthSplit.restrFree A).comp (Subgroup.inclusion OrthSplit.le_stab)).codRestrict
          (freeGroup A)
          (fun a => Subgroup.mem_map.mpr ⟨Subgroup.inclusion OrthSplit.le_stab a,
            Subgroup.mem_subgroupOf.mpr a.2, rfl⟩)
      have hf : Function.Surjective f := by
        intro y
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
        refine ⟨⟨x.val, Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
        apply Subtype.ext
        show OrthSplit.restrFree A x = y.val
        exact hxy
      exact Group.nilpotent_of_surjective f hf
    have hfree := ggA6_shape_orthFree (Q.restrict (freeSp A))
      (nondegenerate_polarBilin_restrict (polarNondegOn_freeSp hQ hA hAO)) (freeGroup A)
      hA₁O hA₁odd hA₁nil hA₁free hJ₂q hJ₂s'
    exact GGA6CharTwoLie.of_mulEquiv ((eJ₁.symm.trans e₂).symm) hfree

end CFSG.StandardType.A6Red

end
