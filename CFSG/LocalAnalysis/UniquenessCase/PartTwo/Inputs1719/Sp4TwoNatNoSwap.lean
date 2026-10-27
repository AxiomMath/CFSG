module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoords
public import CFSG.Quasithin.Background.HMultNorm
public import CFSG.Quasithin.Background.HSp4Rel
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherFieldParabolic
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
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
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.EmptyFaithful.Setting
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
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mult
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (SwapsParabolics)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped Matrix Kronecker

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_sp4_conj_of_mem_normalizer_diag {k : ℕ} [NeZero k]
    {T : MulAut (StdMod (Fin k × (Fin 2 ⊕ Fin 2)) K)}
    (hT : T ∈ Subgroup.normalizer (natImage (diagSub k (StatedSp 2 K)) :
      Set (MulAut (StdMod (Fin k × (Fin 2 ⊕ Fin 2)) K)))) :
    ∃ (B : StatedSp 2 K) (σ : K ≃+* K), ∀ γ : StatedSp 2 K,
      T * matAut (diagGL k (γ : GL (Fin 2 ⊕ Fin 2) K)) * T⁻¹ =
        matAut (diagGL k ((B * fieldSp 2 K σ γ * B⁻¹ : StatedSp 2 K) :
          GL (Fin 2 ⊕ Fin 2) K)) := by
  obtain ⟨A, σ, B, hA, -, -, -, hconj⟩ :=
    CFSG.Quasithin.H.Mult.exists_of_mem_normalizer_diag
      (ι := Fin 2 ⊕ Fin 2) (K := K) (k := k)
      (CFSG.Quasithin.H.Sp4.hasScalarCommutant_statedSp (K := K)) hT
  obtain ⟨Bsp, σ', -, hBsp, -⟩ :=
    CFSG.Quasithin.H.Sp4.exists_eq_of_mem_natNorm hA
  refine ⟨Bsp, σ', fun γ => ?_⟩
  obtain ⟨γ', -, hAγ', hTγ'⟩ := hconj γ γ.2
  have hAconj : A * matAut (γ : GL (Fin 2 ⊕ Fin 2) K) * A⁻¹ =
      matAut ((Bsp * fieldSp 2 K σ' γ * Bsp⁻¹ : StatedSp 2 K) :
        GL (Fin 2 ⊕ Fin 2) K) := by
    have h1 := CFSG.Quasithin.H.natAut_conjHom (StatedSp 2 K) ⟨A, hA⟩ γ
    rw [hBsp γ] at h1
    exact h1.symm
  have hγ'eq : γ' = ((Bsp * fieldSp 2 K σ' γ * Bsp⁻¹ : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) := by
    apply matHom_injective
    exact hAγ'.symm.trans hAconj
  rw [hγ'eq] at hTγ'
  exact hTγ'

theorem map_conj_eq_of_isSylowIn_natImage_diag
    (Y P : Subgroup (MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K)))
    (t : MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K))
    (hY : Y ≤ Subgroup.normalizer
      (natImage (diagSub 2 (StatedSp 2 K)) : Set _))
    (hSyl : IsSylowIn 2 (Y ⊓ natImage (diagSub 2 (StatedSp 2 K)))
      (natImage (diagSub 2 (StatedSp 2 K))))
    (ht : t ∈ Y)
    (hPX : P ≤ natImage (diagSub 2 (StatedSp 2 K)))
    (hPN : natImage (diagSub 2 (StatedSp 2 K)) ⊓
      Subgroup.normalizer ((Y ⊓ natImage (diagSub 2 (StatedSp 2 K)) : Subgroup _) :
        Set _) ≤ P) :
    P.map (MulAut.conj t).toMonoidHom = P := by
  classical
  let Γ := StatedSp 2 K
  let D : Subgroup (GL (Fin 2 × (Fin 2 ⊕ Fin 2)) K) := diagSub 2 Γ
  let X : Subgroup (MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K)) := natImage D
  let S : Subgroup (MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K)) := Y ⊓ X
  have hSylS : IsSylowIn 2 S X := hSyl
  let eD : ↥Γ ≃* ↥D :=
    Subgroup.equivMapOfInjective Γ (diagGL 2) (diagGL_injective (ι := Fin 2 ⊕ Fin 2) (K := K) 2)
  let ψ : ↥Γ ≃* ↥X := eD.trans (natEquiv D)
  let f : Γ →* MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K) :=
    X.subtype.comp ψ.toMonoidHom
  have hf_apply : ∀ γ : Γ, f γ = matAut (diagGL 2 (γ : GL (Fin 2 ⊕ Fin 2) K)) := by
    intro γ
    change (ψ γ : MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K)) = _
    rw [show ψ γ = natEquiv D (eD γ) from rfl, CFSG.Quasithin.H.coe_natEquiv]
    have hDcoe : ((eD γ : ↥D) : GL (Fin 2 × (Fin 2 ⊕ Fin 2)) K) =
        diagGL 2 (γ : GL (Fin 2 ⊕ Fin 2) K) :=
      Subgroup.coe_equivMapOfInjective_apply Γ (diagGL 2)
        (diagGL_injective (ι := Fin 2 ⊕ Fin 2) (K := K) 2) γ
    change matAut (((eD γ : ↥D) : GL (Fin 2 × (Fin 2 ⊕ Fin 2)) K)) =
      matAut (diagGL 2 (γ : GL (Fin 2 ⊕ Fin 2) K))
    exact congrArg matAut hDcoe
  have hf_inj : Function.Injective f := by
    intro a b h
    exact ψ.injective (Subtype.ext h)
  let SΓ : Subgroup Γ := (S.subgroupOf X).comap ψ.toMonoidHom
  let PΓ : Subgroup Γ := (P.subgroupOf X).comap ψ.toMonoidHom
  have hSψ : SΓ.map ψ.toMonoidHom = S.subgroupOf X :=
    Subgroup.map_comap_eq_self (f := ψ.toMonoidHom) (H := S.subgroupOf X)
      (by rw [MonoidHom.range_eq_top.mpr ψ.surjective]; exact le_top)
  have hPψ : PΓ.map ψ.toMonoidHom = P.subgroupOf X :=
    Subgroup.map_comap_eq_self (f := ψ.toMonoidHom) (H := P.subgroupOf X)
      (by rw [MonoidHom.range_eq_top.mpr ψ.surjective]; exact le_top)
  have hSmap : SΓ.map f = S := by
    change SΓ.map (X.subtype.comp ψ.toMonoidHom) = S
    rw [← Subgroup.map_map, hSψ, Subgroup.map_subgroupOf_eq_of_le (inf_le_right : S ≤ X)]
  have hPmap : PΓ.map f = P := by
    change PΓ.map (X.subtype.comp ψ.toMonoidHom) = P
    rw [← Subgroup.map_map, hPψ, Subgroup.map_subgroupOf_eq_of_le hPX]
  have hSe' : IsSylowIn 2 (S.subgroupOf X) ⊤ := by
    refine isSylowIn_of_card_eq le_top ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ≤ X)).toEquiv,
      Subgroup.card_top]
    exact hSylS.card_eq
  have hSΓ : IsSylowIn 2 SΓ ⊤ := by
    refine (E1.isSylowIn_map_mulEquiv ψ).1 ?_
    rw [hSψ, Subgroup.map_top_of_surjective _ ψ.surjective]
    exact hSe'
  have hN : Subgroup.normalizer (SΓ : Set Γ) ≤ PΓ := by
    intro x hx
    have hnorm : (Subgroup.normalizer (SΓ : Set Γ)).map ψ.toMonoidHom =
        Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      rw [Subgroup.map_equiv_normalizer_eq SΓ ψ, hSψ]
    have hxN : ψ x ∈ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      rw [← hnorm]
      exact Subgroup.mem_map_of_mem ψ.toMonoidHom hx
    have hxN' : (ψ x : MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K)) ∈
        Subgroup.normalizer (S : Set (MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K))) := by
      rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_right : S ≤ X)] at hxN
      exact Subgroup.mem_subgroupOf.mp hxN
    have hxP : (ψ x : MulAut _) ∈ P := hPN (Subgroup.mem_inf.mpr ⟨(ψ x).2, hxN'⟩)
    exact hxP
  have hSmax : ∀ {Q : Subgroup Γ}, IsPGroup 2 ↥Q → SΓ ≤ Q → Q = SΓ := by
    intro Q hQ hSQ
    refine (Subgroup.eq_of_le_of_card_ge hSQ ?_).symm
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hQ
    have hdvd : 2 ^ j ∣ Nat.card Γ := by
      rw [← hj]
      exact Subgroup.card_subgroup_dvd_card Q
    have hjfact : j ≤ (Nat.card Γ).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
    have hcard : Nat.card SΓ = 2 ^ (Nat.card Γ).factorization 2 := by
      simpa [Subgroup.card_top] using hSΓ.card_eq
    rw [hj, hcard]
    exact Nat.pow_le_pow_right (by norm_num) hjfact
  let S' : Sylow 2 Γ := Sylow.mk SΓ hSΓ.isPGroup hSmax
  have htN : t ∈ Subgroup.normalizer (S : Set (MulAut _)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Y ⊓ X).map (MulAut.conj t).toMonoidHom = Y ⊓ X
    have hYmap : Y.map (MulAut.conj t).toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ht)
    have hXmap : X.map (MulAut.conj t).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hY ht)
    rw [Subgroup.map_inf_eq Y X (MulAut.conj t).toMonoidHom (MulAut.conj t).injective,
      hYmap, hXmap]
  have hSstable_t : S.map (MulAut.conj t).toMonoidHom = S :=
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp htN)
  obtain ⟨B, σ, hconj⟩ := exists_sp4_conj_of_mem_normalizer_diag (k := 2) (hY ht)
  let α : MulAut Γ := MulAut.conj B * fieldSp 2 K σ
  have hfα : ∀ γ : Γ, f (α γ) = t * f γ * t⁻¹ := by
    intro γ
    have h1 := hconj γ
    have h2 : f (α γ) =
        matAut (diagGL 2 (((B * fieldSp 2 K σ γ * B⁻¹ : Γ) : GL (Fin 2 ⊕ Fin 2) K))) := by
      rw [hf_apply (α γ)]
      congr 1
    rw [h2, hf_apply γ]
    exact h1.symm
  have hSstable : SΓ.map α.toMonoidHom = SΓ := by
    apply Subgroup.map_injective hf_inj
    have hcomp : f.comp α.toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp f :=
      MonoidHom.ext hfα
    calc (SΓ.map α.toMonoidHom).map f
        = SΓ.map (f.comp α.toMonoidHom) := by rw [Subgroup.map_map]
      _ = SΓ.map ((MulAut.conj t).toMonoidHom.comp f) := by rw [hcomp]
      _ = (SΓ.map f).map (MulAut.conj t).toMonoidHom := by rw [← Subgroup.map_map]
      _ = S.map (MulAut.conj t).toMonoidHom := by rw [hSmap]
      _ = S := hSstable_t
      _ = SΓ.map f := hSmap.symm
  have hPΓmap : PΓ.map α.toMonoidHom = PΓ := by
    refine CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.map_eq_of_normalizer_le
      B σ S' ?_ ?_
    · change SΓ.map α.toMonoidHom = SΓ
      exact hSstable
    · change Subgroup.normalizer (SΓ : Set Γ) ≤ PΓ
      exact hN
  have hcomp : f.comp α.toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp f :=
    MonoidHom.ext hfα
  calc P.map (MulAut.conj t).toMonoidHom
      = (PΓ.map f).map (MulAut.conj t).toMonoidHom := by rw [hPmap]
    _ = PΓ.map ((MulAut.conj t).toMonoidHom.comp f) := by rw [Subgroup.map_map]
    _ = PΓ.map (f.comp α.toMonoidHom) := by rw [← hcomp]
    _ = (PΓ.map α.toMonoidHom).map f := by rw [← Subgroup.map_map]
    _ = PΓ.map f := by rw [hPΓmap]
    _ = P := hPmap

theorem k_Sp4TwoNat_noSwap_of_field {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type} [CommGroup W] [Finite W]
    (X Y : Subgroup (MulAut W))
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hSyl : IsSylowIn 2 (Y ⊓ X) X)
    {π : ↥(StatedSp 2 K) →* ↥X}
    (hVia : SumOfNatVia (FFModel.nat (StatedSp 2 K)) X ⊤ ⊥ 2 π)
    (hswap : SwapsParabolics Y X) : False := by
  classical
  obtain ⟨I, e, hreal, he, hmemI⟩ := exists_coords_of_sumOfNatVia (StatedSp 2 K) hVia
  have hπ : Function.Surjective π := (hreal 0).1
  let c : MulAut W ≃* MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K) := MulAut.congr e
  let Xe : Subgroup (MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K)) := X.map c.toMonoidHom
  let Ye : Subgroup (MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K)) := Y.map c.toMonoidHom
  have hXe : Xe = natImage (diagSub 2 (StatedSp 2 K)) :=
    map_congrHom_eq_natImage_diag (Γ := StatedSp 2 K) hπ e he
  have hSe_eq : Ye ⊓ Xe = (Y ⊓ X).map c.toMonoidHom := by
    rw [show Ye = Y.map c.toMonoidHom from rfl, show Xe = X.map c.toMonoidHom from rfl,
      Subgroup.map_inf_eq Y X c.toMonoidHom c.injective]
  have hSyl_e : IsSylowIn 2 (Ye ⊓ Xe) Xe := by
    have h := (E1.isSylowIn_map_mulEquiv c).2 hSyl
    rwa [← hSe_eq, show Xe = X.map c.toMonoidHom from rfl] at h
  have hYe : Ye ≤ Subgroup.normalizer (Xe : Set (MulAut _)) := by
    have h := Subgroup.map_mono (f := c.toMonoidHom) hYX
    rw [Subgroup.map_equiv_normalizer_eq X c] at h
    simpa [Ye, Xe] using h
  obtain ⟨t, htY, P, hP, hPt⟩ := hswap
  have hPX : P.map c.toMonoidHom ≤ natImage (diagSub 2 (StatedSp 2 K)) := by
    rw [← hXe]
    exact Subgroup.map_mono hP.1
  have hPN : natImage (diagSub 2 (StatedSp 2 K)) ⊓
      Subgroup.normalizer ((Ye ⊓ Xe : Subgroup _) : Set _) ≤ P.map c.toMonoidHom := by
    have h := Subgroup.map_mono (f := c.toMonoidHom) hP.2.1
    have hnorm : (Subgroup.normalizer (Y ⊓ X : Set (MulAut W))).map c.toMonoidHom =
        Subgroup.normalizer ((Y ⊓ X).map c.toMonoidHom : Set _) :=
      Subgroup.map_equiv_normalizer_eq (Y ⊓ X) c
    have hL : (X ⊓ Subgroup.normalizer (Y ⊓ X : Set (MulAut W))).map c.toMonoidHom =
        Xe ⊓ Subgroup.normalizer ((Ye ⊓ Xe : Subgroup _) : Set _) := by
      rw [Subgroup.map_inf_eq X (Subgroup.normalizer (Y ⊓ X : Set (MulAut W)))
          c.toMonoidHom c.injective, hnorm, hSe_eq]
    have h' : Xe ⊓ Subgroup.normalizer ((Ye ⊓ Xe : Subgroup _) : Set _) ≤
        P.map c.toMonoidHom := by
      rw [← hL]
      exact h
    have h'' : natImage (diagSub 2 (StatedSp 2 K)) ⊓
        Subgroup.normalizer ((Ye ⊓ Xe : Subgroup _) : Set _) ≤ P.map c.toMonoidHom := by
      rw [← hXe]
      exact h'
    exact h''
  have hPN' : natImage (diagSub 2 (StatedSp 2 K)) ⊓
      Subgroup.normalizer ((Ye ⊓ natImage (diagSub 2 (StatedSp 2 K)) : Subgroup _) :
        Set _) ≤ P.map c.toMonoidHom := by
    have hSeX : (Ye ⊓ natImage (diagSub 2 (StatedSp 2 K)) : Subgroup _) = Ye ⊓ Xe := by
      rw [← hXe]
    rw [hSeX]
    exact hPN
  have hPconj_e : (P.map c.toMonoidHom).map (MulAut.conj (c t)).toMonoidHom =
      P.map c.toMonoidHom :=
    map_conj_eq_of_isSylowIn_natImage_diag Ye (P.map c.toMonoidHom) (c t)
      (hXe ▸ hYe) (hXe ▸ hSyl_e) (Subgroup.mem_map_of_mem c.toMonoidHom htY) hPX hPN'
  have hconjP : P.map (MulAut.conj t).toMonoidHom = P := by
    have hcomp : c.toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj (c t)).toMonoidHom.comp c.toMonoidHom :=
      MonoidHom.ext fun x => by
        simp [MulAut.conj_apply]
    have h1 : (P.map (MulAut.conj t).toMonoidHom).map c.toMonoidHom =
        P.map c.toMonoidHom := by
      calc (P.map (MulAut.conj t).toMonoidHom).map c.toMonoidHom
          = P.map (c.toMonoidHom.comp (MulAut.conj t).toMonoidHom) := by
            rw [Subgroup.map_map]
        _ = P.map ((MulAut.conj (c t)).toMonoidHom.comp c.toMonoidHom) := by rw [hcomp]
        _ = (P.map c.toMonoidHom).map (MulAut.conj (c t)).toMonoidHom := by
              rw [← Subgroup.map_map]
        _ = P.map c.toMonoidHom := hPconj_e
    exact Subgroup.map_injective c.injective h1
  exact hPt hconjP

theorem k_Sp4TwoNat_noSwap_holds : K_Sp4TwoNat_noSwap := by
  intro W _ _ hsq X Y n hYX hSyl hSp hSum hswap
  classical
  obtain ⟨K, hKfield, hKfinite, π, hKcard, hVia⟩ :=
    exists_sumOfNatVia_of_sumOfNatIsoMod_sp4 hSum
  have hchar : CharP K 2 :=
    @CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow K hKfield hKfinite 2 n
      Nat.prime_two hKcard
  exact @k_Sp4TwoNat_noSwap_of_field K hKfield hKfinite hchar
    W _ _ X Y hYX hSyl π hVia hswap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
