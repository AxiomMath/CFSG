module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_8

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.Section8

universe v
universe w
universe u

@[expose] public def theorem_8_12_statement
    {G : Type u} [Group G] [Finite G]
    (M MF U Ms : Subgroup G)
    (A A0 A1 : Set G) : Prop :=
  IsMinCE G →
    theorem_8_12_source_data M MF U Ms A A0 A1 →
      theorem_8_12_source_conclusion M MF U A A1

/-- Peterfalvi `(8.13)`. -/


private theorem theorem_8_12_isMulCommutative_of_mulEquiv
    {R S : Type*} [Group R] [Group S]
    (e : R ≃* S)
    (hS : IsMulCommutative S) :
    IsMulCommutative R := by
  letI : IsMulCommutative S := hS
  refine ⟨⟨fun x y => ?_⟩⟩
  apply e.injective
  calc
    e (x * y) = e x * e y := e.map_mul x y
    _ = e y * e x :=
      (IsMulCommutative.is_comm (M := S)).comm (e x) (e y)
    _ = e (y * x) := (e.map_mul y x).symm

private theorem theorem_8_12_hasAbelianSylowRankAtMostTwo_of_mulEquiv
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (e : R ≃* S)
    (hS : section16HasAbelianSylowRankAtMostTwo S) :
    section16HasAbelianSylowRankAtMostTwo R := by
  classical
  intro p P
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let f : R →* S := e.toMonoidHom
  let Q : Sylow p.val S := P.mapSurjective (f := f) e.surjective
  have hQ := hS p Q
  change IsMulCommutative ((P : Subgroup R).map f) ∧
    generatorRank ((P : Subgroup R).map f) ≤ 2 at hQ
  let ePmap : (P : Subgroup R) ≃* ((P : Subgroup R).map f) :=
    Subgroup.equivMapOfInjective (f := f) (P : Subgroup R) e.injective
  have hQmap_comm : IsMulCommutative ((P : Subgroup R).map f) := hQ.1
  have hcomm : IsMulCommutative (P : Subgroup R) :=
    theorem_8_12_isMulCommutative_of_mulEquiv ePmap hQmap_comm
  have hrank : generatorRank (P : Subgroup R) ≤ 2 := by
    have hle :
        generatorRank (P : Subgroup R) ≤
          generatorRank ((P : Subgroup R).map f) :=
      generatorRank_le_of_equiv ePmap.symm
    exact hle.trans hQ.2
  exact ⟨hcomm, hrank⟩


private theorem theorem_8_12_hasAbelianSylowRankAtMostTwo_of_conjBy
    {G : Type u} [Group G] [Finite G]
    {U V : Subgroup G} {g : G}
    (hV : V = U.conjBy g)
    (hU : section16HasAbelianSylowRankAtMostTwo U) :
    section16HasAbelianSylowRankAtMostTwo V := by
  subst V
  let eUmap : U ≃* U.map (MulAut.conj g).toMonoidHom :=
    Subgroup.equivMapOfInjective (f := (MulAut.conj g).toMonoidHom)
      U (MulAut.conj g).injective
  exact theorem_8_12_hasAbelianSylowRankAtMostTwo_of_mulEquiv eUmap.symm hU

private theorem theorem_8_12_typeI_data_of_source_branch
    {G : Type u} [Group G] [Finite G]
    {M MF U : Subgroup G}
    (hBranch :
      ∃ U1 U0 : Subgroup G,
        typeFData M MF U U1 U0 ∧
          (section16TISubset (section16NonidentityElements (MF : Set G)) ∨
            (IsMulCommutative MF ∧ groupRank MF = 2) ∨
              ((∀ p : Nat.Primes, p ∈ subgroupPrimeSet MF →
                Monoid.exponent U ∣ p.val - 1) ∧
                ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
                  IsCyclic (section10PPrimeCore p MF)))) :
    typeIDefinitionData M MF := by
  rcases hBranch with ⟨U1, U0, hF, hAlt⟩
  exact ⟨U, U1, U0, hF, hAlt⟩

private theorem theorem_8_12_typeII_data_of_source_branch
    {G : Type u} [Group G] [Finite G]
    {M MF U : Subgroup G}
    (hBranch :
      ∃ W1 W2 U1 U0 : Subgroup G,
        typePDefinitionData M MF U W1 W2 ∧
          typeIIToIVSourceCondition M U W1 ∧
          IsMulCommutative U ∧
          ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
          typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    typeIIDefinitionData M MF := by
  rcases hBranch with ⟨W1, W2, U1, U0, hP, hCond, hComm, hNorm, hF⟩
  exact ⟨U, W1, W2, U1, U0, hP, hCond, hComm, hNorm, hF⟩


private theorem theorem_8_12_unique_maximal_of_theoremB_subgroups
    {G : Type u} [Group G] [Finite G]
    {M MF U : Subgroup G}
    (hMF_eq : MF = section10Msigma M)
    (hB :
      ∀ X : Subgroup G, X ≤ U → X ≠ ⊥ →
        subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ →
          section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) :
    ∀ X : Set G, X.Nonempty →
      X ⊆ section16NonidentityElements (U : Set G) →
        section16CentralizerInSet MF X ≠ ⊥ →
          section9MaximalSubgroupsContaining (Subgroup.centralizer X) = {M} := by
  classical
  intro X hXne hXU hCentNe
  let Xsub : Subgroup G := Subgroup.closure X
  have hXsubU : Xsub ≤ U := by
    refine (Subgroup.closure_le (K := U)).2 ?_
    intro x hxX
    exact (hXU hxX).1
  have hXsubNe : Xsub ≠ ⊥ := by
    rcases hXne with ⟨x, hxX⟩
    have hxne : x ≠ 1 := (hXU hxX).2
    have hxSub : x ∈ Xsub := Subgroup.subset_closure hxX
    intro hbot
    exact hxne (by simpa [Xsub, hbot] using hxSub)
  have hCentSubNe : subgroupCentralizerIn (section10Msigma M) Xsub ≠ ⊥ := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hCentNe with ⟨yC, hyCne⟩
    let y : G := yC
    have hyMF : y ∈ MF := yC.property.1
    have hyCentX : y ∈ Subgroup.centralizer X := yC.property.2
    have hySigma : y ∈ section10Msigma M := by
      simpa [hMF_eq] using hyMF
    have hyCentSub : y ∈ Subgroup.centralizer (Xsub : Set G) := by
      simpa [Xsub, Subgroup.centralizer_closure] using hyCentX
    let yCsub : subgroupCentralizerIn (section10Msigma M) Xsub :=
      ⟨y, hySigma, hyCentSub⟩
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨yCsub, ?_⟩
    intro hyOne
    exact hyCne (Subtype.ext (by
      simpa [yCsub, y] using congrArg Subtype.val hyOne))
  have hUniqSub :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Xsub : Set G)) = {M} :=
    hB Xsub hXsubU hXsubNe hCentSubNe
  simpa [Xsub, Subgroup.centralizer_closure] using hUniqSub

private theorem theorem_8_12_unique_maximal_of_theoremB_conjugate
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U Uc : Subgroup G} {d : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF_eq : MF = section10Msigma M)
    (hdM : d ∈ M)
    (hUconj : U = Uc.conjBy d)
    (hB :
      ∀ X : Subgroup G, X ≤ Uc → X ≠ ⊥ →
        subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ →
          section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) :
    ∀ X : Set G, X.Nonempty →
      X ⊆ section16NonidentityElements (U : Set G) →
        section16CentralizerInSet MF X ≠ ⊥ →
          section9MaximalSubgroupsContaining (Subgroup.centralizer X) = {M} := by
  classical
  intro X hXne hXU hCentNe
  let Xsub : Subgroup G := Subgroup.closure X
  have hXsubU : Xsub ≤ U := by
    refine (Subgroup.closure_le (K := U)).2 ?_
    intro x hxX
    exact (hXU hxX).1
  have hXsubNe : Xsub ≠ ⊥ := by
    rcases hXne with ⟨x, hxX⟩
    have hxne : x ≠ 1 := (hXU hxX).2
    have hxSub : x ∈ Xsub := Subgroup.subset_closure hxX
    intro hbot
    exact hxne (by simpa [Xsub, hbot] using hxSub)
  have hCentSubNe : subgroupCentralizerIn (section10Msigma M) Xsub ≠ ⊥ := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hCentNe with ⟨yC, hyCne⟩
    let y : G := yC
    have hyMF : y ∈ MF := yC.property.1
    have hyCentX : y ∈ Subgroup.centralizer X := yC.property.2
    have hySigma : y ∈ section10Msigma M := by
      simpa [hMF_eq] using hyMF
    have hyCentSub : y ∈ Subgroup.centralizer (Xsub : Set G) := by
      simpa [Xsub, Subgroup.centralizer_closure] using hyCentX
    let yCsub : subgroupCentralizerIn (section10Msigma M) Xsub :=
      ⟨y, hySigma, hyCentSub⟩
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨yCsub, ?_⟩
    intro hyOne
    exact hyCne (Subtype.ext (by
      simpa [yCsub, y] using congrArg Subtype.val hyOne))
  let Y : Subgroup G := Xsub.conjBy d⁻¹
  have hU_back : U.conjBy d⁻¹ = Uc := by
    rw [hUconj]
    exact Subgroup.conjBy_inv Uc d
  have hYUc : Y ≤ Uc := by
    intro y hy
    have hyUconj : y ∈ U.conjBy d⁻¹ := by
      rcases Subgroup.mem_map.mp hy with ⟨x, hxXsub, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x, hXsubU hxXsub, rfl⟩
    simpa [Y, hU_back] using hyUconj
  have hYne : Y ≠ ⊥ := by
    simpa [Y] using
      (section11_conjBy_ne_bot (G := G) (H := Xsub) (g := d⁻¹) hXsubNe)
  have hdNormSigma : d ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    section12_le_normalizer_msigma (M := M) hdM
  have hdinvNormSigma :
      d⁻¹ ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    Subgroup.inv_mem _ hdNormSigma
  have hCentY : subgroupCentralizerIn (section10Msigma M) Y ≠ ⊥ := by
    change subgroupCentralizerIn (section10Msigma M) (Xsub.conjBy d⁻¹) ≠ ⊥
    rw [section11_subgroupCentralizerIn_conjBy_eq_self_of_mem_normalizer
      hdinvNormSigma]
    exact section11_conjBy_ne_bot (G := G)
      (H := subgroupCentralizerIn (section10Msigma M) Xsub) (g := d⁻¹)
      hCentSubNe
  have hUniqY :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {M} :=
    hB Y hYUc hYne hCentY
  have hYconj : Y.conjBy d = Xsub := by
    simpa [Y] using (Subgroup.conjBy_inv' Xsub d)
  have hMconj : M.conjBy d = M :=
    section11_conjBy_eq_of_mem_normalizer (H := M) (Subgroup.le_normalizer hdM)
  have hUniqXsub :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Xsub : Set G)) = {M} := by
    have hConj :=
      section16_maximalSubgroupsContaining_centralizer_conjBy
        (G := G) (X := Y) (M := M) hM d hUniqY
    simpa [hYconj, hMconj] using hConj
  simpa [Xsub, Subgroup.centralizer_closure] using hUniqXsub

private theorem theorem_8_12_source_diff_eq_ASet_diff_msigma_of_complement
    {G : Type u} [Group G] [Finite G]
    {M D MF U : Subgroup G}
    {A A1 : Set G}
    (hDM : D ≤ M)
    (hMF : section16MFSubgroup M MF)
    (hMF_eq : MF = section10Msigma M)
    (hcomp : section12ComplementIn D MF U)
    (hA : A = section8CentralizerUnion D MF)
    (hA1 : A1 = a1Set MF) :
    A \ A1 = section16ASet M U \ (section10Msigma M : Set G) := by
  classical
  rcases hMF.1 with ⟨hMFM, hMFnorm, _hMFnil, _hMFHall⟩
  have hM_le_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFnorm
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) := by
    intro u hu
    exact hM_le_norm_MF (hDM (hcomp.2.1 hu))
  have hprod :
      ((U ⊔ MF : Subgroup G) : Set G) = (U : Set G) * (MF : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right U MF hU_norm_MF
  have hD_eq : D = U ⊔ MF := by
    simpa [sup_comm] using hcomp.2.2.1
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyA, hyNotA1⟩
    rw [hA, section8CentralizerUnion] at hyA
    rcases hyA with ⟨x, hxMFsharp, hyCentSharp⟩
    have hxMF : x ∈ MF := hxMFsharp.1
    have hxne : x ≠ 1 := hxMFsharp.2
    have hyCent : y ∈ elementCentralizerIn D x := hyCentSharp.1
    have hyD : y ∈ D := by
      simpa [elementCentralizerIn] using hyCent.1
    have hyM : y ∈ M := hDM hyD
    have hyne : y ≠ 1 := hyCentSharp.2
    have hyNotMF : y ∉ MF := by
      intro hyMF
      have hyA1 : y ∈ A1 := by
        rw [hA1, a1Set]
        exact ⟨hyMF, hyne⟩
      exact hyNotA1 hyA1
    have hyNotSigma : y ∉ section10Msigma M := by
      intro hySigma
      exact hyNotMF (by simpa [hMF_eq] using hySigma)
    have hyProd : y ∈ (U : Set G) * (section10Msigma M : Set G) := by
      have hySup : y ∈ U ⊔ MF := by
        simpa [hD_eq] using hyD
      have hyMul : y ∈ (U : Set G) * (MF : Set G) := by
        have hySupSet : y ∈ ((U ⊔ MF : Subgroup G) : Set G) := hySup
        rw [hprod] at hySupSet
        exact hySupSet
      simpa [← hMF_eq] using hyMul
    have hyHat : y ∈ section16HatMsigmaSet M := by
      refine ⟨hyM, ?_⟩
      have hxSigma : x ∈ section10Msigma M := by
        simpa [← hMF_eq] using hxMF
      have hxCentY : x ∈ Subgroup.centralizer ({y} : Set G) := by
        have hyCentX : y ∈ Subgroup.centralizer ({x} : Set G) := by
          simpa [elementCentralizerIn] using hyCent.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hyCentX).symm
      let xC : elementCentralizerIn (section10Msigma M) y :=
        ⟨x, hxSigma, hxCentY⟩
      refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨xC, ?_⟩
      intro hxC_one
      exact hxne (by simpa [xC] using congrArg Subtype.val hxC_one)
    exact ⟨⟨hyHat, hyProd, hyne⟩, hyNotSigma⟩
  · intro hy
    rcases hy with ⟨hyA, hyNotSigma⟩
    rcases hyA with ⟨hyHat, hyProd, hyne⟩
    have hyD : y ∈ D := by
      have hyMul : y ∈ (U : Set G) * (MF : Set G) := by
        simpa [← hMF_eq] using hyProd
      have hySup : y ∈ U ⊔ MF := by
        have hySupSet : y ∈ ((U ⊔ MF : Subgroup G) : Set G) := by
          rw [hprod]
          exact hyMul
        exact hySupSet
      simpa [hD_eq] using hySup
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hyHat.2 with ⟨xC, hxCne⟩
    let x : G := xC
    have hxSigma : x ∈ section10Msigma M := xC.property.1
    have hxMF : x ∈ MF := by
      simpa [hMF_eq] using hxSigma
    have hxne : x ≠ 1 := by
      intro hxone
      exact hxCne (Subtype.ext (by simp [x, hxone]))
    have hyCentX : y ∈ Subgroup.centralizer ({x} : Set G) := by
      have hxCentY : x ∈ Subgroup.centralizer ({y} : Set G) := xC.property.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxCentY).symm
    have hyCent : y ∈ elementCentralizerIn D x := by
      exact ⟨hyD, hyCentX⟩
    have hySource : y ∈ section8CentralizerUnion D MF := by
      refine ⟨x, ⟨hxMF, hxne⟩, ?_⟩
      exact ⟨hyCent, hyne⟩
    have hyNotA1 : y ∉ A1 := by
      intro hyA1
      rw [hA1, a1Set] at hyA1
      exact hyNotSigma (by simpa [← hMF_eq] using hyA1.1)
    exact ⟨by simpa [hA] using hySource, hyNotA1⟩

private theorem theorem_8_12_ASet_eq_of_complements
    {G : Type u} [Group G] [Finite G]
    {M D MF U V : Subgroup G}
    (hDM : D ≤ M)
    (hMF : section16MFSubgroup M MF)
    (hMF_eq : MF = section10Msigma M)
    (hcompU : section12ComplementIn D MF U)
    (hcompV : section12ComplementIn D MF V) :
    section16ASet M U = section16ASet M V := by
  classical
  rcases hMF.1 with ⟨hMFM, hMFnorm, _hMFnil, _hMFHall⟩
  have hM_le_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFnorm
  have product_iff :
      ∀ W : Subgroup G, section12ComplementIn D MF W →
        ∀ y : G, y ∈ (W : Set G) * (section10Msigma M : Set G) ↔ y ∈ D := by
    intro W hcompW y
    have hW_norm_MF : W ≤ Subgroup.normalizer (MF : Set G) := by
      intro w hw
      exact hM_le_norm_MF (hDM (hcompW.2.1 hw))
    have hprod :
        ((W ⊔ MF : Subgroup G) : Set G) = (W : Set G) * (MF : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right W MF hW_norm_MF
    have hD_eq : D = W ⊔ MF := by
      simpa [sup_comm] using hcompW.2.2.1
    constructor
    · intro hy
      have hyMulMF : y ∈ (W : Set G) * (MF : Set G) := by
        simpa [← hMF_eq] using hy
      have hySup : y ∈ W ⊔ MF := by
        have hySupSet : y ∈ ((W ⊔ MF : Subgroup G) : Set G) := by
          rw [hprod]
          exact hyMulMF
        exact hySupSet
      simpa [hD_eq] using hySup
    · intro hyD
      have hySup : y ∈ W ⊔ MF := by
        simpa [hD_eq] using hyD
      have hyMulMF : y ∈ (W : Set G) * (MF : Set G) := by
        have hySupSet : y ∈ ((W ⊔ MF : Subgroup G) : Set G) := hySup
        rw [hprod] at hySupSet
        exact hySupSet
      simpa [← hMF_eq] using hyMulMF
  ext y
  constructor
  · intro hy
    exact ⟨hy.1, (product_iff V hcompV y).2
      ((product_iff U hcompU y).1 hy.2.1), hy.2.2⟩
  · intro hy
    exact ⟨hy.1, (product_iff U hcompU y).2
      ((product_iff V hcompV y).1 hy.2.1), hy.2.2⟩

private theorem theorem_8_12_msChoiceSource_eq_mf_of_typeI
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    (hChoice : msChoiceSource M MF Ms)
    (hTypeI : typeIDefinitionData M MF) :
    Ms = MF := by
  rcases hChoice with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨_hI, _hnotII, _hnotIII, _hnotIV, _hnotV, hMs⟩
    exact hMs
  · exact False.elim (hII.1 hTypeI)
  · exact False.elim (hIII.1 hTypeI)
  · exact False.elim (hIV.1 hTypeI)
  · exact False.elim (hV.1 hTypeI)

private theorem theorem_8_12_msChoiceSource_eq_mf_of_typeII
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    (hChoice : msChoiceSource M MF Ms)
    (hTypeII : typeIIDefinitionData M MF) :
    Ms = MF := by
  rcases hChoice with hI | hII | hIII | hIV | hV
  · exact False.elim (hI.2.1 hTypeII)
  · rcases hII with ⟨_hnotI, _hII, _hnotIII, _hnotIV, _hnotV, hMs⟩
    exact hMs
  · exact False.elim (hIII.2.1 hTypeII)
  · exact False.elim (hIV.2.1 hTypeII)
  · exact False.elim (hV.2.1 hTypeII)

private theorem theorem_8_12_bg_typeI_of_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms)
    (hSrcI : typeIDefinitionData M MF) :
    section16TypeI M MF := by
  classical
  have hNot :
      ¬ typeIIDefinitionData M MF ∧
        ¬ typeIIIDefinitionData M MF ∧
        ¬ typeIVDefinitionData M MF ∧
        ¬ typeVDefinitionData M MF := by
    rcases hMs with hI | hII | hIII | hIV | hV
    · rcases hI with ⟨_hI, hnotII, hnotIII, hnotIV, hnotV, _hMs⟩
      exact ⟨hnotII, hnotIII, hnotIV, hnotV⟩
    · exact False.elim (hII.1 hSrcI)
    · exact False.elim (hIII.1 hSrcI)
    · exact False.elim (hIV.1 hSrcI)
    · exact False.elim (hV.1 hSrcI)
  rcases section16_type_exhaustive_of_maximal (G := G) hM hMF with
    hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
  · exact hTypeI
  · exact False.elim
      (hNot.1 (theorem_8_8_typeII_to_source_public (G := G) hM hMF hTypeII))
  · exact False.elim
      (hNot.2.1 (theorem_8_8_typeIII_to_source_public (G := G) hM hMF hTypeIII))
  · exact False.elim
      (hNot.2.2.1 (theorem_8_8_typeIV_to_source_public (G := G) hM hMF hTypeIV))
  · exact False.elim
      (hNot.2.2.2 (theorem_8_8_typeV_to_source_public (G := G) hM hMF hTypeV))


private theorem theorem_8_12_bg_typeII_of_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms)
    (hSrcII : typeIIDefinitionData M MF) :
    section16TypeII M MF := by
  classical
  have hNot :
      ¬ typeIDefinitionData M MF ∧
        ¬ typeIIIDefinitionData M MF ∧
        ¬ typeIVDefinitionData M MF ∧
        ¬ typeVDefinitionData M MF := by
    rcases hMs with hI | hII | hIII | hIV | hV
    · exact False.elim (hI.2.1 hSrcII)
    · rcases hII with ⟨hnotI, _hII, hnotIII, hnotIV, hnotV, _hMs⟩
      exact ⟨hnotI, hnotIII, hnotIV, hnotV⟩
    · exact False.elim (hIII.2.1 hSrcII)
    · exact False.elim (hIV.2.1 hSrcII)
    · exact False.elim (hV.2.1 hSrcII)
  rcases section16_type_exhaustive_of_maximal (G := G) hM hMF with
    hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
  · exact False.elim
      (hNot.1 (theorem_8_8_typeI_to_source_public (G := G) hM hMF hTypeI))
  · exact hTypeII
  · exact False.elim
      (hNot.2.1 (theorem_8_8_typeIII_to_source_public (G := G) hM hMF hTypeIII))
  · exact False.elim
      (hNot.2.2.1 (theorem_8_8_typeIV_to_source_public (G := G) hM hMF hTypeIV))
  · exact False.elim
      (hNot.2.2.2 (theorem_8_8_typeV_to_source_public (G := G) hM hMF hTypeV))

public theorem theorem_8_12_bg_typeII_of_source_public
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms)
    (hSrcII : typeIIDefinitionData M MF) :
    section16TypeII M MF :=
  theorem_8_12_bg_typeII_of_source (G := G) hM hMF hMs hSrcII

private theorem theorem_8_12_typeI_theoremB_of_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms)
    (hBranch :
      ∃ U1 U0 : Subgroup G,
        typeFData M MF U U1 U0 ∧
          (section16TISubset (section16NonidentityElements (MF : Set G)) ∨
            (IsMulCommutative MF ∧ groupRank MF = 2) ∨
              ((∀ p : Nat.Primes, p ∈ subgroupPrimeSet MF →
                Monoid.exponent U ∣ p.val - 1) ∧
                ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
                  IsCyclic (section10PPrimeCore p MF)))) :
    section16TheoremBConclusions M (⊥ : Subgroup G) U ∧
      MF = section10Msigma M := by
  classical
  have hSrcI : typeIDefinitionData M MF :=
    theorem_8_12_typeI_data_of_source_branch hBranch
  have hType : section16TypeI M MF :=
    theorem_8_12_bg_typeI_of_source (G := G) hM hMF hMs hSrcI
  rcases hBranch with ⟨U1, U0, hF, _hAlt⟩
  rcases hF with
    ⟨_hsolv, _hodd, _hMFsrc, _hMFpos, _hMFlt, _hUne, hcomp, _hU1le,
      _hU1comm, _hU1norm, _hCent, _hU0le, _hExp, _hFrob⟩
  rcases section16_typeI_KUData_of_complement (G := G) hM hMF hType hcomp with
    ⟨hKU, hMF_eq⟩
  exact ⟨theorem_16_B (G := G) hM hMF hKU, hMF_eq⟩

private theorem theorem_8_12_typeI_conclusion_of_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U Ms : Subgroup G}
    {A A1 : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms)
    (hBranch :
      ∃ U1 U0 : Subgroup G,
        typeFData M MF U U1 U0 ∧
          (section16TISubset (section16NonidentityElements (MF : Set G)) ∨
            (IsMulCommutative MF ∧ groupRank MF = 2) ∨
              ((∀ p : Nat.Primes, p ∈ subgroupPrimeSet MF →
                Monoid.exponent U ∣ p.val - 1) ∧
                ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
                  IsCyclic (section10PPrimeCore p MF))))
    (hA : A = section8CentralizerUnion M MF)
    (hA1 : A1 = a1Set MF) :
    theorem_8_12_source_conclusion M MF U A A1 := by
  classical
  rcases theorem_8_12_typeI_theoremB_of_source
      (G := G) (M := M) (MF := MF) (U := U) (Ms := Ms)
      hM hMF hMs hBranch with
    ⟨hB, hMF_eq⟩
  rcases hBranch with ⟨U1, U0, hF, _hAlt⟩
  rcases hF with
    ⟨_hsolv, _hodd, _hMFsrc, _hMFpos, _hMFlt, _hUne, hcomp, _hU1le,
      _hU1comm, _hU1norm, _hCent, _hU0le, _hExp, _hFrob⟩
  have hSet :
      A \ A1 = section16ASet M U \ (section10Msigma M : Set G) :=
    theorem_8_12_source_diff_eq_ASet_diff_msigma_of_complement
      (G := G) (M := M) (D := M) (MF := MF) (U := U)
      (A := A) (A1 := A1) le_rfl hMF hMF_eq hcomp hA hA1
  refine ⟨hB.1, ?_, ?_⟩
  · exact theorem_8_12_unique_maximal_of_theoremB_subgroups
      (G := G) (M := M) (MF := MF) (U := U) hMF_eq hB.2.2.2.1
  · simpa [hSet] using hB.2.2.2.2

private theorem theorem_8_12_typeII_canonical_conjugate_of_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms)
    (hBranch :
      ∃ W1 W2 U1 U0 : Subgroup G,
        typePDefinitionData M MF U W1 W2 ∧
          typeIIToIVSourceCondition M U W1 ∧
          IsMulCommutative U ∧
          ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
          typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    ∃ K Uc : Subgroup G, ∃ d : ambientDerivedSubgroup M,
      section16KUData M K Uc ∧
        section16TheoremBConclusions M K Uc ∧
          MF = section10Msigma M ∧
            section12ComplementIn (ambientDerivedSubgroup M) MF Uc ∧
              U = Uc.conjBy (d : G) := by
  classical
  have hSrcII : typeIIDefinitionData M MF :=
    theorem_8_12_typeII_data_of_source_branch hBranch
  have hType : section16TypeII M MF :=
    theorem_8_12_bg_typeII_of_source (G := G) hM hMF hMs hSrcII
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, Uc, hKU15⟩
  have hKU : section16KUData M K Uc := by
    simpa [section16KUData] using hKU15
  have hProp :=
    proposition_16_1 (G := G) (M := M) (MF := MF) (K := K) (U := Uc)
      hM hMF hKU
  have hCaseP2 : section16CaseP2 K Uc := hProp.2.1.mp hType
  have hMF_eq : MF = section10Msigma M :=
    hProp.2.2.2.2.2.mpr (Or.inr (Or.inl hType))
  have hCommonCanonical :
      section16TypeCommon M MF Uc K (section16Kstar M K) :=
    (section16_typeII_canonical_caseP2_data
      (G := G) hM hMF hKU hType).1
  have hCompCanonical :
      section12ComplementIn (ambientDerivedSubgroup M) MF Uc :=
    hCommonCanonical.2.2.1
  rcases hBranch with ⟨W1, W2, U1, U0, hP, _hCond, _hComm, _hNorm, _hF⟩
  rcases hP with
    ⟨_hMFsrc, _hW1cyc, _hW1ne, _hW1Hall, _hW1Comp, _hUleD, _hUnil,
      _hW1norm, hCompU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hHatW⟩
  rcases section16_conjugate_ambient_complement_of_caseP2
      (G := G) hM hMF hKU hCaseP2.1 hCaseP2.2 hCompU with
    ⟨d, hUconj⟩
  exact ⟨K, Uc, d, hKU, theorem_16_B (G := G) hM hMF hKU,
    hMF_eq, hCompCanonical, hUconj⟩


public theorem theorem_8_12_typeII_groupRank_le_two_of_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms)
    (hBranch :
      ∃ W1 W2 U1 U0 : Subgroup G,
        typePDefinitionData M MF U W1 W2 ∧
          typeIIToIVSourceCondition M U W1 ∧
          IsMulCommutative U ∧
          ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
          typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    groupRank U ≤ 2 := by
  classical
  rcases theorem_8_12_typeII_canonical_conjugate_of_source
      (G := G) (M := M) (MF := MF) (U := U) (Ms := Ms)
      hM hMF hMs hBranch with
    ⟨K, Uc, d, hKU, _hB, _hMF_eq, _hCompCanonical, hUconj⟩
  have hUc_rank : groupRank Uc ≤ 2 := by
    let E : Subgroup G := K ⊔ Uc
    have hEcomp : section12ComplementToMsigma M E := by
      change section12ComplementIn M (section10Msigma M) E
      simpa [E, section16KUData] using hKU.2.2.1
    have hE_rank : groupRank E ≤ 2 :=
      section12_groupRank_E_le_two (G := G) hM hEcomp
    have hUcE : Uc ≤ E := by
      intro x hx
      exact Subgroup.mem_sup_right hx
    let eU : Uc.subgroupOf E ≃* Uc :=
      Subgroup.subgroupOfEquivOfLe (H := Uc) (K := E) hUcE
    exact ((groupRank_le_of_equiv eU).trans
      (groupRank_le_of_subgroup (R := E) (Uc.subgroupOf E))).trans hE_rank
  subst U
  let eU : Uc ≃* Uc.conjBy (d : G) := (MulAut.conj (d : G)).subgroupMap Uc
  exact (groupRank_le_of_equiv eU).trans hUc_rank

private theorem theorem_8_12_typeII_conclusion_of_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U Ms : Subgroup G}
    {A A1 : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms)
    (hBranch :
      ∃ W1 W2 U1 U0 : Subgroup G,
        typePDefinitionData M MF U W1 W2 ∧
          typeIIToIVSourceCondition M U W1 ∧
          IsMulCommutative U ∧
          ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
          typeFData (ambientDerivedSubgroup M) MF U U1 U0)
    (hA : A = section8CentralizerUnion (ambientDerivedSubgroup M) MF)
    (hA1 : A1 = a1Set MF) :
    theorem_8_12_source_conclusion M MF U A A1 := by
  classical
  rcases theorem_8_12_typeII_canonical_conjugate_of_source
      (G := G) (M := M) (MF := MF) (U := U) (Ms := Ms)
      hM hMF hMs hBranch with
    ⟨K, Uc, d, _hKU, hB, hMF_eq, hCompCanonical, hUconj⟩
  rcases hBranch with ⟨W1, W2, U1, U0, hP, _hCond, _hComm, _hNorm, _hF⟩
  rcases hP with
    ⟨_hMFsrc, _hW1cyc, _hW1ne, _hW1Hall, _hW1Comp, _hUleD, _hUnil,
      _hW1norm, hCompU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hHatW⟩
  have hDleM : ambientDerivedSubgroup M ≤ M :=
    section12_ambientDerivedSubgroup_le (G := G) (E := M)
  have hdM : (d : G) ∈ M := hDleM d.property
  have hSetSource :
      A \ A1 = section16ASet M U \ (section10Msigma M : Set G) :=
    theorem_8_12_source_diff_eq_ASet_diff_msigma_of_complement
      (G := G) (M := M) (D := ambientDerivedSubgroup M) (MF := MF) (U := U)
      (A := A) (A1 := A1) hDleM hMF hMF_eq hCompU hA hA1
  have hASetEq : section16ASet M U = section16ASet M Uc :=
    theorem_8_12_ASet_eq_of_complements
      (G := G) (M := M) (D := ambientDerivedSubgroup M) (MF := MF)
      (U := U) (V := Uc) hDleM hMF hMF_eq hCompU hCompCanonical
  have hSet :
      A \ A1 = section16ASet M Uc \ (section10Msigma M : Set G) := by
    simpa [hASetEq] using hSetSource
  refine ⟨?_, ?_, ?_⟩
  · exact theorem_8_12_hasAbelianSylowRankAtMostTwo_of_conjBy hUconj hB.1
  · exact theorem_8_12_unique_maximal_of_theoremB_conjugate
      (G := G) (M := M) (MF := MF) (U := U) (Uc := Uc) (d := (d : G))
      hM hMF_eq hdM hUconj hB.2.2.2.1
  · simpa [hSet] using hB.2.2.2.2


public theorem theorem_8_12_unique_maximal_of_source_diff_coprime
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U Ms : Subgroup G}
    {A A0 A1 : Set G} {x : G}
    (hSrc : theorem_8_12_source_data M MF U Ms A A0 A1)
    (hx : x ∈ A \ A1)
    (hcop : Nat.Coprime (orderOf x) (Nat.card Ms)) :
    section9MaximalSubgroupsContaining
      (Subgroup.centralizer ({x} : Set G)) = {M} := by
  classical
  rcases hSrc with ⟨hNotation, hCases⟩
  rcases hNotation with ⟨hM, hMF, hMs, _hA1, _hNotationCases⟩
  rcases hCases with hTypeI | hTypeII
  · rcases hTypeI with ⟨hBranch, hA, hA1'⟩
    have hSrcI : typeIDefinitionData M MF :=
      theorem_8_12_typeI_data_of_source_branch hBranch
    have hType : section16TypeI M MF :=
      theorem_8_12_bg_typeI_of_source (G := G) hM hMF hMs hSrcI
    have hMs_eq : Ms = MF :=
      theorem_8_12_msChoiceSource_eq_mf_of_typeI hMs hSrcI
    rcases hBranch with ⟨U1, U0, hF, _hAlt⟩
    rcases hF with
      ⟨_hsolv, _hodd, _hMFsrc, _hMFpos, _hMFlt, _hUne, hcomp, _hU1le,
        _hU1comm, _hU1norm, _hCent, _hU0le, _hExp, _hFrob⟩
    rcases section16_typeI_KUData_of_complement
        (G := G) hM hMF hType hcomp with
      ⟨hKU, hMF_eq⟩
    have hSet :
        A \ A1 = section16ASet M U \ (section10Msigma M : Set G) :=
      theorem_8_12_source_diff_eq_ASet_diff_msigma_of_complement
        (G := G) (M := M) (D := M) (MF := MF) (U := U)
        (A := A) (A1 := A1) le_rfl hMF hMF_eq hcomp hA hA1'
    have hcopSigma :
        Nat.Coprime (orderOf x) (Nat.card (section10Msigma M)) := by
      simpa [hMs_eq, hMF_eq] using hcop
    exact section16_ASet_diff_msigma_unique_centralizer_of_coprime_public
      (G := G) (M := M) (K := (⊥ : Subgroup G)) (U := U)
      hM hKU (by simpa [hSet] using hx) hcopSigma
  · rcases hTypeII with ⟨hBranch, hA, hA1'⟩
    have hSrcII : typeIIDefinitionData M MF :=
      theorem_8_12_typeII_data_of_source_branch hBranch
    have hMs_eq : Ms = MF :=
      theorem_8_12_msChoiceSource_eq_mf_of_typeII hMs hSrcII
    rcases theorem_8_12_typeII_canonical_conjugate_of_source
        (G := G) (M := M) (MF := MF) (U := U) (Ms := Ms)
        hM hMF hMs hBranch with
      ⟨K, Uc, _d, hKU, _hB, hMF_eq, hCompCanonical, _hUconj⟩
    rcases hBranch with ⟨W1, W2, U1, U0, hP, _hCond, _hComm, _hNorm, _hF⟩
    rcases hP with
      ⟨_hMFsrc, _hW1cyc, _hW1ne, _hW1Hall, _hW1Comp, _hUleD, _hUnil,
        _hW1norm, hCompU, _hMFnotCyc, _hSecondLe, _hFittingEq,
        _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hHatW⟩
    have hDleM : ambientDerivedSubgroup M ≤ M :=
      section12_ambientDerivedSubgroup_le (G := G) (E := M)
    have hSetSource :
        A \ A1 = section16ASet M U \ (section10Msigma M : Set G) :=
      theorem_8_12_source_diff_eq_ASet_diff_msigma_of_complement
        (G := G) (M := M) (D := ambientDerivedSubgroup M) (MF := MF) (U := U)
        (A := A) (A1 := A1) hDleM hMF hMF_eq hCompU hA hA1'
    have hASetEq : section16ASet M U = section16ASet M Uc :=
      theorem_8_12_ASet_eq_of_complements
        (G := G) (M := M) (D := ambientDerivedSubgroup M) (MF := MF)
        (U := U) (V := Uc) hDleM hMF hMF_eq hCompU hCompCanonical
    have hSet :
        A \ A1 = section16ASet M Uc \ (section10Msigma M : Set G) := by
      simpa [hASetEq] using hSetSource
    have hcopSigma :
        Nat.Coprime (orderOf x) (Nat.card (section10Msigma M)) := by
      simpa [hMs_eq, hMF_eq] using hcop
    exact section16_ASet_diff_msigma_unique_centralizer_of_coprime_public
      (G := G) (M := M) (K := K) (U := Uc)
      hM hKU (by simpa [hSet] using hx) hcopSigma

public theorem theorem_8_12
    {G : Type u} [Group G] [Finite G]
    (M MF U Ms : Subgroup G)
    (A A0 A1 : Set G) :
    theorem_8_12_statement M MF U Ms A A0 A1 := by
  intro hG hSrc
  haveI : IsMinCE G := hG
  rcases hSrc with ⟨hNotation, hCases⟩
  rcases hNotation with ⟨hM, hMF, hMs, _hA1, _hNotationCase⟩
  rcases hCases with hTypeI | hTypeII
  · rcases hTypeI with ⟨hBranch, hA, hA1'⟩
    exact theorem_8_12_typeI_conclusion_of_source
      (G := G) (M := M) (MF := MF) (U := U) (Ms := Ms)
      (A := A) (A1 := A1) hM hMF hMs hBranch hA hA1'
  · rcases hTypeII with ⟨hBranch, hA, hA1'⟩
    exact theorem_8_12_typeII_conclusion_of_source
      (G := G) (M := M) (MF := MF) (U := U) (Ms := Ms)
      (A := A) (A1 := A1) hM hMF hMs hBranch hA hA1'

end CFSG.Section8
