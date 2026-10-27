module

public import CFSG.ClassicalInvolution.Phan.PhanDn.NodeEichler
public import CFSG.ClassicalInvolution.Phan.PhanDn.MainA
public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinNodes
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.SpinMinusRootTorus
public import CFSG.LocalAnalysis.StandardType.GGRankOneSl2
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Witt
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryBasic
public import CFSG.LieType.Universal.Spin.Generation.Eichler
public import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
public import CFSG.RankThree.PartOne.CTP.PhanBridge
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SeitzGeneration.OuterSpPair
public import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
public import CFSG.LieType.SeitzGeneration.RootPairSp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.CTP.ExtPhan
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.CTP.SeitzSpOuter
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S11d.PSLDescent
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.StandardType

namespace PhanDNative

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.WeakCT CFSG.StandardType.RankOneXfer CFSG.LieType.Steinberg
  CFSG.StandardType.PsiDiagChar CFSG.Timmesfeld QuadraticMap

section Native

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

theorem map_rLong_sl2UpperUniSub {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    (sl2UpperUniSub F).map (rLong n b c hk) = (minusDatum n hirr).rootGroup (Pi.single k 1) := by
  ext g
  constructor
  · rintro ⟨A, ⟨x, rfl⟩, rfl⟩
    rw [← LevisExtras.tv01_eq_sl2Upper]
    exact rLong_upper hirr hk x
  · intro hg
    obtain ⟨x, rfl⟩ := rLong_param_upper hirr hk g hg
    exact ⟨tv 0 1 x, ⟨x, (LevisExtras.tv01_eq_sl2Upper x).symm⟩, rfl⟩

omit hirr in
theorem sl2Diag_eq_diagSL2 (a : Fˣ) : sl2Diag a = diagSL2 a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem rLong_sl2Diag_mem_ggTorus {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) (a : Fˣ) :
    rLong n b c hk (sl2Diag a) ∈ ggTorus (minusDatum n hirr) := by
  rw [sl2Diag_eq_diagSL2, rLong, ← HypFrame.longTorus_apply]
  refine ClassicalPosition.mem_ggTorus_minusDatum_of_frame_scalars hirr _
    (fun i s => a ^ longCoroot k ⟨k.val + 1, hk⟩ true false i s) (fun i s => ?_) (fun p => ?_)
  · have h := (minusFrame n b c).toHypFrame.spinAction_longTorus_vec (succ_ne_of_lt n hk) true
      false a i s
    simpa using h
  · have he : ∀ i, polar (quadMinus n F b c) (planeVec n p) (eVec n i) = 0 := fun i => by
      rw [polar_comm]
      exact polar_eVec_planeVec n b c i p
    have hf : ∀ i, polar (quadMinus n F b c) (planeVec n p) (fVec n i) = 0 := fun i => by
      rw [polar_comm]
      exact polar_fVec_planeVec n b c i p
    rw [HypFrame.spinAction_longTorus]
    simp [he, hf]

end Native

section Main

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.ClassicalInvolution.PhanDn
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.LieType.BorelTits

section Conj

variable {F₀ K : Type} [Field F₀] [Finite F₀] [Field K] [Finite K] [Algebra F₀ K] [CharP K 2]
  {f : ℕ} (E : QuadExt F₀ K (unitaryInvolution K 2 f)) {b c : F₀}
  (hirr : ∀ s : F₀, s ^ 2 + b * s + c ≠ 0)

theorem exists_conj_rLong_range_eq_stdNode {m : ℕ} (hm : 3 ≤ m) (ho : Odd (m + 1))
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (hF : Nat.card F₀ = 2 ^ f)
    (hk : (⟨0, by omega⟩ : Fin (m + 1 - 1)).val + 1 < m + 1 - 1) :
    ∃ v : spinGroup (quadMinus (m + 1) F₀ b c),
      (rLong (m + 1) b c hk).range.map (MulAut.conj v).toMonoidHom =
        (((stdFamilyΩ E m hm hK hq).map
          (omegaEquivSpinMinus E ho (by omega : 4 ≤ m + 1) hirr).toMonoidHom).ι
            (Fin.castSucc ⟨0, by omega⟩)).range := by
  let : CharP F₀ 2 := RingHom.charP (algebraMap F₀ K) (algebraMap F₀ K).injective 2
  have hn : 4 ≤ m + 1 := by omega
  have hspin := fun g => spinAction_omegaEquivSpinMinus_apply E ho hn hirr g
  have hinj : Function.Injective (spinAction (quadMinus (m + 1) F₀ b c)) :=
    RootCentOmega.spinAction_quadMinus_injective hirr
  obtain ⟨l, hl⟩ := E.isUnitary.trace_surj 1 (map_one _)
  have hpolI : ∀ x y, polar (quadMinus (m + 1) F₀ b c) (Qn.isometryEquivQuadMinus E ho hirr x)
      (Qn.isometryEquivQuadMinus E ho hirr y) = polar (Qn E (m + 1)) x y := fun x y => by
    simp only [polar, ← map_add, QuadraticMap.IsometryEquiv.map_app]
  let P₁ := nodeHypPair₁ E (⟨0, by omega⟩ : Fin m) hl
  let P₂ := nodeHypPair₂ E (⟨0, by omega⟩ : Fin m) hl
  have hP : P₁.Orth P₂ := nodeHypPair_orth E _ hl
  let I₀ := Qn.isometryEquivQuadMinus E ho hirr
  let T₁ : HypPair (quadMinus (m + 1) F₀ b c) :=
    ⟨I₀ P₁.e, I₀ P₁.f, by rw [I₀.map_app]; exact P₁.Q_e, by rw [I₀.map_app]; exact P₁.Q_f,
      by rw [hpolI]; exact P₁.polar_ef⟩
  let T₂ : HypPair (quadMinus (m + 1) F₀ b c) :=
    ⟨I₀ P₂.e, I₀ P₂.f, by rw [I₀.map_app]; exact P₂.Q_e, by rw [I₀.map_app]; exact P₂.Q_f,
      by rw [hpolI]; exact P₂.polar_ef⟩
  have hT : T₁.Orth T₂ :=
    ⟨(hpolI _ _).trans hP.ee, (hpolI _ _).trans hP.ef, (hpolI _ _).trans hP.fe,
      (hpolI _ _).trans hP.ff⟩
  let fp : Fin (m + 1 - 1) → HypPair (quadMinus (m + 1) F₀ b c) := fun i =>
    ⟨minusVec (m + 1) i true, minusVec (m + 1) i false, quadMinus_minusVec _ _ _ i true,
      quadMinus_minusVec _ _ _ i false, by rw [polar_minusVec_minusVec]; simp⟩
  have hfp : ∀ i j, i ≠ j → (fp i).Orth (fp j) := fun i j hij =>
    ⟨by rw [polar_minusVec_minusVec]; simp [hij], by rw [polar_minusVec_minusVec]; simp [hij],
      by rw [polar_minusVec_minusVec]; simp [hij], by rw [polar_minusVec_minusVec]; simp [hij]⟩
  have hQnd : (polarBilin (quadMinus (m + 1) F₀ b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite (m + 1) F₀ hirr
  obtain ⟨s, hsE, hs1e, hs1f, hs2e, hs2f⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2.exists_mem_elementaryGroup_two hQnd
      (S₁ := fp ⟨0, by omega⟩) (S₂ := fp ⟨1, by omega⟩) (S₃ := fp ⟨2, by omega⟩)
      (hfp _ _ (by simp [Fin.ext_iff])) (hfp _ _ (by simp [Fin.ext_iff]))
      (hfp _ _ (by simp [Fin.ext_iff])) hT
  have hsO := elementaryGroup_le_orthogonalGroup (quadMinus (m + 1) F₀ b c) hsE
  have hdim : 5 ≤ Module.finrank F₀ (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F₀) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  obtain ⟨v, hv⟩ := elementaryGroup_le_range_spinAction hQnd hdim hsE
  refine ⟨v, ?_⟩
  have hcoe : ∀ A, (((stdFamilyΩ E m hm hK hq).ι (Fin.castSucc ⟨0, by omega⟩) A :
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
        TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆) :
      (Fin (m + 1) → K) ≃ₗ[F₀] (Fin (m + 1) → K)) =
        stdChainIota (F := F₀) (f := f) m ⟨0, by omega⟩ A := fun A => by
    have h := DFunLike.congr_fun (coe_stdFamilyΩ_ι E m hm hK hq (Fin.castSucc ⟨0, by omega⟩)) A
    rw [stdFamilyV_ι_castSucc] at h
    exact h
  have hswap : ∀ {u w : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F₀},
      quadMinus (m + 1) F₀ b c u = 0 → quadMinus (m + 1) F₀ b c w = 0 →
        polar (quadMinus (m + 1) F₀ b c) u w = 0 → ∀ x : F₀,
          eichler (quadMinus (m + 1) F₀ b c) w (x • u) =
            eichler (quadMinus (m + 1) F₀ b c) u (x • w) := by
    intro u w hu hw huw x
    rw [← eichler_smul_left, CFSG.LieType.SeitzGeneration.OmegaF2.eichler_swap_char2 hu
      (by rw [QuadraticMap.map_smul, hw, smul_zero]) (by rw [polar_smul_right, huw, smul_zero])]
  have hgen : ∀ (x : F₀) (i j : Fin (m + 1 - 1)) (hij : i ≠ j) (a a' : Fin (m + 1) → K),
      s (minusVec (m + 1) i true) = I₀ a → s (minusVec (m + 1) j false) = I₀ a' →
      ∀ A : Su K 2 f 2, stdChainIota (F := F₀) (f := f) m ⟨0, by omega⟩ A =
        eichler (Qn E (m + 1)) a (x • a') →
      v * (minusFrame (m + 1) b c).longRoot hij true false (.ofAdd x) * v⁻¹ =
        omegaEquivSpinMinus E ho hn hirr ((stdFamilyΩ E m hm hK hq).ι
          (Fin.castSucc ⟨0, by omega⟩) A) := by
    intro x i j hij a a' hsa hsa' A hA
    apply hinj
    rw [map_mul, map_mul, map_inv, hv, hspin, hcoe, hA, HypFrame.spinAction_longRoot_eq_eichler]
    simp only [minusFrame_vec]
    rw [hswap (quadMinus_minusVec _ _ _ i true) (quadMinus_minusVec _ _ _ j false)
      (by rw [polar_minusVec_minusVec]; simp [hij]) x, eichler_conj hsO, map_smul, hsa, hsa']
    refine LinearEquiv.ext fun y => ?_
    have h := CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.eichler_isometry_apply
      I₀ a (x • a') (I₀.symm y)
    rw [map_smul, I₀.apply_symm_apply] at h
    rw [LinearEquiv.autCongr_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    exact h.symm
  have hle : (rLong (m + 1) b c hk).range.map (MulAut.conj v).toMonoidHom ≤
      (((stdFamilyΩ E m hm hK hq).map (omegaEquivSpinMinus E ho hn hirr).toMonoidHom).ι
        (Fin.castSucc ⟨0, by omega⟩)).range := by
    rw [MonoidHom.range_eq_map, ← closure_sl2Upper_sl2Lower_eq_top (k := F₀), MonoidHom.map_closure,
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    rcases hg with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · obtain ⟨A, hA⟩ := exists_stdChainIota_eq_eichler_upper E (⟨0, by omega⟩ : Fin m) hl x
      refine ⟨A, ?_⟩
      rw [PhanFamilyE.map_ι, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← LevisExtras.tv01_eq_sl2Upper, rLong_tv01]
      exact (hgen x _ _ _ _ _ hs1e hs2f A hA).symm
    · obtain ⟨A, hA⟩ := exists_stdChainIota_eq_eichler_lower E (⟨0, by omega⟩ : Fin m) hl x
      refine ⟨A, ?_⟩
      rw [PhanFamilyE.map_ι, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← LevisExtras.tv10_eq_sl2Lower, rLong_tv10]
      exact (hgen x _ _ _ _ _ hs2e hs1f A hA).symm
  have hιinj : Function.Injective (((stdFamilyΩ E m hm hK hq).map
      (omegaEquivSpinMinus E ho hn hirr).toMonoidHom).ι (Fin.castSucc ⟨0, by omega⟩)) := by
    rw [PhanFamilyE.map_ι]
    refine (omegaEquivSpinMinus E ho hn hirr).injective.comp fun a a' haa' => ?_
    apply stdFamilyV_inj E hm (Fin.castSucc ⟨0, by omega⟩)
    rw [← DFunLike.congr_fun (coe_stdFamilyΩ_ι E m hm hK hq (Fin.castSucc ⟨0, by omega⟩)) a,
      ← DFunLike.congr_fun (coe_stdFamilyΩ_ι E m hm hK hq (Fin.castSucc ⟨0, by omega⟩)) a',
      MonoidHom.comp_apply, MonoidHom.comp_apply, haa']
  obtain ⟨φ⟩ := CFSG.RankThree.PartOne.CTP.exists_suid_two_equiv_sl hK hF
  have : Finite (Su K 2 f 2) := Finite.of_equiv _ φ.toEquiv.symm
  have : Finite (((stdFamilyΩ E m hm hK hq).map
      (omegaEquivSpinMinus E ho hn hirr).toMonoidHom).ι (Fin.castSucc ⟨0, by omega⟩)).range :=
    Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj v).injective,
    ← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective (rLong_injective hk)).toEquiv]
  exact (Nat.card_congr φ.toEquiv).le

end Conj

theorem exists_nativeNode_POmegaMinus {m f : ℕ} (hm : 4 ≤ m) (ho : Odd m) (hq : 4 ≤ 2 ^ f)
    (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∃ T : PhanFamilyE K 2 f (ggCoxeterMatrixD m) (ggU .POmegaMinus m f).K, T.IsUniversal ∧
      ∃ (k₀ : Fin m) (γ : Fin (ggU .POmegaMinus m f).D.rank → ℤ)
        (phi : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* (ggU .POmegaMinus m f).K),
        Function.Injective phi ∧ γ ∈ (ggU .POmegaMinus m f).D.roots ∧
        (sl2UpperUniSub (GaloisField 2 f)).map phi = (ggU .POmegaMinus m f).D.rootGroup γ ∧
        (∀ a : (GaloisField 2 f)ˣ, phi (sl2Diag a) ∈ ggTorus (ggU .POmegaMinus m f).D) ∧
        ∃ v : (ggU .POmegaMinus m f).K,
          phi.range.map (MulAut.conj v).toMonoidHom = (T.ι k₀).range := by
  have hf : f ≠ 0 := by
    rintro rfl
    norm_num at hq
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  let : Algebra (GaloisField 2 f) K := Classical.choice (Aniso.nonempty_algebra hF hK)
  let E := quadExt_of_card_of_char_two (F := GaloisField 2 f) f hF hK
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hm' : 3 ≤ m' := by omega
  have hirr : ∀ s : GaloisField 2 f, s ^ 2 + (minusCoeffs 2 f).1 * s + (minusCoeffs 2 f).2 ≠ 0 :=
    minusCoeffs_irr 2 f
  have hU : (stdFamilyΩ E m' hm' hK hq).IsUniversal :=
    isUniversal_stdFamilyΩ_of_dChamberSystem E hm' hK hq (stdFamilyΩ_good E m' hm' hK hq)
      (dChamberSystemConnected_holds K f hK hq m' hm')
      (dChamberSystemSimplyTwoConnected_holds K f hK hq m' hm')
  have hk : (⟨0, by omega⟩ : Fin (m' + 1 - 1)).val + 1 < m' + 1 - 1 := by
    change 0 + 1 < m' + 1 - 1
    omega
  exact ⟨_, hU.map (omegaEquivSpinMinus E ho hm hirr), Fin.castSucc ⟨0, by omega⟩,
    (Pi.single (⟨0, by omega⟩ : Fin (m' + 1 - 1)) 1 : Fin (m' + 1 - 1) → ℤ),
    rLong (m' + 1) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hk, rLong_injective hk,
    (isCTRootSystem (minusDatum (m' + 1) hirr).isFiniteType
      (minusDatum (m' + 1) hirr).divisible).single_mem _,
    map_rLong_sl2UpperUniSub hirr hk, rLong_sl2Diag_mem_ggTorus hirr hk,
    exists_conj_rLong_range_eq_stdNode E hirr hm' ho hK hq hF hk⟩

end Main

end PhanDNative

end CFSG.StandardType

end
