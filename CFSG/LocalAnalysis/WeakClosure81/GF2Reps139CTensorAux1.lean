module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Basic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139B
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenOmega4UniqueAbstract
public import CFSG.Quasithin.Vol2.KGNatComm
public import CFSG.Quasithin.Background.B1Coprime
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
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13Stmts4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoLem
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
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
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

theorem w1369_no_L3_of_order3 (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)} (hK : IsComponentOf K G)
    (hIrr : commSub ⊤ K ∈ irrSet K)
    (hBNat : BinaryNaturalSL K (commSub ⊤ K) (commSub ⊤ K ⊓ fixV K) 3 1)
    {x : MulAut W} (hxgen : X = Subgroup.zpowers x) (hx3 : x ^ 3 = 1)
    (hfixX : fixV X = ⊥) : False := by
  have hxmem : x ∈ X := hxgen ▸ Subgroup.mem_zpowers x
  have hxK : ∀ k ∈ K, k * x = x * k := fun k hk =>
    Std139.component_commutes_X S hK k hk x hxmem
  have hxne : x ≠ 1 := by
    intro h1
    have hXbot : X = ⊥ := by rw [hxgen, h1, Subgroup.zpowers_one_eq_bot]
    have h3 := S.Xcard
    rw [hXbot, Subgroup.card_bot] at h3
    omega
  let I : Subgroup W := commSub ⊤ K
  let C : Subgroup W := I ⊓ fixV K
  have hIcomm : commSub I K = I := hIrr.1
  have hIirr : IsIrrOn K I C := hIrr.2
  have hIne : I ≠ ⊥ := by
    intro h0
    have h1 : C = ⊥ := by simp [C, h0]
    rw [h0, h1] at hIirr
    exact (lt_irrefl (⊥ : Subgroup W)) hIirr.1
  have hcommY : ∀ y ∈ K, ∀ b ∈ Subgroup.zpowers x, y * b = b * y := by
    intro y hy b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute y x from hxK y hy) i).eq
  have hxIstable : StableUnder (Subgroup.zpowers x) I :=
    CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := K) (B := Subgroup.zpowers x) (M := ⊤)
      hcommY (fun _ _ _ _ => Subgroup.mem_top _)
  have hxI : ∀ u ∈ I, x u ∈ I := fun u hu => hxIstable x (Subgroup.mem_zpowers x) u hu
  have hxIinv : ∀ u ∈ I, x⁻¹ u ∈ I := inv_mem_of_forall_mem x hxI
  have hxC : ∀ u ∈ C, x u ∈ C := by
    intro u hu
    refine ⟨hxI u hu.1, ?_⟩
    have hu2 : ∀ k ∈ K, k u = u := mem_fixV.mp hu.2
    refine mem_fixV.mpr ?_
    intro k hk
    have h1 : k (x u) = x (k u) := congrArg (fun f : MulAut W => f u) (hxK k hk)
    rw [hu2 k hk] at h1
    exact h1
  obtain ⟨E, hEfield, hEfin, hEcard, π, hπ⟩ := hBNat
  letI : Field E := hEfield
  letI : Finite E := hEfin
  obtain ⟨f, hfadd, hfker, hfsurj, hfe⟩ :=
    CFSG.Quasithin.Vol2.KGNat.exists_coord
      (CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL 3 E)) hπ
  have hπUinv : ∀ y : ↥K, ∀ u ∈ I, (y : MulAut W) u ∈ I := hπ.2.2.2.1
  have hf1 : f 1 = 0 := by
    have h := hfadd 1 I.one_mem 1 I.one_mem
    rw [mul_one] at h
    exact (add_left_cancel (show f 1 + 0 = f 1 + f 1 by rw [add_zero]; exact h)).symm
  have hfinv : ∀ u ∈ I, f u⁻¹ = - f u := by
    intro u hu
    have h := hfadd u hu u⁻¹ (I.inv_mem hu)
    rw [mul_inv_cancel, hf1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hwd : ∀ u ∈ I, ∀ v ∈ I, f u = f v → f (x u) = f (x v) := by
    intro u hu v hv huv
    have h1 : f (u * v⁻¹) = 0 := by
      rw [hfadd u hu v⁻¹ (I.inv_mem hv), hfinv v hv, huv, add_neg_cancel]
    have h2 : u * v⁻¹ ∈ C := (hfker (u * v⁻¹) (I.mul_mem hu (I.inv_mem hv))).mp h1
    have h3 : x (u * v⁻¹) ∈ C := hxC (u * v⁻¹) h2
    have h4 : f (x (u * v⁻¹)) = 0 :=
      (hfker (x (u * v⁻¹)) (hxI (u * v⁻¹) (I.mul_mem hu (I.inv_mem hv)))).mpr h3
    rw [map_mul, map_inv] at h4
    have h5 : f (x u * (x v)⁻¹) = f (x u) + f ((x v)⁻¹) :=
      hfadd (x u) (hxI u hu) ((x v)⁻¹) (I.inv_mem (hxI v hv))
    rw [h5, hfinv (x v) (hxI v hv)] at h4
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h4)
  let Tx : (Fin 3 → E) →+ (Fin 3 → E) :=
    { toFun := fun y => f (x (Classical.choose (hfsurj y)))
      map_zero' := by
        have h0 : f (Classical.choose (hfsurj 0)) = 0 := (Classical.choose_spec (hfsurj 0)).2
        have h0' : f (x (Classical.choose (hfsurj 0))) = f (x 1) :=
          hwd _ (Classical.choose_spec (hfsurj 0)).1 1 I.one_mem (by rw [h0, hf1])
        rw [h0', map_one, hf1]
      map_add' := by
        intro y y'
        have hy : f (Classical.choose (hfsurj y)) = y := (Classical.choose_spec (hfsurj y)).2
        have hy' : f (Classical.choose (hfsurj y')) = y' := (Classical.choose_spec (hfsurj y')).2
        have hsum : f (Classical.choose (hfsurj (y + y'))) = y + y' :=
          (Classical.choose_spec (hfsurj (y + y'))).2
        have hsum' : f (Classical.choose (hfsurj y) * Classical.choose (hfsurj y')) = y + y' := by
          rw [hfadd _ (Classical.choose_spec (hfsurj y)).1 _
            (Classical.choose_spec (hfsurj y')).1, hy, hy']
        have hkey := hwd _ (Classical.choose_spec (hfsurj (y + y'))).1 _
          (I.mul_mem (Classical.choose_spec (hfsurj y)).1
            (Classical.choose_spec (hfsurj y')).1) (by rw [hsum, hsum'])
        rw [hkey, map_mul, hfadd _ (hxI _ (Classical.choose_spec (hfsurj y)).1) _
          (hxI _ (Classical.choose_spec (hfsurj y')).1)] }
  have hTcomm : ∀ (γ : ↥(StatedSL 3 E)) (y : Fin 3 → E),
      Tx ((CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL 3 E)).lin γ y) =
        (CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL 3 E)).lin γ (Tx y) := by
    intro γ y
    set u : W := Classical.choose (hfsurj y) with hu
    have huI : u ∈ I := (Classical.choose_spec (hfsurj y)).1
    have hfu : f u = y := (Classical.choose_spec (hfsurj y)).2
    have hπu : ((π γ : ↥K) : MulAut W) u ∈ I := hπUinv (π γ) u huI
    have hxπ : x * ((π γ : ↥K) : MulAut W) = ((π γ : ↥K) : MulAut W) * x :=
      (hxK (π γ) (π γ).2).symm
    have h1 : (CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL 3 E)).lin γ y =
        f (((π γ : ↥K) : MulAut W) u) := by
      rw [← hfu, hfe γ u huI]
    have h2 : Tx ((CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL 3 E)).lin γ y) =
        f (x (((π γ : ↥K) : MulAut W) u)) := by
      rw [h1]
      change f (x (Classical.choose (hfsurj (f (((π γ : ↥K) : MulAut W) u))))) =
        f (x (((π γ : ↥K) : MulAut W) u))
      exact hwd _ (Classical.choose_spec (hfsurj (f (((π γ : ↥K) : MulAut W) u)))).1 _
        hπu (Classical.choose_spec (hfsurj (f (((π γ : ↥K) : MulAut W) u)))).2
    have h3 : (CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL 3 E)).lin γ (Tx y) =
        f (((π γ : ↥K) : MulAut W) (x u)) := by
      change (CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL 3 E)).lin γ
        (f (x (Classical.choose (hfsurj y)))) = f (((π γ : ↥K) : MulAut W) (x u))
      rw [show f (x (Classical.choose (hfsurj y))) = f (x u) from
        hwd _ (Classical.choose_spec (hfsurj y)).1 u huI
          ((Classical.choose_spec (hfsurj y)).2.trans hfu.symm)]
      exact (hfe γ (x u) (hxI u huI)).symm
    rw [h2, h3]
    exact congrArg (fun g : MulAut W => f (g u)) hxπ
  obtain ⟨c, hc⟩ := CFSG.Quasithin.Vol2.KGNat.commutant_statedSL (n := 3) (by norm_num) Tx hTcomm
  have hc3 : c ^ 3 = 1 := by
    have hTx3 : ∀ y : Fin 3 → E, Tx (Tx (Tx y)) = y := by
      intro y
      have h1 : Tx y = f (x (Classical.choose (hfsurj y))) := rfl
      have h2 : Tx (Tx y) = f (x (x (Classical.choose (hfsurj y)))) := by
        rw [h1]
        change f (x (Classical.choose (hfsurj (f (x (Classical.choose (hfsurj y))))))) =
          f (x (x (Classical.choose (hfsurj y))))
        exact hwd _ (Classical.choose_spec (hfsurj (f (x (Classical.choose (hfsurj y)))))).1 _
          (hxI _ (Classical.choose_spec (hfsurj y)).1)
          (Classical.choose_spec (hfsurj (f (x (Classical.choose (hfsurj y)))))).2
      have h3 : Tx (Tx (Tx y)) = f (x (x (x (Classical.choose (hfsurj y))))) := by
        rw [h2]
        change f (x (Classical.choose (hfsurj (f (x (x (Classical.choose (hfsurj y)))))))) =
          f (x (x (x (Classical.choose (hfsurj y)))))
        exact hwd _ (Classical.choose_spec
          (hfsurj (f (x (x (Classical.choose (hfsurj y))))))).1 _
          (hxI _ (hxI _ (Classical.choose_spec (hfsurj y)).1))
          (Classical.choose_spec (hfsurj (f (x (x (Classical.choose (hfsurj y))))))).2
      have h4 : x (x (x (Classical.choose (hfsurj y)))) = Classical.choose (hfsurj y) := by
        have h := congrArg (fun g : MulAut W => g (Classical.choose (hfsurj y))) hx3
        simpa [pow_succ, pow_two, MulAut.mul_apply] using h
      rw [h3, h4]
      exact (Classical.choose_spec (hfsurj y)).2
    have h5 : c • (c • (c • (1 : Fin 3 → E))) = 1 := by
      calc c • (c • (c • (1 : Fin 3 → E)))
          = c • (c • (Tx 1)) := by rw [← hc 1]
        _ = c • (Tx (Tx 1)) := by rw [← hc (Tx 1)]
        _ = Tx (Tx (Tx 1)) := by rw [← hc (Tx (Tx 1))]
        _ = 1 := hTx3 1
    have h6 : c ^ 3 • (1 : Fin 3 → E) = 1 := by
      rw [show c ^ 3 = c * c * c by ring, mul_smul, mul_smul]
      exact h5
    have h7 := congrFun h6 0
    simpa using h7
  have hc1 : c = 1 := by
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0] at hc3
      norm_num at hc3
    haveI : Fintype E := Fintype.ofFinite E
    have h := FiniteField.pow_card_sub_one_eq_one c hc0
    have hcard : Fintype.card E = 2 := by
      rw [← Nat.card_eq_fintype_card, hEcard]; norm_num
    rw [hcard] at h
    norm_num at h
    exact h
  have hTxid : ∀ y : Fin 3 → E, Tx y = y := fun y => by rw [hc y, hc1, one_smul]
  have hxfixI : ∀ u ∈ I, f (x u) = f u := by
    intro u hu
    have h : Tx (f u) = f u := hTxid (f u)
    have h1 : Tx (f u) = f (x (Classical.choose (hfsurj (f u)))) := rfl
    rw [h1] at h
    have h2 : f (x (Classical.choose (hfsurj (f u)))) = f (x u) :=
      hwd _ (Classical.choose_spec (hfsurj (f u))).1 u hu
        (Classical.choose_spec (hfsurj (f u))).2
    rw [h2] at h
    exact h
  have hgen : ∀ u ∈ I, x u * u⁻¹ ∈ C := by
    intro u hu
    refine (hfker (x u * u⁻¹) (I.mul_mem (hxI u hu) (I.inv_mem hu))).mp ?_
    rw [hfadd (x u) (hxI u hu) u⁻¹ (I.inv_mem hu), hfinv u hu, hxfixI u hu, add_neg_cancel]
  have hsub_le : commSub I (Subgroup.zpowers x) ≤ C := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨y, hy, u, hu, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hPm : ∀ a : MulAut W,
        ((∀ u ∈ I, a u ∈ I) ∧ (∀ u ∈ I, a u * u⁻¹ ∈ C)) →
        ((∀ u ∈ I, (x * a) u ∈ I) ∧ (∀ u ∈ I, (x * a) u * u⁻¹ ∈ C)) := by
      intro a ha
      refine ⟨?_, ?_⟩
      · intro u hu
        rw [MulAut.mul_apply]
        exact hxI (a u) (ha.1 u hu)
      · intro u hu
        rw [MulAut.mul_apply]
        have h1 : x (a u) * (a u)⁻¹ ∈ C := hgen (a u) (ha.1 u hu)
        have h2 : a u * u⁻¹ ∈ C := ha.2 u hu
        have h3 : x (a u) * u⁻¹ = (x (a u) * (a u)⁻¹) * (a u * u⁻¹) := by group
        rw [h3]
        exact C.mul_mem h1 h2
    have hPi : ∀ a : MulAut W,
        ((∀ u ∈ I, a u ∈ I) ∧ (∀ u ∈ I, a u * u⁻¹ ∈ C)) →
        ((∀ u ∈ I, (x⁻¹ * a) u ∈ I) ∧ (∀ u ∈ I, (x⁻¹ * a) u * u⁻¹ ∈ C)) := by
      intro a ha
      have hx2 : x⁻¹ = x ^ 2 := by
        have h : x ^ 2 * x = 1 := by
          calc x ^ 2 * x = x ^ 3 := by group
            _ = 1 := hx3
        exact (mul_eq_one_iff_eq_inv.mp h).symm
      have hxa : x⁻¹ * a = x * (x * a) := by
        rw [hx2, pow_two, mul_assoc]
      rw [hxa]
      exact hPm _ (hPm _ ha)
    have hPall : (∀ u ∈ I, (x ^ k) u ∈ I) ∧ (∀ u ∈ I, (x ^ k) u * u⁻¹ ∈ C) :=
      zpow_induction_left (g := x)
        (P := fun a => (∀ u ∈ I, a u ∈ I) ∧ (∀ u ∈ I, a u * u⁻¹ ∈ C))
        ⟨fun u hu => by simpa using hu, fun u hu => by simpa [C.one_mem] using hu⟩
        hPm hPi k
    exact hPall.2 u hu
  have hxodd : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hxne]
    norm_num
  have hcop := CFSG.Quasithin.B1.coprime_decomp hw2 hxodd hxIstable
  have hfixbot : I ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
    rw [show fixV (Subgroup.zpowers x) = fixV X from by rw [hxgen], hfixX]
    simp
  have hIleC : I ≤ C := by
    rw [← hcop.1, hfixbot, bot_sup_eq]
    exact hsub_le
  have hIlefix : I ≤ fixV K := hIleC.trans inf_le_right
  have hfinal : I = ⊥ := by
    have hle : commSub I K ≤ commSub (fixV K) K := commSub_mono hIlefix le_rfl
    rw [hIcomm] at hle
    have hbot : commSub (fixV K) K = ⊥ :=
      commSub_eq_bot_iff.mpr le_rfl
    rw [hbot] at hle
    exact le_bot_iff.mp hle
  exact hIne hfinal

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
