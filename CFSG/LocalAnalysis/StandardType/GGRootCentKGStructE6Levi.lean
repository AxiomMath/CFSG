module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
import CFSG.LocalAnalysis.SeitzReduction.EPilotToral
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoExcStep
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSpCent
import CFSG.LieType.Chevalley.ParabolicRadicalPointwiseRigidity
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.KGE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.E6Pilot CFSG.SeitzReduction.EPilot CFSG.StandardType.InnerDiagA
  CFSG.Timmesfeld.LieEmbed CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint Matrix

variable {K : Type} [Field K]

private theorem conjSL_mul {m : ℕ} {F : Type} [Field F] (A₁ A₂ : GL (Fin (m + 1)) F)
    (B : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (A₁ * A₂) B = InnerDiagA.conjSL A₁ (InnerDiagA.conjSL A₂ B) := by
  apply Subtype.ext
  rw [InnerDiagA.coe_conjSL, InnerDiagA.coe_conjSL, InnerDiagA.coe_conjSL]
  rw [_root_.mul_inv_rev, Units.val_mul]
  simp only [Units.val_mul, Matrix.mul_assoc]

private theorem conjSL_toGL_mul {m : ℕ} {F : Type} [Field F]
    (B₀ Y : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (Matrix.SpecialLinearGroup.toGL B₀) Y = B₀ * Y * B₀⁻¹ := by
  apply Subtype.ext
  rw [InnerDiagA.coe_conjSL]
  rfl

theorem exists_gl_rootDiagAutHom_slToAdjointE6 [Finite K] [CharP K 2]
    (a : Fin Tag.E6.rank → Kˣ) :
    ∃ A : GL (Fin 6) K, ∀ B : Matrix.SpecialLinearGroup (Fin 6) K,
      rootDiagAutHom .E6 K a (slToAdjointE6 K B) = slToAdjointE6 K (InnerDiagA.conjSL A B) := by
  classical
  have h00 : a5Root (0 : Fin 6) 0 = 0 := by
    funext m
    simp [a5Root]
  have hinv : ∀ j : Fin 6, rootChar a (a5Root 0 j) = (rootChar a (a5Root j 0))⁻¹ := by
    intro j
    have hsum : a5Root (0 : Fin 6) j + a5Root j 0 = 0 := by
      rw [← h00]
      exact a5Root_add_check 0 j 0
    have h : rootChar a (a5Root 0 j) * rootChar a (a5Root j 0) = 1 := by
      rw [← rootChar_add, hsum, rootChar_zero]
    exact eq_inv_of_mul_eq_one_left h
  set tau : Fin 6 → Kˣ := fun i => rootChar a (a5Root i 0) with htau
  have hkey : ∀ i j : Fin 6, tau i * (tau j)⁻¹ = rootChar a (a5Root i j) := by
    intro i j
    show rootChar a (a5Root i 0) * (rootChar a (a5Root j 0))⁻¹ = rootChar a (a5Root i j)
    rw [← hinv j, ← rootChar_add, a5Root_add_check i 0 j]
  refine ⟨InnerDiagA.diagGL tau, fun B => ?_⟩
  have hmain :
      (rootDiagAutHom .E6 K a).toMonoidHom.comp (slToAdjointE6 K) =
        (slToAdjointE6 K).comp (InnerDiagA.conjSL (InnerDiagA.diagGL tau)) := by
    refine MonoidHom.eq_of_eqOn_dense
      Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field ?_
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    refine Subtype.ext ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    change ((rootDiagAut .E6 K a)
        (slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection hij c)) : ModGL .E6 K) =
      ((slToAdjointE6 K (InnerDiagA.conjSL (InnerDiagA.diagGL tau)
        (Matrix.SpecialLinearGroup.transvection hij c)) : adjointGroup .E6 K) : ModGL .E6 K)
    rw [coe_rootDiagAut, coe_slToAdjointE6_transvection hij c,
      InnerDiagA.conjSL_diagGL_transvection tau hij c, coe_slToAdjointE6_transvection hij]
    rw [rootDiagUnit_conj_pinnedX a (isRoot_a5Root hij) c]
    congr 1
    rw [← hkey i j, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  exact congrArg (fun f : Matrix.SpecialLinearGroup (Fin 6) K →* adjointGroup .E6 K => f B) hmain

theorem rootDiagAutHom_mem_a5Levi (a : Fin Tag.E6.rank → Kˣ) {k : adjointGroup .E6 K}
    (hk : k ∈ a5Levi K) : rootDiagAutHom .E6 K a k ∈ a5Levi K := by
  rw [mem_a5Levi_iff] at hk ⊢
  have hcoe : ((rootDiagAutHom .E6 K a k : adjointGroup .E6 K) : ModGL .E6 K) =
      (MulAut.conj (rootDiagUnit .E6 a)) (k : ModGL .E6 K) := by
    rw [MulAut.conj_apply]
    exact coe_rootDiagAut a k
  rw [hcoe]
  have hmap : (rootSpan .E6 K a5LeviRoots).map (MulAut.conj (rootDiagUnit .E6 a)).toMonoidHom
      = rootSpan .E6 K a5LeviRoots :=
    map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup a hα.1
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj (rootDiagUnit .E6 a)).toMonoidHom hk
  rwa [hmap] at hmem

private theorem exists_sq_inv_rootChar [Finite K] [CharP K 2]
    (a : Fin Tag.E6.rank → Kˣ) :
    ∃ l : Kˣ, l ^ 2 = (rootChar a (highRoot .E6))⁻¹ := by
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (F := K) (ringChar.eq K 2)
    (((rootChar a (highRoot .E6))⁻¹ : Kˣ) : K)
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : (((rootChar a (highRoot .E6))⁻¹ : Kˣ) : K) = 0 := by rw [hb, mul_zero]
    exact Units.ne_zero _ h0
  exact ⟨Units.mk0 b hb0, Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, pow_two, hb])⟩

private theorem rootDiagAutHom_fixes_pinnedElt (ap : Fin Tag.E6.rank → Kˣ)
    (hθ : rootChar ap (highRoot .E6) = 1) :
    rootDiagAutHom .E6 K ap (EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) =
      EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) := by
  have h := rootDiagUnit_conj_pinnedX (τ := .E6) ap (isRoot_highRoot .E6) (1 : K)
  rw [hθ, Units.val_one, one_mul] at h
  refine Subtype.ext ?_
  change ((rootDiagAut .E6 K ap)
    (EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) : ModGL .E6 K) =
      pinnedX .E6 K (highRoot .E6) 1
  rw [coe_rootDiagAut]
  exact h

private theorem rootDiagAutHom_mul_highDiag (a : Fin Tag.E6.rank → Kˣ) (lam : Kˣ)
    (t : adjointGroup .E6 K)
    (ht : (t : ModGL .E6 K) = rootDiagUnit .E6 (EPilot.highDiag .E6 lam)) :
    rootDiagAutHom .E6 K (a * EPilot.highDiag .E6 lam) =
      MulAut.conj t * rootDiagAutHom .E6 K a := by
  refine MulEquiv.ext fun k => Subtype.ext ?_
  change ((rootDiagAut .E6 K (a * EPilot.highDiag .E6 lam)) k : ModGL .E6 K) =
    ((MulAut.conj t * rootDiagAut .E6 K a) k : ModGL .E6 K)
  rw [coe_rootDiagAut, MulAut.mul_apply, MulAut.conj_apply]
  change rootDiagUnit .E6 (a * EPilot.highDiag .E6 lam) * (k : ModGL .E6 K) *
      (rootDiagUnit .E6 (a * EPilot.highDiag .E6 lam))⁻¹ =
    (t : ModGL .E6 K) * ((rootDiagAut .E6 K a) k : ModGL .E6 K) * (t : ModGL .E6 K)⁻¹
  rw [coe_rootDiagAut, ht, rootDiagUnit_mul]
  have hcomm : rootDiagUnit .E6 a * rootDiagUnit .E6 (EPilot.highDiag .E6 lam) =
      rootDiagUnit .E6 (EPilot.highDiag .E6 lam) * rootDiagUnit .E6 a := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  rw [hcomm]
  group

private theorem pCoreOf_map_eq_self (F : MulAut (adjointGroup .E6 K))
    (hpCore : CFSG.Open.pCoreOf 2 (Subgroup.centralizer
      ({EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)} : Set (adjointGroup .E6 K))) =
      EPilot.highRadical .E6 K)
    (hfx : F (EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) =
      EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) :
    (EPilot.highRadical .E6 K).map F.toMonoidHom = EPilot.highRadical .E6 K := by
  have hpc := KGSp.pCoreOf_range_inf_centralizer (ψ := F.toMonoidHom) (MulEquiv.injective F)
    (EPilot.pinnedElt .E6 (highRoot .E6) (1 : K))
  rw [MonoidHom.range_eq_top_of_surjective _ (MulEquiv.surjective F),
    show F.toMonoidHom (EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) =
      EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) from hfx,
    top_inf_eq, hpCore] at hpc
  exact hpc.symm

private noncomputable def leviConjAut (l₀ : adjointGroup .E6 K) (hl₀ : l₀ ∈ a5Levi K)
    (ap apinv : Fin Tag.E6.rank → Kˣ) (hapinv : apinv = ap⁻¹) :
    MulAut ↥(a5Levi K) := by
  have hinv1 : rootDiagAutHom .E6 K apinv * rootDiagAutHom .E6 K ap =
      (1 : MulAut (adjointGroup .E6 K)) := by rw [← map_mul, hapinv, inv_mul_cancel, map_one]
  have hinv2 : rootDiagAutHom .E6 K ap * rootDiagAutHom .E6 K apinv =
      (1 : MulAut (adjointGroup .E6 K)) := by rw [← map_mul, hapinv, mul_inv_cancel, map_one]
  have hdd : ∀ x : adjointGroup .E6 K,
      rootDiagAutHom .E6 K apinv (rootDiagAutHom .E6 K ap x) = x := by
    intro x
    calc rootDiagAutHom .E6 K apinv (rootDiagAutHom .E6 K ap x)
        = (rootDiagAutHom .E6 K apinv * rootDiagAutHom .E6 K ap) x :=
          (MulAut.mul_apply _ _ _ _).symm
      _ = x := by rw [hinv1, MulAut.one_apply]
  have hdd' : ∀ x : adjointGroup .E6 K,
      rootDiagAutHom .E6 K ap (rootDiagAutHom .E6 K apinv x) = x := by
    intro x
    calc rootDiagAutHom .E6 K ap (rootDiagAutHom .E6 K apinv x)
        = (rootDiagAutHom .E6 K ap * rootDiagAutHom .E6 K apinv) x :=
          (MulAut.mul_apply _ _ _ _).symm
      _ = x := by rw [hinv2, MulAut.one_apply]
  exact
    { toFun := fun l => ⟨l₀ * rootDiagAutHom .E6 K ap (l : adjointGroup .E6 K) * l₀⁻¹,
        mul_mem (mul_mem hl₀ (rootDiagAutHom_mem_a5Levi ap l.2)) (inv_mem hl₀)⟩
      invFun := fun l => ⟨(rootDiagAutHom .E6 K apinv l₀)⁻¹ *
          rootDiagAutHom .E6 K apinv (l : adjointGroup .E6 K) *
          (rootDiagAutHom .E6 K apinv l₀),
        mul_mem (mul_mem (inv_mem (rootDiagAutHom_mem_a5Levi apinv hl₀))
          (rootDiagAutHom_mem_a5Levi apinv l.2))
          (rootDiagAutHom_mem_a5Levi apinv hl₀)⟩
      left_inv := fun l => Subtype.ext (by
        show (rootDiagAutHom .E6 K apinv l₀)⁻¹ *
            rootDiagAutHom .E6 K apinv (l₀ * rootDiagAutHom .E6 K ap
              (l : adjointGroup .E6 K) * l₀⁻¹) *
            (rootDiagAutHom .E6 K apinv l₀) = (l : adjointGroup .E6 K)
        rw [map_mul, map_mul, map_inv, hdd]
        group)
      right_inv := fun l => Subtype.ext (by
        show l₀ * rootDiagAutHom .E6 K ap ((rootDiagAutHom .E6 K apinv l₀)⁻¹ *
            rootDiagAutHom .E6 K apinv (l : adjointGroup .E6 K) *
            (rootDiagAutHom .E6 K apinv l₀)) * l₀⁻¹ = (l : adjointGroup .E6 K)
        rw [map_mul, map_mul, map_inv]
        simp only [hdd']
        group)
      map_mul' := fun l₁ l₂ => Subtype.ext (by
        show l₀ * rootDiagAutHom .E6 K ap ((l₁ : adjointGroup .E6 K) *
            (l₂ : adjointGroup .E6 K)) * l₀⁻¹ =
          (l₀ * rootDiagAutHom .E6 K ap (l₁ : adjointGroup .E6 K) * l₀⁻¹) *
            (l₀ * rootDiagAutHom .E6 K ap (l₂ : adjointGroup .E6 K) * l₀⁻¹)
        rw [map_mul]
        group) }

private theorem leviConjAut_apply (l₀ : adjointGroup .E6 K) (hl₀ : l₀ ∈ a5Levi K)
    (ap apinv : Fin Tag.E6.rank → Kˣ) (hapinv : apinv = ap⁻¹) (l : ↥(a5Levi K)) :
    ((leviConjAut l₀ hl₀ ap apinv hapinv l : ↥(a5Levi K)) : adjointGroup .E6 K) =
      l₀ * rootDiagAutHom .E6 K ap (l : adjointGroup .E6 K) * l₀⁻¹ := rfl

theorem exists_levi_action_of_fix [Finite K] [CharP K 2]
    {g : adjointGroup .E6 K} {a : Fin Tag.E6.rank → Kˣ}
    (hfix : (MulAut.conj g * rootDiagAutHom .E6 K a)
        (EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) =
      EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) :
    ∃ α : MulAut ↥(a5Levi K),
      (∃ A : GL (Fin 6) K, ∀ B : Matrix.SpecialLinearGroup (Fin 6) K,
        α (slToA5Levi B) = slToA5Levi (InnerDiagA.conjSL A B)) ∧
      ∀ s ∈ EPilot.highRadical .E6 K ⊔ a5Levi K, ∀ l : ↥(a5Levi K),
        s * (l : adjointGroup .E6 K)⁻¹ ∈ EPilot.highRadical .E6 K →
        (MulAut.conj g * rootDiagAutHom .E6 K a) s *
            ((α l : ↥(a5Levi K)) : adjointGroup .E6 K)⁻¹ ∈ EPilot.highRadical .E6 K := by
  classical
  obtain ⟨lam, hlam⟩ := exists_sq_inv_rootChar (K := K) a
  obtain ⟨ap, hap⟩ : ∃ ap : Fin Tag.E6.rank → Kˣ, ap = a * EPilot.highDiag .E6 lam := ⟨_, rfl⟩
  have hθ : rootChar ap (highRoot .E6) = 1 := by
    rw [hap, rootChar_mul_tuple, EPilot.rootChar_highDiag,
      EPilot.highRoot_highNode (Or.inl rfl), zpow_ofNat, hlam, mul_inv_cancel]
  obtain ⟨t, ht⟩ : ∃ t : adjointGroup .E6 K,
      t = ⟨rootDiagUnit .E6 (EPilot.highDiag .E6 lam),
        EPilot.highRootSL2_le_adjointGroup
          (EPilot.rootDiagUnit_highDiag_mem_highRootSL2 (Or.inl rfl) lam)⟩ := ⟨_, rfl⟩
  have hfixap := rootDiagAutHom_fixes_pinnedElt (K := K) ap hθ
  have hdt : rootDiagAutHom .E6 K ap = MulAut.conj t * rootDiagAutHom .E6 K a := by
    rw [hap]
    exact rootDiagAutHom_mul_highDiag a lam t (by rw [ht])
  have hδ : MulAut.conj g * rootDiagAutHom .E6 K a =
      MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap := by
    rw [hdt, map_mul, map_inv]
    group
  have hfixh : MulAut.conj (g * t⁻¹) (EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) =
      EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) := by
    have h1 := hfix
    rw [hδ, MulAut.mul_apply, hfixap] at h1
    exact h1
  have hmem : g * t⁻¹ ∈ Subgroup.centralizer
      ({EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)} : Set (adjointGroup .E6 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h2 : (g * t⁻¹) * EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) * (g * t⁻¹)⁻¹ =
        EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) := hfixh
    calc EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) * (g * t⁻¹)
        = ((g * t⁻¹) * EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) * (g * t⁻¹)⁻¹) *
            (g * t⁻¹) := by rw [h2]
      _ = (g * t⁻¹) * EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) := by group
  obtain ⟨hC, hNL, -, hpCore⟩ := KGExc.centralizer_decomp_highRoot (K := K) (Or.inl rfl)
    isQuasisimple_a5Levi center_a5Levi_eq_bot
  have hL : a5Levi K = EPilot.perpLevi .E6 K := rfl
  rw [← hL] at hC hNL
  have hQ : EPilot.highRadical .E6 K ⊔ a5Levi K =
      Subgroup.centralizer ({EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)} :
        Set (adjointGroup .E6 K)) := hC.symm
  have hcoemul := Subgroup.coe_mul_of_right_le_normalizer_left (EPilot.highRadical .E6 K)
    (a5Levi K) hNL
  obtain ⟨q₀, hq₀, l₀, hl₀, hql⟩ : ∃ q₀ ∈ EPilot.highRadical .E6 K,
      ∃ l₀ ∈ a5Levi K, q₀ * l₀ = g * t⁻¹ := by
    have hmem'' : g * t⁻¹ ∈
        (↑(EPilot.highRadical .E6 K ⊔ a5Levi K) : Set (adjointGroup .E6 K)) := by
      rw [hQ]; exact hmem
    rw [hcoemul, Set.mem_mul] at hmem''
    exact hmem''
  obtain ⟨apinv, hapinv⟩ : ∃ apinv : Fin Tag.E6.rank → Kˣ, apinv = ap⁻¹ := ⟨_, rfl⟩
  let α : MulAut ↥(a5Levi K) := leviConjAut l₀ hl₀ ap apinv hapinv
  have hαcoe : ∀ l : ↥(a5Levi K),
      ((α l : ↥(a5Levi K)) : adjointGroup .E6 K) =
        l₀ * rootDiagAutHom .E6 K ap (l : adjointGroup .E6 K) * l₀⁻¹ := fun l =>
    leviConjAut_apply l₀ hl₀ ap apinv hapinv l
  have hmemQ : ∀ F : MulAut (adjointGroup .E6 K),
      F (EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) =
        EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) →
      (EPilot.highRadical .E6 K).map F.toMonoidHom = EPilot.highRadical .E6 K := fun F hF =>
    pCoreOf_map_eq_self F hpCore hF
  have hF : ∀ x y : adjointGroup .E6 K,
      (MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap) (x * y) =
        (MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap) x *
          (MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap) y := fun x y => map_mul _ x y
  obtain ⟨Aap, hAap⟩ := exists_gl_rootDiagAutHom_slToAdjointE6 (K := K) ap
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Matrix.SpecialLinearGroup (Fin 6) K, slToAdjointE6 K B₀ = l₀ :=
    MonoidHom.mem_range.1 (by rw [range_slToAdjointE6]; exact hl₀)
  refine ⟨α, ⟨Matrix.SpecialLinearGroup.toGL B₀ * Aap, fun B => ?_⟩, ?_⟩
  · refine Subtype.ext ?_
    rw [hαcoe]
    show l₀ * rootDiagAutHom .E6 K ap (slToAdjointE6 K B) * l₀⁻¹ =
      slToAdjointE6 K (InnerDiagA.conjSL (Matrix.SpecialLinearGroup.toGL B₀ * Aap) B)
    rw [show l₀ = slToAdjointE6 K B₀ from hB₀.symm, hAap, conjSL_mul,
      conjSL_toGL_mul]
    simp only [map_mul, map_inv]
  · intro s hs l hsl
    have hFx : (MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap)
        (EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) =
        EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) := by
      rw [MulAut.mul_apply, hfixap]
      exact hfixh
    have hδQ := hmemQ (MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap) hFx
    have hs1 : (MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap)
        (s * (l : adjointGroup .E6 K)⁻¹) ∈ EPilot.highRadical .E6 K := by
      have h2 := Subgroup.mem_map_of_mem
        (MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap).toMonoidHom hsl
      rwa [hδQ] at h2
    have hs2 : (MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap)
        (l : adjointGroup .E6 K) * ((α l : ↥(a5Levi K)) : adjointGroup .E6 K)⁻¹ ∈
        EPilot.highRadical .E6 K := by
      have hδl : (MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap)
          (l : adjointGroup .E6 K) =
          q₀ * ((α l : ↥(a5Levi K)) : adjointGroup .E6 K) * q₀⁻¹ := by
        rw [MulAut.mul_apply, MulAut.conj_apply, ← hql, hαcoe]
        group
      have hconj : ((α l : ↥(a5Levi K)) : adjointGroup .E6 K) * q₀⁻¹ *
          ((α l : ↥(a5Levi K)) : adjointGroup .E6 K)⁻¹ ∈ EPilot.highRadical .E6 K :=
        (Subgroup.le_normalizer_iff.1 hNL) _ (α l).2 q₀⁻¹ (Subgroup.inv_mem _ hq₀)
      have hmain : (MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap)
            (l : adjointGroup .E6 K) * ((α l : ↥(a5Levi K)) : adjointGroup .E6 K)⁻¹ =
          q₀ * (((α l : ↥(a5Levi K)) : adjointGroup .E6 K) * q₀⁻¹ *
              ((α l : ↥(a5Levi K)) : adjointGroup .E6 K)⁻¹) := by rw [hδl]; group
      rw [hmain]
      exact Subgroup.mul_mem (EPilot.highRadical .E6 K) hq₀ hconj
    have hsplit : (MulAut.conj g * rootDiagAutHom .E6 K a) s *
        ((α l : ↥(a5Levi K)) : adjointGroup .E6 K)⁻¹ =
        (MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap)
            (s * (l : adjointGroup .E6 K)⁻¹) *
          ((MulAut.conj (g * t⁻¹) * rootDiagAutHom .E6 K ap) (l : adjointGroup .E6 K) *
            ((α l : ↥(a5Levi K)) : adjointGroup .E6 K)⁻¹) := by
      rw [hδ, show s = (s * (l : adjointGroup .E6 K)⁻¹) * (l : adjointGroup .E6 K) from by
        group, hF]
      group
    rw [hsplit]
    exact Subgroup.mul_mem _ hs1 hs2

end CFSG.StandardType.KGE6
