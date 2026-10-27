module

public import CFSG.LocalAnalysis.StandardType.GGTwE6PlusRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenOmit
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenSL
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenGen
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoLSS92Input
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenInput
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenRoot
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup

public section

namespace CFSG.StandardType.TwE6PlusRootGen

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggKGTwY_mem_adjointGroup
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (x : twistedE6RootGroup K σ) :
    ggKGTwY F x ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
  have hfix : CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K σ.toRingHom ≤
      adjointGroup TwistTag.E6.tag K := fun _ h => (Subgroup.mem_inf.1 h).1
  have hpos : graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom ≤
      adjointGroup TwistTag.E6.tag K := inf_le_right.trans hfix
  have hneg : graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom ≤
      adjointGroup TwistTag.E6.tag K := inf_le_right.trans hfix
  have hle : twistedE6RootGroup K σ ≤ adjointGroup TwistTag.E6.tag K := sup_le hpos hneg
  rw [ggKGTwY_apply]
  exact mul_mem (mul_mem (inv_mem F.g0_mem)
    (baseChangeGL_mem_adjointGroup (algebraMap K (AlgebraicClosure K)) (hle x.2))) F.g0_mem

theorem ggKGTwJ_eq_phiTwoCompIn
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (F : TwE6Frame K σ n p E) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ggKGTwJ F γ = phiTwoCompIn (twistedE6RootGroup K σ) F.g0 γ := by
  ext x
  have e := CFSG.HardMathSupport.Timmesfeld.LangTorus.rootRankOneGroup_eq_rootSpan_pair
    (τ := TwistTag.E6.tag) (L := AlgebraicClosure K) (β := γ) hγ
  refine (mem_ggKGTwJ_iff hσ F).trans ?_
  refine Iff.trans ?_ (mem_phiTwoCompIn_iff (twistedE6RootGroup K σ) (g0 := F.g0) (β := γ)
    (x := x)).symm
  rw [e]
  rfl

theorem iSup_ggKGTwJ_eq_top
    (hGen : PhiTwoTwE6GenInput) {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v) :
    (⨆ γ : {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ}, ggKGTwJ F γ.1) = ⊤ := by
  have h := hGen K σ n hn hK hσ F.v F.Fr F.g0 hv F.fr_eq F.g0_mem F.lang
  have hJ : ∀ γ : {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ},
      ggKGTwJ F γ.1 = phiTwoCompIn (twistedE6RootGroup K σ) F.g0 γ.1 := fun γ =>
    ggKGTwJ_eq_phiTwoCompIn hσ F γ.2
  exact (iSup_congr hJ).trans h

theorem iSup_ggKGTwJ_ne
    (hGen : PhiTwoTwE6GenInput) {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (δ : {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ}) :
    (⨆ (i : {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ})
        (_ : ExcSplitRootGen.excRefl (p := p) i.1 ≠ ExcSplitRootGen.excRefl δ.1),
      ggKGTwJ F i.1) = ⊤ := by
  refine PhiTwoRootGen.iSup_excRefl_ne_eq_top (fun γ => ggKGTwJ F γ) ?_ ?_ ?_
    (iSup_ggKGTwJ_eq_top hGen hn hK hσ F hv) δ
  · intro ε hε
    obtain ⟨r, hrJ, hrY⟩ := ggKGTwJ_weyl hK hσ F hv hε
    refine ⟨r, hrJ, fun γ hγ => map_conj_ggKGTwJ hσ F ?_ hγ⟩
    convert Subgroup.one_mem _ using 1
    rw [hrY]
    exact mul_inv_cancel _
  · intro α β hα hβ h
    exact PhiTwoRootGen.eq_or_eq_neg_of_excRefl_eq_excRefl (Or.inl rfl) hp2 hα hβ h
  · intro δ hδ
    exact PhiTwoRootGen.exists_isRoot_smul_ne (Or.inl rfl) hδ

end CFSG.StandardType.TwE6PlusRootGen

end
