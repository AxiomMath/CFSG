module

public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.B4ModelsApi
public import CFSG.Quasithin.Background.HL3NineW9
public import CFSG.Quasithin.Background.HL3NineModel
public import CFSG.Quasithin.Background.H156Gen
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.Milestones.ASVolI.H14
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F7TwoDefs
public import CFSG.Quasithin.Background.HFixSylBase
public import CFSG.Quasithin.Background.HMathieuFacts
public import CFSG.Quasithin.Background.HTriSolv
public import CFSG.Quasithin.Background.HTriU3
public import CFSG.Quasithin.Background.HZ82Base
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Fischer Matrix
open CFSG.Monster.Code (bvec bvec_apply)
open CFSG.Quasithin.H13.Ch9.Herm9
open CFSG.Quasithin.H CFSG.Quasithin.H.L3W9
open CFSG.Quasithin.H.L3Nine (HMod rhoT tw frobPow_eq_conjM)
open CFSG.Quasithin.H.Mathieu (actM bvec_actM)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable (hD : (FFModel.twistTensor 1 (StatedSL 3 K)).IsActionModel)

private def w183_l34Aux2_matOf (X : ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec) :
    Matrix (Fin 3) (Fin 3) K :=
  Multiplicative.toAdd (X.1 : Multiplicative (Matrix (Fin 3) (Fin 3) K))

private theorem w183_l34Aux2_matOf_actSec (γ : ↥(StatedSL 3 K))
    (m : ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec) :
    w183_l34Aux2_matOf (K := K) (hD.actSec γ m) =
      (((γ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) * w183_l34Aux2_matOf (K := K) m *
        (frobPow 1 (((γ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K))ᵀ := rfl

private theorem w183_l34Aux2_rhoT_eq_actSec (hK : Nat.card K = 4) (γ : ↥(StatedSL 3 K))
    (m : ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec) :
    rhoT (n := 1) (by rw [hK]; norm_num) (γ : GL (Fin 3) K)
        (⟨m.1, m.2⟩ : HMod 1 K) =
      ⟨(hD.actSec γ m).1, (hD.actSec γ m).2⟩ := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  show tw 1 (((γ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) (w183_l34Aux2_matOf (K := K) m) =
    w183_l34Aux2_matOf (K := K) (hD.actSec γ m)
  rw [w183_l34Aux2_matOf_actSec, frobPow_eq_conjM]
  rfl

@[expose] noncomputable def w183_l34Aux2_modEquiv (φ : K ≃+* F4) :
    (FFModel.twistTensor 1 (StatedSL 3 K)).Mod ≃* W9 :=
  ((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf
      (hermSub 1 (Fin 3) K))).trans QuotientGroup.quotientBot).trans (hmodEquiv φ)

theorem w183_l34Aux2_modEquiv_mk (φ : K ≃+* F4)
    (m : ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec) :
    w183_l34Aux2_modEquiv (K := K) φ (QuotientGroup.mk m) = hmodEquiv φ ⟨m.1, m.2⟩ := rfl

theorem w183_l34Aux2_intertwine (hK : Nat.card K = 4) (φ : K ≃+* F4)
    (γ : ↥(StatedSL 3 K))
    (m : ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec) :
    w183_l34Aux2_modEquiv (K := K) φ (hD.modAct γ (QuotientGroup.mk m)) =
      rho9 (mapGLF φ γ) (w183_l34Aux2_modEquiv (K := K) φ (QuotientGroup.mk m)) := by
  have hmodAct : hD.modAct γ (QuotientGroup.mk m) =
      QuotientGroup.mk (hD.actSec γ m) := rfl
  rw [hmodAct, w183_l34Aux2_modEquiv_mk, w183_l34Aux2_modEquiv_mk]
  have hρ := congrArg (hmodEquiv φ) (w183_l34Aux2_rhoT_eq_actSec (K := K) hD hK γ m)
  rw [← hρ]
  have h := congrArg (fun f : MulAut W9 => f (hmodEquiv φ ⟨m.1, m.2⟩))
    (congrHom_hmodEquiv_rhoT φ (by rw [hK]; norm_num) (γ : GL (Fin 3) K))
  exact (CFSG.Quasithin.H156.congrHom_apply_eg (hmodEquiv φ) (rhoT hK γ)
    ⟨m.1, m.2⟩).symm.trans h

@[expose] def w183_l34Aux2_P4 : Matrix (Fin 3) (Fin 3) F4 := !![0,1,0;0,0,1;1,0,0]

@[expose] def w183_l34Aux2_B4 : Matrix (Fin 3) (Fin 3) F4 := !![1,1,F4.ω;0,1,1;0,1,0]

@[expose] def w183_l34Aux2_B4' : Matrix (Fin 3) (Fin 3) F4 := !![1,1,F4.ω ^ 2;0,1,1;0,1,0]

def w183_l34Aux2_colMat (cs : List ℕ) : Matrix (Fin 9) (Fin 9) (ZMod 2) :=
  fun i j => if (cs.getD j.val 0).testBit i.val then 1 else 0

private theorem w183_l34Aux2_bvec_act (g : Matrix (Fin 3) (Fin 3) F4) (m : Fin 512) :
    bvec 9 (act g m) = (w183_l34Aux2_colMat (cols g)).mulVec (bvec 9 m) := by
  have h1 : bvec 9 (act g m) = bvec 9 (actM (cols g) m) := by rw [actM_cols]
  rw [h1, bvec_actM]
  have hlen : (cols g).length = 9 := by
    rw [cols, CFSG.Quasithin.H.Mathieu.length_matOf]
  rw [hlen]
  funext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  cases h : (m : ℕ).testBit j.val
  · simp [h, w183_l34Aux2_colMat, bvec_apply]
  · simp [h, w183_l34Aux2_colMat, bvec_apply]

theorem w183_l34Aux2_toAdd_rho9 (g : GL (Fin 3) F4) (x : W9) :
    Multiplicative.toAdd (rho9 g x) =
      (w183_l34Aux2_colMat (cols (g : Matrix (Fin 3) (Fin 3) F4))).mulVec
        (Multiplicative.toAdd x) := by
  obtain ⟨m, rfl⟩ := toW9.surjective x
  rw [rho9_toW9]
  exact w183_l34Aux2_bvec_act (g : Matrix (Fin 3) (Fin 3) F4) m

private theorem w183_l34Aux2_card_image_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2)) : (Finset.univ.image A.mulVec).card = 2 ^ A.rank := by
  have h1 : (Finset.univ.image A.mulVec).card = Nat.card (Set.range A.mulVec) := by
    rw [Nat.card_eq_card_toFinset, Set.toFinset_range]
  have h2 : Set.range A.mulVec = (LinearMap.range A.mulVecLin : Set (ι → ZMod 2)) := by
    rw [LinearMap.coe_range, Matrix.coe_mulVecLin]
  have hfin : Module.Finite (ZMod 2) (LinearMap.range A.mulVecLin) := Module.Finite.range _
  have h3 := @Module.natCard_eq_pow_finrank (ZMod 2) (LinearMap.range A.mulVecLin) _
    (Submodule.addCommGroup _) (Submodule.module _) hfin
  rw [h1, h2, SetLike.coe_sort_coe, h3, Nat.card_zmod]
  rfl

private theorem w183_l34Aux2_rank_eq_iff_card_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2)) (r : ℕ) :
    A.rank = r ↔ (Finset.univ.image A.mulVec).card = 2 ^ r := by
  rw [w183_l34Aux2_card_image_mulVec]
  exact (Nat.pow_right_injective le_rfl).eq_iff.symm

theorem w183_l34Aux2_rank_P4 :
    (1 + w183_l34Aux2_colMat (cols w183_l34Aux2_P4) +
      w183_l34Aux2_colMat (cols w183_l34Aux2_P4) ^ 2).rank = 3 := by
  rw [w183_l34Aux2_rank_eq_iff_card_image]
  decide +kernel

theorem w183_l34Aux2_rank_B4 :
    (1 + w183_l34Aux2_colMat (cols w183_l34Aux2_B4) +
      w183_l34Aux2_colMat (cols w183_l34Aux2_B4) ^ 2).rank = 3 := by
  rw [w183_l34Aux2_rank_eq_iff_card_image]
  decide +kernel

theorem w183_l34Aux2_rank_B4' :
    (1 + w183_l34Aux2_colMat (cols w183_l34Aux2_B4') +
      w183_l34Aux2_colMat (cols w183_l34Aux2_B4') ^ 2).rank = 3 := by
  rw [w183_l34Aux2_rank_eq_iff_card_image]
  decide +kernel

theorem w183_l34Aux2_fix_dual :
    (∀ f : Fin 9 → ZMod 2, (w183_l34Aux2_colMat (cols w183_l34Aux2_P4))ᵀ.mulVec f = f →
      (w183_l34Aux2_colMat (cols w183_l34Aux2_B4))ᵀ.mulVec f = f → f = 0) := by
  decide +kernel

theorem w183_l34Aux2_fix_dual_B4' :
    (∀ f : Fin 9 → ZMod 2, (w183_l34Aux2_colMat (cols w183_l34Aux2_P4))ᵀ.mulVec f = f →
      (w183_l34Aux2_colMat (cols w183_l34Aux2_B4'))ᵀ.mulVec f = f → f = 0) := by
  decide +kernel

theorem w183_l34Aux2_finrank_range_mulVecLin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2)) :
    Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) = A.rank := by
  rw [Matrix.range_mulVecLin, ← Matrix.rank_eq_finrank_span_cols]

theorem w183_l34Aux2_finrank_range_norm_congr {Q Q' : Type} [AddCommGroup Q]
    [Module (ZMod 2) Q] [AddCommGroup Q'] [Module (ZMod 2) Q'] (L : Q ≃ₗ[ZMod 2] Q')
    {A : Q →ₗ[ZMod 2] Q} {B : Q' →ₗ[ZMod 2] Q'} (h : ∀ x, L (A x) = B (L x)) (n : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range n, A ^ i)) =
      Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range n, B ^ i)) := by
  have key : ∀ x : Q, (L : Q →ₗ[ZMod 2] Q') (A x) = B ((L : Q →ₗ[ZMod 2] Q') x) :=
    fun x => h x
  have hpow : ∀ i : ℕ, ∀ x : Q,
      (L : Q →ₗ[ZMod 2] Q') ((A ^ i) x) = (B ^ i) ((L : Q →ₗ[ZMod 2] Q') x) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
        intro x
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih (A x), key x]
  have hcomp : ∀ x : Q, (L : Q →ₗ[ZMod 2] Q') ((∑ i ∈ Finset.range n, A ^ i) x) =
      (∑ i ∈ Finset.range n, B ^ i) ((L : Q →ₗ[ZMod 2] Q') x) := by
    intro x
    rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hpow i x
  have hmap : (LinearMap.range (∑ i ∈ Finset.range n, A ^ i)).map
      (L : Q →ₗ[ZMod 2] Q') = LinearMap.range (∑ i ∈ Finset.range n, B ^ i) := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := hx
      rw [hcomp z]
      exact ⟨(L : Q →ₗ[ZMod 2] Q') z, rfl⟩
    · intro y hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨(∑ i ∈ Finset.range n, A ^ i) (L.symm z), ⟨L.symm z, rfl⟩, ?_⟩
      rw [hcomp]
      congr 1
      exact L.apply_symm_apply z
  have h := LinearEquiv.finrank_map_eq L (LinearMap.range (∑ i ∈ Finset.range n, A ^ i))
  rw [hmap] at h
  exact h.symm

theorem w183_l34Aux2_fix_dual_two {Q Q' : Type} [AddCommGroup Q] [Module (ZMod 2) Q]
    [AddCommGroup Q'] [Module (ZMod 2) Q'] (L : Q ≃ₗ[ZMod 2] Q')
    {A₁ A₂ : Q →ₗ[ZMod 2] Q} {B₁ B₂ : Q' →ₗ[ZMod 2] Q'}
    (h₁ : ∀ x, L (A₁ x) = B₁ (L x)) (h₂ : ∀ x, L (A₂ x) = B₂ (L x))
    (hfix : ∀ f : Q' →ₗ[ZMod 2] ZMod 2,
      B₁.dualMap f = f → B₂.dualMap f = f → f = 0) :
    ∀ f : Q →ₗ[ZMod 2] ZMod 2,
      A₁.dualMap f = f → A₂.dualMap f = f → f = 0 := by
  intro f hf₁ hf₂
  set g : Q' →ₗ[ZMod 2] ZMod 2 := L.dualMap.symm f with hg_def
  have hLg : L.dualMap g = f := L.dualMap.apply_symm_apply f
  have key : ∀ (A : Q →ₗ[ZMod 2] Q) (B : Q' →ₗ[ZMod 2] Q'),
      (∀ x, L (A x) = B (L x)) →
      A.dualMap (L.dualMap g) = L.dualMap (B.dualMap g) := by
    intro A B hAB
    have hcomp : (L : Q →ₗ[ZMod 2] Q').comp A = B.comp (L : Q →ₗ[ZMod 2] Q') := by
      ext x; exact hAB x
    have hdual := congrArg LinearMap.dualMap hcomp
    rw [← LinearMap.dualMap_comp_dualMap A (L : Q →ₗ[ZMod 2] Q'),
      ← LinearMap.dualMap_comp_dualMap (L : Q →ₗ[ZMod 2] Q') B] at hdual
    exact DFunLike.congr_fun hdual g
  have hB₁ : B₁.dualMap g = g := by
    apply L.dualMap.injective
    rw [(key A₁ B₁ h₁).symm, hLg, hf₁]
  have hB₂ : B₂.dualMap g = g := by
    apply L.dualMap.injective
    rw [(key A₂ B₂ h₂).symm, hLg, hf₂]
  have hg0 := hfix g hB₁ hB₂
  rw [← hLg, hg0, map_zero]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
