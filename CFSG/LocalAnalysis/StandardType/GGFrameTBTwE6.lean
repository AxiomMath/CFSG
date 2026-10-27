module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBExcNum
public import CFSG.LocalAnalysis.StandardType.GGFrameWholeFacts
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelData
import CFSG.LocalAnalysis.StandardType.GGFrameTBExcMat
import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
import CFSG.LocalAnalysis.StandardType.GGTBRowE6Equiv
import CFSG.LocalAnalysis.StandardType.GGDepED4Weyl
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHeart
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTv
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitE6ThreeAux
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem

theorem not_isTransvection_of_e6ThreeData
    {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'}
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'}
    {w : Fin 6 → L'} (h : GGE6ThreeData Z A Φ T w) :
    ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, ¬ GGIsTransvection 3 φ := by
  have hle : ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤
      (A.normalizerMonoidHom).range := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro φ ⟨g, -, hgN, hφg⟩
    refine ⟨⟨g, hgN⟩, ?_⟩
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hφg b]
  intro φ hφ
  obtain ⟨α, rfl⟩ := hle hφ
  exact h.not_isTransvection α

private theorem frameTwE6_coxeterE6_eq :
    coxeterMatrix (isFiniteType_cartan .E6) = CoxeterMatrix.E₆ := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E6 = CartanMatrix.E 6 := cartanE_eq 6
  exact coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E6) (hc.symm ▸ ggIntCartan_E₆)

private theorem frameTwE6_simple_eq (i : Fin 6) :
    (coxeterMatrix (isFiniteType_cartan .E6)).simple i = simple .E6 i :=
  congrFun (CoxeterMatrix.toCoxeterSystem_simple _).symm i

theorem frameNumIs_frameConn_of_e6ThreeData
    {L' : Type} [Group L']
    [Finite L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}
    (hA : IsElemAbelian 3 A) (h : GGE6ThreeData Z A Φ T w) :
    FrameNumIs (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) 36 (some 20) ∧
      FrameConn (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) := by
  classical
  let e := h.automizerEquivWeyl
  let ρ : ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) →* FEMat 6 :=
    (frameAdMat .E6).comp e.symm.toMonoidHom
  have hpres : GGCoxeterPres 3 (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
      (coxeterMatrix (isFiniteType_cartan .E6)) e := by
    refine ⟨ggWTSE6_isWeylMatrix_E6, fun i => ?_⟩
    rw [show e = h.automizerEquivWeyl from rfl, frameTwE6_simple_eq i,
      h.automizerEquivWeyl_simple i]
    exact h.conjAut_isReflection i
  have h3 : ∀ i j : Fin 6, i ≠ j →
      (coxeterMatrix (isFiniteType_cartan .E6)).M i j ≤ 3 := by
    intro i j _
    rw [frameTwE6_coxeterE6_eq]
    fin_cases i <;> fin_cases j <;> decide
  have hnt : ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
      ¬ GGIsTransvection 3 φ :=
    not_isTransvection_of_e6ThreeData h
  have hρi : Function.Injective ρ := by
    intro x y hxy
    exact MulEquiv.injective e.symm (frameAdMat_injective .E6 hxy)
  have hρ : ∀ i : Fin 6,
      ρ (e ((coxeterMatrix (isFiniteType_cartan .E6)).simple i)) = feS 6 i := by
    intro i
    show frameAdMat .E6 (e.symm (e ((coxeterMatrix (isFiniteType_cartan .E6)).simple i))) =
      feS 6 i
    rw [MulEquiv.symm_apply_apply, frameTwE6_simple_eq i]
    exact frameAdMat_simple (Or.inl rfl) i
  obtain ⟨hN, hd, hconn⟩ :=
    frameWhole_facts (n := 6) (N := 36) (d := 20) (Or.inl ⟨rfl, rfl, rfl⟩)
  exact frameNumIs_frameConn_of_frameRep (Bs := A) hA hpres h3 hnt hρi hρ hN hd hconn

theorem exists_noncyclic_three_of_e6ThreeData {L' : Type} [Group L'] [Finite L']
    {Z : Subgroup L'} {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin 6 → ZMod 3)}
    {T : Subgroup L'} {w : Fin 6 → L'} (hA : IsElemAbelian 3 A) (h : GGE6ThreeData Z A Φ T w) :
    ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S := by
  have hA₀ : IsElemAbelian 3 (heartOf Φ) := hA.mono heartOf_le
  have h9 : 3 ^ 2 ≤ Nat.card (heartOf Φ) := by
    rw [h.card_heart]
    norm_num
  have hinn : ∀ a ∈ heartOf Φ, ∃ l : L', a = MulAut.conj l := by
    intro a ha
    obtain ⟨hxA, hxhyp⟩ := mem_heartOf_iff.mp ha
    obtain ⟨t, -, -, b, hb, hbΦ⟩ := h.torus (Multiplicative.toAdd (Φ ⟨a, hxA⟩)) hxhyp
    have hbeq : (⟨a, hxA⟩ : A) = b :=
      h.injective (Multiplicative.toAdd.injective hbΦ.symm)
    refine ⟨t, ?_⟩
    rw [hb, ← hbeq]
  exact exists_noncyclic_three_of_forall_conj hA₀ h9 hinn

private theorem frameTwE6_tbGroup_pow_five {R : Type} [Group R] {I : Set (MulAut R)}
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R} {A : Subgroup (MulAut L')} {r : ℕ}
    (hr : 6 ≤ r) (hA : GGTorusTBGroup 3 r R I L' ψ A) :
    GGTorusTBGroup 3 5 R I L' ψ A :=
  ggTorusTBGroup_of_pow_le hA
    (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : 5 ≤ r)) hA.2.2.2.2.2.1)

theorem frameTBBody_twE6
    {lab : LargeEvenLabel} (ht : lab.tag = .twE6)
    (hn : lab.n = 1) : LargeEvenLabelAll lab (frameTBBody lab) := by
  refine frameTBBody_of_rowGe (N := 36) (d := some 20)
    (by simp [frameLabNum, frameTagNum, ht]) ?_
  refine TwE6Delta.labelAll ht
    (Q := fun R _ I => ∀ r : ℕ, 6 ≤ r → GGTorusReflGenW 3 r R I ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup 3 r R I L' ψ A →
          (FrameNumIs (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) 36 (some 20) ∧
            FrameConn (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) ∧
          ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S) ?_
  intro K _ _ hK
  have hn1 : 1 ≤ lab.n := by omega
  have h3dvd : 3 ∣ 2 ^ lab.n + 1 := by rw [hn]; norm_num
  have hM : GGE6ThreeModelSCr (TwE6Delta.RecipeR K lab.n) (TwE6Delta.RecipeI K lab.n) :=
    E6ThreeModel.e6ThreeModel_holds.2 K lab.n hn1 hK h3dvd
  intro r hr
  refine ⟨fun L' _ _ ψ A hA => ggTorusReflGenW_of_e6ThreeModel hM L' ψ A
    (frameTwE6_tbGroup_pow_five hr hA), ?_⟩
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, h5, h3, hsc⟩ := frameTwE6_tbGroup_pow_five hr hA
  obtain ⟨Φ, T, w, hdata⟩ := (hM L' ψ hψ hker hperf A hAe hAI h5 hsc).exists_data
  exact ⟨frameNumIs_frameConn_of_e6ThreeData hAe hdata,
    exists_noncyclic_three_of_e6ThreeData hAe hdata⟩

end CFSG.StandardType.FrameRoute

end
