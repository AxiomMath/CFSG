module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthFrameExists
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthTauMemOmega
import CFSG.LocalAnalysis.StandardType.GGQ2OrthTorusAutCoord
import CFSG.LocalAnalysis.StandardType.GGQ2OrthType
import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksGroup
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagOmegaQuasisimple
import CFSG.RankThree.PartOne.KF.ClsOmega

public section

namespace CFSG.StandardType.CommonJOmPlusTwo

open CFSG.Assembly CFSG.StandardType.GGQ2Frame
  CFSG.StandardType.GGQ2Frame.OrthBlocks CFSG.StandardType.GGQ2Frame.SpBlocks

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def ggCommonJOmPlusTwo_tau (hK : Nat.card K = 2) (m : ℕ) :
    (Fin m → Multiplicative (ZMod 3)) →* ↥(omegaQ (K := K) m 1) where
  toFun f := ⟨otau (otc_zeta K) m 1 (fun i => (f i).toAdd),
    orthTauMemOmega_holds (otc_zeta K) m 1 hK _⟩
  map_one' := by
    apply Subtype.ext
    have h : (fun i : Fin m => ((1 : Fin m → Multiplicative (ZMod 3)) i).toAdd) = 0 := by
      funext i
      rfl
    rw [h]
    simpa using otc_otau_zero (otc_zeta K) m 1
  map_mul' f g := by
    apply Subtype.ext
    have h : (fun i => ((f * g) i).toAdd) =
        (fun i => (f i).toAdd) + (fun i => (g i).toAdd) := by
      funext i
      rfl
    rw [h]
    simpa using otc_otau_mul (otc_zeta K) m 1
      (fun i => (f i).toAdd) (fun i => (g i).toAdd)

theorem ggCommonJOmPlusTwo_tau_injective (hK : Nat.card K = 2) (m : ℕ) :
    Function.Injective (ggCommonJOmPlusTwo_tau hK m) := by
  intro f g h
  have h1 : (SpBlocks.tau (otc_zeta K) (m + 1)
      (liftV m 1 fun i => (f i).toAdd) : ↥(CFSG.Open.StatedSp (m + 1) K)) =
      SpBlocks.tau (otc_zeta K) (m + 1) (liftV m 1 fun i => (g i).toAdd) := by
    apply Subtype.ext
    have h2 := congrArg (fun x : ↥(omegaQ (K := K) m 1) =>
      (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K)) h
    simpa [ggCommonJOmPlusTwo_tau, otau] using h2
  have h3 := SpBlocks.tau_injective (otc_zeta_injective K) (m + 1) h1
  have h4 := liftV_injective m 1 h3
  funext i
  exact Multiplicative.toAdd.injective (congrFun h4 i)

theorem ggCommonJOmPlusTwo_signed (hK : Nat.card K = 2) (m : ℕ) :
    ∀ g : ↥(omegaQ (K := K) m 1),
      (∀ s ∈ (ggCommonJOmPlusTwo_tau hK m).range,
        g * s * g⁻¹ ∈ (ggCommonJOmPlusTwo_tau hK m).range) →
      ∃ u : (Fin m → Multiplicative (ZMod 3)) → (Fin m → Multiplicative (ZMod 3)),
        SpCoord.IsSignedPerm u ∧ ∀ f, g * ggCommonJOmPlusTwo_tau hK m f * g⁻¹ =
          ggCommonJOmPlusTwo_tau hK m (u f) := by
  classical
  intro g hg
  have hpre : ∀ f : Fin m → Multiplicative (ZMod 3),
      ∃ f' : Fin m → Multiplicative (ZMod 3),
        g * ggCommonJOmPlusTwo_tau hK m f * g⁻¹ = ggCommonJOmPlusTwo_tau hK m f' := by
    intro f
    obtain ⟨f', hf'⟩ :=
      MonoidHom.mem_range.mp (hg _ (MonoidHom.mem_range.mpr ⟨f, rfl⟩))
    exact ⟨f', hf'.symm⟩
  let φ : PlaneRaw.V m → PlaneRaw.V m := fun u =>
    fun i => (Classical.choose (hpre (fun j => Multiplicative.ofAdd (u j))) i).toAdd
  have hφ : ∀ u : PlaneRaw.V m,
      (g : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) * otau (otc_zeta K) m 1 u *
        (g : GL (Fin (m + 1) ⊕ Fin (m + 1)) K)⁻¹ =
        otau (otc_zeta K) m 1 (φ u) := by
    intro u
    have h := congrArg (fun x : ↥(omegaQ (K := K) m 1) =>
      (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K))
      (Classical.choose_spec (hpre (fun j => Multiplicative.ofAdd (u j))))
    simpa [ggCommonJOmPlusTwo_tau, φ] using h
  obtain ⟨π, η, -, hπη⟩ :=
    exists_moveExp_of_conj_otau (K := K) (t := m) (δ := 1) (ζ := otc_zeta K) hK
      (otc_zeta_injective K) (Q := planeQForm K m 1)
      (coe_planeQForm (K := K) (t := m) (δ := 1)) (nondegenerate_planeQForm)
      (y := (g : GL (Fin (m + 1) ⊕ Fin (m + 1)) K)) g.property hφ
  let u : (Fin m → Multiplicative (ZMod 3)) → (Fin m → Multiplicative (ZMod 3)) :=
    fun f i => Multiplicative.ofAdd (ChoiceTwo.moveExp π η (fun j => (f j).toAdd) i)
  refine ⟨u, ?_, ?_⟩
  · refine ⟨π.symm, fun i => if η (π.symm i) then -1 else 1, ?_, ?_⟩
    · intro i
      by_cases hη : η (π.symm i) = true <;> simp [hη]
    · intro f i
      simp only [u, toAdd_ofAdd, ChoiceTwo.moveExp_apply, Equiv.symm_apply_apply]
      by_cases hη : η (π.symm i) = true <;> simp [ChoiceTwo.sgnZ, hη]
  · intro f
    apply Subtype.ext
    have htoadd : (fun i => (u f i).toAdd) =
        ChoiceTwo.moveExp π η (fun j => (f j).toAdd) := by
      funext i
      simp [u]
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    change (g : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) *
        otau (otc_zeta K) m 1 (fun j => (f j).toAdd) *
        (g : GL (Fin (m + 1) ⊕ Fin (m + 1)) K)⁻¹ =
        otau (otc_zeta K) m 1 (fun i => (u f i).toAdd)
    rw [hφ, hπη, htoadd]

theorem ggCommonJOmPlusTwo_equiv (hK : Nat.card K = 2) {m : ℕ} (hme : Even m) :
    Nonempty (↥(omegaQ (K := K) m 1) ≃*
      LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K (m + 1)))) := by
  obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadPlus (K := K) m (1 : Fin 2) hme
  have hsub : omegaQ (K := K) m 1 = CFSG.Open.StatedOmega ⇑(planeQForm K m 1) := by
    unfold omegaQ
    rw [← coe_planeQForm]
  let F₁ : ↥(omegaQ (K := K) m 1) ≃*
      ↥(CFSG.Open.StatedOmega ⇑(planeQForm K m 1)) := MulEquiv.subgroupCongr hsub
  let F₂ : ↥(CFSG.Open.StatedOmega ⇑(planeQForm K m 1)) ≃*
      ↥(CFSG.Open.StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadPlus (m + 1) K)) :=
    statedOmegaMulEquivOfIsometry e
  let F₃ : ↥(CFSG.Open.StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadPlus (m + 1) K)) ≃*
      ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus (m + 1) K)) :=
    MulEquiv.subgroupCongr (congrArg CFSG.Open.StatedOmega
      (CFSG.LieType.Universal.Spin.coe_quadPlus (m + 1) K))
  let F₄ : ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus (m + 1) K)) ≃*
      LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K (m + 1))) :=
    CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _
      (CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot
        (K := K) (n := m + 1) (by omega))
  exact ⟨F₁.trans (F₂.trans (F₃.trans F₄))⟩

end CFSG.StandardType.CommonJOmPlusTwo

end
