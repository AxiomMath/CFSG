module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelEFrame
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Gen

variable {k : Type} [Field k]

private theorem rootChar_single_E6 (a : Fin Tag.E6.rank → kˣ) (i : Fin Tag.E6.rank) :
    rootChar a (Pi.single i 1) = a i := by
  simpa using rootChar_nsmul_single a i 1

private theorem zetaVec_apply_ne_one {ζ : kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {v : Fin Tag.E6.rank → ZMod 3} {j : Fin Tag.E6.rank} (hv : v j ≠ 0) :
    zetaVec ζ hζ v j ≠ 1 := by
  intro h
  have h1 : zmodPowHom ζ hζ (Multiplicative.ofAdd (v j)) = 1 := h
  have h3 : Multiplicative.ofAdd (v j) = (1 : Multiplicative (ZMod 3)) :=
    zmodPowHom_injective hζo hζ (by
      rw [h1]
      exact (map_one (zmodPowHom ζ hζ)).symm)
  have h2 : v j = 0 := by
    have := congrArg Multiplicative.toAdd h3
    simpa using this
  exact hv h2

private theorem inv_smul_reflect_E6 (i : Fin Tag.E6.rank) (β : Fin Tag.E6.rank → ℤ) :
    (simple .E6 i)⁻¹ • reflect .E6 i β = β := by
  rw [← simple_smul, ← mul_smul, inv_mul_cancel, one_smul]

theorem exists_mem_hypE6_rootChar_ne_one {ζ : kˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) :
    ∀ α : Fin Tag.E6.rank → ℤ, IsRoot .E6 α →
      ∃ v : Fin Tag.E6.rank → ZMod 3, v ∈ NoOffRest.hypE6 ∧
        rootChar (zetaVec ζ hζ v) α ≠ 1 := by
  intro α hα
  induction hα with
  | basis j =>
    refine ⟨fun _ => 1, ?_, ?_⟩
    · rw [NoOffRest.mem_hypE6]
      decide
    · rw [rootChar_single_E6]
      exact zetaVec_apply_ne_one hζo hζ one_ne_zero
  | reflect i _ ih =>
    obtain ⟨v, hv, hne⟩ := ih
    refine ⟨adRefl .E6 3 i v, ?_, ?_⟩
    · rw [NoOffRest.mem_hypE6, NoOffRest.kDotP_adRefl (NoOffRest.kDot_cartan i)]
      exact NoOffRest.mem_hypE6.mp hv
    · have h1 : weylTuple (simple .E6 i) (zetaVec ζ hζ v) =
          zetaVec ζ hζ (adRefl .E6 3 i v) := by
        rw [weylTuple_zetaVec, adAct_simple]
      rw [← h1, rootChar_weylTuple, inv_smul_reflect_E6]
      exact hne

private theorem adAct_eq_of_mem_rootCharStabilizer_zetaVec {ζ : kˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) {w : WeylGroup .E6} {v : Fin Tag.E6.rank → ZMod 3}
    (hw : w ∈ rootCharStabilizer (zetaVec ζ hζ v)) :
    adAct .E6 3 w v = v := by
  have hzeta : zetaVec ζ hζ (adAct .E6 3 w⁻¹ v) = zetaVec ζ hζ v := by
    funext i
    have h := hw (Pi.single i 1)
    have h1 : rootChar (zetaVec ζ hζ (adAct .E6 3 w⁻¹ v)) (Pi.single i 1) =
        rootChar (zetaVec ζ hζ v) (Pi.single i 1) := by
      rw [← h]
      rw [← weylTuple_zetaVec ζ hζ w⁻¹ v, rootChar_weylTuple, inv_inv]
    rwa [rootChar_single_E6, rootChar_single_E6] at h1
  have hfix : adAct .E6 3 w⁻¹ v = v := zetaVec_injective hζo hζ hzeta
  calc adAct .E6 3 w v = adAct .E6 3 w (adAct .E6 3 w⁻¹ v) := by rw [hfix]
    _ = adAct .E6 3 (w * w⁻¹) v := (adAct_mul w w⁻¹ v).symm
    _ = v := by rw [mul_inv_cancel, adAct_one]

theorem mem_torusGroup_of_commute_zetaVec {ζ : kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {r : ModGL .E6 k} (hr : r ∈ adjointGroup .E6 k)
    (hc : ∀ v ∈ NoOffRest.hypE6,
      rootDiagUnit .E6 (zetaVec ζ hζ v) * r * (rootDiagUnit .E6 (zetaVec ζ hζ v))⁻¹ = r) :
    r ∈ torusGroup .E6 k := by
  let a : NoOffRest.hypE6 → Fin Tag.E6.rank → kˣ :=
    fun v => zetaVec ζ hζ (v : Fin Tag.E6.rank → ZMod 3)
  have hfam : r ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer .E6 k a := by
    rw [CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer]
    exact ⟨hr, fun v => hc v v.2⟩
  obtain ⟨w, hw, m, hm, hrm⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer_le_mul .E6 k a hfam
  have hw1 : w = 1 := by
    have hfix : ∀ v : NoOffRest.hypE6,
        adAct .E6 3 w (v : Fin Tag.E6.rank → ZMod 3) = (v : Fin Tag.E6.rank → ZMod 3) :=
      fun v => adAct_eq_of_mem_rootCharStabilizer_zetaVec hζo hζ (hw v)
    have hperm : NoOffRest.hypPerm w = 1 :=
      Equiv.ext fun x => Subtype.ext (hfix x)
    exact NoOffRest.hypPerm_injective (hperm.trans (map_one NoOffRest.hypPerm).symm)
  have hker : CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel a = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun α hα => ?_
    obtain ⟨hαroot, hαtriv⟩ := hα
    obtain ⟨v, hv, hne⟩ := exists_mem_hypE6_rootChar_ne_one hζo hζ α hαroot
    exact hne (hαtriv ⟨v, hv⟩)
  have hmT : m ∈ torusGroup .E6 k := by
    have hm' : m ∈ torusGroup .E6 k ⊔
        rootSpan .E6 k (CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel a) := hm
    rw [hker] at hm'
    have hbot : rootSpan .E6 k (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm'
  rw [hrm, hw1, canonicalRep_one, mul_one]
  exact hmT

end Gen

variable {K : Type} [Field K] [Finite K]

theorem eFrame_cent [CharP K 2] {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    (eFrame K ζ hζ).Cent := by
  intro r
  constructor
  · intro hr
    refine Subgroup.mem_subgroupOf.mpr
      (mem_torusGroup_of_commute_zetaVec hζo hζ r.2 fun v hv => ?_)
    have h2 := congrArg (fun x : adjointGroup .E6 K => (x : ModGL .E6 K)) (hr v hv)
    rw [show ((eFrame K ζ hζ).ad v r : ModGL .E6 K) =
        rootDiagUnit .E6 (zetaVec ζ hζ v) * (r : ModGL .E6 K) *
          (rootDiagUnit .E6 (zetaVec ζ hζ v))⁻¹
        from NoOffE6Three.diag3_apply ζ hζ v r] at h2
    exact h2
  · intro hr v hv
    have hrT : (r : ModGL .E6 K) ∈ torusGroup .E6 K := Subgroup.mem_subgroupOf.mp hr
    exact Subtype.ext (by
      rw [show ((eFrame K ζ hζ).ad v r : ModGL .E6 K) =
          rootDiagUnit .E6 (zetaVec ζ hζ v) * (r : ModGL .E6 K) *
            (rootDiagUnit .E6 (zetaVec ζ hζ v))⁻¹
          from NoOffE6Three.diag3_apply ζ hζ v r]
      exact conj_rootDiagUnit_of_mem_torusGroup (zetaVec ζ hζ v) hrT)

end CFSG.StandardType.E6ThreeModel
