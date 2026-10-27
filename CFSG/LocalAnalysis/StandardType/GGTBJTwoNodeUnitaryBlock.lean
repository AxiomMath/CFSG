module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSUComp
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepWitt
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUModel
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace UFusion

variable {F : Type} [Field F] [Finite F] [CharP F 2]
  {f m : ℕ} {G : Type} [Group G]

theorem uFrameBlock_eq_map_blockSU
    (hF : Nat.card F = (2 ^ f) ^ 2)
    {ψ : SU (unitaryInvolution F 2 f) (m + 1) →* G}
    {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame (unitaryInvolution F 2 f) Q)
    (I : Finset (Fin (m + 1))) :
    uFrameBlock ψ Q I =
      (TableBUE.blockSU (K := F) (n := f) I).map
        (SURep.ggFrameU hF ψ Q hQ) := by
  classical
  let E := SURep.ggFrameEquiv hF Q hQ
  have hEblock : (suBlock (σ := unitaryInvolution F 2 f) Q I).map E.toMonoidHom =
      TableBUE.blockSU (K := F) (n := f) I := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (u : SU (unitaryInvolution F 2 f) (m + 1)) ∈ suBlock Q I at hu
      rw [TableBUE.mem_blockSU]
      change TableBUE.IsBlockOn I
        (((E u : ↥(unitarySU 2 f F (m + 1))) : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      have hcoe : ((E u : ↥(unitarySU 2 f F (m + 1))) : GL (Fin (m + 1)) F) =
          Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ := by
        have h1 := SURep.coe_ggFrameEquiv_symm hF Q hQ (E u)
        rw [MulEquiv.symm_apply_apply] at h1
        calc
          ((E u : ↥(unitarySU 2 f F (m + 1))) : GL (Fin (m + 1)) F) =
              Q * (Q⁻¹ * ((E u : ↥(unitarySU 2 f F (m + 1))) :
                GL (Fin (m + 1)) F) * Q) * Q⁻¹ := by group
          _ = Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ := by rw [← h1]
      rw [hcoe]
      exact mem_glBlock.mp (mem_suBlock.mp hu)
    · intro hx
      refine ⟨E.symm x, ?_, ?_⟩
      · change (E.symm x : SU (unitaryInvolution F 2 f) (m + 1)) ∈ suBlock Q I
        rw [mem_suBlock]
        have hcoe : ((x : ↥(unitarySU 2 f F (m + 1))) : GL (Fin (m + 1)) F) =
            Q * ((E.symm x : SU (unitaryInvolution F 2 f) (m + 1)) :
              GL (Fin (m + 1)) F) * Q⁻¹ := by
          have h1 := SURep.coe_ggFrameEquiv_symm hF Q hQ x
          rw [h1]
          group
        rw [← hcoe]
        exact mem_glBlock.mpr (TableBUE.mem_blockSU.mp hx)
      · exact E.apply_symm_apply x
  dsimp only [uFrameBlock]
  rw [← hEblock, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, SURep.ggFrameU, MulEquiv.coe_toMonoidHom]
  rw [MulEquiv.symm_apply_apply]

theorem isQuasisimple_or_isSolvable_uFrameBlock
    (hf : 1 ≤ f) (hF : Nat.card F = (2 ^ f) ^ 2)
    {ψ : SU (unitaryInvolution F 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 1)))
    {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame (unitaryInvolution F 2 f) Q)
    {I : Finset (Fin (m + 1))} (hI : 2 ≤ I.card) :
    Assembly.IsQuasisimple (uFrameBlock ψ Q I) ∨
      Group.IsSolvable ↥(uFrameBlock ψ Q I) := by
  classical
  let φ := SURep.ggFrameU hF ψ Q hQ
  have hkerφ : φ.ker ≤ Subgroup.center (↥(unitarySU 2 f F (m + 1))) :=
    SURep.ker_ggFrameU_le hF ψ Q hQ hker
  have hKd : UnitaryFieldData 2 f F := TableBU.unitaryFieldData_of_card hF hf
  rw [uFrameBlock_eq_map_blockSU hF hQ I]
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · have hf_eq : f = 1 := by omega
    subst hf_eq
    by_cases h4 : I.card ≤ 3
    · right
      exact WitSU.isSolvable_map_blockSU_two_one hKd φ (S := I) (by omega) h4
    · left
      exact SUTorus.isQuasisimple_map_blockSU hKd hkerφ (by omega) (by
        intro h
        have := congrArg Prod.fst h
        omega)
  · left
    by_cases h2 : I.card = 2
    · exact SURepair.isQuasisimple_map_blockSU_of_two_le hKd hf2 hkerφ (by omega)
    · exact SUTorus.isQuasisimple_map_blockSU hKd hkerφ (by omega) (by
        intro h
        have h2pow : 2 ^ f = 2 := (Prod.ext_iff.mp h).2
        have hle : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
        omega)

theorem eq_uFrameBlock_of_isComponentOf_of_class
    [Finite G]
    (hf : 1 ≤ f) (hF : Nat.card F = (2 ^ f) ^ 2)
    {ψ : SU (unitaryInvolution F 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 1)))
    {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame (unitaryInvolution F 2 f) Q)
    {S : Set G} (hS : S ⊆ uFrameTorus ψ Q)
    {L₁ : Subgroup G}
    (hL : Assembly.IsComponentOf L₁
      (ψ.range ⊓ Subgroup.centralizer S))
    (a : Fin (m + 1))
    (hle : L₁ ≤ uFrameBlock ψ Q (uClass ψ Q S a)) :
    L₁ = uFrameBlock ψ Q (uClass ψ Q S a) ∧
      (∀ g ∈ S, ∃ e : Fin (m + 1) → Fˣ,
        (g, LinFusion.ggFrameDiag Q e) ∈ suInducedPairs ψ ∧
          ∀ i ∈ uClass ψ Q S a, ∀ j ∈ uClass ψ Q S a, e i = e j) := by
  classical
  let C₀ := (frameCent Q (inducedDiag ψ Q S)).map ψ
  let B := uFrameBlock ψ Q (uClass ψ Q S a)
  have hLC₀ : L₁ ≤ C₀ := by
    rw [← LinSemisimple.commutator_eq_self_of_isQuasisimple hL.2.2]
    exact (Subgroup.commutator_mono hL.1 hL.1).trans (commutator_le_map_frameCent hker)
  have hcomp : Assembly.IsComponentOf L₁ C₀ :=
    isComponentOf_of_le hL hLC₀ (map_frameCent_le hS)
  have hBle : B ≤ C₀ := Subgroup.map_mono (suBlock_uClass_le_frameCent a)
  by_cases hcard1 : (uClass ψ Q S a).card ≤ 1
  · exfalso
    have hbot : B = ⊥ := uFrameBlock_eq_bot_of_card_le_one ψ Q hcard1
    have hLbot : L₁ = ⊥ := le_bot_iff.mp (hle.trans_eq hbot)
    have hLsol : Group.IsSolvable ↥L₁ := by
      rw [hLbot]
      infer_instance
    have hLq_native : CFSG.IsQuasisimple ↥L₁ :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hL.2.2
    exact not_isSolvable_of_isQuasisimple hLq_native hLsol
  · have hI : 2 ≤ (uClass ψ Q S a).card := by omega
    rcases isQuasisimple_or_isSolvable_uFrameBlock hf hF hker hQ hI with hq | hsol
    · have hBcomp : Assembly.IsComponentOf B C₀ :=
        ⟨hBle, Assembly.IsSubnormal.step hBle
          (normal_subgroupOf_uFrameBlock_uClass (ψ := ψ) (Q := Q) (S := S) a)
          (Assembly.IsSubnormal.refl C₀), hq⟩
      have hEq : L₁ = B := eq_of_isComponentOf_le hcomp hBcomp hle
      refine ⟨hEq, fun g hg => ?_⟩
      obtain ⟨e, he⟩ := hS hg
      exact ⟨e, he, const_on_uClass hg he a⟩
    · exfalso
      have hsolI : Group.IsSolvable ↥B := hsol
      have hLsol : Group.IsSolvable ↥L₁ :=
        Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
      have hLq_native : CFSG.IsQuasisimple ↥L₁ :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hL.2.2
      exact not_isSolvable_of_isQuasisimple hLq_native hLsol

theorem exists_eq_uFrameBlock_of_isComponentOf [Finite G]
    (hf : 1 ≤ f) (hF : Nat.card F = (2 ^ f) ^ 2)
    {ψ : SU (unitaryInvolution F 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 1)))
    {Q : GL (Fin (m + 1)) F}
    (hQ : IsUFrame (unitaryInvolution F 2 f) Q)
    {ζ : Fˣ} (hζ1 : ζ ≠ 1)
    (hζσ : (unitaryInvolution F 2 f) (ζ : F) * ζ = 1)
    {S : Set G} (hS : S ⊆ uFrameTorus ψ Q)
    {L₁ : Subgroup G}
    (hL : Assembly.IsComponentOf L₁
      (ψ.range ⊓ Subgroup.centralizer S)) :
    ∃ a : Fin (m + 1),
      L₁ = uFrameBlock ψ Q (uClass ψ Q S a) ∧
        (∀ g ∈ S, ∃ e : Fin (m + 1) → Fˣ,
          (g, LinFusion.ggFrameDiag Q e) ∈ suInducedPairs ψ ∧
            ∀ i ∈ uClass ψ Q S a, ∀ j ∈ uClass ψ Q S a, e i = e j) := by
  obtain ⟨a, hle⟩ :=
    exists_le_uClass_of_isComponentOf hker hQ hζ1 hζσ hS hL
  obtain ⟨hEq, hconst⟩ :=
    eq_uFrameBlock_of_isComponentOf_of_class hf hF hker hQ hS hL a hle
  exact ⟨a, hEq, hconst⟩

end UFusion

end CFSG.StandardType

end
