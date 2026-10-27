module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionLang
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6InnerBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInner

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType.TwE6CorootCore

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot
  CFSG.StandardType.TableBExcTwo CFSG.StandardType.TableBExcTwoFusion CFSG.RankThree.Chevalley

local instance twE6CorootCoreFrameNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

theorem list_prod_ofFn_mul_eq {G : Type*} [Group G] :
    ∀ {n : ℕ} (f : Fin n → G) (i : Fin n) {x y : G}, f i * x = y * f i →
      (∀ j, j ≠ i → Commute (f j) x ∧ Commute (f j) y) →
        (List.ofFn f).prod * x = y * (List.ofFn f).prod
  | 0, _, i, _, _, _, _ => i.elim0
  | n + 1, f, i, x, y, hi, hj => by
    rw [List.ofFn_succ, List.prod_cons]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · have hR : Commute (List.ofFn fun j : Fin n => f j.succ).prod x :=
        Commute.list_prod_left _ _ fun z hz => by
          obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hz
          exact (hj j.succ (Fin.succ_ne_zero j)).1
      rw [mul_assoc, hR.eq, ← mul_assoc, hi, mul_assoc]
    · have ih := list_prod_ofFn_mul_eq (fun j : Fin n => f j.succ) i hi
        fun j hji => hj j.succ fun e => hji (Fin.succ_injective _ e)
      rw [mul_assoc, ih, ← mul_assoc, (hj 0 (Fin.succ_ne_zero i).symm).2.eq, mul_assoc]

@[expose] def corootFrameRoot : Fin 4 → (Fin Tag.E6.rank → ℤ) :=
  ![![1, 2, 2, 3, 2, 1], ![1, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 0, 0]]

theorem corootFrameRoot_mem : ∀ i, corootFrameRoot i ∈ rootFinset .E6 := by decide +kernel

theorem corootFrameRoot_orth : ∀ i j, i ≠ j →
    iform (corootFrameRoot i) (corootFrameRoot j) = 0 := by
  decide +kernel

theorem permLattice_corootFrameRoot : ∀ i : Fin 4,
    @Eq (Fin Tag.E6.rank → ℤ) (permLattice TwistTag.E6.perm (corootFrameRoot i))
      (corootFrameRoot i) := by
  decide +kernel

theorem coPair_corootFrameRoot : ∀ i : Fin 4,
    coPair .E6 0 (corootFrameRoot i) = coPair .E6 5 (corootFrameRoot i) ∧
      coPair .E6 2 (corootFrameRoot i) = coPair .E6 4 (corootFrameRoot i) := by
  decide +kernel

theorem corootFrameRoot_apply_one : ∀ i : Fin 4, i ≠ 0 → corootFrameRoot i 1 = 0 := by decide

section Frame


@[expose] def corootFrame : OrthFrame .E6 3 where
  root := corootFrameRoot
  symm_one := fun i => by simp [Tag.symmetrizer]
  isRoot := fun i => mem_rootFinset.1 (corootFrameRoot_mem i)
  orth := corootFrameRoot_orth

end Frame


section Product

variable {τ : Tag} {d : ℕ} {L : Type} [Field L]

theorem coe_frameProd (F : OrthFrame τ d) (A : SL2 L) :
    ((frameProd L F A : adjointGroup τ L) : ModGL τ L) =
      (List.ofFn fun i => rootSL2 τ L (F.root i) A).prod := by
  rw [frameProd, SubmonoidClass.coe_list_prod, List.map_ofFn]
  rfl

theorem frameProd_mul_rootSL2 (F : OrthFrame τ d) (i : Fin (d + 1)) (A B : SL2 L) :
    (frameProd L F A : ModGL τ L) * rootSL2 τ L (F.root i) (A⁻¹ * B * A) =
      rootSL2 τ L (F.root i) B * (frameProd L F A : ModGL τ L) := by
  rw [coe_frameProd]
  refine list_prod_ofFn_mul_eq _ i ?_ fun j hj =>
    ⟨commute_rootSL2 F hj A _, commute_rootSL2 F hj A B⟩
  rw [← map_mul, ← map_mul]
  congr 1
  group

end Product

variable {K : Type} [Field K]

theorem commute_rootSL2_rootDiagUnit {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    {a : Fin Tag.E6.rank → Kˣ} (ha : rootChar a β = 1) (M : SL2 K) :
    Commute (rootSL2 .E6 K β M) (rootDiagUnit .E6 a) := by
  have e := rootDiagUnit_conj_rootSL2 a hβ M
  rw [ha, conjSL_diagUnitOne_one] at e
  exact (mul_inv_eq_iff_eq_mul.1 e).symm

theorem commute_frameProd_rootDiagUnit {a : Fin Tag.E6.rank → Kˣ}
    (ha : ∀ i, rootChar a (corootFrameRoot i) = 1) (P : SL2 K) :
    Commute (frameProd K corootFrame P : ModGL .E6 K) (rootDiagUnit .E6 a) := by
  rw [coe_frameProd]
  exact Commute.list_prod_left _ _ fun z hz => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
    exact commute_rootSL2_rootDiagUnit (corootFrame.isRoot i) (ha i) P

theorem twistHom_rootSL2_of_perm [CharP K 2] (σ : K →+* K) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (hρβ : permLattice TwistTag.E6.perm β = β) (B : SL2 K) :
    twistHom TwistTag.E6 K σ (rootSL2 TwistTag.E6.tag K β B) =
      rootSL2 TwistTag.E6.tag K β (Matrix.SpecialLinearGroup.map σ B) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h := MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower
    (f := (twistHom TwistTag.E6 K σ).comp (rootSL2 TwistTag.E6.tag K β))
    (g := (rootSL2 TwistTag.E6.tag K β).comp (Matrix.SpecialLinearGroup.map σ)) (by
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change twistHom TwistTag.E6 K σ (rootSL2 TwistTag.E6.tag K β (uSL c)) =
          rootSL2 TwistTag.E6.tag K β (Matrix.SpecialLinearGroup.map σ (uSL c))
        rw [E6GraphLevi.map_uSL, rootSL2_uSL_of_charTwo hβ, rootSL2_uSL_of_charTwo hβ,
          twistHom_pinnedX_eq_of_charTwo h2 σ hβ, hρβ]
      · change twistHom TwistTag.E6 K σ (rootSL2 TwistTag.E6.tag K β (vSL c)) =
          rootSL2 TwistTag.E6.tag K β (Matrix.SpecialLinearGroup.map σ (vSL c))
        rw [E6GraphLevi.map_vSL, rootSL2_vSL_of_charTwo hβ, rootSL2_vSL_of_charTwo hβ,
          twistHom_pinnedX_eq_of_charTwo h2 σ (IsRoot.neg hβ), permLattice_neg, hρβ])
  exact DFunLike.congr_fun h B

theorem rootSL2_mem_subsystemGroup_setA {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (h1 : β 1 = 0) (M : SL2 K) :
    rootSL2 .E6 K β M ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
  have hneg : (-β) 1 = 0 := by rw [Pi.neg_apply, h1, neg_zero]
  have hle : rootSubgroup .E6 K β ⊔ rootSubgroup .E6 K (-β) ≤
      subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA :=
    sup_le ((le_iSup₂_of_le β ⟨hβ, h1⟩ le_rfl :
        rootSubgroup .E6 K β ≤ rootSpan .E6 K (EPilot.perpRoots .E6)).trans
        rootSpan_perpRoots_le_subsystemGroup)
      ((le_iSup₂_of_le (-β) ⟨IsRoot.neg hβ, hneg⟩ le_rfl :
        rootSubgroup .E6 K (-β) ≤ rootSpan .E6 K (EPilot.perpRoots .E6)).trans
        rootSpan_perpRoots_le_subsystemGroup)
  exact hle (by rw [← range_rootSL2_of_isRoot hβ]; exact ⟨M, rfl⟩)

theorem rootSL2_frame_mem_su6Levi {f : ℕ} {k : Type} [Field k] [Algebra k K] (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {i : Fin 4} (hi : i ≠ 0) (B : SL2 k) :
    rootSL2 .E6 K (corootFrameRoot i) (Matrix.SpecialLinearGroup.map (algebraMap k K) B) ∈
      su6Levi σ := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP K 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hK
  have hβ : IsRoot TwistTag.E6.tag (corootFrameRoot i) := corootFrame.isRoot i
  have hsub := rootSL2_mem_subsystemGroup_setA hβ (corootFrameRoot_apply_one i hi)
    (Matrix.SpecialLinearGroup.map (algebraMap k K) B)
  rw [(su6Levi_facts hf hk hK hσ).2.2.2.2.1]
  refine ⟨hsub, (mem_twistedFixedGroup_iff_twistHom _ _ _).2
    ⟨E6GraphLevi.subsystemGroup_le_adjointGroup hsub, ?_⟩⟩
  have hσB : Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map (algebraMap k K) B) =
      Matrix.SpecialLinearGroup.map (algebraMap k K) B := by
    ext a b
    simp [E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card hk hσ)]
  calc twistHom TwistTag.E6 K σ (rootSL2 TwistTag.E6.tag K (corootFrameRoot i)
        (Matrix.SpecialLinearGroup.map (algebraMap k K) B)) =
        rootSL2 TwistTag.E6.tag K (corootFrameRoot i)
          (Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map (algebraMap k K) B)) :=
        twistHom_rootSL2_of_perm σ hβ (permLattice_corootFrameRoot i) _
    _ = _ := by rw [hσB]; rfl

end CFSG.StandardType.TwE6CorootCore

end
