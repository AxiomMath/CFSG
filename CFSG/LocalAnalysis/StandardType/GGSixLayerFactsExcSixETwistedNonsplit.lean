module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixENonsplit
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandard

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.SeitzReduction CFSG.LieType.Chevalley.E6GraphLevi

section Defs

@[expose] def GGTwE6InndiagHighNonsplit
    (f : ℕ) (A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Algebra k (GaloisField 2 (2 * f))), Nat.card k = 2 ^ f ∧
    ∃ (g : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (X : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))),
      X ≤ thetaRankOneGroup (algebraMap k (GaloisField 2 (2 * f))) ∧ IsCyclic X ∧
        Nat.card X = 2 ^ f + 1 ∧
          A = ((X.subgroupOf (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
            (frobQ 2 f))).map (MulAut.conj g⁻¹).toMonoidHom).map MulAut.conj

end Defs

section Nonsplit


theorem LayerSixE.exists_subCoreFamily_autFix_highNonsplit_twistedE6 {f : ℕ} (hf : 1 ≤ f)
    (A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))) (h : GGTwE6InndiagHighNonsplit f A) :
    ∃ (β : Type) (S : β → Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))), LayerCores.IsSubCoreFamily (autFix A) S := by
  obtain ⟨k, _, _, hk, g, X, hXJ, hcyc, hX, rfl⟩ := h
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  rw [autFix_map_conj]
  refine LayerExc.exists_subCoreFamily_centralizer_of_conj g _ ?_
  have hmap : ((X.subgroupOf (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = X.subgroupOf (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id (X.subgroupOf (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    refine MonoidHom.ext fun x => ?_
    change g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
    group
  rw [hmap]
  obtain ⟨hC, -, hXD, hXC⟩ := TwistedE6Pilot.centralizer_nonsplit_twistedE6 hf hk hK hσ hXJ hX hcyc
  rw [TwistedE6Pilot.centralizer_subgroupOf_eq_sup hXC hXC
    (TwistedE6Pilot.su6Levi_le_graphFixedRootGroup _) hC]
  have : IsSimpleGroup (TwistedE6Pilot.su6Levi (frobQ 2 f)) :=
    TwistedE6Pilot.isSimpleGroup_su6Levi (k := k) hf hk hK hσ
  have hq := TwistedE6Pilot.isQuasisimple_su6Levi_subgroupOf (k := k) hf hk hK hσ
  have hZ : Subgroup.center ((TwistedE6Pilot.su6Levi (frobQ 2 f)).subgroupOf (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) = ⊥ := by
    have hnc : ∃ a b : TwistedE6Pilot.su6Levi (frobQ 2 f), a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      have := TwistedE6Pilot.isPerfect_su6Levi (k := k) hf hk hK hσ
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hc a b⟩⟩
    exact F4Pilot.center_eq_bot_congr
      (Subgroup.subgroupOfEquivOfLe (TwistedE6Pilot.su6Levi_le_graphFixedRootGroup _)).symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2
  refine ⟨Unit, fun _ => (TwistedE6Pilot.su6Levi (frobQ 2 f)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
    LayerExc.isSubCoreFamily_sup_of_centralizer (fun a ha b hb => Subtype.ext ?_) ?_ hq hZ⟩
  · exact LayerExc.commute_of_isCyclic hcyc _ ha _ hb
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_iff.mp (hXD hx) d hd

@[expose] def GGTwE6InndiagCoreRestInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))), IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
        A ≤ LayerSixE.twInndiagAut f → ¬ GGTwE6InndiagHighNonsplit f A →
          ∃ (β : Type) (S : β → Subgroup ↥(graphFixedRootGroup TwistTag.E6
            (GaloisField 2 (2 * f)) (frobQ 2 f))), LayerCores.IsSubCoreFamily (LayerSixE.autFix A) S

theorem ggTwE6InndiagCoreInput_of_rest (h : GGTwE6InndiagCoreRestInput) :
    GGTwE6InndiagCoreInput := by
  intro f hf p hp hp2 A hA hAc hAD
  by_cases hn : GGTwE6InndiagHighNonsplit f A
  · exact LayerSixE.exists_subCoreFamily_autFix_highNonsplit_twistedE6 hf A hn
  · exact h f hf p hp hp2 A hA hAc hAD hn

theorem ggLayerTags_twistedE6_of_rest (h : GGTwE6InndiagCoreRestInput) :
    GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6 :=
  ggLayerTags_twistedE6_of_inndiagCore (ggTwE6InndiagCoreInput_of_rest h)

end Nonsplit

end CFSG.StandardType
