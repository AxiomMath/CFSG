module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltLayer

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGLieParabolicCharInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → d.1.characteristic ≠ 2 →
      ∀ S X : Subgroup K, IsPGroup d.1.characteristic S → ¬ d.1.characteristic ∣ S.index →
        Subgroup.normalizer (S : Set K) ≤ X → X ≠ ⊤ → IsCharacteristicP d.1.characteristic ↥X

@[expose] def GGLieOuterFieldAutInput : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (E : Subgroup W) (d : TauCeti.ValidLieTypeIndex),
    IsSimpleGroup ↥(CFSG.generalizedFitting W) →
      (∃ a b : ↥(CFSG.generalizedFitting W), a * b ≠ b * a) →
        Nonempty (↥(CFSG.generalizedFitting W) ≃* (TauCeti.CFSGIndex.lie d).Group) →
          d.1.characteristic ≠ 2 → IsElemAbelian d.1.characteristic E →
            Nat.card E = d.1.characteristic ^ 2 → E ⊓ CFSG.generalizedFitting W = ⊥ →
              ∃ e ∈ E, e ≠ 1 ∧ ∀ Y : Subgroup W, Y ≤ CFSG.generalizedFitting W →
                Subgroup.centralizer ({e} : Set W) ⊓ CFSG.generalizedFitting W ≤ Y →
                  ¬ d.1.characteristic ∣ Y.relIndex (CFSG.generalizedFitting W) →
                    Y = CFSG.generalizedFitting W

section Inner

variable {W : Type} [Group W]

@[expose] def ggSubgroupOfEquivKer (H K : Subgroup W) [K.Normal] :
    ↥(H.subgroupOf K) ≃* ↥((QuotientGroup.mk' K).comp H.subtype).ker where
  toFun x := ⟨⟨((x : K) : W), Subgroup.mem_subgroupOf.mp x.2⟩,
    (ggMem_ker_mk_comp_subtype _).mpr (x : K).2⟩
  invFun y := ⟨⟨((y : H) : W), (ggMem_ker_mk_comp_subtype _).mp y.2⟩,
    Subgroup.mem_subgroupOf.mpr (y : H).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem ggMem_normalizer_of_mem_normalizer_subgroupOf {S K : Subgroup W} (hSK : S ≤ K)
    {k : ↥K} (hk : k ∈ Subgroup.normalizer ((S.subgroupOf K : Subgroup K) : Set K)) :
    (k : W) ∈ Subgroup.normalizer (S : Set W) := by
  have h : (k : W) ∈ (Subgroup.normalizer ((S.subgroupOf K : Subgroup K) : Set K)).map
      K.subtype := Subgroup.mem_map_of_mem _ hk
  rw [CFSG.LocalAnalysis.ComponentInitial.map_normalizer_subgroupOf hSK] at h
  exact h.1

variable [Finite W]

theorem ggKGroupFusionDefiningInnerInput_of_parabolic
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hpar : GGLieParabolicCharInput) : GGKGroupFusionDefiningInnerInput := by
  intro W _ _ p H E d hpd hyp hL hKH he _ S hSK hSp hSidx _ hNH
  exfalso
  apply hL
  have hKn : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have hp : p.Prime := hyp.1.1
  have hp2 : p ≠ 2 := hyp.1.2.1
  have hX : IsCharacteristicP p ↥(H.subgroupOf (CFSG.generalizedFitting W)) := by
    subst hpd
    refine hpar _ d he hp2 (S.subgroupOf (CFSG.generalizedFitting W))
      (H.subgroupOf (CFSG.generalizedFitting W)) ?_ hSidx ?_ ?_
    · exact hSp.comap_of_injective _ (CFSG.generalizedFitting W).subtype_injective
    · intro k hk
      exact Subgroup.mem_subgroupOf.mpr (hNH (ggMem_normalizer_of_mem_normalizer_subgroupOf hSK hk))
    · intro htop
      exact hKH (Subgroup.subgroupOf_eq_top.mp htop)
  have hN := CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
    (ggSubgroupOfEquivKer H (CFSG.generalizedFitting W)) hX
  exact ggLayer_quot_pCore_two_eq_bot hp hp2 _ (ggIsSolvable_quot_inf_generalizedFitting hSch hyp)
    hN

end Inner

section Outer

variable {W : Type} [Group W] [Finite W]

theorem GGControlsStrongFusion.not_dvd_relIndex_inf {p : ℕ} [Fact p.Prime] {H E : Subgroup W}
    (h : GGControlsStrongFusion H E) (hE : IsElemAbelian p E) {e : W} (he : e ∈ E) (he1 : e ≠ 1)
    (K : Subgroup W) [K.Normal] : ¬ p ∣ (H ⊓ K).relIndex K := by
  obtain ⟨R, hRHK, -, hR⟩ := h.exists_sylow_le hE he he1
    (Subgroup.le_normalizer_of_normal (H := K) (Subgroup.mem_top e))
  intro hdvd
  apply hR
  rw [← Subgroup.relIndex_mul_relIndex R (H ⊓ K) K hRHK inf_le_right]
  exact Dvd.dvd.mul_left hdvd _

theorem ggKGroupFusionDefiningOuterInput_of_fieldAut (hout : GGLieOuterFieldAutInput) :
    GGKGroupFusionDefiningOuterInput := by
  intro W _ _ p H E d hpd hyp _ hKH he hEK
  exfalso
  have hKn : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  obtain ⟨⟨hp, hp2, hE, hEcard, hfus⟩, ⟨hsimple, hnab, -⟩, -⟩ := hyp
  have : Fact p.Prime := ⟨hp⟩
  subst hpd
  obtain ⟨e, heE, he1, hmax⟩ := hout W E d hsimple hnab he hp2 hE hEcard hEK
  apply hKH
  have hY := hmax (H ⊓ CFSG.generalizedFitting W) inf_le_right
    (inf_le_inf_right _ (hfus.centralizer_le heE he1))
    (hfus.not_dvd_relIndex_inf hE heE he1 _)
  exact hY ▸ inf_le_left

end Outer

theorem ggKGroupFusionAt_lieDefining_of_inputs
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hpar : GGLieParabolicCharInput) (hout : GGLieOuterFieldAutInput) :
    GGKGroupFusionAt GGKFLieDefining :=
  ggKGroupFusionAt_lieDefining_of (ggKGroupFusionDefiningInnerInput_of_parabolic hSch hpar)
    (ggKGroupFusionDefiningOuterInput_of_fieldAut hout)

end CFSG.StandardType
