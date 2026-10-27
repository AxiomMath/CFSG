module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotKindsX

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def HR8FieldKind (t : G) (N D : Subgroup G) : Prop :=
  ∃ htN : t ∈ centralizer (N : Set G),
    ∃ Kc : Subgroup (centralizer (N : Set G) ⧸ oddCore (centralizer (N : Set G))),
      IsComponent Kc ∧
      ⁅(D.subgroupOf (centralizer (N : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (N : Set G)))), Kc⁆ ≠ ⊥ ∧
      Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (N : Set G))) ⟨t, htN⟩)).toMonoidHom = Kc

@[expose] def HR8SwapKind (t : G) (N D : Subgroup G) : Prop :=
  ∃ htN : t ∈ centralizer (N : Set G),
    ∃ Kc : Subgroup (centralizer (N : Set G) ⧸ oddCore (centralizer (N : Set G))),
      IsComponent Kc ∧
      (D.subgroupOf (centralizer (N : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (N : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj
          (QuotientGroup.mk' (oddCore (centralizer (N : Set G))) ⟨t, htN⟩)).toMonoidHom ∧
      Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (N : Set G))) ⟨t, htN⟩)).toMonoidHom ≠ Kc ∧
      ⁅Kc, Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (N : Set G))) ⟨t, htN⟩)).toMonoidHom⁆ = ⊥ ∧
      center Kc = ⊥ ∧
      Nonempty (Kc ≃* (D.subgroupOf (centralizer (N : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (N : Set G)))))

theorem mk_mem_centralizer_map_subgroupOf_2E6 {N D : Subgroup G} {t : G}
    (htN : t ∈ centralizer (N : Set G)) (hDt : D ≤ centralizer ({t} : Set G)) :
    QuotientGroup.mk' (oddCore (centralizer (N : Set G))) ⟨t, htN⟩ ∈
      centralizer (((D.subgroupOf (centralizer (N : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (N : Set G)))) : Subgroup _) :
        Set (centralizer (N : Set G) ⧸ oddCore (centralizer (N : Set G)))) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨d, hd, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))

theorem mk_mul_self_eq_one_2E6 {N : Subgroup G} {t : G} (htN : t ∈ centralizer (N : Set G))
    (ht : orderOf t = 2) :
    QuotientGroup.mk' (oddCore (centralizer (N : Set G))) ⟨t, htN⟩ *
      QuotientGroup.mk' (oddCore (centralizer (N : Set G))) ⟨t, htN⟩ = 1 := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  rw [← map_mul, show (⟨t, htN⟩ : centralizer (N : Set G)) * ⟨t, htN⟩ = 1 from
    Subtype.ext htt, map_one]

end Defs

section Seitz

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.UnitaryPilot (SUmNotOddLieInputAt)
open CFSG.SeitzReduction.OmegaPilot (OmegaNotOddLieInputAt)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem hr8FieldKind_or_hr8SwapKind_X (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : SUmNotOddLieInputAt 6) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    HR8FieldKind t (modelToG e (E6GraphLevi.thetaTorus (algebraMap k K)))
        (modelToG e (su6Levi σ)) ∨
      HR8SwapKind t (modelToG e (E6GraphLevi.thetaTorus (algebraMap k K)))
        (modelToG e (su6Levi σ)) := by
  have hf : 1 ≤ f := by omega
  have : CharP K 2 := charP_two_of_card hf hK
  have htX : t ∈ centralizer ((modelToG e (E6GraphLevi.thetaTorus (algebraMap k K)) :
      Subgroup G) : Set G) := centralizer_le (SetLike.coe_subset_coe.2 (modelToG_le e _)) htC
  have hDt : modelToG e (su6Levi σ) ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (modelToG_le e _ hd))
  obtain ⟨⟨Kc, hKc, hDKK, hrow⟩, -⟩ := neighbour_overgroup_2E6_X hGLS hXodd hMinn hMcomp hset hf2
    hk hK hσ e htC ht (twistedFusionIn_xiAut hf2 hk hK σ hσ)
    (X := modelToG e (E6GraphLevi.thetaTorus (algebraMap k K))) rfl htX
    (D := modelToG e (su6Levi σ)) rfl
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_2E6_X hset hf2 hk hK hσ e htC ht
    (X := modelToG e (E6GraphLevi.thetaTorus (algebraMap k K))) rfl htX
    (D := modelToG e (su6Levi σ)) rfl
  obtain ⟨h1, -⟩ := commutator_ne_bot_of_le_sup_conj (mk_mul_self_eq_one_2E6 htX ht) hDKK
    (mk_mem_centralizer_map_subgroupOf_2E6 htX hDt)
    (commutator_eq_self_of_isQuasisimple' hcomp.2.2) (ne_bot_of_isQuasisimple hcomp.2.2)
  rcases hrow with ⟨hKt, -⟩ | ⟨hne, hcomm, hZ, hφ⟩
  · exact Or.inl ⟨htX, Kc, hKc, by rw [commutator_comm]; exact h1, hKt⟩
  · exact Or.inr ⟨htX, Kc, hKc, hDKK, hne, hcomm, hZ, hφ⟩

theorem hr8FieldKind_or_hr8SwapKind_Y (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    HR8FieldKind t (modelToG e (shortRootTorus (algebraMap k K))) (modelToG e (omegaMinusLevi σ)) ∨
      HR8SwapKind t (modelToG e (shortRootTorus (algebraMap k K)))
        (modelToG e (omegaMinusLevi σ)) := by
  have hf : 1 ≤ f := by omega
  have : CharP K 2 := charP_two_of_card hf hK
  obtain ⟨⟨htY, -, hall, -⟩, Kc, hKc, hDK⟩ := exists_isComponent_2E6_Y_of_leafInputs hGLS hXodd
    hMinn hMcomp hset hf2 hk hK hσ e htC ht (X := modelToG e (shortRootTorus (algebraMap k K)))
    rfl (D := modelToG e (omegaMinusLevi σ)) rfl
  obtain ⟨hDKK, ⟨hKt, -⟩ | ⟨hne, hcomm, hZ, hφ⟩⟩ := hall Kc hKc hDK
  · exact Or.inl ⟨htY, Kc, hKc, hDK, hKt⟩
  · exact Or.inr ⟨htY, Kc, hKc, hDKK, hne, hcomm, hZ, hφ⟩

theorem not_hr8FieldKind_Y_of_hr8SwapKind_X (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hX : HR8SwapKind t (modelToG e (E6GraphLevi.thetaTorus (algebraMap k K)))
      (modelToG e (su6Levi σ))) :
    ¬ HR8FieldKind t (modelToG e (shortRootTorus (algebraMap k K)))
      (modelToG e (omegaMinusLevi σ)) := by
  rintro ⟨htY, KY, hKY, hDKY, hKtY⟩
  obtain ⟨htX, Kc, hKc, hDKK, hne, hcomm, hZ, hφ⟩ := hX
  exact false_of_swap_X_of_field_Y hGLS hXodd hMinn hMcomp hset hf2 hk hK hσ e htC ht rfl htX rfl
    hKc hDKK hne hcomm hZ hφ rfl htY rfl hKY hDKY hKtY

theorem not_hr8SwapKind_Y_of_hr8FieldKind_X (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : SUmNotOddLieInputAt 6) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hX : HR8FieldKind t (modelToG e (E6GraphLevi.thetaTorus (algebraMap k K)))
      (modelToG e (su6Levi σ))) :
    ¬ HR8SwapKind t (modelToG e (shortRootTorus (algebraMap k K)))
      (modelToG e (omegaMinusLevi σ)) := by
  rintro ⟨htY, KY, hKY, hDKY, hneY, hcommY, -, hφY⟩
  obtain ⟨htX, Kc, hKc, hDKc, hKt⟩ := hX
  exact false_of_field_X_of_swap_Y hGLS hXodd hMinn hMcomp hset hf2 hk hK hσ e htC ht rfl htX rfl
    hKc hDKc hKt rfl htY rfl hKY hDKY hneY hcommY hφY

theorem kinds_2E6 (hGLS : GLS3OddLieAutComponentsInput) (hSU : SUmNotOddLieInputAt 6)
    (hOm : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    (HR8FieldKind t (modelToG e (E6GraphLevi.thetaTorus (algebraMap k K)))
          (modelToG e (su6Levi σ)) ∧
        HR8FieldKind t (modelToG e (shortRootTorus (algebraMap k K)))
          (modelToG e (omegaMinusLevi σ))) ∨
      (HR8SwapKind t (modelToG e (E6GraphLevi.thetaTorus (algebraMap k K)))
          (modelToG e (su6Levi σ)) ∧
        HR8SwapKind t (modelToG e (shortRootTorus (algebraMap k K)))
          (modelToG e (omegaMinusLevi σ))) := by
  rcases hr8FieldKind_or_hr8SwapKind_X hGLS hSU hMinn hMcomp hset hf2 hk hK hσ e htC ht with
    hX | hX <;>
  rcases hr8FieldKind_or_hr8SwapKind_Y hGLS hOm hMinn hMcomp hset hf2 hk hK hσ e htC ht with
    hY | hY
  · exact Or.inl ⟨hX, hY⟩
  · exact (not_hr8SwapKind_Y_of_hr8FieldKind_X hGLS hSU hMinn hMcomp hset hf2 hk hK hσ e htC ht
      hX hY).elim
  · exact (not_hr8FieldKind_Y_of_hr8SwapKind_X hGLS hOm hMinn hMcomp hset hf2 hk hK hσ e htC ht
      hX hY).elim
  · exact Or.inr ⟨hX, hY⟩

theorem fieldRowData_2E6 (hGLS : GLS3OddLieAutComponentsInput) (hSU : SUmNotOddLieInputAt 6)
    (hOm : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hX : HR8FieldKind t (modelToG e (E6GraphLevi.thetaTorus (algebraMap k K)))
      (modelToG e (su6Levi σ)))
    (hY : HR8FieldKind t (modelToG e (shortRootTorus (algebraMap k K)))
      (modelToG e (omegaMinusLevi σ))) :
    Nonempty (FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) e t
        (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .X))) ∧
      Nonempty (FieldNeighbourIso2E6 e t
        (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .Y))
        (subsystemGroup TwistTag.E6.tag K C2E6Std.setD) (d4LeviTwist (apply_apply_eq hK hσ))
        (omegaMinusLevi σ)) := by
  obtain ⟨htX, Kc, hKc, hDKc, hKt⟩ := hX
  obtain ⟨htY, KY, hKY, hDKY, hKtY⟩ := hY
  rw [(neighbourTorus_X_Y (algebraMap k K)).1, (neighbourTorus_X_Y (algebraMap k K)).2]
  exact ⟨nonempty_fieldCoverParamX_2E6_of_leafInputs hGLS hSU hMinn hMcomp hset hf2 hk hK hσ e htC
      ht rfl htX rfl hKc hDKc hKt,
    nonempty_fieldNeighbourIso2E6_Y_of_leafInputs' hGLS hOm hMinn hMcomp hset hf2 hk hK hσ e htC
      ht rfl htY rfl hKY hDKY hKtY⟩

end Seitz

end CFSG.SeitzReduction.TwistedE6Pilot
