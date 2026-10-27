module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotKindsBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYRigid
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYLeaf
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapNormalize

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

local instance twistedE6PilotKindsYNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotKindsYNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Levi


variable {K : Type} [Field K]

theorem isSimpleGroup_relLevi_one [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (relLevi K {1}) := by
  have : IsSimpleGroup (SL2 K) := CFSG.RankThree.PartOne.KCRootAxis.sl2_isSimpleGroup hK4
  have e := MonoidHom.ofInjective (rankOneHom_injective_of_charTwo (K := K) TwistTag.E6 nodeAlpha4)
  rw [← relLevi_one_eq_range] at e
  exact e.symm.isSimpleGroup

end Levi

section Swap


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {σ : K →+* K} (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (A : Subgroup Kˣ)

theorem false_of_swapCover_of_pieceDichotomy (hAo : Odd (Nat.card A)) {k : Type} [Field k]
    (ι : k →+* K) (hσk : ∀ c, σ (ι c) = ι c) (hq : 4 ≤ Nat.card k) {t : G}
    (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1) {N : F4Pilot.AmalgamNeighbour}
    (hN : (1 : Fin Tag.F4.rank) ∈ N.nodes) {D : Subgroup G} (hRD : relRankOneG e 1 ≤ D)
    (h : SwapCover t (modelToG e (neighbourTorus K A N)) D (neighbourCore e A N))
    (hdich : PieceDichotomy (pieceCore e A {1})) : False := by
  have hRp : ⁅relRankOne σ 1, relRankOne σ 1⁆ = relRankOne σ 1 :=
    commutator_relRankOne_of_le ι hσk hq 1
  have hq1 : 4 ≤ Nat.card (orbitField TwistTag.E6 K σ (relOrbit 1)) :=
    hq.trans (card_le_card_orbitField ι hσk _)
  have hsimple := isSimpleGroup_relRankOneG_one e hq1
  have hne : h.piece (relTorusG e A 1) ≠ ⊥ := by
    intro hbot
    obtain ⟨y, hy⟩ := exists_ne (1 : relRankOneG e 1)
    obtain ⟨x, hx, hxy⟩ := exists_mem_piece_diag_eq_relRankOneG e A h htL hAo hN hRD hRp y y.2
    rw [hbot, mem_bot] at hx
    subst hx
    apply hy
    apply Subtype.ext
    rw [← hxy]
    simp
  exact false_of_pieceDichotomy_of_eq_sup_conj hdich
    (pieceCore_eq_sup_of_mem_nodes e A h htL htt hAo hN)
    (h.map_piece_le_centralizer_piece _ _) (h.commutator_piece _) hne
    (le_normalizer_pieceCore e A htL {1})

end Swap

section FieldY


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]

theorem pieceDichotomy_of_fieldNeighbourIso2E6_Y (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {e : L ≃* graphFixedRootGroup TwistTag.E6 K σ}
    {t : G} (htL : t ∈ centralizer (L : Set G)) {A : Subgroup Kˣ} (hA3 : 3 ≤ Nat.card A)
    (hAo : Odd (Nat.card A)) (hAσ : ∀ c ∈ A, Units.map σ.toMonoidHom c = c)
    (h : FieldNeighbourIso2E6 e t (modelToG e (neighbourTorus K A .Y))
      (subsystemGroup TwistTag.E6.tag K C2E6Std.setD) (d4LeviTwist (apply_apply_eq hK hσ))
      (omegaMinusLevi σ)) :
    PieceDichotomy (pieceCore e A {1}) := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, ← pow_mul]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAm : ∀ c ∈ A, c ^ Nat.card A = 1 := fun c hc => by
    have h1 : (⟨c, hc⟩ : A) ^ Nat.card A = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  have hle : relLevi K {1} ≤ subsystemGroup TwistTag.E6.tag K C2E6Std.setD :=
    relLevi_le_subsystemGroup fun j hj => by
      have hj' : e6IndexToF4 j = 1 := Finset.mem_singleton.1 (mem_relNodeSet.1 hj)
      have key : ∀ j : Fin Tag.E6.rank, e6IndexToF4 j = 1 → j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
        decide
      exact key j hj'
  have hpiece := h.pieceCore_eq_map_relLevi_Y' hf hK hσ htL hA3 hAσ hAo hAm (I := {1})
    (by decide) (by decide)
    (modelToG_mono e (neighbourTorus_le_relLeviTorus A .Y (by decide)))
  rw [hpiece, Subgroup.map_map]
  refine pieceDichotomy_map_of_isSimpleGroup ?_ _
    (subsystemGroup TwistTag.E6.tag K C2E6Std.setD).subtype ?_ ?_
  · exact CFSG.SeitzReduction.commutator_subgroupOf_eq_self hle (commutator_relLevi_eq hA3 {1})
  · rw [(MonoidHom.ker_eq_bot_iff _).2 (subtype_injective _)]
    exact bot_le
  · rw [map_subgroupOf_eq_of_le hle]
    exact isSimpleGroup_relLevi_one hK4

end FieldY

section Seitz

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.OmegaPilot (OmegaNotOddLieInputAt)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem false_of_swap_X_of_field_Y (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDKK : (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom)
    (hne : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥)
    (hZ : center Kc = ⊥)
    (hφ : Nonempty (Kc ≃* (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    {Y : Subgroup G} (hY : Y = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htY : t ∈ centralizer (Y : Set G)) {DY : Subgroup G}
    (hDYe : DY = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {KY : Subgroup (centralizer (Y : Set G) ⧸ oddCore (centralizer (Y : Set G)))}
    (hKY : IsComponent KY)
    (hDKY : ⁅(DY.subgroupOf (centralizer (Y : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (Y : Set G)))), KY⁆ ≠ ⊥)
    (hKtY : KY.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (Y : Set G))) ⟨t, htY⟩)).toMonoidHom = KY) :
    False := by
  have hf : 1 ≤ f := by omega
  have : CharP K 2 := charP_two_of_card hf hK
  have := finite_of_card hK
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hA3, hAo, hAσ, hσk⟩ := unitsRange_facts hf2 hk hσ
  have hq : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  set A : Subgroup Kˣ := (Units.map (algebraMap k K).toMonoidHom).range with hAdef
  obtain ⟨hXc⟩ := nonempty_swapCover_2E6_X hset hf2 hk hK hσ e htC ht hX htX hDe hKc hDKK hne
    hcomm hZ hφ
  have hTX : X = modelToG e (neighbourTorus K A .X) := by
    rw [hX, (neighbourTorus_X_Y (algebraMap k K)).1]; rfl
  have hXc' : SwapCover t (modelToG e (neighbourTorus K A .X)) (modelToG e (su6Levi σ))
      (neighbourCore e A .X) :=
    hXc.cast hTX (by rw [hDe]; rfl) (by rw [neighbourCore_def, ← hTX])
  obtain ⟨hYi⟩ := nonempty_fieldNeighbourIso2E6_Y_of_leafInputs' hGLS hXodd hMinn hMcomp hset hf2
    hk hK hσ e htC ht hY htY hDYe hKY hDKY hKtY
  have hTY : Y = modelToG e (neighbourTorus K A .Y) := by
    rw [hY, (neighbourTorus_X_Y (algebraMap k K)).2]; rfl
  subst hTY
  have hdich := pieceDichotomy_of_fieldNeighbourIso2E6_Y hf hK hσ htC hA3 hAo hAσ hYi
  exact false_of_swapCover_of_pieceDichotomy e A hAo (algebraMap k K) hσk hq htC htt
    (N := .X) (by decide) (modelToG_mono e (relRankOne_le_su6Levi σ (by decide))) hXc' hdich

end Seitz

end CFSG.SeitzReduction.TwistedE6Pilot
