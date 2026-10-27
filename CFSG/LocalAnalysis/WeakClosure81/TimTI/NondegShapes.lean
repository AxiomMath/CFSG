module

public import CFSG.LocalAnalysis.WeakClosure81.TimTI.Quot
public import CFSG.CGT.Timmesfeld75.ListWCLin
public import CFSG.ClassicalGroups.Linear.CentreGroupsDual
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsG
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoDA
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem coe_transvImage_transvCenter {m : ℕ} {F : Type} [Field F] (c : Fin m → F) :
    ((CFSG.CGT.Timmesfeld75.transvImage m F (CFSG.CGT.Timmesfeld75.transvCenter m F c) :
      Subgroup (StatedProj (StatedSL m F))) : Set (StatedProj (StatedSL m F))) =
      transvectionCenterSet m F c := by
  ext x
  change x ∈ (QuotientGroup.mk' ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F))) ''
      ((CFSG.CGT.Timmesfeld75.transvCenter m F c).subgroupOf (StatedSL m F)) ↔
      x ∈ transvectionCenterSet m F c
  constructor
  · rintro ⟨g, hg, rfl⟩
    change (g : GL (Fin m) F) ∈ CFSG.CGT.Timmesfeld75.transvCenter m F c at hg
    obtain ⟨f, hfc, hg⟩ := hg
    exact ⟨g, rfl, f, hfc, hg⟩
  · rintro ⟨g, hgx, f, hfa, hg⟩
    refine ⟨g, ?_, ?_⟩
    · change (g : GL (Fin m) F) ∈ CFSG.CGT.Timmesfeld75.transvCenter m F c
      exact ⟨f, hfa, hg⟩
    · rw [QuotientGroup.mk'_apply]
      exact hgx

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

namespace Hyp

theorem linearShape (h : Hyp X S)
    (hwc : CFSG.CGT.Timmesfeld75.IsWC (S.map (QuotientGroup.mk' (Subgroup.center X))))
    {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hL : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL n 2 f) :
    SevenElevenLinearShape X S := by
  have hLc := hL
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL
  haveI : CharP K 2 := CFSG.CGT.Timmesfeld75.charP_two_of_card hK
  have hSne : S.map (QuotientGroup.mk' (Subgroup.center X)) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (S.map (QuotientGroup.mk' (Subgroup.center X))) = 1 := by
      rw [hbot, Subgroup.card_bot]
    have h2 : Nat.card S = 1 := by
      rw [← h.card_map_center]
      exact h1
    have hc := h.card
    rw [h2] at hc
    exact absurd hc (by norm_num)
  obtain ⟨-, hid, -⟩ := CFSG.CGT.Timmesfeld75.lin_wc hn e hwc hSne
  refine ⟨n, f, hn, Or.inl ⟨by decide, hLc⟩, ?_, h.exists_sylow_isWeaklyClosedIn hwc⟩
  rcases hid with ⟨c, hc0, hc⟩ | ⟨a, ha0, ha⟩
  · refine ⟨K, inferInstance, inferInstance, hK, e, c, hc0, fun y => ?_⟩
    have h1 : (∃ x ∈ S, (QuotientGroup.mk x : X ⧸ Subgroup.center X) = y) ↔
        y ∈ S.map (QuotientGroup.mk' (Subgroup.center X)) := by
      rw [Subgroup.mem_map]
      simp [QuotientGroup.mk'_apply]
    have h2 : y ∈ S.map (QuotientGroup.mk' (Subgroup.center X)) ↔
        e y ∈ (S.map (QuotientGroup.mk' (Subgroup.center X))).map e.toMonoidHom :=
      (Subgroup.mem_map_iff_mem e.injective).symm
    have h3 : e y ∈ (CFSG.CGT.Timmesfeld75.transvImage n K
          (CFSG.CGT.Timmesfeld75.transvCenter n K c) :
            Subgroup (StatedProj (StatedSL n K))) ↔ e y ∈ transvectionCenterSet n K c := by
      change e y ∈ ((CFSG.CGT.Timmesfeld75.transvImage n K
          (CFSG.CGT.Timmesfeld75.transvCenter n K c) :
            Subgroup (StatedProj (StatedSL n K))) : Set (StatedProj (StatedSL n K))) ↔
        e y ∈ transvectionCenterSet n K c
      rw [coe_transvImage_transvCenter]
    rw [h1, h2, hc, h3]
  · obtain ⟨δ, hδ⟩ := CFSG.ClassicalGroups.Linear.Model.exists_dualEquiv n K
    let e' : (X ⧸ Subgroup.center X) ≃* StatedProj (StatedSL n K) := e.trans δ
    refine ⟨K, inferInstance, inferInstance, hK, e', a, ha0, fun y => ?_⟩
    have hmap'' : (S.map (QuotientGroup.mk' (Subgroup.center X))).map e'.toMonoidHom =
        ((S.map (QuotientGroup.mk' (Subgroup.center X))).map e.toMonoidHom).map
          δ.toMonoidHom := by
      rw [Subgroup.map_map (S.map (QuotientGroup.mk' (Subgroup.center X))) δ.toMonoidHom
        e.toMonoidHom]
      rfl
    have hmap' : (S.map (QuotientGroup.mk' (Subgroup.center X))).map e'.toMonoidHom =
        CFSG.ClassicalGroups.Linear.Model.cg n K a := by
      rw [hmap'', ha]
      exact hδ a
    have hmap : (S.map (QuotientGroup.mk' (Subgroup.center X))).map e'.toMonoidHom =
        CFSG.CGT.Timmesfeld75.transvImage n K (CFSG.CGT.Timmesfeld75.transvCenter n K a) :=
      hmap'
    have h1 : (∃ x ∈ S, (QuotientGroup.mk x : X ⧸ Subgroup.center X) = y) ↔
        y ∈ S.map (QuotientGroup.mk' (Subgroup.center X)) := by
      rw [Subgroup.mem_map]
      simp [QuotientGroup.mk'_apply]
    have h2 : y ∈ S.map (QuotientGroup.mk' (Subgroup.center X)) ↔
        e' y ∈ (S.map (QuotientGroup.mk' (Subgroup.center X))).map e'.toMonoidHom :=
      (Subgroup.mem_map_iff_mem e'.injective).symm
    have h3 : e' y ∈ (CFSG.CGT.Timmesfeld75.transvImage n K
          (CFSG.CGT.Timmesfeld75.transvCenter n K a) :
            Subgroup (StatedProj (StatedSL n K))) ↔ e' y ∈ transvectionCenterSet n K a := by
      change e' y ∈ ((CFSG.CGT.Timmesfeld75.transvImage n K
          (CFSG.CGT.Timmesfeld75.transvCenter n K a) :
            Subgroup (StatedProj (StatedSL n K))) : Set (StatedProj (StatedSL n K))) ↔
        e' y ∈ transvectionCenterSet n K a
      rw [coe_transvImage_transvCenter]
    rw [h1, h2, hmap, h3]

theorem aSixShape (h : Hyp X S)
    (hwc : CFSG.CGT.Timmesfeld75.IsWC (S.map (QuotientGroup.mk' (Subgroup.center X))))
    (hA : Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6))) :
    SevenElevenASixShape X S := by
  obtain ⟨eA⟩ := hA
  refine ⟨⟨eA⟩, ?_, h.exists_sylow_isWeaklyClosedIn hwc⟩
  have hle : Nat.card S ≤ 4 := by
    have hb := rank_transport eA (CFSG.LocalAnalysis.WeakClosure81.kFacts_rank_A6)
      (S.map (QuotientGroup.mk' (Subgroup.center X))) h.isElemAbelian_map_center
    rwa [h.card_map_center] at hb
  obtain ⟨k, hk⟩ := (IsElemAbelian.isPGroup h.elem).exists_card_eq
  have hgt : 2 < 2 ^ k := by rw [← hk]; exact h.card
  have hk2 : k ≤ 2 := by
    by_contra hk2
    have h3 : 3 ≤ k := by have := not_le.mp hk2; omega
    have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h3
    norm_num at h8
    omega
  have hk1 : 2 ≤ k := by
    by_contra hk1
    have h1 : k ≤ 1 := by have := not_le.mp hk1; omega
    have h2 : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    norm_num at h2
    omega
  have hk2' : k = 2 := by omega
  rw [hk, hk2']
  norm_num

end Hyp

end CFSG.LocalAnalysis.WeakClosure81.TimTI
