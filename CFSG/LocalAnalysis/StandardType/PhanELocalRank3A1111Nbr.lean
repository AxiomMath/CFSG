module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A1111Def
public import CFSG.LocalAnalysis.StandardType.PhanELocalSel

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K]

private lemma plh_ne_top_of_finrank_lt_four {T : Submodule K (Fin 4 → K)}
    (h : finrank K T < 4) : T ≠ ⊤ := by
  intro hT
  rw [hT, finrank_top, Module.finrank_fin_fun] at h
  omega

private lemma plh_sup_span_inf_eq_bot {p T : Submodule K (Fin 4 → K)} {v : Fin 4 → K}
    (hpT : p ⊓ T = ⊥) (hvT : v ∉ p ⊔ T) : (p ⊔ K ∙ v) ⊓ T = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxL, hxT⟩ := hx
  rw [Submodule.mem_sup] at hxL
  obtain ⟨a, ha, b, hb, hab⟩ := hxL
  rw [Submodule.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  by_cases hc : c = 0
  · rw [hc, zero_smul, add_zero] at hab
    have haT : a ∈ T := by
      rw [hab]
      exact hxT
    have : a ∈ p ⊓ T := ⟨ha, haT⟩
    rw [hpT, Submodule.mem_bot] at this
    rw [← hab]
    exact this
  · exfalso
    apply hvT
    have hcv : c • v = x - a := by
      rw [← hab]
      abel
    have hmem : c • v ∈ p ⊔ T := by
      rw [hcv, sup_comm]
      exact Submodule.sub_mem_sup hxT ha
    have h1 : c⁻¹ • (c • v) = v := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [← h1]
    exact Submodule.smul_mem _ _ hmem

theorem adm1111_commonNbr (hQ : 16 ≤ Nat.card K) : AdmCommonNbr (Adm1111 (K := K)) := by
  classical
  intro s hsne hscard hflag
  have hdat : ∀ p ∈ s, finrank K p = 1 ∧ p ⊓ Vsub 4 3 = ⊥ ∧ p ⊓ Vsub 4 2 = ⊥ := by
    intro p hp
    obtain ⟨_, _, hch⟩ := hflag p hp
    refine ⟨hch.1.p1, hch.2.1, ?_⟩
    exact le_bot_iff.mp ((inf_le_inf (le_refl p)
      (Vsub_mono (show 2 ≤ 3 by norm_num))).trans (le_of_eq hch.2.1))
  let S : Finset (Submodule K (Fin 4 → K)) :=
    insert (Vsub 4 3) (s.image (fun p => p ⊔ Vsub 4 2) ∪ s)
  have hSne : ∀ T ∈ S, T ≠ ⊤ := by
    intro T hT
    rw [Finset.mem_insert] at hT
    rcases hT with rfl | hT
    · exact plh_ne_top_of_finrank_lt_four
        (by rw [finrank_Vsub (show 3 ≤ 4 by norm_num)]; norm_num)
    · rw [Finset.mem_union] at hT
      rcases hT with hT | hT
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hT
        exact plh_ne_top_of_finrank_lt_four (by
          have h1 : finrank K ↥(p ⊔ Vsub 4 2) ≤ finrank K p + finrank K (Vsub 4 2) :=
            Submodule.finrank_add_le_finrank_add_finrank p (Vsub 4 2)
          rw [(hdat p hp).1, finrank_Vsub (show 2 ≤ 4 by norm_num)] at h1
          omega)
      · exact plh_ne_top_of_finrank_lt_four (by
          rw [(hdat T hT).1]
          norm_num)
  have hSle : S.card ≤ 9 := by
    have h1 : S.card ≤ (s.image (fun p => p ⊔ Vsub 4 2) ∪ s).card + 1 :=
      Finset.card_insert_le (Vsub 4 3) (s.image (fun p => p ⊔ Vsub 4 2) ∪ s)
    have h2 : (s.image (fun p => p ⊔ Vsub 4 2) ∪ s).card ≤
        (s.image (fun p => p ⊔ Vsub 4 2)).card + s.card := Finset.card_union_le _ _
    have h3 : (s.image (fun p => p ⊔ Vsub 4 2)).card ≤ s.card :=
      Finset.card_image_le (s := s) (f := fun p => p ⊔ Vsub 4 2)
    omega
  obtain ⟨v, hv⟩ := exists_notMem_of_card_lt (K := K) (V := Fin 4 → K) S hSne (by omega)
  have hvV3 : v ∉ Vsub (K := K) 4 3 := hv _ (Finset.mem_insert_self _ _)
  have hv0 : v ≠ 0 := by
    intro h0
    apply hvV3
    rw [h0]
    exact Submodule.zero_mem _
  have ht1 : finrank K (K ∙ v) = 1 := finrank_span_singleton hv0
  have htv3 : (K ∙ v) ⊓ Vsub (K := K) 4 3 = ⊥ := by
    rw [inf_comm]
    exact (Submodule.disjoint_span_singleton_of_notMem hvV3).eq_bot
  refine ⟨K ∙ v, fun p hp => ?_⟩
  obtain ⟨_, _, hchp⟩ := hflag p hp
  have hp1 : finrank K p = 1 := hchp.1.p1
  have hpV3 : p ⊓ Vsub 4 3 = ⊥ := hchp.2.1
  have hpV2 : p ⊓ Vsub 4 2 = ⊥ := (hdat p hp).2.2
  have hvp : v ∉ p := hv p (Finset.mem_insert_of_mem (Finset.mem_union_right _ hp))
  have hne : p ≠ K ∙ v := by
    intro hpv
    exact hvp (by rw [hpv]; exact Submodule.mem_span_singleton_self v)
  have hvsup : v ∉ p ⊔ Vsub 4 2 :=
    hv (p ⊔ Vsub 4 2) (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))
  let L : Submodule K (Fin 4 → K) := p ⊔ K ∙ v
  have hL2 : finrank K L = 2 := by
    change finrank K ↥(p ⊔ K ∙ v) = 2
    rw [Submodule.finrank_sup_span_singleton hvp, hp1]
  have hLinf2 : L ⊓ Vsub 4 2 = ⊥ := by
    change (p ⊔ K ∙ v) ⊓ Vsub 4 2 = ⊥
    exact plh_sup_span_inf_eq_bot hpV2 hvsup
  have hLinf1 : L ⊓ Vsub 4 1 = ⊥ := by
    refine le_bot_iff.mp ?_
    calc L ⊓ Vsub 4 1 ≤ L ⊓ Vsub 4 2 :=
          inf_le_inf (le_refl L) (Vsub_mono (show 1 ≤ 2 by norm_num))
      _ = ⊥ := hLinf2
  have hLsup1 : L ⊔ Vsub 4 1 ≠ ⊤ := by
    apply plh_ne_top_of_finrank_lt_four
    have hfr : finrank K ↥(L ⊔ Vsub 4 1) ≤ finrank K L + finrank K (Vsub 4 1) :=
      Submodule.finrank_add_le_finrank_add_finrank L (Vsub 4 1)
    rw [hL2, finrank_Vsub (show 1 ≤ 4 by norm_num)] at hfr
    omega
  obtain ⟨w, hw⟩ := exists_notMem_of_card_lt (K := K) (V := Fin 4 → K)
    ({L ⊔ Vsub 4 1} : Finset (Submodule K (Fin 4 → K)))
    (by
      intro T hT
      rw [Finset.mem_singleton] at hT
      rw [hT]
      exact hLsup1)
    (by rw [Finset.card_singleton]; omega)
  have hwL1 : w ∉ L ⊔ Vsub 4 1 := hw _ (Finset.mem_singleton_self _)
  have hwL : w ∉ L := fun h => hwL1 (Submodule.mem_sup_left h)
  let H : Submodule K (Fin 4 → K) := L ⊔ K ∙ w
  have hH3 : finrank K H = 3 := by
    change finrank K ↥(L ⊔ K ∙ w) = 3
    rw [Submodule.finrank_sup_span_singleton hwL, hL2]
  have hHinf1 : H ⊓ Vsub 4 1 = ⊥ := by
    change (L ⊔ K ∙ w) ⊓ Vsub 4 1 = ⊥
    exact plh_sup_span_inf_eq_bot hLinf1 hwL1
  refine ⟨hne, L, H,
    ⟨⟨hp1, hL2, hH3, le_sup_left, le_sup_left⟩, hpV3, hLinf2, hHinf1⟩,
    ⟨⟨ht1, hL2, hH3, le_sup_right, le_sup_left⟩, htv3, hLinf2, hHinf1⟩⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
