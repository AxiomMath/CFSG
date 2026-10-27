module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A22xDef
public import CFSG.LocalAnalysis.StandardType.PhanELocalSigma

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private def plh_v2 (s : K) : Fin 2 → K := ![s, 1]

private theorem plh_v2_ne_zero (s : K) : plh_v2 s ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simpa [plh_v2] using h1

private theorem plh_v2_mem_iff (s t : K) (h : plh_v2 t ∈ K ∙ plh_v2 s) : t = s := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have h1 : a = 1 := by
    have h := congrFun ha 1
    simpa [plh_v2] using h
  have h0 : a * s = t := by
    have h := congrFun ha 0
    simpa [plh_v2] using h
  rw [← h0, h1, one_mul]

private theorem plh_v2_finrank (s : K) : finrank K (K ∙ plh_v2 s) = 1 :=
  finrank_span_singleton (plh_v2_ne_zero s)

private def plh_lift (u : Fin 2 → K) : Fin 4 → K := ![u 0, u 1, 0, 0]

private noncomputable def plh_bad (u : Fin 2 → K) : Submodule K (Fin 4 → K) :=
  sgS K f 4 (K ∙ plh_lift u)

private theorem plh_lift_apply_of_le (u : Fin 2 → K) {j : Fin 4} (hj : 2 ≤ j.val) :
    plh_lift u j = 0 := by
  fin_cases j <;> simp_all [plh_lift]

private theorem plh_lift_mem_Vsub (u : Fin 2 → K) : plh_lift u ∈ Vsub 4 2 := by
  intro j hj
  fin_cases j <;> simp_all [plh_lift]

private theorem plh_lift_ne_zero {u : Fin 2 → K} (hu : u ≠ 0) : plh_lift u ≠ 0 := by
  intro h
  apply hu
  funext i
  fin_cases i
  · have h0 := congrFun h 0
    simpa [plh_lift] using h0
  · have h1 := congrFun h 1
    simpa [plh_lift] using h1

private theorem plh_bad_finrank (hK : Nat.card K = (2 ^ f) ^ 2) {u : Fin 2 → K}
    (hu : u ≠ 0) : finrank K (plh_bad f u) = 1 := by
  change finrank K (sgS K f 4 (K ∙ plh_lift u)) = 1
  rw [finrank_sgS hK, finrank_span_singleton (plh_lift_ne_zero hu)]

private theorem plh_bad_le_Vsub {u : Fin 2 → K} : plh_bad f u ≤ Vsub 4 2 := by
  change sgS K f 4 (K ∙ plh_lift u) ≤ Vsub 4 2
  rw [← sgS_Vsub (K := K) (f := f) (n := 4) 2]
  exact sgS_mono ((Submodule.span_singleton_le_iff_mem _ _).mpr (plh_lift_mem_Vsub u))

private theorem plh_rho_jShift (v : Fin 4 → K) :
    rho (jShift f v) = ![sg K f (v 0), sg K f (v 1)] := by
  funext i
  fin_cases i <;> simp [rho_apply, jShift]

private def plh_e1 : Fin 4 → K := ![1, 0, 0, 0]
private def plh_e2 : Fin 4 → K := ![0, 1, 0, 0]
private def plh_e3 : Fin 4 → K := ![1, 1, 0, 0]

private theorem plh_e1_mem_Vsub : plh_e1 (K := K) ∈ Vsub 4 2 := by
  intro j hj
  fin_cases j <;> simp_all [plh_e1]

private theorem plh_e2_mem_Vsub : plh_e2 (K := K) ∈ Vsub 4 2 := by
  intro j hj
  fin_cases j <;> simp_all [plh_e2]

private theorem plh_e3_mem_Vsub : plh_e3 (K := K) ∈ Vsub 4 2 := by
  intro j hj
  fin_cases j <;> simp_all [plh_e3]

private theorem plh_e1_ne_zero : plh_e1 (K := K) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [plh_e1] at h0

private theorem plh_e2_ne_zero : plh_e2 (K := K) ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simp [plh_e2] at h1

private theorem plh_e3_ne_zero : plh_e3 (K := K) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [plh_e3] at h0

private theorem plh_e1_span_finrank : finrank K (K ∙ plh_e1 (K := K)) = 1 :=
  finrank_span_singleton plh_e1_ne_zero

private theorem plh_e2_span_finrank : finrank K (K ∙ plh_e2 (K := K)) = 1 :=
  finrank_span_singleton plh_e2_ne_zero

private theorem plh_e3_span_finrank : finrank K (K ∙ plh_e3 (K := K)) = 1 :=
  finrank_span_singleton plh_e3_ne_zero

private theorem plh_e1_le_Vsub : (K ∙ plh_e1 (K := K) : Submodule K (Fin 4 → K)) ≤ Vsub 4 2 :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr plh_e1_mem_Vsub

private theorem plh_e2_le_Vsub : (K ∙ plh_e2 (K := K) : Submodule K (Fin 4 → K)) ≤ Vsub 4 2 :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr plh_e2_mem_Vsub

private theorem plh_e3_le_Vsub : (K ∙ plh_e3 (K := K) : Submodule K (Fin 4 → K)) ≤ Vsub 4 2 :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr plh_e3_mem_Vsub

private theorem plh_e1_ne_e2 :
    (K ∙ plh_e1 (K := K) : Submodule K (Fin 4 → K)) ≠ K ∙ plh_e2 := by
  intro h
  have hmem : plh_e2 (K := K) ∈ K ∙ plh_e1 (K := K) := by
    rw [h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 := congrFun ha 1
  simpa [plh_e1, plh_e2] using h1

private theorem plh_e1_ne_e3 :
    (K ∙ plh_e1 (K := K) : Submodule K (Fin 4 → K)) ≠ K ∙ plh_e3 := by
  intro h
  have hmem : plh_e3 (K := K) ∈ K ∙ plh_e1 (K := K) := by
    rw [h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 := congrFun ha 1
  simpa [plh_e1, plh_e3] using h1

private theorem plh_e2_ne_e3 :
    (K ∙ plh_e2 (K := K) : Submodule K (Fin 4 → K)) ≠ K ∙ plh_e3 := by
  intro h
  have hmem : plh_e3 (K := K) ∈ K ∙ plh_e2 (K := K) := by
    rw [h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have h0 := congrFun ha 0
  simpa [plh_e2, plh_e3] using h0

private theorem plh_good_of_not_mem (hK : Nat.card K = (2 ^ f) ^ 2) {u : Fin 2 → K}
    {w : Fin 4 → K} (hw : w ∈ Vsub 4 2) (hwbad : w ∉ plh_bad f u) :
    (D22x (K := K) f).good (K ∙ u) (K ∙ w) := by
  change (K ∙ u).comap rho ≠ Vsub 4 2 ⊔
    Submodule.span K (jShift f '' (K ∙ w : Set (Fin 4 → K)))
  intro hbad
  have hmem_sup : jShift f w ∈ Vsub 4 2 ⊔
      Submodule.span K (jShift f '' (K ∙ w : Set (Fin 4 → K))) :=
    Submodule.mem_sup_right
      (Submodule.subset_span ⟨w, Submodule.mem_span_singleton_self w, rfl⟩)
  have hmem : rho (jShift f w) ∈ K ∙ u := by
    have h := hmem_sup
    rw [← hbad] at h
    exact h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have ha' : rho (jShift f w) = a • u := ha.symm
  have h0 : sg K f (w 0) = a * u 0 := by
    have h := congrFun ha' 0
    rw [plh_rho_jShift] at h
    simpa using h
  have h1 : sg K f (w 1) = a * u 1 := by
    have h := congrFun ha' 1
    rw [plh_rho_jShift] at h
    simpa using h
  have h0' : w 0 = sg K f a * sg K f (u 0) := by
    have h := congrArg (⇑(sg K f)) h0
    simpa only [map_mul, sg_sg hK] using h
  have h1' : w 1 = sg K f a * sg K f (u 1) := by
    have h := congrArg (⇑(sg K f)) h1
    simpa only [map_mul, sg_sg hK] using h
  have hw_eq : w = sg K f a • sgv K f 4 (plh_lift u) := by
    funext i
    fin_cases i
    · simpa [plh_lift, sgv_apply] using h0'
    · simpa [plh_lift, sgv_apply] using h1'
    · simp only [sgv_apply, Pi.smul_apply, smul_eq_mul]
      rw [hw _ (by decide), plh_lift_apply_of_le u (by decide)]
      simp
    · simp only [sgv_apply, Pi.smul_apply, smul_eq_mul]
      rw [hw _ (by decide), plh_lift_apply_of_le u (by decide)]
      simp
  apply hwbad
  change w ∈ sgS K f 4 (K ∙ plh_lift u)
  rw [sgS_span_singleton hK]
  exact Submodule.mem_span_singleton.mpr ⟨sg K f a, hw_eq.symm⟩

private theorem plh_good_of_ne_bad (hK : Nat.card K = (2 ^ f) ^ 2) {u : Fin 2 → K}
    (hu : u ≠ 0) {w : Fin 4 → K} (hw : w ∈ Vsub 4 2) (hw0 : w ≠ 0)
    (hne : K ∙ w ≠ plh_bad f u) : (D22x (K := K) f).good (K ∙ u) (K ∙ w) := by
  refine plh_good_of_not_mem f hK hw ?_
  intro hwmem
  apply hne
  have hfin : finrank K (plh_bad f u) = 1 := plh_bad_finrank f hK hu
  exact (eq_span_singleton_of_mem_of_finrank_eq_one hfin hwmem hw0).symm

private theorem plh_two_good (hK : Nat.card K = (2 ^ f) ^ 2) {u : Fin 2 → K} (hu : u ≠ 0) :
    ∃ M₁ M₂ : Submodule K (Fin 4 → K), M₁ ≠ M₂ ∧ M₁ ≤ Vsub 4 2 ∧ M₂ ≤ Vsub 4 2 ∧
      finrank K M₁ = 1 ∧ finrank K M₂ = 1 ∧
      (D22x (K := K) f).good (K ∙ u) M₁ ∧ (D22x (K := K) f).good (K ∙ u) M₂ := by
  by_cases h1 : plh_bad f u = K ∙ plh_e1 (K := K)
  · refine ⟨K ∙ plh_e2, K ∙ plh_e3, plh_e2_ne_e3, plh_e2_le_Vsub, plh_e3_le_Vsub,
      plh_e2_span_finrank, plh_e3_span_finrank, ?_, ?_⟩
    · exact plh_good_of_ne_bad f hK hu plh_e2_mem_Vsub plh_e2_ne_zero
        (fun h => plh_e1_ne_e2 ((h.trans h1).symm))
    · exact plh_good_of_ne_bad f hK hu plh_e3_mem_Vsub plh_e3_ne_zero
        (fun h => plh_e1_ne_e3 ((h.trans h1).symm))
  · by_cases h2 : plh_bad f u = K ∙ plh_e2 (K := K)
    · refine ⟨K ∙ plh_e1, K ∙ plh_e3, plh_e1_ne_e3, plh_e1_le_Vsub, plh_e3_le_Vsub,
        plh_e1_span_finrank, plh_e3_span_finrank, ?_, ?_⟩
      · exact plh_good_of_ne_bad f hK hu plh_e1_mem_Vsub plh_e1_ne_zero (fun h => h1 h.symm)
      · exact plh_good_of_ne_bad f hK hu plh_e3_mem_Vsub plh_e3_ne_zero
          (fun h => plh_e2_ne_e3 ((h.trans h2).symm))
    · refine ⟨K ∙ plh_e1, K ∙ plh_e2, plh_e1_ne_e2, plh_e1_le_Vsub, plh_e2_le_Vsub,
        plh_e1_span_finrank, plh_e2_span_finrank, ?_, ?_⟩
      · exact plh_good_of_ne_bad f hK hu plh_e1_mem_Vsub plh_e1_ne_zero (fun h => h1 h.symm)
      · exact plh_good_of_ne_bad f hK hu plh_e2_mem_Vsub plh_e2_ne_zero (fun h => h2 h.symm)

private theorem plh_pair_good (hK : Nat.card K = (2 ^ f) ^ 2) {u u' : Fin 2 → K}
    (hu : u ≠ 0) (hu' : u' ≠ 0) :
    ∃ M : Submodule K (Fin 4 → K), M ≤ Vsub 4 2 ∧ finrank K M = 1 ∧
      (D22x (K := K) f).good (K ∙ u) M ∧ (D22x (K := K) f).good (K ∙ u') M := by
  by_cases h1 : plh_bad f u = K ∙ plh_e1 (K := K)
  · by_cases h1' : plh_bad f u' = K ∙ plh_e1 (K := K)
    · refine ⟨K ∙ plh_e2, plh_e2_le_Vsub, plh_e2_span_finrank, ?_, ?_⟩
      · exact plh_good_of_ne_bad f hK hu plh_e2_mem_Vsub plh_e2_ne_zero
          (fun h => plh_e1_ne_e2 ((h.trans h1).symm))
      · exact plh_good_of_ne_bad f hK hu' plh_e2_mem_Vsub plh_e2_ne_zero
          (fun h => plh_e1_ne_e2 ((h.trans h1').symm))
    · by_cases h2' : plh_bad f u' = K ∙ plh_e2 (K := K)
      · refine ⟨K ∙ plh_e3, plh_e3_le_Vsub, plh_e3_span_finrank, ?_, ?_⟩
        · exact plh_good_of_ne_bad f hK hu plh_e3_mem_Vsub plh_e3_ne_zero
            (fun h => plh_e1_ne_e3 ((h.trans h1).symm))
        · exact plh_good_of_ne_bad f hK hu' plh_e3_mem_Vsub plh_e3_ne_zero
            (fun h => plh_e2_ne_e3 ((h.trans h2').symm))
      · refine ⟨K ∙ plh_e2, plh_e2_le_Vsub, plh_e2_span_finrank, ?_, ?_⟩
        · exact plh_good_of_ne_bad f hK hu plh_e2_mem_Vsub plh_e2_ne_zero
            (fun h => plh_e1_ne_e2 ((h.trans h1).symm))
        · exact plh_good_of_ne_bad f hK hu' plh_e2_mem_Vsub plh_e2_ne_zero
            (fun h => h2' h.symm)
  · by_cases h1' : plh_bad f u' = K ∙ plh_e1 (K := K)
    · by_cases h2 : plh_bad f u = K ∙ plh_e2 (K := K)
      · refine ⟨K ∙ plh_e3, plh_e3_le_Vsub, plh_e3_span_finrank, ?_, ?_⟩
        · exact plh_good_of_ne_bad f hK hu plh_e3_mem_Vsub plh_e3_ne_zero
            (fun h => plh_e2_ne_e3 ((h.trans h2).symm))
        · exact plh_good_of_ne_bad f hK hu' plh_e3_mem_Vsub plh_e3_ne_zero
            (fun h => plh_e1_ne_e3 ((h.trans h1').symm))
      · refine ⟨K ∙ plh_e2, plh_e2_le_Vsub, plh_e2_span_finrank, ?_, ?_⟩
        · exact plh_good_of_ne_bad f hK hu plh_e2_mem_Vsub plh_e2_ne_zero
            (fun h => h2 h.symm)
        · exact plh_good_of_ne_bad f hK hu' plh_e2_mem_Vsub plh_e2_ne_zero
            (fun h => plh_e1_ne_e2 ((h.trans h1').symm))
    · refine ⟨K ∙ plh_e1, plh_e1_le_Vsub, plh_e1_span_finrank, ?_, ?_⟩
      · exact plh_good_of_ne_bad f hK hu plh_e1_mem_Vsub plh_e1_ne_zero (fun h => h1 h.symm)
      · exact plh_good_of_ne_bad f hK hu' plh_e1_mem_Vsub plh_e1_ne_zero (fun h => h1' h.symm)

private theorem plh_card_le_three {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α).card ≤ 3 := by
  classical
  calc ({a, b, c} : Finset α).card
      ≤ ({b, c} : Finset α).card + 1 := Finset.card_insert_le a _
    _ ≤ (({c} : Finset α).card + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le b _) 1
    _ ≤ 3 := by simp

theorem clsHyp_a3_22x (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ClsHyp (D22x (K := K) f) 3 := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    by_contra h
    haveI : Fintype K := Fintype.ofFinite K
    have hmem : ∀ s : K, K ∙ plh_v2 s ∈ S := by
      intro s
      by_contra hs
      exact h ⟨K ∙ plh_v2 s, trivial, plh_v2_finrank s, hs⟩
    let g : K → ↥S := fun s => ⟨K ∙ plh_v2 s, hmem s⟩
    have hg : Function.Injective g := by
      intro s t hst
      have hst' : K ∙ plh_v2 s = K ∙ plh_v2 t := congrArg Subtype.val hst
      exact (plh_v2_mem_iff s t (by rw [hst']; exact Submodule.mem_span_singleton_self _)).symm
    have hcard := Fintype.card_le_of_injective g hg
    rw [Fintype.card_coe] at hcard
    have h16 : 16 ≤ Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hK]
      simpa using Nat.pow_le_pow_left hq 2
    omega
  · intro c _ hc1
    obtain ⟨u, hu, hc_eq⟩ := exists_eq_span_of_finrank_eq_one hc1
    rw [hc_eq]
    exact plh_two_good f hK hu
  · intro c c' _ _ hc1 hc1' _
    obtain ⟨u, hu, hc_eq⟩ := exists_eq_span_of_finrank_eq_one hc1
    obtain ⟨u', hu', hc'_eq⟩ := exists_eq_span_of_finrank_eq_one hc1'
    rw [hc_eq, hc'_eq]
    exact plh_pair_good f hK hu hu'
  · intro a b d _ _ _ ha1 hb1 hd1 _ _ _
    obtain ⟨ua, hua, ha_eq⟩ := exists_eq_span_of_finrank_eq_one ha1
    obtain ⟨ub, hub, hb_eq⟩ := exists_eq_span_of_finrank_eq_one hb1
    obtain ⟨ud, hud, hd_eq⟩ := exists_eq_span_of_finrank_eq_one hd1
    rw [ha_eq, hb_eq, hd_eq]
    refine ⟨({plh_bad f ua, plh_bad f ub, plh_bad f ud} :
      Finset (Submodule K (Fin 4 → K))), ?_, ?_, ?_, ?_⟩
    · exact Finset.insert_nonempty _ _
    · exact plh_card_le_three _ _ _
    · intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨plh_bad_le_Vsub f, plh_bad_finrank f hK hua⟩
      · exact ⟨plh_bad_le_Vsub f, plh_bad_finrank f hK hub⟩
      · exact ⟨plh_bad_le_Vsub f, plh_bad_finrank f hK hud⟩
    · intro w hwV hwB
      have hw0 : w ≠ 0 := by
        intro h0
        have : w ∈ plh_bad f ua := by
          rw [h0]
          exact Submodule.zero_mem _
        exact hwB (plh_bad f ua) (Finset.mem_insert_self _ _) this
      have hne_a : K ∙ w ≠ plh_bad f ua := by
        intro h
        exact hwB (plh_bad f ua) (Finset.mem_insert_self _ _)
          (by rw [← h]; exact Submodule.mem_span_singleton_self w)
      have hne_b : K ∙ w ≠ plh_bad f ub := by
        intro h
        exact hwB (plh_bad f ub) (by simp)
          (by rw [← h]; exact Submodule.mem_span_singleton_self w)
      have hne_d : K ∙ w ≠ plh_bad f ud := by
        intro h
        exact hwB (plh_bad f ud) (by simp)
          (by rw [← h]; exact Submodule.mem_span_singleton_self w)
      exact ⟨hw0, plh_good_of_ne_bad f hK hua hwV hw0 hne_a,
        plh_good_of_ne_bad f hK hub hwV hw0 hne_b,
        plh_good_of_ne_bad f hK hud hwV hw0 hne_d⟩
  · rw [hK]
    nlinarith [hq]

end CFSG.ClassicalInvolution.Phan.PhanE

end
