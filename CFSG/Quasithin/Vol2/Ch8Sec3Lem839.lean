module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8311
public import CFSG.Quasithin.Background.HL3WrA3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Ch839

theorem aSet_three_autI_eq_empty {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (hV : IsElemAbelian 2 (fsuV T I)) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) : E3.aSet 3 (autI hV T) = ∅ := by
  obtain ⟨e, he, hY⟩ := Ch8311.exists_model_sylU hyp hV hrow
  have hTL₀ : T ≤ Subgroup.normalizer (fsuL0 T L : Set G) := le_normalizer_conjClosure L T
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_normalizer_conjClosure I T
  have hYn : (autI hV T).map (congrHom e) ≤ norm := by
    rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hψ
    exact congrHom_mem_norm e he (convI_mem_normalizer_autI hV (hTL₀ hg))
  have hY2 : IsPGroup 2 ↥((autI hV T).map (congrHom e)) := by
    have h1 : IsPGroup 2 ↥(T.subgroupOf (Subgroup.normalizer (fsuV T I : Set G))) :=
      hyp.fsu.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTV).symm
    exact (h1.map (convI hV)).map _
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hA
  have h1 := (map_mem_aSet_iff e).2 hA
  rw [aSet_three_eq_empty_of hYn hY2 hY] at h1
  exact h1

end Ch839

theorem stmt8_3_9_of (hmod : StmtFSUModule) (huniq : Input7_0_2_unique) (h832 : Stmt8_3_2)
    (h734 : Stmt7_3_4) (h838 : Stmt8_3_8) : Stmt8_3_9 := by
  intro G _ _ T L I hyp h731 hc hrow H hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hs := h832 G T L I hyp h731 hc hrow hV
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hTN : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_normalizer_conjClosure I T
  have hTsyl : ∀ K : Subgroup G, T ≤ K → IsSylowIn 2 T K := fun K hTK =>
    ⟨hTK, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
      (h2.trans (Subgroup.relIndex_dvd_index_of_le hTK))⟩
  have hrk : 3 ≤ rk ↥(fsuV T I) := by
    have := sParam_le_rk hV
    rw [hs] at this
    exact this
  have hA3 := Ch839.aSet_three_autI_eq_empty hyp hV hrow
  have hW0 : wClos (fsuV T I) 0 T ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, g, hAg, hAm⟩ := hA
    refine le_inf hAT ?_
    by_contra hAC
    have hmem := autI_mem_aSet_of_le hV hAg (hAT.trans hTN) hAT (k := 3) (by norm_num)
      (le_of_eq (by rw [hs, hAm])) hAC
    rw [hA3] at hmem
    exact hmem
  have hQ2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
    hyp.fsu.sylow.1.to_le inf_le_left
  have hNW : Subgroup.normalizer (wClos (fsuV T I) 0 T : Set G) ≤ fsuM T L :=
    (e3_16_one (hTsyl T le_rfl) inf_le_left hQ2 hW0 (wClos_ne_bot hV hVT (by omega))
      (huniq G T L I hyp)).2
  have hCR : ch83CR hV ≤ cClos (fsuV T I) 1 T := by
    rintro _ ⟨v, hv, rfl⟩
    have hvV : v.val ∈ fsuV T I := v.val_mem
    refine ⟨hVT hvV, ?_⟩
    have key : wClos (fsuV T I) 1 T ≤ Subgroup.centralizer ({v.val} : Set G) := by
      refine iSup₂_le fun A hA => ?_
      obtain ⟨hAT, g, hAg, hAm⟩ := hA
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hAC : A ≤ Subgroup.centralizer (fsuV T I : Set G)
      · exact (Subgroup.mem_centralizer_iff.mp (hAC ha) _ hvV).symm
      · have hmem := autI_mem_aSet_of_le hV hAg (hAT.trans hTN) hAT (k := 2) (by norm_num)
          (le_of_eq (by rw [hs, hAm])) hAC
        have hx : convI hV ⟨a, hTN (hAT ha)⟩ ∈ ⨆ B ∈ E3.aSet 2 (autI hV T), B :=
          le_iSup₂_of_le (f := fun B (_ : B ∈ E3.aSet 2 (autI hV T)) => B) (autI hV A) hmem le_rfl
            (convI_mem_autI hV ha (hTN (hAT ha)))
        have h1 := congrArg IntMod.val (hv _ hx)
        rw [convI_apply_val] at h1
        calc a * v.val = (a * v.val * a⁻¹) * a := by group
          _ = v.val * a := by rw [h1]
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mp (key hw)
  have hCM : Subgroup.centralizer (cClos (fsuV T I) 1 T : Set G) ≤ fsuM T L :=
    (Subgroup.centralizer_le hCR).trans (h838 G T L I hyp h731 hc hrow hV)
  obtain ⟨h734a, -, -, hn721⟩ := h734 G T L I hyp h731 hV
  have hn2 : nPrime (autI hV ⊤) = 2 := (hn721 hc).2.2.2.2.2.2.2.2 hrow
  have hle : E1.nParam H ≤ 2 := by
    have h := (h734a H hH).2
    rw [hn2] at h
    exact_mod_cast h
  have hTH : T ≤ H := hH.1.1
  have h0 : E1.nParam H ≠ 0 := by
    intro h
    have hodd := E1.odd_of_nParam_le_zero (le_of_eq h)
    have hV2 : IsPGroup 2 ↥(fsuV T I) := B2F.isPGroup_of_isElemAbelian hV
    have h2V : 2 ∣ Nat.card ↥(fsuV T I) := by
      rw [card_eq_two_pow_of_isPGroup hV2]
      exact dvd_pow_self 2 (by omega)
    exact Nat.not_even_iff_odd.mpr hodd
      (even_iff_two_dvd.mpr (h2V.trans (Subgroup.card_dvd_of_le (hVT.trans hTH))))
  have h1 : E1.nParam H ≠ 1 := by
    intro h
    have h19 := e3_19 hV (hTsyl H hTH) (i := 0) (j := 1) (by rw [h]; rfl)
      (by rw [hs]; norm_num)
    apply hH.2.1
    rw [← h19]
    exact sup_le (inf_le_right.trans hCM) (inf_le_right.trans hNW)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) hle)
  rw [← hk] at hle h0 h1 ⊢
  have hk2 : k ≤ 2 := by exact_mod_cast hle
  have hk0 : k ≠ 0 := by exact_mod_cast h0
  have hk1 : k ≠ 1 := by exact_mod_cast h1
  have hk : k = 2 := by omega
  rw [hk]
  rfl

end CFSG.Quasithin.H13
