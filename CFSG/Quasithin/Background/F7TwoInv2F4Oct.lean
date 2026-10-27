module

public import CFSG.Quasithin.Background.F7TwoInv2F4Xi
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctConj

public section

namespace CFSG.Quasithin.F7Two

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {m : ℕ}

theorem octSig₁_octSig₁ : ∀ k ∈ octKeys, octSig₁ (octSig₁ k) = k ∧ octSig₁ k ∈ octKeys := by
  decide +kernel

theorem octSig₂_octSig₂ : ∀ k ∈ octKeys, octSig₂ (octSig₂ k) = k ∧ octSig₂ k ∈ octKeys := by
  decide +kernel

theorem map_conj_weylTwo {k : ℤ} (hk : k ∈ octKeys) :
    (largeReeBlockGroup K m (octBlock k)).map (MulAut.conj (weylTwo K)).toMonoidHom =
      largeReeBlockGroup K m (octBlock (octSig₁ k)) := by
  have h := largeReeBlockGroup_map_conj (K := K) (a := m)
    (w := F4.fixedOrbitElement (⟨1, by decide⟩ : Fin F4.fixedOrbitCount))
    (fixedOrbitElement_mem _) (S := octBlock k) fun α hα => isRoot_of_mem_octBlock hk hα
  rw [image_smul_octBlock (octL_z₂ k hk)] at h
  exact h

theorem map_conj_weylOne {k : ℤ} (hk : k ∈ octKeys) :
    (largeReeBlockGroup K m (octBlock k)).map (MulAut.conj (weylOne K)).toMonoidHom =
      largeReeBlockGroup K m (octBlock (octSig₂ k)) := by
  have h := largeReeBlockGroup_map_conj (K := K) (a := m)
    (w := F4.fixedOrbitElement (⟨0, by decide⟩ : Fin F4.fixedOrbitCount))
    (fixedOrbitElement_mem _) (S := octBlock k) fun α hα => isRoot_of_mem_octBlock hk hα
  rw [image_smul_octBlock (octL_z₁ k hk)] at h
  exact h

theorem map_conj_weylTwo_inv {k : ℤ} (hk : k ∈ octKeys) :
    (largeReeBlockGroup K m (octBlock k)).map (MulAut.conj (weylTwo K)⁻¹).toMonoidHom =
      largeReeBlockGroup K m (octBlock (octSig₁ k)) := by
  obtain ⟨h1, h2⟩ := octSig₁_octSig₁ k hk
  have h := map_conj_weylTwo (K := K) (m := m) h2
  rw [h1] at h
  exact conjSub_inv_of_eq h

theorem map_conj_weylOne_inv {k : ℤ} (hk : k ∈ octKeys) :
    (largeReeBlockGroup K m (octBlock k)).map (MulAut.conj (weylOne K)⁻¹).toMonoidHom =
      largeReeBlockGroup K m (octBlock (octSig₂ k)) := by
  obtain ⟨h1, h2⟩ := octSig₂_octSig₂ k hk
  have h := map_conj_weylOne (K := K) (m := m) h2
  rw [h1] at h
  exact conjSub_inv_of_eq h

theorem octX_one :
    largeReeBlockGroup K m (octBlock 1) = F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩ := by
  rw [octBlock_pos (by norm_num), octPos_one]
  rfl

theorem octX_neg_one :
    largeReeBlockGroup K m (octBlock (-1)) = F4.reeFixedOrbitNegUnipotent K m ⟨1, by decide⟩ := by
  rw [octBlock_neg (k := 1) (by norm_num), octPos_one]
  rfl

theorem octX_eight :
    largeReeBlockGroup K m (octBlock 8) = F4.reeFixedOrbitUnipotent K m ⟨0, by decide⟩ := by
  rw [octBlock_pos (by norm_num), octPos_eight]
  rfl

theorem octX_neg_eight :
    largeReeBlockGroup K m (octBlock (-8)) = F4.reeFixedOrbitNegUnipotent K m ⟨0, by decide⟩ := by
  rw [octBlock_neg (k := 8) (by norm_num), octPos_eight]
  rfl

theorem reeGamma_le_of_octX {T : Subgroup (ModGL F4.tag K)} (hK : Nat.card K = 2 ^ (2 * m + 1))
    (h8 : largeReeBlockGroup K m (octBlock 8) ≤ T)
    (h8' : largeReeBlockGroup K m (octBlock (-8)) ≤ T)
    (h1 : largeReeBlockGroup K m (octBlock 1) ≤ T)
    (h1' : largeReeBlockGroup K m (octBlock (-1)) ≤ T) : F4.reeGamma K m ≤ T := by
  rw [large_Ree_simple_pair_generation m K hK]
  rw [octX_eight] at h8
  rw [octX_neg_eight] at h8'
  rw [octX_one] at h1
  rw [octX_neg_one] at h1'
  exact sup_le (sup_le h8 h8') (sup_le h1 h1')

theorem octX_le_complement {k : ℤ} (hk : k ∈ [1, 2, 3, 4, 5, 6, 7, 8]) {j : Fin F4.fixedOrbitCount}
    (hdisj : ∀ x ∈ octL k, x ∉ F4.fixedOrbitRootList j) :
    largeReeBlockGroup K m (octBlock k) ≤ F4.reeFixedOrbitComplementUnipotent K m j := by
  have hk' : 0 < k := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  have hkeys : k ∈ octKeys := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    exact mem_octKeys_iff.2 (Or.inl ⟨by omega, by omega⟩)
  have hsub : octBlock k ⊆ F4.fixedOrbitComplementRoots j := by
    intro x hx
    rw [octBlock_eq] at hx
    have hx' : x ∈ octLP k := by
      simpa [octL, hk'] using hx
    rw [F4.fixedOrbitComplementRoots_eq]
    refine ⟨⟨isRoot_of_mem_octBlock hkeys (by rw [octBlock_eq]; exact hx), ?_⟩, ?_⟩
    · exact height_octLP_pos k hk x hx'
    · rw [F4.fixedOrbitRoots_eq_list]
      exact hdisj x hx
  exact inf_le_inf_right _ (rootSpan_mono hsub)

theorem rankOneGroupOne_eq_octX (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    rankOneGroupOne K m =
      largeReeBlockGroup K m (octBlock 8) ⊔ largeReeBlockGroup K m (octBlock (-8)) := by
  rw [rankOneGroupOne_eq_range hK, largeReeA1Hom_range hK, octX_eight, octX_neg_eight]
  rfl

theorem octX_one_le_rankOneGroupTwo :
    largeReeBlockGroup K m (octBlock 1) ≤ rankOneGroupTwo K m := by
  rw [octX_one]
  exact fun g hg => Subgroup.subset_closure (Or.inl (Or.inl hg))

theorem weylTwo_mem_rankOneGroupTwo : weylTwo K ∈ rankOneGroupTwo K m :=
  Subgroup.subset_closure (Or.inr rfl)

theorem octX_neg_one_le_rankOneGroupTwo :
    largeReeBlockGroup K m (octBlock (-1)) ≤ rankOneGroupTwo K m := by
  have h := map_conj_weylTwo (K := K) (m := m) (k := 1) (by decide)
  have e : octSig₁ 1 = -1 := by decide
  rw [e] at h
  rw [← h]
  exact conjSub_le_of_mem weylTwo_mem_rankOneGroupTwo octX_one_le_rankOneGroupTwo

theorem zOne_sq : sylowH m K 0 1 ^ 2 = 1 := by
  rw [(blocks_eq_sylowV (m := m) (K := K) 0 0 0 1 0 0 0).2.2.2.1]
  exact (sylowV_zero_zero_sq_eq_one_iff (m := m) (K := K) 0 0 0 0 0 0 1 0 0 0).2
    ⟨rfl, rfl, rfl, rfl, zero_mul _⟩

theorem tOne_sq : sylowL m K 1 ^ 2 = 1 := by
  rw [(blocks_eq_sylowV (m := m) (K := K) 0 0 0 0 0 0 1).2.2.2.2.2.2]
  exact (sylowV_zero_zero_sq_eq_one_iff (m := m) (K := K) 0 0 0 0 0 0 0 0 0 1).2
    ⟨rfl, rfl, rfl, rfl, zero_mul _⟩

theorem zOne_ne_one : sylowH m K 0 1 ≠ 1 := by
  intro h
  rw [sylowH_zero_eq_centralZ] at h
  exact one_ne_zero (centralZ_injective (h.trans centralZ_zero.symm))

theorem tOne_ne_one (hK : Nat.card K = 2 ^ (2 * m + 1)) : sylowL m K 1 ≠ 1 := by
  intro h
  have h1 : sylowVec m K (Pi.single 11 1) = sylowVec m K 0 := by
    have e1 : sylowVec m K (Pi.single 11 1) = sylowL m K 1 := by
      simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowX,
        largeReeSigma_zero, pinnedX_zero]
    have e0 : sylowVec m K 0 = 1 := by
      simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL,
        sylowX, largeReeSigma_zero, pinnedX_zero]
    rw [e1, e0, h]
  have h2 := congrFun ((bijOn_sylowVec hK).injOn (Set.mem_univ _) (Set.mem_univ _) h1) 11
  simp at h2

end CFSG.Quasithin.F7Two
