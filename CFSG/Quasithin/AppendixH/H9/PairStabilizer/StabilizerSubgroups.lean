module

public import CFSG.Quasithin.AppendixH.H9.PairStabilizer.CentralizerOfV

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.PairStab

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH.AutPair

variable {m : ℕ}

@[expose] noncomputable def Pv (m : ℕ) : Subgroup (MulAut (PairN (m + 1))) :=
  (utriGL m).map (leviAct m)

@[expose] noncomputable def Sv (m : ℕ) : Subgroup (MulAut (PairN (m + 1))) :=
  Pv m ⊔ Subgroup.zpowers (tInv m)

private theorem eq_one_or_eq_of_mem_zpowers_sq {G : Type*} [Group G] {v x : G}
    (hv : v ^ 2 = 1) (hx : x ∈ Subgroup.zpowers v) : x = 1 ∨ x = v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨t, ht | ht⟩ := Int.even_or_odd' k
  · left
    rw [ht, zpow_mul, zpow_ofNat, hv, one_zpow]
  · right
    rw [ht, zpow_add, zpow_mul, zpow_one, zpow_ofNat, hv, one_zpow, one_mul]

theorem Pv_le_range : Pv m ≤ (leviAct m).range :=
  Subgroup.map_le_range _ _

private theorem range_le_Lg : (leviAct m).range ≤ Lg (m + 1) := by
  rintro g ⟨B, rfl⟩
  exact leviAct_mem_Lg B

theorem range_le_Mv : (leviAct m).range ≤
    Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m))) := by
  rintro g ⟨B, rfl⟩
  exact ⟨Lg_le_Mg (leviAct_mem_Lg B), mem_centSub_zpowers_iff.2 (leviAct_pairVec_self B)⟩

theorem T0_inf_centSub_eq_Pv (hm : 1 ≤ m) :
    T0 (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m))) = Pv m := by
  apply le_antisymm
  · rintro s ⟨hs, hfix⟩
    have hfix' : s (pairVec (ez m) (ez m)) = pairVec (ez m) (ez m) :=
      mem_centSub_zpowers_iff.1 hfix
    rcases mem_T0_iff.1 hs with ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
    · obtain ⟨B, rfl⟩ := exists_levi_of_pairActN_fix hfix'
      exact Subgroup.mem_map.2 ⟨B, levi_mem_utriGL_iff.1 hA, rfl⟩
    · exfalso
      have hsL : pairActN (m + 1) A * (pairActN (m + 1) (revGL (m + 1)) * swapN (m + 1)) ∉
          Lg (m + 1) := by
        rw [← mul_assoc, ← map_mul]
        exact outer_not_mem_Lg (Nat.succ_pos m) _
      exact T0_outer_not_fix m hm hs hsL ez_zero hfix'
  · intro s hs
    obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.1 hs
    exact ⟨mem_T0_iff.2 (Or.inl ⟨levi m B, levi_mem_utriGL_iff.2 hB, rfl⟩),
      mem_centSub_zpowers_iff.2 (leviAct_pairVec_self B)⟩

theorem tInv_mem_normalizer_Pv :
    tInv m ∈ Subgroup.normalizer (Pv m : Set (MulAut (PairN (m + 1)))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hfwd : ∀ h ∈ Pv m, tInv m * h * (tInv m)⁻¹ ∈ Pv m := by
    intro h hh
    obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.1 hh
    rw [tInv_mul_leviAct_mul_inv]
    exact Subgroup.mem_map.2 ⟨_, revGL_mul_dualGLn_mul_revGL_mem_utriGL hB, rfl⟩
  have hsq : tInv m * tInv m = 1 := by rw [← pow_two]; exact tInv_sq
  constructor
  · exact hfwd h
  · intro hh
    have heq : tInv m * (tInv m * h * (tInv m)⁻¹) * (tInv m)⁻¹ = h := by
      calc tInv m * (tInv m * h * (tInv m)⁻¹) * (tInv m)⁻¹
          = (tInv m * tInv m) * h * (tInv m * tInv m)⁻¹ := by group
        _ = h := by rw [hsq]; group
    rw [← heq]
    exact hfwd _ hh

theorem mem_Sv_iff {s : MulAut (PairN (m + 1))} :
    s ∈ Sv m ↔ s ∈ Pv m ∨ ∃ p ∈ Pv m, s = p * tInv m := by
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left (Pv m) (Subgroup.zpowers (tInv m))
    (Subgroup.zpowers_le.2 tInv_mem_normalizer_Pv)
  have hmem : s ∈ Sv m ↔ ∃ p ∈ Pv m, ∃ z ∈ Subgroup.zpowers (tInv m), p * z = s := by
    rw [← SetLike.mem_coe]
    change s ∈ ((Pv m ⊔ Subgroup.zpowers (tInv m) : Subgroup _) : Set _) ↔ _
    rw [hcoe]
    exact Set.mem_mul
  rw [hmem]
  constructor
  · rintro ⟨p, hp, z, hz, rfl⟩
    rcases eq_one_or_eq_of_mem_zpowers_sq tInv_sq hz with rfl | rfl
    · left
      simpa using hp
    · right
      exact ⟨p, hp, rfl⟩
  · rintro (hs | ⟨p, hp, rfl⟩)
    · exact ⟨s, hs, 1, Subgroup.one_mem _, mul_one s⟩
    · exact ⟨p, hp, tInv m, Subgroup.mem_zpowers _, rfl⟩

theorem Sv_inf_Lg : Sv m ⊓ Lg (m + 1) = Pv m := by
  apply le_antisymm
  · rintro s ⟨hs, hsL⟩
    rcases mem_Sv_iff.1 hs with hp | ⟨p, hp, rfl⟩
    · exact hp
    · exfalso
      have hpL : p ∈ Lg (m + 1) := range_le_Lg (Pv_le_range hp)
      apply tInv_not_mem_Lg (m := m)
      have h1 : tInv m = p⁻¹ * (p * tInv m) := by group
      rw [h1]
      exact (Lg (m + 1)).mul_mem ((Lg (m + 1)).inv_mem hpL) hsL
  · intro p hp
    exact ⟨(le_sup_left : Pv m ≤ Sv m) hp, range_le_Lg (Pv_le_range hp)⟩

theorem Sv_le_Mv : Sv m ≤ Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m))) :=
  sup_le (Pv_le_range.trans range_le_Mv) (Subgroup.zpowers_le.2 tInv_mem_Mv)

theorem Mv_eq_sup : Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m))) =
    Subgroup.zpowers (tInv m) ⊔ (leviAct m).range := by
  apply le_antisymm
  · intro g hg
    rcases mem_Mv_iff.1 hg with ⟨B, rfl⟩ | ⟨B, rfl⟩
    · exact Subgroup.mem_sup_right ⟨B, rfl⟩
    · rw [leviAct_mul_swapN_eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨B * revGL m, rfl⟩)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  · exact sup_le (Subgroup.zpowers_le.2 tInv_mem_Mv) range_le_Mv

theorem Mg_inf_centSub_sup_eq_range :
    Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0) ⊔
      Subgroup.zpowers (pairVec 0 (ez m))) = (leviAct m).range := by
  apply le_antisymm
  · rintro g ⟨hMg, hfix⟩
    obtain ⟨h1, h2⟩ := mem_centSub_zpowers_sup_iff.1 hfix
    have hv : g (pairVec (ez m) (ez m)) = pairVec (ez m) (ez m) := by
      have e : g (pairVec (ez m) 0 * pairVec 0 (ez m)) = pairVec (ez m) (ez m) :=
        (map_mul g _ _).trans ((congrArg₂ (· * ·) h1 h2).trans pairVec_ez_mul_pairVec_ez)
      exact (congrArg g pairVec_ez_mul_pairVec_ez).symm.trans e
    have hgMv : g ∈ Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m))) :=
      ⟨hMg, mem_centSub_zpowers_iff.2 hv⟩
    rcases mem_Mv_iff.1 hgMv with ⟨B, rfl⟩ | ⟨B, rfl⟩
    · exact ⟨B, rfl⟩
    · exfalso
      have h3 : (leviAct m B * swapN (m + 1)) (pairVec (ez m) 0) = pairVec 0 (ez m) := by
        change leviAct m B (swapN (m + 1) (pairVec (ez m) 0)) = _
        rw [swapN_pairVec, leviAct_pairVec_zero_ez]
      have h4 := congrFun (pairVec_inj.1 (h3.symm.trans h1)).1 0
      rw [ez_zero] at h4
      exact zero_ne_one h4
  · rintro g ⟨B, rfl⟩
    exact ⟨Lg_le_Mg (leviAct_mem_Lg B),
      mem_centSub_zpowers_sup_iff.2 ⟨leviAct_pairVec_ez_zero B, leviAct_pairVec_zero_ez B⟩⟩

end CFSG.ASVolI.ChH.PairStab
