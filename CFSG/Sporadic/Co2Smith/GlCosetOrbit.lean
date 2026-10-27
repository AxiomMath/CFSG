module

public import CFSG.Sporadic.Co2Smith.GlCosetFacts

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Sporadic.Co2Rank3 CFSG.Sporadic.Co2Rank3.Native MulAction

theorem zero_not_mem_co2Delta : (0 : Fin 2300) ∉ orbit co2P0 (3 : Fin 2300) := by
  intro h
  obtain ⟨k, hk, e⟩ := mem_orbit_subgroup_iff.1 h
  have h0 : k • (0 : Fin 2300) = 0 := mem_stabilizer_iff.1 hk.2
  rw [← h0] at e
  have e' := congrArg (fun t : Fin 2300 => k⁻¹ • t) e
  simp only [inv_smul_smul] at e'
  exact absurd e' (by decide)


theorem cPerm_val {x : ℕ} (hx : x < 2300) :
    ((cPerm ⟨x, hx⟩ : Fin 2300) : ℕ) = Native.glCArr[x]! :=
  (rep_glCArr ⟨x, hx⟩).symm


theorem not_mem_orbit_co2P0_of_label {y : Fin 2300} (hy : y ∈ orbit co2P0 (3 : Fin 2300))
    {r : Fin 2300} {n : ℕ} (hrn : (r : ℕ) = n) (hr : p0Rec.1[n]! = 1) : y ∉ orbit co2P0 r := by
  intro h
  have h1 := mem_orbit_co2P0.1 h
  have h3 := mem_orbit_co2P0.1 hy
  rw [hrn, hr] at h1
  rw [show ((3 : Fin 2300) : ℕ) = 3 from rfl, p0Rec_three, h1] at h3
  exact absurd h3 (by norm_num)


theorem exists_mem_orbit_co2N {y : Fin 2300} (hy : y ∈ orbit co2P0 (3 : Fin 2300)) :
    ∃ x ∈ Native.glWit0Pts 1, ∃ hx : x < 2300, y ∈ orbit co2N (cPerm ⟨x, hx⟩) := by
  obtain ⟨hl578, hl3, hl487, -, hl2, -, hpts⟩ := glCosetLab_parts
  obtain ⟨r, hr, hrl⟩ := co2N_rec.2.1 y
  have hroot := co2N_rec.2.2.1 r hr
  have key : ∀ x (hx : x < 2300), x ∈ [578, 3, 487, 1172] →
      stabRec.1[Native.glCArr[x]!]! = r.1 →
      ∃ x ∈ Native.glWit0Pts 1, ∃ hx : x < 2300, y ∈ orbit co2N (cPerm ⟨x, hx⟩) :=
    fun x hx hmem hl => ⟨x, hpts x hmem, hx, (co2N_rec.1 _ y).2 (by
      rw [← hrl, cPerm_val hx, hl])⟩
  have hsub : ∀ z : Fin 2300, y ∈ orbit co2N z → y ∈ orbit co2P0 z :=
    fun z h => orbit_subgroup_mono co2N_le_P0 z h
  have hmem : ∀ (z : Fin 2300) (n : ℕ), (z : ℕ) = n → stabRec.1[n]! = n → r.1 = n →
      y ∈ orbit co2N z := fun z n hzn hz hrz => (co2N_rec.1 z y).2 (by
        rw [← hrl, hrz, hzn, hz])
  simp only [stabRoots, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hroot hrl key hmem
  · exfalso
    have h0 := hmem 0 0 rfl hroot rfl
    rw [orbit_subgroup_eq_singleton fun _ hk => mem_stabilizer_iff.1 (co2N_le hk).1.2] at h0
    rw [Set.mem_singleton_iff.1 h0] at hy
    exact zero_not_mem_co2Delta hy
  · exact absurd (hsub 1 (hmem 1 1 rfl hroot rfl)) (not_mem_orbit_co2P0_of_label hy rfl p0Rec_one)
  · exact absurd (hsub 2 (hmem 2 2 rfl hroot rfl)) (not_mem_orbit_co2P0_of_label hy rfl hl2)
  · refine key 1172 (by norm_num) (by simp) ?_
    rw [glC_spec.2.2.2.1]
    exact hroot
  · exact key 3 (by norm_num) (by simp) hl3
  · exact key 487 (by norm_num) (by simp) hl487
  · exact key 578 (by norm_num) (by simp) hl578

theorem exists_mem_orbit_co2P01 {y : Fin 2300} (hy : y ∈ orbit co2P0 (3 : Fin 2300)) :
    ∃ x ∈ Native.glWit0Pts 1, ∃ hx : x < 2300, y ∈ orbit co2P01 (cPerm ⟨x, hx⟩) := by
  obtain ⟨-, -, -, hl3, hl2, hl8, hpts⟩ := glCosetLab_parts
  obtain ⟨r, hr, hrl⟩ := co2P01_rec.2.1 y
  have hroot := co2P01_rec.2.2.1 r hr
  have hsub : ∀ z : Fin 2300, y ∈ orbit co2P01 z → y ∈ orbit co2P0 z :=
    fun z h => orbit_subgroup_mono inf_le_left z h
  have hmem : ∀ (z : Fin 2300) (n : ℕ), (z : ℕ) = n → p01Rec.1[n]! = n → r.1 = n →
      y ∈ orbit co2P01 z := fun z n hzn hz hrz => (co2P01_rec.1 z y).2 (by
        rw [← hrl, hrz, hzn, hz])
  simp only [p01Roots, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hroot hrl hmem
  · exfalso
    have h0 := hmem 0 0 rfl hroot rfl
    rw [orbit_subgroup_eq_singleton (K := co2P01) fun _ hk => mem_stabilizer_iff.1 hk.1.2]
      at h0
    rw [Set.mem_singleton_iff.1 h0] at hy
    exact zero_not_mem_co2Delta hy
  · exact absurd (hsub 1 (hmem 1 1 rfl hroot rfl)) (not_mem_orbit_co2P0_of_label hy rfl p0Rec_one)
  · exact absurd (hsub 2 (hmem 2 2 rfl hroot rfl)) (not_mem_orbit_co2P0_of_label hy rfl hl2)
  · refine ⟨1172, hpts 1172 (by simp), by norm_num, (co2P01_rec.1 _ y).2 ?_⟩
    rw [← hrl, cPerm_val, glC_spec.2.2.2.1, hroot]
  · exact ⟨3, hpts 3 (by simp), by norm_num, (co2P01_rec.1 _ y).2 (by
      rw [← hrl, cPerm_val (by norm_num), hl3])⟩
  · exact absurd (hsub 8 (hmem 8 8 rfl hroot rfl)) (not_mem_orbit_co2P0_of_label hy rfl hl8)

end CFSG.Sporadic.Co2Smith
