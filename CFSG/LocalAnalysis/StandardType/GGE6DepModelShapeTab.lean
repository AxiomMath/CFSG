module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeFin

public section

namespace CFSG.StandardType

namespace E6Dep

@[expose] def rl (i : ℕ) : Mat6 := reflNorm (cen i)

@[expose] def idx (S : Finset Mat6) : Finset ℕ := (Finset.range 36).filter fun i => rl i ∈ S

private lemma cen_norm5 : ∀ i < 36, norm6 (cen i) = 1 ∧ (cen i) 5 = 0 := by
  decide +kernel

private lemma exists_cen_aux : ∀ v : Vec6, v 5 = 0 → norm6 v = 1 →
    ∃ c < 36, v = cen c ∨ v = -cen c := by
  decide +kernel

private lemma reflNorm_neg_cen : ∀ i < 36, reflNorm (-cen i) = rl i := by
  decide +kernel

private lemma gram6_transpose : gram6.transpose = gram6 := by
  decide +kernel

private lemma rl_nodup : ((List.range 36).map rl).Nodup := by
  decide +kernel

private lemma cjN_lt : ∀ a < 36, ∀ b < 36, cjN a b < 36 := by
  decide +kernel

private theorem rl_conj_0 : ∀ a < 6, ∀ b < 36, rl a * rl b * rl a = rl (cjN a b) := by
  decide +kernel

private theorem rl_conj_6 : ∀ a < 6, ∀ b < 36,
    rl (a + 6) * rl b * rl (a + 6) = rl (cjN (a + 6) b) := by
  decide +kernel

private theorem rl_conj_12 : ∀ a < 6, ∀ b < 36,
    rl (a + 12) * rl b * rl (a + 12) = rl (cjN (a + 12) b) := by
  decide +kernel

private theorem rl_conj_18 : ∀ a < 6, ∀ b < 36,
    rl (a + 18) * rl b * rl (a + 18) = rl (cjN (a + 18) b) := by
  decide +kernel

private theorem rl_conj_24 : ∀ a < 6, ∀ b < 36,
    rl (a + 24) * rl b * rl (a + 24) = rl (cjN (a + 24) b) := by
  decide +kernel

private theorem rl_conj_30 : ∀ a < 6, ∀ b < 36,
    rl (a + 30) * rl b * rl (a + 30) = rl (cjN (a + 30) b) := by
  decide +kernel

private lemma zmod_refl_aux : ∀ a c d : ZMod 3, a - (2 * c) * d = a + c * d := by
  decide +kernel

private lemma reflNorm_mulVec (u v : Vec6) : (reflNorm v).mulVec u = u + bil6 u v • v := by
  simp only [reflNorm, reflMat, bil6, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  rw [smul_dotProduct, dotProduct_comm]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact zmod_refl_aux (u i) (u ⬝ᵥ Matrix.mulVec gram6 v) (v i)

private lemma bil6_comm (u v : Vec6) : bil6 u v = bil6 v u := by
  have h : dotProduct u (Matrix.mulVec gram6 v) = dotProduct v (Matrix.mulVec gram6 u) := by
    have ht := Matrix.dotProduct_transpose_mulVec (A := gram6) u v
    rw [gram6_transpose] at ht
    exact ht
  simpa only [bil6] using h

private lemma bil6_neg_right (u v : Vec6) : bil6 u (-v) = -bil6 u v := by
  simp only [bil6, Matrix.mulVec_neg, dotProduct_neg]

private lemma bil6_smul_right (c : ZMod 3) (u v : Vec6) : bil6 u (c • v) = c * bil6 u v := by
  simp only [bil6, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma bil6_zero_right (u : Vec6) : bil6 u 0 = 0 := by
  simp only [bil6]
  simp

theorem rl_mem {i : ℕ} (hi : i < 36) : rl i ∈ refl36 := by
  rw [refl36, Finset.mem_image]
  refine ⟨cen i, ?_, rfl⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (cen_norm5 i hi).2, (cen_norm5 i hi).1⟩

theorem exists_rl_of_mem {t : Mat6} (ht : t ∈ refl36) : ∃ i < 36, rl i = t := by
  rw [refl36, Finset.mem_image] at ht
  obtain ⟨w, hw, hwt⟩ := ht
  rw [Finset.mem_filter] at hw
  obtain ⟨-, hw5, hwnorm⟩ := hw
  obtain ⟨c, hc, hwc⟩ := exists_cen_aux w hw5 hwnorm
  refine ⟨c, hc, ?_⟩
  rcases hwc with hwc | hwc
  · rw [hwc] at hwt
    simpa only [rl] using hwt
  · rw [hwc] at hwt
    rw [reflNorm_neg_cen c hc] at hwt
    exact hwt

theorem rl_injOn {i j : ℕ} (hi : i < 36) (hj : j < 36) (h : rl i = rl j) : i = j :=
  List.inj_on_of_nodup_map rl_nodup (List.mem_range.mpr hi) (List.mem_range.mpr hj) h

theorem rl_conj {a b : ℕ} (ha : a < 36) (hb : b < 36) : rl a * rl b * rl a = rl (cjN a b) := by
  rcases lt_or_ge a 6 with h0 | h0
  · exact rl_conj_0 a h0 b hb
  rcases lt_or_ge a 12 with h1 | h1
  · have ha' : a - 6 < 6 := by omega
    have hae : a = (a - 6) + 6 := by omega
    rw [hae]
    exact rl_conj_6 (a - 6) ha' b hb
  rcases lt_or_ge a 18 with h2 | h2
  · have ha' : a - 12 < 6 := by omega
    have hae : a = (a - 12) + 12 := by omega
    rw [hae]
    exact rl_conj_12 (a - 12) ha' b hb
  rcases lt_or_ge a 24 with h3 | h3
  · have ha' : a - 18 < 6 := by omega
    have hae : a = (a - 18) + 18 := by omega
    rw [hae]
    exact rl_conj_18 (a - 18) ha' b hb
  rcases lt_or_ge a 30 with h4 | h4
  · have ha' : a - 24 < 6 := by omega
    have hae : a = (a - 24) + 24 := by omega
    rw [hae]
    exact rl_conj_24 (a - 24) ha' b hb
  · have ha' : a - 30 < 6 := by omega
    have hae : a = (a - 30) + 30 := by omega
    rw [hae]
    exact rl_conj_30 (a - 30) ha' b hb

theorem exists_cen {v : Vec6} (hv5 : v 5 = 0) (hv : norm6 v = 1) :
    ∃ c < 36, v = cen c ∨ v = -cen c :=
  exists_cen_aux v hv5 hv

theorem zset_neg (v : Vec6) : zset (-v) = zset v := by
  ext i
  simp only [zset, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, h⟩
    rw [bil6_neg_right] at h
    exact ⟨hi, neg_eq_zero.mp h⟩
  · rintro ⟨hi, h⟩
    exact ⟨hi, by rw [bil6_neg_right, h, neg_zero]⟩

theorem idx_reflFix (v : Vec6) : idx (reflFix v) = zset v := by
  ext i
  simp only [idx, zset, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, hfix⟩
    rw [reflFix, Finset.mem_filter] at hfix
    have hformula : (rl i).mulVec v = v + bil6 v (cen i) • cen i := by
      simpa only [rl] using reflNorm_mulVec v (cen i)
    have hv : v + bil6 v (cen i) • cen i = v := by
      rw [← hformula]
      exact hfix.2
    have hzero : bil6 v (cen i) • cen i = 0 :=
      add_left_cancel (a := v)
        (show v + bil6 v (cen i) • cen i = v + 0 by rw [add_zero]; exact hv)
    have hww : bil6 (cen i) (cen i) = 1 := (cen_norm5 i hi).1
    have hbil : bil6 v (cen i) = 0 := by
      have h1 := congrArg (fun x => bil6 (cen i) x) hzero
      rw [bil6_smul_right, hww, mul_one] at h1
      exact h1.trans (bil6_zero_right (cen i))
    rw [bil6_comm] at hbil
    exact ⟨hi, hbil⟩
  · rintro ⟨hi, hbil⟩
    rw [reflFix, Finset.mem_filter]
    refine ⟨hi, rl_mem hi, ?_⟩
    have hformula : (rl i).mulVec v = v + bil6 v (cen i) • cen i := by
      simpa only [rl] using reflNorm_mulVec v (cen i)
    rw [hformula, bil6_comm, hbil, zero_smul, add_zero]

theorem idx_mono {S S' : Finset Mat6} (h : S ⊆ S') : idx S ⊆ idx S' := by
  intro i hi
  simp only [idx, Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨hi.1, h hi.2⟩

theorem idx_injOn {S S' : Finset Mat6} (hS : S ⊆ refl36) (hS' : S' ⊆ refl36)
    (h : idx S = idx S') : S = S' := by
  apply Finset.Subset.antisymm
  · intro t ht
    obtain ⟨i, hi, hri⟩ := exists_rl_of_mem (hS ht)
    have hiS : i ∈ idx S := by
      simp only [idx, Finset.mem_filter, Finset.mem_range]
      exact ⟨hi, by rw [hri]; exact ht⟩
    have hiS' : i ∈ idx S' := by rw [h] at hiS; exact hiS
    simp only [idx, Finset.mem_filter, Finset.mem_range] at hiS'
    rw [← hri]
    exact hiS'.2
  · intro t ht
    obtain ⟨i, hi, hri⟩ := exists_rl_of_mem (hS' ht)
    have hiS' : i ∈ idx S' := by
      simp only [idx, Finset.mem_filter, Finset.mem_range]
      exact ⟨hi, by rw [hri]; exact ht⟩
    have hiS : i ∈ idx S := by rw [← h] at hiS'; exact hiS'
    simp only [idx, Finset.mem_filter, Finset.mem_range] at hiS
    rw [← hri]
    exact hiS.2

theorem idx_insert {r : Mat6} (hr : r ∈ refl36) (S : Finset Mat6) :
    ∃ r' < 36, rl r' = r ∧ idx (insert r S) = insert r' (idx S) := by
  obtain ⟨r', hr'lt, hr'⟩ := exists_rl_of_mem hr
  refine ⟨r', hr'lt, hr', ?_⟩
  ext i
  simp only [idx, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨hi, hri | hri⟩
    · exact Or.inl (rl_injOn hi hr'lt (by rw [hri, ← hr']))
    · exact Or.inr ⟨hi, hri⟩
  · rintro (h | ⟨hi, hri⟩)
    · subst h
      exact ⟨hr'lt, Or.inl hr'⟩
    · exact ⟨hi, Or.inr hri⟩

theorem conjClosed_idx {S : Finset Mat6} (hS : S ⊆ refl36) (h : ConjClosed S) :
    CjClosed (idx S) := by
  intro a ha b hb
  simp only [idx, Finset.mem_filter, Finset.mem_range] at ha hb ⊢
  refine ⟨cjN_lt a ha.1 b hb.1, ?_⟩
  have hmem := h (rl a) ha.2 (rl b) hb.2
  rw [rl_conj ha.1 hb.1] at hmem
  exact hmem

theorem cjGen_of_conjGenerates {X : Finset Mat6} (hX : X ⊆ refl36)
    (h : ConjGenerates refl36 X) : CjGen (idx X) := by
  intro I hI hcl hXI
  set S : Finset Mat6 := I.image rl with hS
  have hSsub : S ⊆ refl36 := by
    intro t ht
    rw [hS] at ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    exact rl_mem (Finset.mem_range.mp (hI hi))
  have hScl : ConjClosed S := by
    intro a ha b hb
    rw [hS] at ha hb ⊢
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hjI, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨cjN i j, hcl i hiI j hjI, ?_⟩
    exact (rl_conj (Finset.mem_range.mp (hI hiI)) (Finset.mem_range.mp (hI hjI))).symm
  have hXS : X ⊆ S := by
    intro t ht
    rw [hS]
    obtain ⟨i, hi, hri⟩ := exists_rl_of_mem (hX ht)
    refine Finset.mem_image.mpr ⟨i, ?_, hri⟩
    exact hXI (by
      simp only [idx, Finset.mem_filter, Finset.mem_range]
      exact ⟨hi, by rw [hri]; exact ht⟩)
  have hSeq : S = refl36 := h S hSsub hScl hXS
  apply Finset.Subset.antisymm hI
  intro i hi36
  have hriS : rl i ∈ S := by rw [hSeq]; exact rl_mem (Finset.mem_range.mp hi36)
  rw [hS] at hriS
  obtain ⟨j, hjI, hrj⟩ := Finset.mem_image.mp hriS
  have hji : j = i := rl_injOn (Finset.mem_range.mp (hI hjI)) (Finset.mem_range.mp hi36) hrj
  rw [← hji]
  exact hjI

end E6Dep

end CFSG.StandardType

end
