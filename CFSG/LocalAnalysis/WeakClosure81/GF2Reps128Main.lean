module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Three
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128D

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

theorem w4Lem12_8_of (hD : W4Lem6_3Swap) : W4Lem12_8 := by
  intro W _ _ hW Y hO hB L hL H hH
  by_cases hd : dMinDeg ↥L ≤ E3.mParam Y
  · exact Or.inl hd
  push Not at hd
  obtain ⟨h1, hLH, hHY, hn, hnorm, hHne⟩ := h_facts hL hH
  have hnorm' : ∀ g ∈ Y, ∀ x ∈ H, g⁻¹ * x * g ∈ H := fun g hg x hx => by
    simpa using hn g⁻¹ (Y.inv_mem hg) x hx
  have hLne : L ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L).mp (CFSG.LocalCores.isQuasisimple_nontrivial
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.2.2))
  have htop : (⨆ I ∈ irrSet H, I) = ⊤ :=
    ((w4Lem12_5_holds W hW Y hO hB H hHne hHY hnorm).2 L hL h1).1.1
  by_cases hev : Even (Nat.card Y)
  swap
  ·
    exfalso
    have hmY : E3.mParam Y = rk W := by simp only [E3.mParam, hev, ↓reduceIte]
    have hnt : ¬ (⊤ : Subgroup W) ≤ fixV L := by
      intro h
      apply hLne
      rw [eq_bot_iff]
      intro l hl
      rw [Subgroup.mem_bot]
      exact MulEquiv.ext fun w => h (Subgroup.mem_top w) l hl
    have h2 := dMinDeg_le_rk_of_not_le_fixV hW (fun _ _ _ _ => Subgroup.mem_top _) hnt
    rw [rk_top] at h2
    omega
  have hne : {n : ℕ | ∃ t ∈ Y, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))}.Nonempty := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 (even_iff_two_dvd.mp hev)
    exact ⟨_, x.1, x.2, (Subgroup.orderOf_coe x).trans hx, rfl⟩
  obtain ⟨t, htY, ht2, hteq⟩ := Nat.sInf_mem hne
  have hmY : E3.mParam Y = rkIdx (fixV (Subgroup.zpowers t)) := by
    simp only [E3.mParam, hev, ↓reduceIte]
    exact hteq
  by_cases hmove : ∃ I ∈ irrSet H, I.map t.toMonoidHom ≠ I
  · obtain ⟨I, hI, hIt⟩ := hmove
    exact Or.inl (hmY ▸ dMinDeg_le_of_map_ne hW hL hH htY hI hIt)
  push Not at hmove
  have htI : ∃ I ∈ irrSet H, ¬ commSub I (Subgroup.zpowers t) ≤ fixV H := by
    by_contra hall
    push Not at hall
    have ht1 : t = 1 := by
      refine eq_one_of_mem_fixV_quot hW hO hB hL hH htY fun w => ?_
      have hw : w ∈ ⨆ I ∈ irrSet H, I := by rw [htop]; trivial
      rw [iSup_subtype'] at hw
      refine Subgroup.iSup_induction (fun I : irrSet H => (I : Subgroup W))
        (C := fun w => t w * w⁻¹ ∈ fixV H) hw ?_ ?_ ?_
      · intro I w hw
        exact hall I I.2 (Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, w, hw, rfl⟩)
      · simp
      · intro a b ha hb
        have he : t (a * b) * (a * b)⁻¹ = (t a * a⁻¹) * (t b * b⁻¹) := by
          rw [map_mul, mul_inv, mul_mul_mul_comm]
        rw [he]
        exact (fixV H).mul_mem ha hb
    rw [ht1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  obtain ⟨I₀, hI₀, htI₀⟩ := htI
  obtain ⟨X, ⟨h, hh, rfl⟩, hXI₀⟩ := exists_conj_not_le hL hH hI₀
  have hgY : h⁻¹ ∈ Y := Y.inv_mem hh
  have ht'Y : h⁻¹ * t * h⁻¹⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hgY htY) (Y.inv_mem hgY)
  have ht'2 : orderOf (h⁻¹ * t * h⁻¹⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact ht2
  have hU : I₀.map h⁻¹.toMonoidHom ∈ irrSet H := map_mem_irrSet (hn _ hgY) (hnorm' _ hgY) hI₀
  have hfix' : ∀ I ∈ irrSet H, I.map (h⁻¹ * t * h⁻¹⁻¹).toMonoidHom = I := by
    intro I hI
    have hJ : I.map h⁻¹⁻¹.toMonoidHom ∈ irrSet H :=
      map_mem_irrSet (hn _ (Y.inv_mem hgY)) (hnorm' _ (Y.inv_mem hgY)) hI
    have h2 := hmove _ hJ
    have e : (h⁻¹ * t * h⁻¹⁻¹).toMonoidHom =
        h⁻¹.toMonoidHom.comp (t.toMonoidHom.comp h⁻¹⁻¹.toMonoidHom) := by
      ext x
      simp [MulAut.mul_apply]
    rw [e, ← Subgroup.map_map, ← Subgroup.map_map, h2, Subgroup.map_map]
    ext x
    simp
  have hmin' : rkIdx (fixV (Subgroup.zpowers (h⁻¹ * t * h⁻¹⁻¹))) = E3.mParam Y := by
    rw [hmY, CFSG.Quasithin.fixV_zpowers_conj]
    unfold rkIdx
    rw [Subgroup.index_map_of_bijective h⁻¹.bijective]
  have hm : rkIdx (fixV (Subgroup.zpowers (h⁻¹ * t * h⁻¹⁻¹))) < dMinDeg ↥L := hmin' ▸ hd
  have hLU : ¬ commSub (I₀.map h⁻¹.toMonoidHom) L ≤ fixV H := by
    have h2 := not_commSub_le_map_conj hL hH hgY hXI₀
    rwa [CFSG.Quasithin.B19.map_conj_map_conj, inv_mul_cancel,
      CFSG.Quasithin.Asc81c.Pf.map_conj_one] at h2
  have htU : ¬ commSub (I₀.map h⁻¹.toMonoidHom) (Subgroup.zpowers (h⁻¹ * t * h⁻¹⁻¹)) ≤
      fixV H := by
    have h2 := not_commSub_le_map_conj hL hH hgY htI₀
    rwa [MonoidHom.map_zpowers] at h2
  rcases local_cases hD hW hO hB hL hH ht'Y ht'2 hfix' hm hU hLU htU with
    ⟨hLt, hLc, huniqU⟩ | ⟨hmove', -, -⟩
  ·
    have huniq := forall_unique_of_unique hW hO hB hL hH hU huniqU
    obtain ⟨I, hI, hbound⟩ := exists_mul_le_rkIdx hW hO hB hL hH ht'Y ht'2 hfix' hLt hLc huniq
    refine Or.inr (Or.inl ⟨isDirSumOver_of_unique hW hO hB hL hH huniq, I, hI, ?_⟩)
    rw [← hmin']
    exact hbound
  ·
    exact Or.inr (Or.inr (case_three_of_moves hD hW hO hB hL hH ht'Y ht'2 hfix' hmin' hd hU hLU
      htU hmove'))

theorem w4Lem12_8_holds : W4Lem12_8 :=
  w4Lem12_8_of w4Lem6_3Swap_holds

end CFSG.LocalAnalysis.WeakClosure81
