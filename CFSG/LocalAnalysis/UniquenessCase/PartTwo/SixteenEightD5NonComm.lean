module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Family
public import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
  {K : Fin 4 → Subgroup (MulAut W)} {Z : Fin 4 → Subgroup W}

private lemma s16e_d5_fix_of_comm (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    {a : Fin 4 → MulAut W} (hfam : s16e_d5_CoordFam A L Z a) {t : MulAut W} (ht2 : t ^ 2 = 1)
    {i : Fin 4} (hci : a i * t = t * a i) : ∀ z ∈ Z i, t z = z := by
  have hξ3 : (a i) ^ 3 = 1 := s16e_d5_cent_pow_three hfr (hfam.mem_cent i)
  have hξZ : ∀ z ∈ Z i, a i z ∈ Z i :=
    fun z hz => s16e_d5_cent_stable hfr (hfam.mem_cent i) i hz
  have hfix : ∀ z ∈ Z i, a i z = z → z = 1 :=
    fun z hz hz' => s16e_d5_cent_fix hfr (hfam.mem_cent i) (hfam.off i) (hfam.ne_one i) hz hz'
  have htt : ∀ z : W, t (t z) = z := by
    intro z
    have h := congrArg (fun f : MulAut W => f z) ht2
    simpa [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have hconj : (MulAut.conj t).toMonoidHom (a i) = a i := by
    change MulAut.conj t (a i) = a i
    rw [MulAut.conj_apply, ← hci, mul_assoc, mul_inv_cancel, mul_one]
  have hX : (Subgroup.zpowers (a i)).map (MulAut.conj t).toMonoidHom =
      Subgroup.zpowers (a i) := by
    rw [MonoidHom.map_zpowers, hconj]
  have hZi : Z i = commSub ⊤ (Subgroup.zpowers (a i)) :=
    (s16e_d5_commSub_zpowers hfr (hfam.mem_cent i) (hfam.off i) (hfam.ne_one i)).symm
  have hmap : (Z i).map t.toMonoidHom = Z i := by
    have h := Asc81c.commSub_map_conj (Subgroup.zpowers (a i)) t
    rw [hX] at h
    rw [← hZi] at h
    exact h.symm
  have hgZ : ∀ z ∈ Z i, t z ∈ Z i := by
    intro z hz
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hcomm : ∀ z ∈ Z i, t (a i z) = a i (t z) := by
    intro z hz
    have h := congrArg (fun f : MulAut W => f z) hci
    simpa [MulAut.mul_apply] using h.symm
  obtain ⟨e, he3, hte⟩ :=
    s16e_d5_schur_local (Z := Z i) (ξ := a i) (g := t) (hfr.card_Z i) hξ3 hξZ hfix hgZ hcomm
  have he0 : e = 0 := by
    by_contra he
    have he12 : e = 1 ∨ e = 2 := by omega
    have hbot : Z i = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall (Z i)).mpr fun z hz => ?_
      have hzz : (a i ^ e) ((a i ^ e) z) = z := by
        rw [← hte z hz, ← hte (t z) (hgZ z hz), htt z]
      have hpow : (a i ^ (e + e)) z = z := by
        rw [pow_add, MulAut.mul_apply]
        exact hzz
      rcases he12 with rfl | rfl
      · exact s16e_d5_pow_fix hξ3 hfix (e := 2) (by norm_num) (by norm_num) z hz
          (by simpa using hpow)
      · have h4 : a i ^ (2 + 2) = a i := by
          rw [show (2 : ℕ) + 2 = 3 + 1 by norm_num, pow_add, hξ3, one_mul, pow_one]
        exact hfix z hz (by rw [h4] at hpow; exact hpow)
    exact hfr.Z_ne_bot i hbot
  intro z hz
  rw [hte z hz, he0, pow_zero, MulAut.one_apply]

theorem s16e_d5_noncomm (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    {a : Fin 4 → MulAut W} (hfam : s16e_d5_CoordFam A L Z a) {t : MulAut W} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) : ∃ i, a i * t ≠ t * a i := by
  by_contra hcon
  have hcon' : ∀ i, a i * t = t * a i := fun i => by
    by_contra h
    exact hcon ⟨i, h⟩
  have hfix : ∀ i, ∀ z ∈ Z i, t z = z := fun i => s16e_d5_fix_of_comm hfr hfam ht2 (hcon' i)
  have hall : ∀ w : W, t w = w := by
    intro w
    have hw : w ∈ ⨆ i, Z i := by rw [hfr.Z_top]; exact Subgroup.mem_top w
    refine Subgroup.iSup_induction Z (C := fun w => t w = w) hw ?_ ?_ ?_
    · intro k z hz
      exact hfix k z hz
    · exact map_one t
    · intro x y hx hy
      rw [map_mul, hx, hy]
  exact ht1 (MulEquiv.ext hall)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
