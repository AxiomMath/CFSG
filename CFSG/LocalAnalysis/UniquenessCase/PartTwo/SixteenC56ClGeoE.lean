module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClGeoD2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

variable {W : Type} [CommGroup W] {S : OmegaModel W} {E : Subgroup (MulAut W)}

theorem Geo2.perp_fix_le_gammaCheck (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 4) : S.perp (fixV E) ≤ E3.gammaCheck 2 E := fun _ hh =>
  mem_gammaCheck_of_mQuot_stabAt_le (hE.mQuot_stabAt_le_two (U := fixV E)
    (fun _ he => hE.comm_mem_fix_of_mem_perp hSK hF hh he) hF.le)

theorem Geo2.mem_perp_of_comm_mem_fix (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 4) {e : MulAut W} (he : e ∈ E) (hne : e ≠ 1) {w : W}
    (hw : e w * w⁻¹ ∈ fixV E) : w ∈ S.perp (fixV E) := by
  classical
  haveI := S.finite_carrier
  by_contra hwp
  have hbot : fixV E ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hF; omega
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hz1' : (z : W) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hsm := S.exists_smul_eq_of_card_eq hE.isSub_fixV (by rw [hF, hSK]) z.2 hz1'
  have hwz : S.pol w z ≠ 0 := by
    intro h0
    apply hwp
    rw [S.mem_perp]
    intro f hf
    obtain ⟨c, rfl⟩ := hsm f hf
    rw [S.pol_smul_right, h0, mul_zero]
  have hzw : S.pol (z : W) w ≠ 0 := by rwa [S.pol_comm]
  have hew : e w = w := by
    obtain ⟨c, hc⟩ := hsm _ hw
    have hQ : S.Q (e w * w⁻¹) = 0 := hE.Q_eq_zero_of_card_fix_four hSK hF _ hw
    have h1 := S.Q_commutator_eq_pol (hE.iso e he) w
    rw [hQ, hc, S.pol_smul_right] at h1
    have hc0 : c = 0 := (mul_eq_zero.1 h1.symm).resolve_right hwz
    rw [hc0, S.smul_zero_eq] at hc
    exact mul_inv_eq_one.1 hc
  have hperp : ∀ x ∈ S.perp (fixV E), e x = x := by
    intro x hx
    have hδ := hE.comm_mem_fix_of_mem_perp hSK hF hx he
    obtain ⟨c, hc⟩ := hsm _ hδ
    have hpol : S.pol (e x) w = S.pol x w := by
      have := OmegaModel.pol_apply_apply_of_isometry (S := S) (hE.iso e he) x w
      rwa [hew] at this
    have hex : e x = (e x * x⁻¹) * x := (inv_mul_cancel_right _ _).symm
    rw [hex, S.pol_mul_left, hc, S.pol_smul_left] at hpol
    have hc0 : c = 0 := by
      have h2 : c * S.pol (z : W) w = 0 := by
        have := hpol
        rw [add_eq_right] at this
        exact this
      exact (mul_eq_zero.1 h2).resolve_right hzw
    rw [hc0, S.smul_zero_eq] at hc
    exact mul_inv_eq_one.1 hc
  set T : Subgroup W := S.perp (fixV E) ⊔ S.line w with hT
  have hw1 : w ∈ S.line w := ⟨1, (S.smul_one_eq w).symm⟩
  have hlt : S.perp (fixV E) < T := by
    refine lt_of_le_of_ne le_sup_left fun heq => hwp ?_
    rw [heq]
    exact Subgroup.mem_sup_right hw1
  have hc1 : 64 < Nat.card T := by
    rw [← hE.card_perp_fix hSK hF]; exact Subgroup.card_lt_of_lt hlt
  have hsup : S.IsSub T := S.isSub_sup (S.isSub_perp _) (S.isSub_line w)
  have hc3 : Nat.card T = 256 := by
    rcases S.card_isSub_cases hSK hsup with h | h | h | h | h <;> omega
  have hTtop : T = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, hc3, S.card_eq, hSK]
    norm_num
  apply hne
  refine MulEquiv.ext fun y => ?_
  have hy : y ∈ T := by rw [hTtop]; exact Subgroup.mem_top y
  obtain ⟨x, hx, l, ⟨c, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hy
  show e (x * S.smul c w) = x * S.smul c w
  rw [map_mul, hperp x hx, hE.lin e he c w, hew]

theorem Geo2.singLineShape_of_card_fix_four (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 4) : SingLineShape E where
  fix_ne_bot := fun h => by rw [h, Subgroup.card_bot] at hF; omega
  index_le := by
    haveI := S.finite_carrier
    have h1 : (S.perp (fixV E)).index * Nat.card (S.perp (fixV E)) = Nat.card W :=
      Subgroup.index_mul_card _
    rw [hE.card_perp_fix hSK hF, S.card_eq, hSK] at h1
    have h2 : (S.perp (fixV E)).index = 4 := by omega
    have h3 := Subgroup.index_dvd_of_le (hE.perp_fix_le_gammaCheck hSK hF)
    rw [h2] at h3
    exact Nat.le_of_dvd (by norm_num) h3
  fix_le_comm := by
    classical
    haveI := S.finite_carrier
    have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact S.mul_self_eq_one w
    obtain ⟨w, hwF, hw2⟩ :=
      exists_mem_secondLayer hW2 hE.elem (le_refl (fixV E)) (fixV_ne_top hE.ne_bot)
    intro f hf
    obtain ⟨e, he, hef⟩ := hE.comm_surj_of_card_fix_four hF hwF hw2 f hf
    exact ⟨e, he, w, hE.perp_fix_le_gammaCheck hSK hF (hE.secondLayer_le_perp hSK hF hw2), hef⟩
  mem_of_comm := fun _ he hne _ hw =>
    hE.perp_fix_le_gammaCheck hSK hF (hE.mem_perp_of_comm_mem_fix hSK hF he hne hw)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
