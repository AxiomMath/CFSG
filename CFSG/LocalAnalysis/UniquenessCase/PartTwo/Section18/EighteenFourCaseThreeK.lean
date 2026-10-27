module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCaseThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RTheta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RModel
public import CFSG.GroupTheory.SubgroupCardMul

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem k_OmegaFour_scalarOfLine_holds : K_OmegaFour_scalarOfLine := by
  intro W _ _ S hK a haN ha3 hline
  obtain ⟨e, he1, _heQ, hfix⟩ := hline
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha_lin : a ∈ OmegaModel.linSub S := by
    have hle : Subgroup.zpowers a ≤ OmegaModel.linSub S := by
      refine OmegaModel.le_linSub_of_isPGroup_three S hK ?_ (Subgroup.zpowers_le.mpr haN)
      refine IsPGroup.of_card_dvd_pow (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one ha3
    exact hle (Subgroup.mem_zpowers a)
  obtain ⟨z, hz, h, hh, hzh⟩ :=
    (OmegaModel.mem_scalarSub_sup_isoSub_iff S (g := a)).mp
      (OmegaModel.omegaNorm_inf_linSub_le_sup S ⟨haN, ha_lin⟩)
  have hh_lin : h ∈ OmegaModel.linSub S := ((OmegaModel.mem_isoSub_iff S).mp hh).1
  have hcomm : Commute z h := OmegaModel.scalarSub_commute S hz hh_lin
  have hz3 : z ^ 3 = 1 := by
    have h' := pow_card_eq_one' (G := OmegaModel.scalarSub S) (x := ⟨z, hz⟩)
    rw [OmegaModel.card_scalarSub_of_card_four S hK] at h'
    simpa using congrArg Subtype.val h'
  have hh3 : h ^ 3 = 1 := by
    have h1 : (z * h) ^ 3 = z ^ 3 * h ^ 3 := hcomm.mul_pow 3
    rw [hzh, ha3, hz3, one_mul] at h1
    exact h1.symm
  have hω0 : Nat.card S.omega0 = 3600 := by
    rw [OmegaModel.card_omega0_eq S, hK]
    norm_num
  have hωge : 3600 ≤ Nat.card S.omega := by
    have hdvd : Nat.card S.omega0 ∣ Nat.card S.omega :=
      Subgroup.card_dvd_of_le (OmegaModel.omega0_le_omega S)
    rw [hω0] at hdvd
    exact Nat.le_of_dvd (Nat.card_pos (α := ↥S.omega)) hdvd
  have hIcard : Nat.card (OmegaModel.isoSub S) = 7200 :=
    OmegaModel.card_isoSub_of_card_four S hK
  have hωI : S.omega ≤ OmegaModel.isoSub S := OmegaModel.omega_le_isoSub S
  have hhΩ : h ∈ S.omega := by
    by_contra hnot
    have : Finite (MulAut W) :=
      Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective
    have hzp : Nat.card (Subgroup.zpowers h) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hh3 (by
        intro h1
        exact hnot (by rw [h1]; exact S.omega.one_mem))
    have hinf : Subgroup.zpowers h ⊓ S.omega = ⊥ := by
      have hdvd : Nat.card ↥(Subgroup.zpowers h ⊓ S.omega) ∣ 3 := by
        rw [← hzp]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exact (Subgroup.eq_bot_iff_card (H := Subgroup.zpowers h ⊓ S.omega)).mpr h1
      · exfalso
        have heq : Subgroup.zpowers h ⊓ S.omega = Subgroup.zpowers h :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hzp])
        have hle : Subgroup.zpowers h ≤ S.omega := by
          rw [← heq]
          exact inf_le_right
        exact hnot (hle (Subgroup.mem_zpowers h))
    have hle := CFSG.card_mul_card_le_of_inf_eq_bot (A := OmegaModel.isoSub S)
      (D := Subgroup.zpowers h) (D' := S.omega) (Subgroup.zpowers_le.mpr hh) hωI hinf
    rw [hzp, hIcard] at hle
    omega
  have hz_ne : z ≠ 1 := by
    intro hz1
    have ha_eq : a = h := by rw [← hzh, hz1, one_mul]
    have haω : a ∈ S.omega := by rw [ha_eq]; exact hhΩ
    have hae : a e = e := (hfix e).mpr ⟨1, (OmegaModel.smul_one_eq S e).symm⟩
    have hae' : a⁻¹ e = e := by
      have h := congrArg (fun w => a⁻¹ w) hae
      simpa using h.symm
    have hiso : ∀ w : W, S.Q (a w) = S.Q w := fun w => OmegaModel.omega_Q S haω w
    have hpol : ∀ y : W, S.pol e y = 0 := by
      intro y
      have hu : a (y * (a y) * (a (a y))) = y * (a y) * (a (a y)) := by
        have h3y : a (a (a y)) = y := by
          have h := congrArg (fun f : MulAut W => f y) ha3
          simpa [pow_succ, MulAut.mul_apply] using h
        simp only [map_mul]
        rw [h3y]
        ac_rfl
      obtain ⟨c, hc⟩ := (hfix _).mp hu
      have h1 : S.pol e (y * (a y) * (a (a y))) = 0 := by
        rw [hc, OmegaModel.pol_smul_right, OmegaModel.pol_self, mul_zero]
      have h2 : S.pol e (y * (a y) * (a (a y))) =
          S.pol e y + S.pol e (a y) + S.pol e (a (a y)) := by
        rw [OmegaModel.pol_mul_right, OmegaModel.pol_mul_right]
      have h3 : S.pol e (a y) = S.pol e y := by
        have hp := OmegaModel.pol_apply_apply_of_isometry S hiso (a⁻¹ e) y
        rw [MulAut.apply_inv_self, hae'] at hp
        exact hp
      have h4 : S.pol e (a (a y)) = S.pol e y := by
        have hp := OmegaModel.pol_apply_apply_of_isometry S hiso (a⁻¹ e) (a y)
        rw [MulAut.apply_inv_self, hae', h3] at hp
        exact hp
      have hsum : S.pol e y + S.pol e y + S.pol e y = 0 := by
        rw [h3, h4] at h2
        rw [h2] at h1
        exact h1
      have hxx : S.pol e y + S.pol e y = 0 := by
        rw [← two_mul (S.pol e y),
          show (2 : S.K) = 0 from CharP.cast_eq_zero S.K 2, zero_mul]
      rw [hxx] at hsum
      simpa using hsum
    exact he1 (OmegaModel.eq_one_of_pol_eq_zero S hpol)
  refine ⟨h, hhΩ, ?_, ?_, ?_⟩
  · have haz : a * h⁻¹ = z := by rw [← hzh]; group
    rw [haz]
    exact hz_ne
  · have haz : a * h⁻¹ = z := by rw [← hzh]; group
    rw [haz]
    exact hz3
  · have haz : a * h⁻¹ = z := by rw [← hzh]; group
    rw [haz]
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg_lin : g ∈ OmegaModel.linSub S :=
      (OmegaModel.mem_linSub_iff S).mpr (fun c w => OmegaModel.omega_smul S hg c w)
    exact (OmegaModel.scalarSub_commute (z := z) (g := g) S hz hg_lin).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
