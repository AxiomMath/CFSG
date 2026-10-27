module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClGeoA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56AsetA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

variable {W : Type} [CommGroup W] {S : OmegaModel W} {E : Subgroup (MulAut W)}

theorem Geo2.pol_eq_zero_of_card_fix_four (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 4) : ∀ x ∈ fixV E, ∀ y ∈ fixV E, S.pol x y = 0 := by
  have hbot : fixV E ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hF; omega
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hz1' : (z : W) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hsm := S.exists_smul_eq_of_card_eq hE.isSub_fixV (by rw [hF, hSK]) z.2 hz1'
  intro x hx y hy
  obtain ⟨a, rfl⟩ := hsm x hx
  obtain ⟨b, rfl⟩ := hsm y hy
  rw [S.pol_smul_left, S.pol_smul_right, S.pol_self, mul_zero, mul_zero]

theorem Geo2.comm_surj_of_card_fix_four (hE : Geo2 S E) (hF : Nat.card (fixV E) = 4) {w : W}
    (hw : w ∉ fixV E) (hw2 : ∀ e ∈ E, e w * w⁻¹ ∈ fixV E) :
    ∀ f ∈ fixV E, ∃ e ∈ E, e w * w⁻¹ = f := by
  haveI := S.finite_carrier
  refine exists_comm_eq_of_card_le hE.elem hw2 ?_
  rw [hF]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ E3.mQuot E (stabAt E w) := Nat.pow_le_pow_right (by norm_num)
        (hE.two_le_mQuot_stabAt hw)

theorem Geo2.Q_eq_zero_of_card_fix_four (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 4) : ∀ z ∈ fixV E, S.Q z = 0 := by
  classical
  haveI := S.finite_carrier
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact S.mul_self_eq_one w
  obtain ⟨w, hwF, hw2⟩ :=
    exists_mem_secondLayer hW2 hE.elem (le_refl (fixV E)) (fixV_ne_top hE.ne_bot)
  intro z hz
  have key : ∀ c : S.K, c ^ 2 * S.Q z = c * S.pol w z := by
    intro c
    obtain ⟨e, he, hec⟩ := hE.comm_surj_of_card_fix_four hF hwF hw2 (S.smul c z)
      (hE.isSub_fixV c z hz)
    have h := S.Q_commutator_eq_pol (hE.iso e he) w
    rw [hec, S.Q_smul, S.pol_smul_right] at h
    exact h
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : S.K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    letI := Fintype.ofFinite S.K
    have hcard : Fintype.card S.K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hSK
    have hsub : (Finset.univ : Finset S.K) ⊆ {0, 1} := fun c _ => by
      by_cases h0 : c = 0
      · simp [h0]
      · simp [hcon c h0]
    have h2 := Finset.card_le_card hsub
    have h3 : ({0, 1} : Finset S.K).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, hcard] at h2
    omega
  have h1 := key 1
  have hω := key ω
  have hp : S.pol w z = S.Q z := by simpa using h1.symm
  rw [hp] at hω
  have h0 : ω * (ω - 1) * S.Q z = 0 := by
    have : ω * (ω - 1) * S.Q z = ω ^ 2 * S.Q z - ω * S.Q z := by ring
    rw [this, hω, sub_self]
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h (mul_ne_zero hω0 (sub_ne_zero.2 hω1))
  · exact h

theorem Geo2.pol_eq_zero_of_secondLayer (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 4) {w : W} (hw2 : ∀ e ∈ E, e w * w⁻¹ ∈ fixV E) :
    ∀ z ∈ fixV E, S.pol w z = 0 := by
  intro z hz
  by_cases hw : w ∈ fixV E
  · exact hE.pol_eq_zero_of_card_fix_four hSK hF w hw z hz
  · obtain ⟨e, he, hec⟩ := hE.comm_surj_of_card_fix_four hF hw hw2 z hz
    have h := S.Q_commutator_eq_pol (hE.iso e he) w
    rw [hec] at h
    rw [← h]
    exact hE.Q_eq_zero_of_card_fix_four hSK hF z hz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
