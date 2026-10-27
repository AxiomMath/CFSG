module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClGeoA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56AsetA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

variable {W : Type} [CommGroup W] {S : OmegaModel W} {E : Subgroup (MulAut W)}

theorem Geo2.gammaCheck_eq_top_of_card_fix_64 (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 64) : E3.gammaCheck 2 E = ⊤ := by
  have hperp : Nat.card (S.perp (fixV E)) ≤ 4 := by
    have h := S.card_mul_card_perp hE.isSub_fixV
    rw [hF, hSK] at h
    omega
  rw [Subgroup.eq_top_iff']
  intro w
  exact mem_gammaCheck_of_mQuot_stabAt_le (hE.mQuot_stabAt_le_two (U := S.perp (fixV E))
    (fun e he => S.commutator_mem_perp_fixV hE.iso he w) hperp)

theorem OmegaModel.le_perp_of_card_sq (S : OmegaModel W) (hSK : Nat.card S.K = 4)
    {F : Subgroup W} (hF : S.IsSub F) (hcard : Nat.card F = 16) (hR : F ⊓ S.perp F ≠ ⊥) :
    F ≤ S.perp F := by
  classical
  haveI := S.finite_carrier
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hR
  have hzF : (z : W) ∈ F := z.2.1
  have hzP : (z : W) ∈ S.perp F := z.2.2
  have hz1' : (z : W) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hlineF : S.line (z : W) ≤ F := by
    rintro _ ⟨c, rfl⟩
    exact hF c z hzF
  have hcl : Nat.card (S.line (z : W)) = 4 := by rw [S.card_line hz1', hSK]
  obtain ⟨u, huF, hu⟩ : ∃ u ∈ F, u ∉ S.line (z : W) := by
    by_contra hcon
    push Not at hcon
    have hle : F ≤ S.line (z : W) := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    omega
  set N : Subgroup W := S.line (z : W) ⊔ S.line u with hN
  have hNF : N ≤ F := sup_le hlineF (by rintro _ ⟨c, rfl⟩; exact hF c u huF)
  have hu1 : u ∈ S.line u := ⟨1, (S.smul_one_eq u).symm⟩
  have hlt : S.line (z : W) < N := by
    refine lt_of_le_of_ne le_sup_left fun heq => hu ?_
    rw [heq]
    exact Subgroup.mem_sup_right hu1
  have hc1 : 4 < Nat.card N := by
    rw [← hcl]; exact Subgroup.card_lt_of_lt hlt
  have hsup : S.IsSub N := S.isSub_sup (S.isSub_line _) (S.isSub_line u)
  have hc2 : Nat.card N ≤ 16 := by
    rw [← hcard]; exact Subgroup.card_le_of_le hNF
  have hc3 : Nat.card N = 16 := by
    rcases S.card_isSub_cases hSK hsup with h | h | h | h | h <;> omega
  have hNeq : N = F := Subgroup.eq_of_le_of_card_ge hNF (by rw [hc3, hcard])
  have hzu : S.pol (z : W) u = 0 := hzP u huF
  have huz : S.pol u (z : W) = 0 := by rw [S.pol_comm]; exact hzu
  intro x hx
  rw [S.mem_perp]
  intro y hy
  rw [← hNeq] at hx hy
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hx
  obtain ⟨_, ⟨a', rfl⟩, _, ⟨b', rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hy
  simp [S.pol_mul_left, S.pol_mul_right, S.pol_smul_left, S.pol_smul_right, S.pol_self, hzu, huz]

theorem Geo2.perp_eq_of_card_fix_16 (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 16) : S.perp (fixV E) = fixV E := by
  classical
  haveI := S.finite_carrier
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact S.mul_self_eq_one w
  obtain ⟨w, hwF, hw2⟩ :=
    exists_mem_secondLayer hW2 hE.elem (le_refl (fixV E)) (fixV_ne_top hE.ne_bot)
  have hU : ∀ e ∈ E, e w * w⁻¹ ∈ fixV E ⊓ S.perp (fixV E) := fun e he =>
    ⟨hw2 e he, S.commutator_mem_perp_fixV hE.iso he w⟩
  have h4 : 4 ≤ Nat.card ↥(fixV E ⊓ S.perp (fixV E)) := by
    have h1 := two_pow_mQuot_stabAt_le hE.elem hU
    have h2 : 2 ^ 2 ≤ 2 ^ E3.mQuot E (stabAt E w) :=
      Nat.pow_le_pow_right (by norm_num) (hE.two_le_mQuot_stabAt hwF)
    omega
  have hR : fixV E ⊓ S.perp (fixV E) ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at h4; omega
  have hle : fixV E ≤ S.perp (fixV E) := S.le_perp_of_card_sq hSK hE.isSub_fixV hF hR
  have hcp : Nat.card (S.perp (fixV E)) = 16 := by
    have h := S.card_mul_card_perp hE.isSub_fixV
    rw [hF, hSK] at h
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcp, hF])).symm

theorem Geo2.gammaCheck_eq_top_of_card_fix_16 (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 16) : E3.gammaCheck 2 E = ⊤ := by
  classical
  haveI := S.finite_carrier
  have hperp := hE.perp_eq_of_card_fix_16 hSK hF
  have hiso : ∀ x ∈ fixV E, ∀ y ∈ fixV E, S.pol x y = 0 := fun x hx y hy => by
    have : x ∈ S.perp (fixV E) := by rw [hperp]; exact hx
    exact this y hy
  obtain ⟨θ, hθF, hθ1, hθQ⟩ :=
    S.exists_singular_of_isotropic hiso (by rw [hF, hSK]; norm_num)
  have hcardF : Nat.card (fixV E) = Nat.card S.K ^ 2 := by rw [hF, hSK]; norm_num
  set T : Subgroup W := S.perp (S.line θ) with hT
  have hθ1' : θ ∈ S.line θ := ⟨1, (S.smul_one_eq θ).symm⟩
  have hTtop : T ≠ ⊤ := by
    intro htop
    apply hθ1
    apply S.eq_one_of_pol_eq_zero
    intro w'
    have hw' : w' ∈ T := by rw [htop]; exact Subgroup.mem_top w'
    rw [S.pol_comm]
    exact hw' θ hθ1'
  refine eq_top_of_forall_notMem hTtop fun w hwT => ?_
  have hw : S.pol w θ ≠ 0 := fun h0 => hwT (by
    rintro _ ⟨c, rfl⟩
    rw [S.pol_smul_right, h0, mul_zero])
  obtain ⟨N, hNF, hNcard, hN⟩ := S.exists_subgroup_card_le hE.isSub_fixV hiso hcardF hθF hθQ hw
  have hcomm : ∀ e ∈ E, e w * w⁻¹ ∈ N := fun e he => by
    apply hN
    · have h := S.commutator_mem_perp_fixV hE.iso he w
      rwa [hperp] at h
    · exact S.Q_commutator_eq_pol (hE.iso e he) w
  rw [hSK] at hNcard
  exact mem_gammaCheck_of_mQuot_stabAt_le (hE.mQuot_stabAt_le_two hcomm hNcard)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
