module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154DeltaSupp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

theorem s168e3_kernel_of_transitive
    {W : Type*} [CommGroup W] [Finite W]
    {p : ℕ} (hp : p.Prime) {A : Subgroup (MulAut W)}
    (hcop : ¬ p ∣ Nat.card W)
    (hrank : CFSG.Open.pRank p A ≤ 2)
    (htrans : ∀ u x : W, u ≠ 1 → x ≠ 1 →
      ∃ g ∈ A, g u = x) :
    S168e3Kernel A p := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨hrank, ?_⟩
  intro x hx1 E hEA hEel
  have hEcomm : ∀ a b : ↥E, a * b = b * a := s16h_dc_comm_of_elem hEel
  have hEpow : ∀ a : ↥E, a ^ p = 1 := s16h_dc_pow_eq_one_of_elem hEel
  have hEcard : Nat.card ↥E = p ^ 2 := s16h_dc_card_of_elem hEel
  let : CFSG.IsElementaryAbelian p ↥E :=
    { toIsMulCommutative := IsMulCommutative.of_comm hEcomm
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hEpow }
  let : MulDistribMulAction ↥E W := MulDistribMulAction.compHom W E.subtype
  have hgen : (⨆ (a : ↥E) (_ : a ≠ 1),
      CFSG.fixedPointSubgroup (Subgroup.zpowers a) W) = ⊤ :=
    CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := ↥E) (H := W)
      (by rw [hEcard]) hcop
  have hsome : ∃ a : ↥E, a ≠ 1 ∧
      CFSG.fixedPointSubgroup (Subgroup.zpowers a) W ≠ ⊥ := by
    by_contra h
    have hbotall : ∀ a : ↥E, a ≠ 1 →
        CFSG.fixedPointSubgroup (Subgroup.zpowers a) W = ⊥ := by
      intro a ha
      by_contra hne
      exact h ⟨a, ha, hne⟩
    have hbot : (⨆ (a : ↥E) (_ : a ≠ 1),
        CFSG.fixedPointSubgroup (Subgroup.zpowers a) W) = ⊥ :=
      iSup₂_eq_bot.mpr hbotall
    rw [hgen] at hbot
    have htop : (⊤ : Subgroup W) ≠ ⊥ := by
      intro hh
      have hx : x ∈ (⊥ : Subgroup W) := by rw [← hh]; exact Subgroup.mem_top x
      exact hx1 (Subgroup.mem_bot.mp hx)
    exact htop hbot
  obtain ⟨a, ha1, hane⟩ := hsome
  obtain ⟨u, hu1sub⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hane
  have hu : (u : W) ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers a) W := u.2
  have hu1 : (u : W) ≠ 1 := fun h => hu1sub (Subtype.ext h)
  have hau : a • (u : W) = (u : W) :=
    (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a (u : W)).mp hu
  have hb0u : (a : MulAut W) (u : W) = (u : W) := by
    simpa [MulDistribMulAction.compHom, Subgroup.smul_def, MulAut.smul_def] using hau
  obtain ⟨g, hgA, hgu⟩ := htrans (u : W) x hu1 hx1
  refine ⟨g, hgA, (a : MulAut W), a.2, ?_, ?_⟩
  · intro hb
    exact ha1 (Subtype.ext hb)
  · have hgu' : g⁻¹ x = (u : W) := by
      simpa using (congrArg (fun y : W => g⁻¹ y) hgu).symm
    calc (g * (a : MulAut W) * g⁻¹) x
        = g ((a : MulAut W) (g⁻¹ x)) := by simp [MulAut.mul_apply]
      _ = g ((a : MulAut W) (u : W)) := by rw [hgu']
      _ = g (u : W) := by rw [hb0u]
      _ = x := hgu

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
