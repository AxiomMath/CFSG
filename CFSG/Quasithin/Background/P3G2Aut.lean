module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5aAut
public import CFSG.Quasithin.Background.G2UCodes

public section

namespace CFSG.Quasithin.G11.P3G2

open Matrix CFSG.LinearGroups.UnitaryThreeOverNine CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X5 CFSG.Quasithin.G2U

theorem card_mulAut_psu : Nat.card (MulAut (PSUThree card_F9)) = 12096 := by
  have hK := card_F9
  have hfinS : Finite (StatedSU 3 3 F9) :=
    Nat.finite_of_card_ne_zero (by rw [card_statedSU hK]; norm_num)
  have hfinP : Finite (PSUThree hK) := Finite.of_surjective _ (toPSU_surjective hK)
  have hcardP : Nat.card (PSUThree hK) = 6048 :=
    (Nat.card_congr (Equiv.ofBijective _ ⟨toPSU_injective hK, toPSU_surjective hK⟩)).symm.trans
      (card_statedSU hK)
  have h := unitaryFieldData_of_card hK
  have hq : ¬(3 = 3 ∧ 3 ^ 1 = 2) := by norm_num
  have hreal := unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_one' : IsPrimeFormGram (1 : GL (Fin 3) F9)) (le_refl 3) hq
  obtain ⟨ψ⟩ := hreal.1
  have hsimple : IsSimpleGroup (PSUThree hK) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Finite F9 := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    have := (CFSG.ClassicalGroups.Unitary.fam_unitary_projective_simple F9 3 1
      (by rw [hK]; norm_num) 3 le_rfl (by norm_num)).2.2
    exact MulEquiv.isSimpleGroup (ψ.trans (unitaryPSUEquiv h (by norm_num)))
  have hnc : ∃ a b : PSUThree hK, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup (PSUThree hK) :=
      { (inferInstance : Group (PSUThree hK)) with mul_comm := hcon }
    have hp := IsSimpleGroup.prime_card (α := PSUThree hK)
    rw [hcardP] at hp
    exact absurd hp (by norm_num)
  have hZ : Subgroup.center (PSUThree hK) = ⊥ := center_eq_bot_of_simple_of_noncomm hsimple hnc
  have hconj : Function.Injective (MulAut.conj : PSUThree hK →* MulAut (PSUThree hK)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : g ∈ Subgroup.center (PSUThree hK) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun φ : MulAut (PSUThree hK) => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rwa [hZ, Subgroup.mem_bot] at hmem
  set N : Subgroup (MulAut (PSUThree hK)) :=
    (MulAut.conj : PSUThree hK →* MulAut (PSUThree hK)).range with hN
  have hψN : psiBar hK ∉ N := psiBar_not_mem_range hK
  have hindex : N.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨psiBar hK, fun b => ?_⟩
    by_cases hb : b ∈ N
    · have hn : b * psiBar hK ∉ N := fun hbn => hψN (by
        have := N.mul_mem (N.inv_mem hb) hbn
        rwa [inv_mul_cancel_left] at this)
      exact Or.inr ⟨hb, hn⟩
    · rcases psi_aut_cases hK b with hb' | ⟨i, hi, hbi⟩
      · exact absurd hb' hb
      · have hy : b * psiBar hK ∈ N := by
          rw [hbi, mul_assoc, psiBar_mul_self, mul_one]
          exact hi
        exact Or.inl ⟨hy, hb⟩
  have hcardN : Nat.card N = 6048 := by
    rw [← hcardP]
    exact (Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv).symm
  have hmul := Subgroup.card_mul_index N
  rw [hindex, hcardN] at hmul
  omega

theorem card_mulAut_of_equiv {Q : Type} [Group Q] (e : Q ≃* StatedSU 3 3 F9) :
    Nat.card (MulAut Q) = 12096 := by
  have e' : Q ≃* PSUThree card_F9 :=
    e.trans (MulEquiv.ofBijective (toPSU card_F9)
      ⟨toPSU_injective card_F9, toPSU_surjective card_F9⟩)
  rw [Nat.card_congr (MulAut.congr e').toEquiv]
  exact card_mulAut_psu

end CFSG.Quasithin.G11.P3G2
