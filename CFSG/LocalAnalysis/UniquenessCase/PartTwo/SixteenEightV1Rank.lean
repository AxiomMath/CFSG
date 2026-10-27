module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Star
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Image
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaStepOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private noncomputable def s16e_quadPlusTwoProjEquiv (K : Type) [Field K] [Finite K] [CharP K 2] :
    StatedProj (StatedOmega (StatedQuadPlus 2 K)) ≃* ↥(StatedOmega (StatedQuadPlus 2 K)) :=
  CFSG.SeitzReduction.SymplecticPilot.statedProjOmegaEquiv
    (Q := CFSG.LieType.Universal.Spin.quadPlus 2 K) (Q₀ := StatedQuadPlus 2 K)
    (CFSG.LieType.Universal.Spin.coe_quadPlus 2 K) (by
      refine ⟨Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1, ?_⟩
      rw [← CFSG.LieType.Universal.Spin.coe_quadPlus 2 K]
      rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
      simp [Pi.single_apply, Fin.sum_univ_two, add_comm])

private theorem s16e_sl2_orderOf_three (k : Type*) [Field k] [CharP k 2] :
    ∃ t : Matrix.SpecialLinearGroup (Fin 2) k, orderOf t = 3 := by
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  obtain ⟨t, ht⟩ : ∃ t : Matrix.SpecialLinearGroup (Fin 2) k,
      (t : Matrix (Fin 2) (Fin 2) k) = !![0, 1; 1, 1] :=
    ⟨⟨_, by simp [Matrix.det_fin_two]; linear_combination (-1 : k) * h2⟩, rfl⟩
  have ht1 : t ≠ 1 := by
    intro h
    have := congrArg
      (fun A : Matrix.SpecialLinearGroup (Fin 2) k => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
    simp [ht] at this
  have ht3 : t ^ 3 = 1 := by
    have e : t ^ 3 = t * t * t := by rw [pow_succ, pow_two]
    rw [e]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ht,
      Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | rfl | linear_combination h2
  exact ⟨t, orderOf_eq_prime (p := 3) (hp := ⟨Nat.prime_three⟩) ht3 ht1⟩

theorem s16e_exists_noncyclic_three_of_isOmegaPlus_four {X : Type} [Group X]
    (h : IsOmegaPlus X 4 2) : ∃ E : Subgroup X, IsPGroup 3 E ∧ ¬ IsCyclic E := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  have h4 : 4 ≤ Nat.card K := by rw [hKcard]; norm_num
  haveI : CharP K 2 := uc22p22d_charP_two (n := 2) (by norm_num) hKcard
  obtain ⟨eΩ⟩ := uc22p22d_omegaPlus4_equiv (F := K) h4
  let SL := Matrix.SpecialLinearGroup (Fin 2) K
  let ψ : X ≃* SL × SL := (e.trans (s16e_quadPlusTwoProjEquiv K)).trans eΩ.symm
  obtain ⟨t, ht⟩ := s16e_sl2_orderOf_three K
  let E' : Subgroup (SL × SL) := (Subgroup.zpowers t).prod (Subgroup.zpowers t)
  have hcard_t : Nat.card (Subgroup.zpowers t) = 3 := by
    rw [Nat.card_zpowers t, ht]
  have hcardE' : Nat.card E' = 9 := by
    have h1 : Nat.card E' = Nat.card (↥(Subgroup.zpowers t) × ↥(Subgroup.zpowers t)) :=
      Nat.card_congr (Subgroup.prodEquiv (Subgroup.zpowers t) (Subgroup.zpowers t)).toEquiv
    rw [h1, Nat.card_prod, hcard_t]
  have hE'p : IsPGroup 3 E' := IsPGroup.of_card (n := 2) (by rw [hcardE']; norm_num)
  have hcube : ∀ a : SL, a ∈ Subgroup.zpowers t → a ^ 3 = 1 := by
    intro a ha
    have hdvd : orderOf a ∣ orderOf t := orderOf_dvd_of_mem_zpowers ha
    rw [ht] at hdvd
    exact (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have hE'nc : ¬ IsCyclic E' := by
    intro hcyc
    haveI : IsCyclic E' := hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E')
    have hord : orderOf g = Nat.card E' := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg3 : g ^ 3 = 1 := by
      have h1 : (g : SL × SL).1 ∈ Subgroup.zpowers t := (Subgroup.mem_prod.mp g.2).1
      have h2 : (g : SL × SL).2 ∈ Subgroup.zpowers t := (Subgroup.mem_prod.mp g.2).2
      have hg3' : (g : SL × SL) ^ 3 = 1 := by
        refine Prod.ext ?_ ?_
        · exact (map_pow (MonoidHom.fst SL SL) (g : SL × SL) 3).trans (hcube _ h1)
        · exact (map_pow (MonoidHom.snd SL SL) (g : SL × SL) 3).trans (hcube _ h2)
      apply Subtype.ext
      simpa using hg3'
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    rw [hord, hcardE'] at hdvd
    exact absurd hdvd (by norm_num)
  refine ⟨E'.map ψ.symm.toMonoidHom, hE'p.map ψ.symm.toMonoidHom, ?_⟩
  intro hcyc
  exact hE'nc ((Subgroup.equivMapOfInjective E' ψ.symm.toMonoidHom
    ψ.symm.injective).isCyclic.mpr hcyc)

theorem s16e_exists_noncyclic_cent_of_case168_5Star (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Hyp151 D V₀ V L) (h0 : V₀ = ⊥)
    (hc : Case168_5Star D V₀ V hV L) :
    ∃ B : Subgroup G, B ≤ D.M ∧ IsPGroup 3 B ∧ ¬ IsCyclic B ∧
      ∀ b ∈ B, ∀ u ∈ v1Sub D.M V₀ V hV L, b * u = u * b := by
  obtain ⟨E, hEp, hEc⟩ := s16e_exists_noncyclic_three_of_isOmegaPlus_four hc.2.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj : Function.Injective (lBar V₀ V hV L).subtype := (lBar V₀ V hV L).subtype_injective
  have hEc' : ¬ IsCyclic (E.map (lBar V₀ V hV L).subtype) := fun hcyc =>
    hEc ((Subgroup.equivMapOfInjective E (lBar V₀ V hV L).subtype hinj).isCyclic.mpr hcyc)
  obtain ⟨Y, hYL, hYp, hYc⟩ := c8_exists_noncyclic_le_of_le_barSub (p := 3)
    (hE := Subgroup.map_subtype_le E) (hEp.map _) hEc'
  exact ⟨Y, hYL.trans hS.le, hYp, hYc, fun b hb u hu =>
    Sixteen21.commute_of_mem_v1Sub hV hS h0 (hYL hb) hu⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
