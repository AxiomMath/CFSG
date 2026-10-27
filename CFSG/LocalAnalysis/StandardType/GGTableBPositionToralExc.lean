module

public import CFSG.LocalAnalysis.StandardType.GGTableBPositionToral
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylGenAdjoint
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreExc
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestScalar
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEvenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestExc
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RecipeExcLang

private theorem five_le_of_prime_ne_two_ne_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : 5 ≤ p := by
  by_contra h
  have hlt : p < 5 := Nat.lt_of_not_le h
  have h2 : 2 ≤ p := hp.two_le
  interval_cases p
  · exact hp2 rfl
  · exact hp3 rfl
  · exact (by norm_num : ¬ Nat.Prime 4) hp

private theorem rootDiagUnit_mem_torusGroup_of_E7E8F4
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (a : Fin τ.rank → Kˣ) :
    rootDiagUnit τ a ∈ torusGroup τ K := by
  have h : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exact Or.inr (Or.inl rfl)
  exact (even_power_two_Cartan_root_diagonals_inner τ h K (ringChar.eq K 2)).1 a

private theorem range_inndiagConj_subset_conj_of_E7E8F4
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) :
    Set.range (inndiagConj τ K) ⊆
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  intro φ hφ
  obtain ⟨w, rfl⟩ := hφ
  have hfull : ∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ torusGroup τ K :=
    fun a => rootDiagUnit_mem_torusGroup_of_E7E8F4 hτ a
  have hwmem : (w : ModGL τ K) ∈ adjointGroup τ K := by
    obtain ⟨b, j, hj, hwj⟩ := w.2
    rw [hwj]
    exact mul_mem (CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup (hfull b)) hj
  have hconj : inndiagConj τ K w =
      MulAut.conj (⟨(w : ModGL τ K), hwmem⟩ : adjointGroup τ K) := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [coe_inndiagConj, MulAut.conj_apply]
    rfl
  exact ⟨_, hconj.symm⟩

private theorem inndiagConj_mem_range_conj_E6
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {φ : MulAut (adjointGroup .E6 K)}
    (hφ : φ ∈ Set.range (inndiagConj .E6 K)) (hφp : φ ^ p = 1) :
    φ ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  have hcube : ∀ w : inndiagGroup .E6 K,
      (inndiagConj .E6 K w) ^ 3 ∈
        (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
    intro w
    rw [← map_pow]
    have hw3 : ((w ^ 3 : inndiagGroup .E6 K) : ModGL .E6 K) ∈ adjointGroup .E6 K := by
      obtain ⟨b, j, hj, hbw⟩ := w.2
      have hident : (rootDiagUnit .E6 b * j) ^ 3 =
          rootDiagUnit .E6 (b ^ 3) *
            (rootDiagUnit .E6 (b⁻¹ ^ 2) * j * (rootDiagUnit .E6 (b⁻¹ ^ 2))⁻¹) *
            (rootDiagUnit .E6 b⁻¹ * j * (rootDiagUnit .E6 b⁻¹)⁻¹) * j := by
        rw [← rootDiagUnit_pow, ← rootDiagUnit_pow, ← rootDiagUnit_inv]
        simp only [pow_succ, pow_zero, one_mul, mul_assoc, inv_inv, mul_inv_rev,
          mul_inv_cancel_left]
      rw [Subgroup.coe_pow, hbw, hident]
      exact mul_mem
        (mul_mem
          (mul_mem
            (CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup
              (TableBExc.rootDiagUnit_cube_mem_torusGroup_E6 b))
            (conj_rootDiagUnit_mem_adjointGroup (b⁻¹ ^ 2) hj))
          (conj_rootDiagUnit_mem_adjointGroup b⁻¹ hj))
        hj
    have hconj : inndiagConj .E6 K (w ^ 3) =
        MulAut.conj (⟨((w ^ 3 : inndiagGroup .E6 K) : ModGL .E6 K), hw3⟩ :
          adjointGroup .E6 K) := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [coe_inndiagConj, MulAut.conj_apply]
      rfl
    exact ⟨_, hconj.symm⟩
  obtain ⟨w, rfl⟩ := hφ
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)) hp.one_lt
  rw [← TableBExc.pow_mul_eq_self_of_mod hk hφp, pow_mul]
  exact Subgroup.pow_mem _ (hcube w) k

theorem exists_position_conj_torusPow
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* adjointGroup τ K}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hP : GGTableBPosition p L' E (Set.range (inndiagConj τ K)) θ hE) :
    ∃ g : adjointGroup τ K, ∀ e : E, ∃ v ∈ TableBExc.torusPow τ K p,
      ggLAut L' θ ⟨e, hE e.2⟩ = MulAut.conj (g⁻¹ * v * g) := by
  rcases hτ with rfl | rfl | rfl
  · have : Finite (adjointGroup .E7 K) := CFSG.LieType.Chevalley.generated_group_finite .E7 K
    refine exists_conj_of_position_toral (R := adjointGroup .E7 K) (r := Tag.E7.rank)
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot hp
      (TableBExc.torusPow .E7 K p) ?_ ?_ hP ?_
    · exact TableBExc.ggTorusLift_adjoint (τ := .E7) (by decide) hp hp2 hpq
        (TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E7
          ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))
    · exact IOneRest.ggExcToralRankInput_E7E8 (Or.inl rfl) hp hp2 hpq
    · intro e
      exact range_inndiagConj_subset_conj_of_E7E8F4 (Or.inl rfl) (hP.2.2.2.1 e)
  · have : Finite (adjointGroup .E8 K) := CFSG.LieType.Chevalley.generated_group_finite .E8 K
    refine exists_conj_of_position_toral (R := adjointGroup .E8 K) (r := Tag.E8.rank)
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot hp
      (TableBExc.torusPow .E8 K p) ?_ ?_ hP ?_
    · exact TableBExc.ggTorusLift_adjoint (τ := .E8) (by decide) hp hp2 hpq
        (TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E8 (Nat.coprime_one_left p))
    · exact IOneRest.ggExcToralRankInput_E7E8 (Or.inr rfl) hp hp2 hpq
    · intro e
      exact range_inndiagConj_subset_conj_of_E7E8F4 (Or.inr (Or.inl rfl)) (hP.2.2.2.1 e)
  · have : Finite (adjointGroup .F4 K) := CFSG.LieType.Chevalley.generated_group_finite .F4 K
    refine exists_conj_of_position_toral (R := adjointGroup .F4 K) (r := 4)
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot hp
      (TableBExc.torusPow .F4 K p) ?_ ?_ hP ?_
    · exact TableBF4.ggTorusLift_adjointF4 hp hp2 hpq
    · by_cases hp3 : p = 3
      · subst hp3
        exact TableBF4.ggF4ToralRankInput_three hpq
      · exact TableBF4.ggF4ToralRankInput_of_five_le hp
          (five_le_of_prime_ne_two_ne_three hp hp2 hp3) hpq
    · intro e
      exact range_inndiagConj_subset_conj_of_E7E8F4 (Or.inr (Or.inr rfl)) (hP.2.2.2.1 e)

theorem exists_position_conj_torusPow_E6
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* adjointGroup .E6 K}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hP : GGTableBPosition p L' E (Set.range (inndiagConj .E6 K)) θ hE) :
    ∃ g : adjointGroup .E6 K, ∀ e : E, ∃ v ∈ TableBExc.torusPow .E6 K p,
      ggLAut L' θ ⟨e, hE e.2⟩ = MulAut.conj (g⁻¹ * v * g) := by
  have : Finite (adjointGroup .E6 K) := CFSG.LieType.Chevalley.generated_group_finite .E6 K
  refine exists_conj_of_position_toral (R := adjointGroup .E6 K) (r := Tag.E6.rank)
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot hp
    (TableBExc.torusPow .E6 K p) ?_ ?_ hP ?_
  · exact TableBExc.ggTorusLift_adjoint (τ := .E6) (by decide) hp hp2 hpq
      (TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E6
        ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)))
  · exact TableBExc.ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq
  · intro e
    have hep : (⟨e, hE e.2⟩ : Subgroup.normalizer (L' : Set M)) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hP.2.1.2 e e.2, OneMemClass.coe_one]
    have hφp : (ggLAut L' θ ⟨e, hE e.2⟩) ^ p = 1 := by
      rw [← map_pow, hep, map_one]
    exact inndiagConj_mem_range_conj_E6 hp hp3 (hP.2.2.2.1 e) hφp

end CFSG.StandardType
