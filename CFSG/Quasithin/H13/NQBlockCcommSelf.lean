module

public import CFSG.Quasithin.H13.NQBlockCcommWholeFrattini

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup

theorem odd_Fitting_cores_self {L : Type*} [Group L] [Finite L]
    (hSQT : CFSG.IsStronglyQuasithin L) (hO2 : CFSG.pCore 2 L = ⊥)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L)) (hq : ¬ CFSG.IsQuasisimple L) :
    CFSG.generalizedFitting L = CFSG.fittingSubgroup L ∧ CFSG.fittingSubgroup L ≠ ⊥ ∧
      Odd (Nat.card (CFSG.fittingSubgroup L)) ∧
      centralizer (CFSG.fittingSubgroup L : Set L) ≤ CFSG.fittingSubgroup L ∧
      ⁅(⊤ : Subgroup L), CFSG.fittingSubgroup L⁆ ≠ ⊥ ∧
      ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
        CFSG.pCore r L ≠ ⊥ ∧ CFSG.pRank r (CFSG.pCore r L) ≤ 2 := by
  classical
  have hLperf : Group.IsPerfect L := Group.isPerfect_def.mpr (by
    rw [commutator_def]
    exact hLC.2.1)
  have hLnt : Nontrivial L := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hLC.1
    ext x
    simp [Subsingleton.elim x 1]
  have hE : CFSG.layer L = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun K hK => ?_)
    exfalso
    obtain ⟨hKq, hKs⟩ := hK
    have hKne : K ≠ ⊥ :=
      (nontrivial_iff_ne_bot K).mp (CFSG.LocalCores.isQuasisimple_nontrivial hKq)
    have hKp : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKq.1
    have hKtop : K = ⊤ := by
      by_contra hne
      exact hLC.2.2.2 K (lt_top_iff_ne_top.mpr hne) hKne hKp hKs
    apply hq
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr hKtop).trans topEquiv) hKq
  have hFstar : CFSG.generalizedFitting L = CFSG.fittingSubgroup L := by
    rw [CFSG.generalizedFitting, hE, sup_bot_eq]
  have hCF : centralizer (CFSG.fittingSubgroup L : Set L) ≤ CFSG.fittingSubgroup L := by
    have h1 := CFSG.centralizer_generalizedFitting_le L
    rwa [hFstar] at h1
  have hcomm : ⁅(⊤ : Subgroup L), CFSG.fittingSubgroup L⁆ ≠ ⊥ := by
    intro h
    have hle : (⊤ : Subgroup L) ≤ CFSG.fittingSubgroup L :=
      (commutator_eq_bot_iff_le_centralizer.mp h).trans hCF
    have hnil : Group.IsNilpotent L := by
      have e : CFSG.fittingSubgroup L ≃* L :=
        (MulEquiv.subgroupCongr (top_le_iff.mp hle)).trans topEquiv
      exact Group.nilpotent_of_surjective e.toMonoidHom e.surjective
    exact Group.IsPerfect.not_isSolvable L inferInstance
  have hFne : CFSG.fittingSubgroup L ≠ ⊥ := by
    intro h
    apply hcomm
    rw [h, commutator_bot_right]
  have hodd : Odd (Nat.card (CFSG.fittingSubgroup L)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨S⟩ : Nonempty (Sylow 2 (CFSG.fittingSubgroup L)) := inferInstance
    have h1 := sylow_fitting_map_eq_pCore S
    rw [hO2, map_eq_bot_iff_of_injective _ (CFSG.fittingSubgroup L).subtype_injective] at h1
    have h2 := S.card_eq_multiplicity
    rw [h1, card_bot] at h2
    have h3 : (Nat.card (CFSG.fittingSubgroup L)).factorization 2 = 0 := by
      by_contra hk
      have := Nat.one_lt_two_pow hk
      omega
    rw [Nat.factorization_eq_zero_iff] at h3
    rcases h3 with h3 | h3 | h3
    · exact absurd Nat.prime_two h3
    · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h3)
    · exact absurd h3 Nat.card_pos.ne'
  refine ⟨hFstar, hFne, hodd, hCF, hcomm, fun r hr => ?_⟩
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have : Fact r.Prime := ⟨hrp⟩
  have hrF : r ∣ Nat.card (CFSG.fittingSubgroup L) := Nat.dvd_of_mem_primeFactors hr
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrF)
  have hne : CFSG.pCore r L ≠ ⊥ := by
    obtain ⟨S⟩ : Nonempty (Sylow r (CFSG.fittingSubgroup L)) := inferInstance
    rw [← sylow_fitting_map_eq_pCore S]
    intro h
    rw [map_eq_bot_iff_of_injective _ (CFSG.fittingSubgroup L).subtype_injective] at h
    have h2 := S.card_eq_multiplicity
    rw [h, card_bot] at h2
    have h3 := hrp.factorization_pos_of_dvd Nat.card_pos.ne' hrF
    have h4 : 1 < r ^ (Nat.card (CFSG.fittingSubgroup L)).factorization r :=
      Nat.one_lt_pow h3.ne' hrp.one_lt
    omega
  refine ⟨hne, ?_⟩
  have h1 : CFSG.pRank r (CFSG.pCore r L) ≤ CFSG.pRank r L := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_top_le_of_injective hrp.one_lt (CFSG.pCore r L).subtype
      (CFSG.pCore r L).subtype_injective
  exact h1.trans (hSQT r hrp hr2)

theorem all_prime_critical_actions_self
    {L : Type*} [Group L] [Finite L]
    (hSQT : CFSG.IsStronglyQuasithin L) (hO2 : CFSG.pCore 2 L = ⊥)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L)) (hq : ¬ CFSG.IsQuasisimple L) :
    ⁅CFSG.fittingSubgroup L, (⊤ : Subgroup L)⁆ = CFSG.fittingSubgroup L ∧
      ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
        ⁅CFSG.pCore r L, (⊤ : Subgroup L)⁆ = CFSG.pCore r L ∧
        ∃ (D : Subgroup (CFSG.pCore r L)) (_ : D.Characteristic),
          IsCriticalData r (CFSG.pCore r L) D ∧
          (criticalAction D).ker = CFSG.fittingSubgroup L := by
  obtain ⟨-, -, hodd, hCF, hcomm, hcores⟩ := odd_Fitting_cores_self hSQT hO2 hLC hq
  exact all_prime_critical_actions_core hLC hCF hodd hcomm hcores

theorem whole_Frattini_assembly_self {L : Type*} [Group L] [Finite L]
    (hSQT : CFSG.IsStronglyQuasithin L) (hO2 : CFSG.pCore 2 L = ⊥)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L)) (hq : ¬ CFSG.IsQuasisimple L) :
    ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
      (∀ S : Sylow r (CFSG.fittingSubgroup L),
        (S : Subgroup (CFSG.fittingSubgroup L)).map (CFSG.fittingSubgroup L).subtype =
          CFSG.pCore r L) ∧
      r ≠ 2 ∧ CFSG.pCore r L ≠ ⊥ ∧
      Nat.card (CFSG.pCore r L ⧸ frattini (CFSG.pCore r L)) = r ^ 2 ∧
      (wholeFrattiniAction (CFSG.pCore r L)).range ≠ ⊥ ∧
      CFSG.IsQuasisimple (wholeFrattiniAction (CFSG.pCore r L)).range ∧
      (∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧ (s = r ∨ s = 5) ∧
        Nonempty ((wholeFrattiniAction (CFSG.pCore r L)).range ⧸
            center (wholeFrattiniAction (CFSG.pCore r L)).range ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s))) ∧
      ((¬ IsMulCommutative (CFSG.pCore r L) ∧ Nat.card (CFSG.pCore r L) = r ^ 3 ∧
          ∀ x : CFSG.pCore r L, x ^ r = 1) ∨
        (IsMulCommutative (CFSG.pCore r L) ∧ ∃ a : ℕ, 1 ≤ a ∧
          Nonempty (CFSG.pCore r L ≃*
            Multiplicative (ZMod (r ^ a)) × Multiplicative (ZMod (r ^ a))))) := by
  obtain ⟨-, -, hodd, hCF, hcomm, hcores⟩ := odd_Fitting_cores_self hSQT hO2 hLC hq
  exact whole_Frattini_assembly_core hLC hCF hodd hcomm hcores

end CFSG.Quasithin.H13.NQBlock
