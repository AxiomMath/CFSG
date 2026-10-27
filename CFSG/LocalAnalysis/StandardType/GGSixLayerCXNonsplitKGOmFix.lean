module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmFree
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmegaRegular
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaSplit

public section

namespace CFSG.StandardType

namespace OmNonsplit

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  LayerCores LayerCores.OrthRegular LayerFacts
open scoped MatrixGroups

theorem zpow_apply_eq_self {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {a : V ≃ₗ[K] V} {v : V} (h : a v = v) (k : ℤ) : (a ^ k) v = v := by
  have hs : a ∈ MulAction.stabilizer (V ≃ₗ[K] V) v := h
  exact Subgroup.zpow_mem _ hs k

theorem not_le_of_isSolvable {G : Type*} [Group G] {T H : Subgroup G} (hTq : CFSG.IsQuasisimple T)
    (hH : Group.IsSolvable H) : ¬ T ≤ H := by
  intro hTH
  obtain ⟨k, hk⟩ := exists_ggDer_eq_bot hH
  have h1 : T ≤ ⊥ := by
    calc T = ggDer T k := (ggDer_of_perfect (ggCommutator_eq_of_isQuasisimple hTq) k).symm
      _ ≤ ggDer H k := ggDer_mono hTH k
      _ = ⊥ := hk
  obtain ⟨u, u', huu⟩ := exists_mul_ne_of_isQuasisimple hTq
  have hu : u = 1 := Subtype.ext (Subgroup.mem_bot.mp (h1 u.2))
  have hu' : u' = 1 := Subtype.ext (Subgroup.mem_bot.mp (h1 u'.2))
  exact huu (by rw [hu, hu'])

theorem not_dvd_sq_sub_one {p f : ℕ} (hp : p.Prime) (hq1 : ¬ p ∣ 2 ^ f - 1)
    (hq2 : ¬ p ∣ 2 ^ f + 1) : ¬ p ∣ (2 ^ f) ^ 2 - 1 := by
  have e : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    simpa using Nat.sq_sub_sq (2 ^ f) 1
  rw [e]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact hq2 h
  · exact hq1 h

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W}

abbrev SplitFour (R : QuadraticForm K W) : Prop :=
  finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0

theorem structure_of_isSubnormal (hR : (polarBilin R).Nondegenerate)
    {T : Subgroup (W ≃ₗ[K] W)} (hTq : CFSG.IsQuasisimple T)
    (hTs : CFSG.Assembly.IsSubnormal T (TauCeti.QuadraticMap.orthogonalGroup R)) :
    4 ≤ finrank K W ∧
      ((¬ SplitFour R ∧ T = ⁅TauCeti.QuadraticMap.orthogonalGroup R,
          TauCeti.QuadraticMap.orthogonalGroup R⁆) ∨
        (SplitFour R ∧ 4 ≤ Nat.card K ∧ ∃ ψ : SL(2, K) →* (W ≃ₗ[K] W),
          Function.Injective ψ ∧ ψ.range = T)) := by
  classical
  have := finite_linearEquiv (K := K) (V := W)
  set O := TauCeti.QuadraticMap.orthogonalGroup R with hO
  have hTO : T ≤ O := ggSubnormal_le hTs
  have h3 : 3 ≤ finrank K W := by
    by_contra h
    exact not_le_of_isSolvable hTq (isSolvable_orthogonalGroup_of_finrank_le_two hR (by omega))
      hTO
  have h4 : 4 ≤ finrank K W := by
    obtain ⟨k, hk⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo R hR
    omega
  have hTA : CFSG.Assembly.IsComponentOf T O :=
    ⟨hTO, hTs, (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      hTq⟩
  have hTc : T ≤ ⁅O, O⁆ := by
    rw [← ggCommutator_eq_of_isQuasisimple hTq]
    exact Subgroup.commutator_mono hTO hTO
  refine ⟨h4, ?_⟩
  by_cases hsp : SplitFour R
  · right
    have hns : ¬ SmallFixedException R := by
      intro hsmall
      obtain ⟨hexc, -⟩ := orthogonal_regular_space_coverage R hR h3
      exact not_le_of_isSolvable hTq (isSolvable_of_no_prime_gt_three' (hexc hsmall)) hTO
    have hK2 : Nat.card K ≠ 2 := fun h => hns (Or.inr ⟨hsp, Or.inl h⟩)
    have hK3 : Nat.card K ≠ 3 := fun h => hns (Or.inr ⟨hsp, Or.inr h⟩)
    refine ⟨hsp, by have := Finite.one_lt_card (α := K); omega, ?_⟩
    obtain ⟨-, e, -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, -, -⟩ :=
      orthogonal_split_four_derived hK2 hK3 R hR hsp.1 hsp.2
    have hinl : Function.Injective ((specialRho (K := K)).comp (MonoidHom.inl _ _)) := by
      rw [injective_iff_map_eq_one]
      intro A hA
      have h := congrArg (fun g : DeterminantIsometries K =>
        g.val (1 : Matrix (Fin 2) (Fin 2) K)) hA
      simp only [MonoidHom.comp_apply, MonoidHom.inl_apply] at h
      rw [specialRho_apply] at h
      exact Subtype.ext (by simpa using h)
    have hinr : Function.Injective ((specialRho (K := K)).comp (MonoidHom.inr _ _)) := by
      rw [injective_iff_map_eq_one]
      intro B hB
      have h := congrArg (fun g : DeterminantIsometries K =>
        g.val (1 : Matrix (Fin 2) (Fin 2) K)) hB
      simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at h
      rw [specialRho_apply] at h
      have h1 : B⁻¹ = 1 := Subtype.ext (by simpa using h)
      rw [← inv_inv B, h1, inv_one]
    have hcn : ((commutator ↥O).subgroupOf (⊤ : Subgroup ↥O)).Normal :=
      (Subgroup.normal_subgroupOf_iff le_top).mpr fun x k hx _ =>
        (inferInstance : (commutator ↥O).Normal).conj_mem x hx k
    have hcomp : ∀ L : Subgroup ↥O, L ≤ commutator ↥O → (L.subgroupOf (commutator ↥O)).Normal →
        CFSG.IsQuasisimple L → CFSG.Assembly.IsComponentOf (L.map O.subtype) O := by
      intro L hLle hLn hLq
      refine ⟨Subgroup.map_subtype_le L, ?_, ?_⟩
      · have h1 : CFSG.Assembly.IsSubnormal L ⊤ := CFSG.Assembly.IsSubnormal.step hLle hLn
          (CFSG.Assembly.IsSubnormal.step le_top hcn (CFSG.Assembly.IsSubnormal.refl ⊤))
        have h2 := ggSubnormal_map O.subtype h1
        rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
      · exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
          (CFSG.LocalCores.isQuasisimple_of_mulEquiv
            (L.equivMapOfInjective _ O.subtype_injective) hLq)
    have hL₁ := hcomp _ (by rw [hsup]; exact le_sup_left) hn₁ hq₁
    have hL₂ := hcomp _ (by rw [hsup]; exact le_sup_right) hn₂ hq₂
    set ψ₁ : SL(2, K) →* (W ≃ₗ[K] W) := O.subtype.comp
      (e.symm.toMonoidHom.comp ((specialRho (K := K)).comp (MonoidHom.inl _ _))) with hψ₁
    set ψ₂ : SL(2, K) →* (W ≃ₗ[K] W) := O.subtype.comp
      (e.symm.toMonoidHom.comp ((specialRho (K := K)).comp (MonoidHom.inr _ _))) with hψ₂
    have hr₁ : ψ₁.range = ((determinantLeftFactor K).map e.symm.toMonoidHom).map O.subtype := by
      rw [hψ₁, MonoidHom.range_comp, MonoidHom.range_comp, determinantLeftFactor]
    have hr₂ : ψ₂.range = ((determinantRightFactor K).map e.symm.toMonoidHom).map O.subtype := by
      rw [hψ₂, MonoidHom.range_comp, MonoidHom.range_comp, determinantRightFactor]
    rcases isComponentOf_eq_or_commute hTA hL₁ with h1 | h1
    · exact ⟨ψ₁, O.subtype_injective.comp (e.symm.injective.comp hinl), by rw [hr₁, h1]⟩
    rcases isComponentOf_eq_or_commute hTA hL₂ with h2 | h2
    · exact ⟨ψ₂, O.subtype_injective.comp (e.symm.injective.comp hinr), by rw [hr₂, h2]⟩
    exfalso
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1 h2
    have h5 : ⁅O, O⁆ ≤ Subgroup.centralizer (T : Set (W ≃ₗ[K] W)) := by
      rw [← Subgroup.map_subtype_commutator, hsup, Subgroup.map_sup]
      exact sup_le h1 h2
    exact not_le_centralizer_self_of_isQuasisimple hTA.2.2 (hTc.trans h5)
  · left
    obtain ⟨hq, -⟩ := LayerPDiv.isQuasisimple_commutator_of_not_split hR h3 hsp
    refine ⟨hsp, ?_⟩
    have hOA : CFSG.Assembly.IsComponentOf ⁅O, O⁆ O :=
      ⟨ggCommutator_self_le O, ggSubnormal_of_normal (ggCommutator_self_le O)
        fun u hu s hs => LayerPDiv.conj_mem_commutator_self O hu hs,
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq⟩
    rcases isComponentOf_eq_or_commute hTA hOA with h | h
    · exact h
    · exfalso
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact not_le_centralizer_self_of_isQuasisimple hTA.2.2 (h.trans (Subgroup.centralizer_le hTc))

theorem eq_one_of_pow_eq_one_orth (hR : (polarBilin R).Nondegenerate) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ f) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    {T : Subgroup (W ≃ₗ[K] W)} (hTq : CFSG.IsQuasisimple T)
    (hTs : CFSG.Assembly.IsSubnormal T (TauCeti.QuadraticMap.orthogonalGroup R))
    (hpT : ¬ p ∣ Nat.card T)
    {g : W ≃ₗ[K] W} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup R) (hgp : g ^ p = 1) :
    g = 1 := by
  classical
  have := finite_linearEquiv (K := K) (V := W)
  have hgo : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  obtain ⟨h4, ⟨hsp, hT⟩ | ⟨hsp, -, -⟩⟩ := structure_of_isSubnormal hR hTq hTs
  · obtain ⟨-, hodd⟩ := LayerPDiv.isQuasisimple_commutator_of_not_split hR (by omega) hsp
    have hgT : g ∈ T := hT ▸ hodd g hg (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) hgo)
    have h1 : orderOf g ∣ Nat.card T := by
      rw [← Subgroup.orderOf_mk g hgT]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hp).mp hgo with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ h1) hpT
  · obtain ⟨S, hS2, hSQ⟩ := hsp.2
    have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hR (m := 1)
      (by rw [hsp.1]) (ε := 1) (Or.inl ⟨rfl, S, by rw [hS2, hsp.1], hSQ⟩)
    have hq1' : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Finite.card_pos
    have hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) =
        2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - 1) := by
      apply Nat.cast_injective (R := ℤ)
      rw [hcard, Finset.Icc_self, Finset.prod_singleton]
      push_cast [Nat.cast_sub hq1']
      ring
    have hpO : ¬ p ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) := by
      have hpq := not_dvd_sq_sub_one hp hq1 hq2
      have hp0 : ¬ p ∣ Nat.card K := by
        rw [hK]
        intro h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
      rw [hO, ← hK] at *
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
          · exact hp0 (hp.dvd_of_dvd_pow h)
        · exact hpq h
      · exact hpq h
    have h1 : orderOf g ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) := by
      rw [← Subgroup.orderOf_mk g hg]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hp).mp hgo with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ h1) hpO

end OmNonsplit

end CFSG.StandardType
