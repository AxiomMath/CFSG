module

public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagConcl
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpRes
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp StatedLieTag StatedClassicalModel)
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
  (isQuasisimple_statedSp_of_not_small)

variable {K : Type} [Field K] [Finite K]

theorem exists_statedClassicalModel_statedSp [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (h : ¬ (n ≤ 2 ∧ Nat.card K = 2)) :
    ∃ (t : StatedLieTag) (n' f : ℕ),
      StatedClassicalModel (↥(StatedSp n K) ⧸ Subgroup.center ↥(StatedSp n K)) t n' 2 f := by
  obtain ⟨f, -, hK⟩ :=
    @FiniteField.card K _ (Fintype.ofFinite K) 2 (by infer_instance)
  have hK' : Nat.card K = 2 ^ (f : ℕ) := by
    rw [@Nat.card_eq_fintype_card K (Fintype.ofFinite K), hK]
  by_cases hn2 : 2 ≤ n
  · exact ⟨.PSp, n, (f : ℕ),
      CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient n K
        ⟨Nat.prime_two, f.pos, hn2, by
          intro hc
          have h1 : n = 2 := by simpa using congrArg Prod.fst hc
          have h2 : 2 ^ (f : ℕ) = 2 := by simpa using congrArg Prod.snd hc
          exact h ⟨by rw [h1], by rw [hK', h2]⟩⟩ hK'⟩
  · have hn1 : n = 1 := by omega
    subst hn1
    refine ⟨.PSL, 2, (f : ℕ), ⟨⟨Nat.prime_two, f.pos, le_rfl, ?_, ?_⟩,
      K, inferInstance, inferInstance, hK', ?_⟩⟩
    · intro hc
      have h2 : 2 ^ (f : ℕ) = 2 := by simpa using congrArg Prod.snd hc
      exact h ⟨by norm_num, by rw [hK', h2]⟩
    · intro hc
      have h2eq : 2 ^ (f : ℕ) = 3 := by simpa using congrArg Prod.snd hc
      have h2 : 2 ∣ 2 ^ (f : ℕ) := dvd_pow_self 2 f.pos.ne'
      rw [h2eq] at h2
      norm_num at h2
    · let eSL : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥(StatedSp 1 K) :=
        CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K
      exact ⟨(QuotientGroup.congr _ _ eSL.symm (Subgroup.map_center_eq eSL.symm)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩

theorem not_isComponentOf_statedSp_of_small {n : ℕ} (h : n = 0 ∨ (n = 1 ∧ Nat.card K = 2))
    (C : Subgroup (GL (Fin n ⊕ Fin n) K)) : ¬ IsComponentOf C (StatedSp n K) := by
  rcases h with rfl | ⟨rfl, hK⟩
  · exact CFSG.StandardType.ResU3Three.not_isComponentOf_of_isSolvable inferInstance
  · have hcard : Nat.card (StatedSp 1 K) = 6 := by
      have e : ↥(StatedSp 1 K) ≃* ↥(CFSG.Open.StatedSL 2 K) :=
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm.trans
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
      rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hK]
      norm_num
    have hsol : Group.IsSolvable ↥(StatedSp 1 K) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hcard]; norm_num)
    exact CFSG.StandardType.ResU3Three.not_isComponentOf_of_isSolvable hsol

theorem ggE0Concl_statedSp_of_ne [CharP K 2] {n : ℕ} (h : ¬ (n = 2 ∧ Nat.card K = 2))
    (C : Subgroup (GL (Fin n ⊕ Fin n) K)) (hC : IsComponentOf C (StatedSp n K)) :
    GGE0Concl (StatedSp n K) C := by
  by_cases hsmall : n = 0 ∨ (n = 1 ∧ Nat.card K = 2)
  · exact absurd hC (not_isComponentOf_statedSp_of_small hsmall C)
  · have hn : 1 ≤ n := by omega
    have h' : ¬ (n ≤ 2 ∧ Nat.card K = 2) := by omega
    obtain ⟨t, n', f, hmodel⟩ := exists_statedClassicalModel_statedSp hn h'
    have hq : CFSG.Assembly.IsQuasisimple ↥(StatedSp n K) :=
      isQuasisimple_statedSp_of_not_small hn (by omega) (by omega)
    exact ggE0Concl_of_isQuasisimple hq hmodel C hC

private theorem eq_commutator_of_isComponentOf_statedSp_two_two (hK : Nat.card K = 2)
    {C : Subgroup (GL (Fin 2 ⊕ Fin 2) K)} (hC : IsComponentOf C (StatedSp 2 K)) :
    C = ⁅StatedSp 2 K, StatedSp 2 K⁆ := by
  let T : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := StatedSp 2 K
  let J : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := ⁅T, T⁆
  have hJle : J ≤ T := Subgroup.commutator_le_self T
  have hmark := CFSG.StandardType.isQuasisimple_largeEvenMarking_commutator_of_equiv_statedSp_two
    (G := GL (Fin 2 ⊕ Fin 2) K) hK (T := T) (MulEquiv.refl ↥(StatedSp 2 K))
  have hCJ : C ≤ J := by
    have hperf : ⁅C, C⁆ = C := by
      have h := Subgroup.map_subtype_commutator C
      rw [hC.2.2.1, Subgroup.map_top, Subgroup.range_subtype] at h
      exact h.symm
    calc C = ⁅C, C⁆ := hperf.symm
      _ ≤ ⁅T, T⁆ := Subgroup.commutator_mono hC.1 hC.1
  have hCcompJ : IsComponentOf C J :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hC hCJ hJle
  exact GGHalf.eq_of_isComponentOf_isQuasisimple hmark.1 hCcompJ

theorem ggE0Concl_statedSp_two_two (hK : Nat.card K = 2) (C : Subgroup (GL (Fin 2 ⊕ Fin 2) K))
    (hC : IsComponentOf C (StatedSp 2 K)) : GGE0Concl (StatedSp 2 K) C := by
  let T : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := StatedSp 2 K
  let J : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := ⁅T, T⁆
  have hJle : J ≤ T := Subgroup.commutator_le_self T
  have hJnorm : (J.subgroupOf T).Normal := by
    have h := Subgroup.normal_subgroupOf_commutator_sup (H₁ := T) (H₂ := T)
    rwa [sup_idem] at h
  have hmark := CFSG.StandardType.isQuasisimple_largeEvenMarking_commutator_of_equiv_statedSp_two
    (G := GL (Fin 2 ⊕ Fin 2) K) hK (T := T) (MulEquiv.refl ↥(StatedSp 2 K))
  obtain rfl := eq_commutator_of_isComponentOf_statedSp_two_two hK hC
  refine ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hJle).mp hJnorm, ?_⟩
  intro _
  refine largeEvenMarking_mono ?_ hmark.2
  intro lab R _ I F θ hP
  refine ⟨hP.1, ?_⟩
  intro ε hε
  let g : Subgroup.normalizer (J : Set (GL (Fin 2 ⊕ Fin 2) K)) :=
    ⟨ε, (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).mp hJnorm hε⟩
  let α : MulAut ↥J := J.normalizerMonoidHom g⁻¹
  have hα_coe : ∀ y : ↥J,
      ((α y : ↥J) : GL (Fin 2 ⊕ Fin 2) K) = ε⁻¹ * (y : GL (Fin 2 ⊕ Fin 2) K) * ε := by
    intro y
    rfl
  have hα_mem : α ∈ {α : MulAut ↥J | ∃ t ∈ T, ∀ y : ↥J,
      ((α y : ↥J) : GL (Fin 2 ⊕ Fin 2) K) = t⁻¹ * (y : GL (Fin 2 ⊕ Fin 2) K) * t} :=
    ⟨ε, hε, hα_coe⟩
  obtain ⟨φ, hφI, hφ⟩ := hP.2 α hα_mem
  refine ⟨φ, hφI, ?_⟩
  intro l l' hrel
  have hαl : α l = l' := Subtype.ext (by rw [hα_coe l]; exact hrel.symm)
  simpa [hαl] using hφ l

theorem ggE0Concl_statedSp [CharP K 2] {n : ℕ} (C : Subgroup (GL (Fin n ⊕ Fin n) K))
    (hC : IsComponentOf C (StatedSp n K)) : GGE0Concl (StatedSp n K) C := by
  by_cases h : n = 2 ∧ Nat.card K = 2
  · obtain ⟨rfl, hK⟩ := h
    exact ggE0Concl_statedSp_two_two hK C hC
  · exact ggE0Concl_statedSp_of_ne h C hC

theorem largeEvenMarking_of_isComponentOf_statedSp [CharP K 2] {n : ℕ}
    (C : Subgroup (GL (Fin n ⊕ Fin n) K)) (hC : IsComponentOf C (StatedSp n K)) :
    LargeEvenMarking ↥C fun _ _ _ _ _ _ => True := by
  by_cases h : n = 2 ∧ Nat.card K = 2
  · obtain ⟨rfl, hK⟩ := h
    obtain rfl := eq_commutator_of_isComponentOf_statedSp_two_two hK hC
    exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (isQuasisimple_largeEvenMarking_commutator_of_equiv_statedSp_two
        (G := GL (Fin 2 ⊕ Fin 2) K) hK (T := StatedSp 2 K) (MulEquiv.refl _)).2
  · by_cases hsmall : n = 0 ∨ (n = 1 ∧ Nat.card K = 2)
    · exact absurd hC (not_isComponentOf_statedSp_of_small hsmall C)
    · have hn : 1 ≤ n := by omega
      have h' : ¬ (n ≤ 2 ∧ Nat.card K = 2) := by omega
      obtain ⟨t, n', f, hmodel⟩ := exists_statedClassicalModel_statedSp hn h'
      have hq : CFSG.Assembly.IsQuasisimple ↥(StatedSp n K) :=
        isQuasisimple_statedSp_of_not_small hn (by omega) (by omega)
      have hCeq : C = StatedSp n K := GGHalf.eq_of_isComponentOf_isQuasisimple hq hC
      subst C
      exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
        (largeEvenMarking_inn_of_statedClassicalModel hq hmodel)

end CFSG.StandardType
