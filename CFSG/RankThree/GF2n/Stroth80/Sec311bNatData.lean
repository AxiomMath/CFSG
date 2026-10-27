module

public import CFSG.RankThree.GF2n.Stroth80.Sec311bGenOrth
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalarsPlusTwo
public import CFSG.RankThree.GF2n.Stroth80.Sec310RootMain
public import CFSG.RankThree.GF2n.Stroth80.Sec5SpConsumers
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatReindex
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClOmegaPlusFour
public import CFSG.RankThree.GF2n.Stroth80.Sec310Assembly

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def NatDataSO (hc : Ctx M Q Z B) (t : G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = Nat.card Z ∧
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (_ : Nonempty ι)
      (X : Subgroup (GL ι K)) (φ : ↥(Rt M (LB M Q B) t) →* GL ι K),
      AddCommutantScalar X ∧ φ.range = X ∧
      φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
      ∃ (_ : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal)
        (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
          Multiplicative (ι → K)),
        (∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
          (w : G) = (s : G) * v * (s : G)⁻¹ →
          Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
            (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))) ∧
        ∃ r ∈ Rt M (LB M Q B) t,
          Rt M (LB M Q B) t ≤ hc.CN t ⊔ (LB M Q B ⊔ LB M Q (conjSubgroup r B))

theorem exists_ne_zero_ne_one_of_nat_card_ge_four {K : Type} [Field K] [Finite K]
    (h4 : 4 ≤ Nat.card K) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun c _ => by
    by_cases hc : c = 0
    · exact Or.inl hc
    · exact Or.inr (h c hc)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ, Set.ncard_pair zero_ne_one] at h1
  omega

theorem Ctx.natDataSO_of_orth (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [hn : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    NatDataSO hc t :=
  ⟨K, inferInstance, inferInstance, inferInstance, hK, ι, inferInstance, inferInstance,
    inferInstance, X, φ, hX, hφ, hker, hn, ψ, hψ,
    hc.exists_gen_orth h34 hs hnotQB hK E hQ h3 hX φ hφ hker ψ hψ⟩

theorem Ctx.exists_nat_data (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hR : Rt M (LB M Q B) t ≠ LB M Q B) (hnotSL : ¬ SLNat hc t) : NatDataSO hc t := by
  classical
  have hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B := fun hV =>
    hnotSL (stroth310SLBranch_of_34 h34 G M Q Z B hc n t hs hR hV)
  rcases h310 G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen t hs.mem hs.notQ with
    hRL | ⟨K, fK, finK, hK, hfam⟩
  · exact absurd hRL hR
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  rcases hfam with ⟨m, hm, hnat⟩ | ⟨m, hm, hnat⟩ | ⟨m, hm, hnat⟩ | ⟨m, b, c, hm, hirr, hnat⟩
  · exact absurd ⟨K, fK, finK, hK, m, hm, hnat⟩ hnotSL
  · by_cases hm1 : m = 1
    · subst hm1
      exact absurd ⟨K, fK, finK, hK, 2, le_refl 2, NaturalRep.sp_one_to_sl_two hnat⟩ hnotSL
    · have hm2 : 2 ≤ m := by omega
      have hspnat : SpNat hc t := ⟨K, fK, finK, hK, m, hm2, hnat⟩
      obtain ⟨φ, hφ, hker, hact⟩ := hnat
      obtain ⟨-, hn, ψ, hψ⟩ := hact
      haveI := hn
      refine ⟨K, fK, finK, inferInstance, hK, Fin m ⊕ Fin m, inferInstance, inferInstance,
        ⟨Sum.inl ⟨0, by omega⟩⟩, StatedSp m K, φ, addCommutantScalar_statedSp, hφ, hker, hn, ψ,
        hψ, ?_⟩
      obtain ⟨r, hr, -, hgen⟩ := hc.exists_hypPlane_sp h34 (stroth310Root_of_34 h34) hs hspnat
      exact ⟨r, hr, hgen⟩
  · haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    obtain ⟨φ, hφ, hker, hact⟩ := hnat
    obtain ⟨-, hn, ψ, hψ⟩ := hact
    haveI := hn
    have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
    by_cases hm2 : m = 2
    · subst hm2
      obtain ⟨c0, hc0, hc1⟩ := exists_ne_zero_ne_one_of_nat_card_ge_four hq4
      exact hc.natDataSO_of_orth h34 hs hnotQB hK
        (ElemMatrixIso.ofStated (coe_quadPlus 2 K)
          (Classify.commutator_orthogonalGroup_quadPlus_two K hc0 hc1))
        (nondegenerate_polarBilin_quadPlus 2 K) h3
        (addCommutantScalar_statedOmegaPlus_two ⟨c0, hc0, hc1⟩) φ hφ hker ψ hψ
    · exact hc.natDataSO_of_orth h34 hs hnotQB hK (ElemMatrixIso.plus (by omega))
        (nondegenerate_polarBilin_quadPlus m K) h3
        (addCommutantScalar_statedOmegaPlus (by omega)) φ hφ hker ψ hψ
  · haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    obtain ⟨φ, hφ, hker, hact⟩ := hnat
    obtain ⟨-, hn, ψ, hψ⟩ := hact
    haveI := hn
    have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]; omega
    exact hc.natDataSO_of_orth h34 hs hnotQB hK (ElemMatrixIso.minus hm hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
      (addCommutantScalar_statedOmegaMinus hm hirr) φ hφ hker ψ hψ

end CFSG.RankThree.GF2n.Stroth80
