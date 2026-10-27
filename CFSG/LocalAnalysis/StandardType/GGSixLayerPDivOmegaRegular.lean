module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivBasic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.StandardType

namespace LayerPDiv

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  LayerCores LayerCores.OrthRegular

theorem card_determinantLeftFactor (K : Type*) [Field K] :
    Nat.card (determinantLeftFactor K) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hinj : Function.Injective ((specialRho (K := K)).comp (MonoidHom.inl _ _)) := by
    rw [injective_iff_map_eq_one]
    intro A hA
    have h := congrArg (fun g : DeterminantIsometries K => g.val (1 : Matrix (Fin 2) (Fin 2) K))
      hA
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply] at h
    rw [specialRho_apply] at h
    exact Subtype.ext (by simpa using h)
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem card_determinantRightFactor (K : Type*) [Field K] :
    Nat.card (determinantRightFactor K) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hinj : Function.Injective ((specialRho (K := K)).comp (MonoidHom.inr _ _)) := by
    rw [injective_iff_map_eq_one]
    intro B hB
    have h := congrArg (fun g : DeterminantIsometries K => g.val (1 : Matrix (Fin 2) (Fin 2) K))
      hB
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at h
    rw [specialRho_apply] at h
    have h1 : B⁻¹ = 1 := Subtype.ext (by simpa using h)
    rw [← inv_inv B, h1, inv_one]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem dvd_card_orthogonalGroup_of_regular {K : Type} [Field K] [Finite K] {W : Type}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q : QuadraticForm K W}
    (hQ : (polarBilin Q).Nondegenerate) {m : ℕ} (hdim : finrank K W = 2 * (m + 1)) (hm : 1 ≤ m)
    {p : ℕ} (hpK : p ∣ Nat.card K ^ 2 - 1) :
    p ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (ε = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q) ∨
      (ε = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) := by
    by_cases h : CFSG.GroupTheory.WeirSylow.IsPlusType Q
    · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨-1, Or.inr ⟨rfl, h⟩⟩
  have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hdim hε
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hq2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq
  have h1 : ((Nat.card K : ℤ) ^ 2) ^ 1 - 1 ∣
      ∏ i ∈ Finset.Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨le_rfl, hm⟩)
  have h2 : ((p : ℕ) : ℤ) ∣ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) := by
    rw [hcard]
    refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_ h1) _
    rw [pow_one]
    have h3 := Int.natCast_dvd_natCast.mpr hpK
    rwa [Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_one] at h3
  exact Int.natCast_dvd_natCast.mp h2

theorem conj_mem_commutator_self {G : Type*} [Group G] (H : Subgroup G) {u s : G}
    (hu : u ∈ H) (hs : s ∈ ⁅H, H⁆) : u * s * u⁻¹ ∈ ⁅H, H⁆ := by
  rw [← Subgroup.map_subtype_commutator] at hs ⊢
  obtain ⟨s', hs', rfl⟩ := hs
  exact ⟨⟨u, hu⟩ * s' * ⟨u, hu⟩⁻¹,
    (inferInstance : (_root_.commutator H).Normal).conj_mem s' hs' ⟨u, hu⟩, by simp⟩

theorem isQuasisimple_commutator_of_not_split {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q : QuadraticForm K W}
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K W)
    (hns : ¬ (finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)) :
    CFSG.IsQuasisimple ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, Odd (orderOf g) →
        g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  classical
  by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  · obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
    exact ⟨isQuasisimple_orthDerived hQ hT, hodd⟩
  · obtain ⟨⟨n, hn⟩, -, hnf, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
        Q hQ
    by_cases hS : ∃ U : Submodule K W, finrank K U = n ∧ ∀ u ∈ U, Q u = 0
    · obtain ⟨U, hUn, hUQ⟩ := hS
      have hn2 : n = 2 := by
        by_contra hne
        exact hT (exists_threeSingular_of_le Q hUQ (by omega))
      subst hn2
      exact absurd ⟨by omega, U, hUn, hUQ⟩ hns
    · have hts : ∀ U : Submodule K W, finrank K U = n → ∃ u ∈ U, Q u ≠ 0 := by
        intro U hU
        by_contra hcon
        push Not at hcon
        exact hS ⟨U, hU, hcon⟩
      rcases hnf n (by omega) hn with ⟨b, hb⟩ | ⟨β, γ, -, -, b, hb⟩
      · exfalso
        refine hS ⟨Submodule.span K (Set.range fun i : Fin n => b (Sum.inl i)), ?_, ?_⟩
        · exact (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans
            (by simp)
        · intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0
      · have hU : ∀ u ∈ Submodule.span K (Set.range fun i : Fin (n - 1) => b (Sum.inl i)),
            Q u = 0 := by
          intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0 0 0
        have hdU : finrank K (Submodule.span K (Set.range fun i : Fin (n - 1) =>
            b (Sum.inl i))) = n - 1 :=
          (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans (by simp)
        have hn23 : n = 2 ∨ n = 3 := by
          by_contra hne
          exact hT (exists_threeSingular_of_le Q hU (by omega))
        rcases hn23 with rfl | rfl
        · obtain ⟨E, _, _, D, ψ, ρ, hψ, hρψ, hinj, hmem, hcomm, hsimple, hperf, hnonab, hcard,
            hidx, hnorm, hodd⟩ :=
            CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction Q hQ (by omega) hts
          have := hsimple
          rw [hcomm]
          exact ⟨isQuasisimple_of_simple_nonabelian hnonab, hodd⟩
        · obtain ⟨E, _, _, D, ψ, ρ, hψ, hρψ, hinj, hmem, hcomm, hsimple, hperf, hnonab, hcard,
            hidx, hnorm, hodd⟩ :=
            CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction Q hQ (by omega) hts
          have := hsimple
          rw [hcomm]
          exact ⟨isQuasisimple_of_simple_nonabelian hnonab, hodd⟩

theorem exists_subCoreFamily_orthRegular_pDiv {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K ^ 2 - 1) :
    ∃ (β : Type) (S : β → Subgroup (W ≃ₗ[K] W)),
      IsSubCoreFamily (TauCeti.QuadraticMap.orthogonalGroup Q) S ∧ ∀ c, p ∣ Nat.card (S c) := by
  classical
  have := finite_linearEquiv (K := K) (V := W)
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  by_cases h3 : 3 ≤ finrank K W
  · obtain ⟨hexc, -⟩ := orthogonal_regular_space_coverage Q hQ h3
    by_cases hsmall : SmallFixedException Q
    · exact ⟨Empty, _, isSubCoreFamily_of_isSolvable
        (isSolvable_of_no_prime_gt_three' (hexc hsmall)), fun c => c.elim⟩
    have hZ : ∀ z ∈ ⁅O, O⁆, (∀ y ∈ ⁅O, O⁆, z * y = y * z) → z ^ 2 = 1 → z = 1 :=
      fun z hz hzc _ => eq_one_of_commute_orthDerived hQ h3 hsmall
        (LayerFacts.ggCommutator_self_le O hz) hzc
    have hder : LayerFacts.ggDer O 1 = ⁅O, O⁆ := by
      rw [LayerFacts.ggDer_succ, LayerFacts.ggDer_zero]
    by_cases hsplit : finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
    ·
      have hK2 : Nat.card K ≠ 2 := fun h => hsmall (Or.inr ⟨hsplit, Or.inl h⟩)
      have hK3 : Nat.card K ≠ 3 := fun h => hsmall (Or.inr ⟨hsplit, Or.inr h⟩)
      obtain ⟨-, e, -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, -, -⟩ :=
        orthogonal_split_four_derived hK2 hK3 Q hQ hsplit.1 hsplit.2
      set L₁ := (determinantLeftFactor K).map e.symm.toMonoidHom with hL₁
      set L₂ := (determinantRightFactor K).map e.symm.toMonoidHom with hL₂
      let L : Bool → Subgroup ↥O := fun b => cond b L₁ L₂
      have hLle : ∀ b, L b ≤ commutator ↥O := by
        rintro (_ | _)
        · show L₂ ≤ _
          rw [hsup]
          exact le_sup_right
        · show L₁ ≤ _
          rw [hsup]
          exact le_sup_left
      have hLn : ∀ b, ((L b).subgroupOf (commutator ↥O)).Normal := by
        rintro (_ | _)
        · exact hn₂
        · exact hn₁
      have hLq : ∀ b, CFSG.IsQuasisimple (L b) := by
        rintro (_ | _)
        · exact hq₂
        · exact hq₁
      have hLcard : ∀ b, Nat.card (L b) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
        rintro (_ | _)
        · show Nat.card L₂ = _
          rw [hL₂, Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective,
            card_determinantRightFactor]
        · show Nat.card L₁ = _
          rw [hL₁, Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective,
            card_determinantLeftFactor]
      have hsupL : (⨆ b, (L b).map O.subtype) = ⁅O, O⁆ := by
        rw [← Subgroup.map_iSup, iSup_bool_eq]
        show (L₁ ⊔ L₂).map O.subtype = ⁅O, O⁆
        rw [← hsup, Subgroup.map_subtype_commutator]
      refine ⟨Bool, fun b => (L b).map O.subtype, ⟨fun b => Subgroup.map_subtype_le _,
        fun b => ?_, fun b => ?_, ⟨1, ?_⟩, fun z hz hzc hz2 => ?_⟩, fun b => ?_⟩
      · have hnorm : ((commutator ↥O).subgroupOf (⊤ : Subgroup ↥O)).Normal :=
          (Subgroup.normal_subgroupOf_iff le_top).mpr fun x k hx _ =>
            (inferInstance : (commutator ↥O).Normal).conj_mem x hx k
        have h1 : CFSG.Assembly.IsSubnormal (L b) ⊤ :=
          CFSG.Assembly.IsSubnormal.step (hLle b) (hLn b)
            (CFSG.Assembly.IsSubnormal.step le_top hnorm (CFSG.Assembly.IsSubnormal.refl ⊤))
        have h2 := ggSubnormal_map O.subtype h1
        rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
      · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
          ((L b).equivMapOfInjective _ O.subtype_injective) (hLq b)
      · rw [hder, hsupL]
      · rw [hsupL] at hz hzc
        exact hZ z hz hzc hz2
      · rw [Subgroup.card_map_of_injective O.subtype_injective, hLcard]
        exact hpK.trans (sq_sub_one_dvd_card_SL (D := K) le_rfl)
    ·
      obtain ⟨hq, hodd⟩ := isQuasisimple_commutator_of_not_split hQ h3 hsplit
      refine ⟨Unit, fun _ => ⁅O, O⁆, ⟨fun _ => LayerFacts.ggCommutator_self_le O,
        fun _ => ggSubnormal_of_normal (LayerFacts.ggCommutator_self_le O)
          fun u hu s hs => conj_mem_commutator_self O hu hs, fun _ => hq, ⟨1, ?_⟩,
        fun z hz hzc hz2 => ?_⟩, fun _ => ?_⟩
      · rw [hder, iSup_const]
      · rw [iSup_const] at hz hzc
        exact hZ z hz hzc hz2
      ·
        obtain ⟨m, hm⟩ : ∃ m, finrank K W = 2 * (m + 1) := by
          obtain ⟨k, hk⟩ :=
            CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
          exact ⟨k - 1, by omega⟩
        have hpO := dvd_card_orthogonalGroup_of_regular hQ hm (by omega) hpK
        have : Fact p.Prime := ⟨hp⟩
        obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpO
        have hgodd : Odd (orderOf (g : W ≃ₗ[K] W)) := by
          rw [Subgroup.orderOf_coe, hg]
          exact hp.odd_of_ne_two hp2
        have hgmem := hodd g g.2 hgodd
        have h1 : orderOf (⟨g, hgmem⟩ : ↥⁅O, O⁆) = p := by
          rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hg]
        rw [← h1]
        exact orderOf_dvd_natCard _
  · exact ⟨Empty, _, isSubCoreFamily_of_isSolvable
      (isSolvable_orthogonalGroup_of_finrank_le_two hQ (by omega)), fun c => c.elim⟩

end LayerPDiv

end CFSG.StandardType
