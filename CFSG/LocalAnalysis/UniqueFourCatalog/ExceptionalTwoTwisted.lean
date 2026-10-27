module

public import CFSG.LocalAnalysis.UniqueFourCatalog.Glue
public import CFSG.LieType.Chevalley.FixedRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open Subgroup CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.RankThreeUC (twoLocalClosure twoLocalClosure_eq_top_of_invariant_two_subgroups)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

theorem exc2t_closure_top_of_conj {G : Type} [Group G] (E : Subgroup G) (x : G)
    (h : twoLocalClosure (E.map (MulAut.conj x).toMonoidHom) = ⊤) :
    twoLocalClosure E = ⊤ := by
  have hle := CFSG.LocalAnalysis.RankThreeUC.map_twoLocalClosure_le (MulAut.conj x).symm
    (E.map (MulAut.conj x).toMonoidHom)
  have hE : (E.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).symm.toMonoidHom = E := by
    ext y
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      have e1 : x⁻¹ * (x * w * x⁻¹) * x = w := by group
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply, MulAut.conj_apply]
      rw [e1]
      exact hw
    · intro hy
      refine ⟨(MulAut.conj x) y, ⟨y, hy, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply, MulAut.conj_apply]
      group
  rw [hE, h, Subgroup.map_top, MonoidHom.range_eq_top.2 (MulAut.conj x).symm.surjective] at hle
  exact top_le_iff.mp hle

theorem exc2t_isElementaryAbelian {G : Type} [Group G] {p : ℕ} {E : Subgroup G}
    (h : IsElemAbelian p E) : CFSG.IsElementaryAbelian p E :=
  { toIsMulCommutative := h.1
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
      Subtype.ext (by simpa using h.2 (x : G) x.2) }

theorem exc2t_charP_two {K : Type} [Field K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    CharP K 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK

theorem exc2t_derived_equiv {G : Type} [Group G] (H C : Subgroup G)
    (h : ⁅H, H⁆ = C) (hZ : Subgroup.center C = ⊥) :
    Nonempty (DerivedCentralQuotient H ≃* C) := by
  subst h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩

theorem exc2t_closure_top_of_two_radicalsTwisted {M : Type*} [Group M] (C : Subgroup M)
    [Nontrivial C] (E : Subgroup C) (Q Q' : Subgroup M) (hQ : IsPGroup 2 Q) (hQ' : IsPGroup 2 Q')
    (hQC : Q ≤ C) (hQ'C : Q' ≤ C) (hEQ : ∀ e ∈ E, (e : M) ∈ Subgroup.normalizer (Q : Set M))
    (hEQ' : ∀ e ∈ E, (e : M) ∈ Subgroup.normalizer (Q' : Set M)) (hgen : C ≤ Q ⊔ Q') :
    twoLocalClosure E = ⊤ := by
  classical
  set Q₀ : Subgroup C := Q.subgroupOf C
  set Q₀' : Subgroup C := Q'.subgroupOf C
  have hsup : Q₀ ⊔ Q₀' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQC hQ'C]
    exact Subgroup.subgroupOf_eq_top.2 hgen
  have hp : ∀ {R : Subgroup M}, IsPGroup 2 R → IsPGroup 2 (R.subgroupOf C) := fun hR =>
    hR.comap_subtype
  have hnorm : ∀ {R : Subgroup M}, (∀ e ∈ E, (e : M) ∈ Subgroup.normalizer (R : Set M)) →
      E ≤ Subgroup.normalizer ((R.subgroupOf C : Subgroup C) : Set C) := by
    intro R hR e he
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have := Subgroup.mem_normalizer_iff.mp (hR e he) (z : M)
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  by_cases h1 : Q₀ = ⊥
  · have h2 : Q₀' = ⊤ := by
      rw [h1, bot_sup_eq] at hsup
      exact hsup
    refine twoLocalClosure_eq_top_of_invariant_two_subgroups E {Q₀'} ?_ ?_
    · intro S hS
      rw [Set.mem_singleton_iff] at hS
      subst hS
      exact ⟨by rw [h2]; exact top_ne_bot, hp hQ', hnorm hEQ'⟩
    · simp [h2]
  by_cases h2 : Q₀' = ⊥
  · have h1' : Q₀ = ⊤ := by
      rw [h2, sup_bot_eq] at hsup
      exact hsup
    refine twoLocalClosure_eq_top_of_invariant_two_subgroups E {Q₀} ?_ ?_
    · intro S hS
      rw [Set.mem_singleton_iff] at hS
      subst hS
      exact ⟨h1, hp hQ, hnorm hEQ⟩
    · simp [h1']
  refine twoLocalClosure_eq_top_of_invariant_two_subgroups E {Q₀, Q₀'} ?_ ?_
  · intro S hS
    rcases hS with rfl | hS
    · exact ⟨h1, hp hQ, hnorm hEQ⟩
    · rw [Set.mem_singleton_iff] at hS
      subst hS
      exact ⟨h2, hp hQ', hnorm hEQ'⟩
  · rw [iSup_insert, iSup_singleton]
    exact hsup

theorem exc2t_radicals_of_normalizes
    (t : TwistTag) (k : Type) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k 2]
    (hp2 : p ≠ 2) (σ : k ≃+* k) (hσ : σ ^ t.order = 1)
    [IsSimpleGroup (graphFixedRootGroup t k σ.toRingHom)]
    (A : Subgroup (ModGL t.tag k)) (hAC : A ≤ graphFixedRootGroup t k σ.toRingHom)
    (hA : IsPGroup p A) (R : Subgroup (ModGL t.tag k))
    (hRC : R ≤ graphFixedRootGroup t k σ.toRingHom) (hRr : IsPGroup 2 R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL t.tag k))) :
    ∃ x ∈ graphFixedRootGroup t k σ.toRingHom, ∃ Q Q' : Subgroup (ModGL t.tag k),
      IsPGroup 2 Q ∧ IsPGroup 2 Q' ∧ Q ≤ graphFixedRootGroup t k σ.toRingHom ∧
      Q' ≤ graphFixedRootGroup t k σ.toRingHom ∧
      graphFixedRootGroup t k σ.toRingHom ≤ Q ⊔ Q' ∧
      ∀ a ∈ A, x * a * x⁻¹ ∈ Subgroup.normalizer (Q : Set (ModGL t.tag k)) ∧
        x * a * x⁻¹ ∈ Subgroup.normalizer (Q' : Set (ModGL t.tag k)) := by
  have := finite_modGL (τ := t.tag) (K := k)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, -, -, -, F, -, -, ⟨g, hg, l, hl, hl1, hgl⟩, hdom, -⟩ :=
    (RootWeightDatum.fixed t σ hσ : RootWeightDatum k).root_p_subgroup_optimal_parabolic_containment
      2 R hRC hRr hR
  obtain ⟨hJ, -, hN, hset, -⟩ := hdom g hg l hl hl1 hgl
  obtain ⟨g', rfl⟩ : ∃ g' : ModGL t.tag k, g' = g := ⟨g, rfl⟩
  have hgC : g' ∈ graphFixedRootGroup t k σ.toRingHom := hg
  have hJ' : ((RootWeightDatum.fixed t σ hσ : RootWeightDatum k).face l :
      Set (Fin t.foldedTag.rank)) ≠ Set.univ := hJ
  set J : Set (Fin t.foldedTag.rank) := (RootWeightDatum.fixed t σ hσ : RootWeightDatum k).face l
  change {x : ModGL t.tag k | x ∈ graphFixedRootGroup t k σ.toRingHom ∧
      ∀ c : ℝ, (F c).map (x : Module.End k (RootModule t.tag k)) = F c} =
    ((graphFixedParabolic t k σ.toRingHom J).map (MulAut.conj g').toMonoidHom :
      Set (ModGL t.tag k)) at hset
  have hA1' : A.map (MulAut.conj g'⁻¹).toMonoidHom ≤ graphFixedParabolic t k σ.toRingHom J := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem := (Set.ext_iff.1 hset a).1
      (And.intro (hAC ha) (hN a (Subgroup.mem_inf.2 ⟨hAC ha, hAR ha⟩)))
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hmem
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hmem
  have hindex : ¬ p ∣ ((graphFixedParabolicLevi t k σ.toRingHom J).subgroupOf
      (graphFixedParabolic t k σ.toRingHom J)).index := by
    rw [graphFixedParabolicLevi_index_eq]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfin, -⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors t k σ J
    exact not_dvd_card_of_isPGroup (Ne.symm hp2) (hfin 2)
  have hA1p : IsPGroup p (A.map (MulAut.conj g'⁻¹).toMonoidHom) := hA.map _
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_not_dvd_index hA1' hA1p hindex
  have hyC : y ∈ graphFixedRootGroup t k σ.toRingHom := graphFixedParabolic_le t k σ.toRingHom J hy
  have hxC : y * g'⁻¹ ∈ graphFixedRootGroup t k σ.toRingHom := mul_mem hyC (inv_mem hgC)
  have hmap : A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom =
      (A.map (MulAut.conj g'⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map, map_mul]
    rfl
  have hAx : A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom ≤
      graphFixedParabolicLevi t k σ.toRingHom J := hmap ▸ hyA
  obtain ⟨Q, Q', hQp, hQ'p, hQC, hQ'C, hLQ, hLQ', hCX⟩ :=
    exists_radicals_of_graphFixedParabolicLevi (r := 2) σ hJ'
  refine ⟨y * g'⁻¹, hxC, Q, Q', hQp, hQ'p, hQC, hQ'C, hCX, fun a ha => ⟨?_, ?_⟩⟩
  · exact hLQ (hAx (Subgroup.mem_map_of_mem _ ha))
  · exact hLQ' (hAx (Subgroup.mem_map_of_mem _ ha))

theorem exc2t_closure_top_of_fixedRoot
    (t : TwistTag) (k : Type) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k 2]
    (hp2 : p ≠ 2) (σ : k ≃+* k) (hσ : σ ^ t.order = 1)
    [IsSimpleGroup (graphFixedRootGroup t k σ.toRingHom)]
    (E S₀ : Subgroup (graphFixedRootGroup t k σ.toRingHom)) (hE : IsElemAbelian p E)
    (hS₀ : S₀ ≠ ⊥) (hS₀2 : IsPGroup 2 S₀) (hEN : E ≤ normalizer (S₀ : Set _)) :
    twoLocalClosure E = ⊤ := by
  haveI : CFSG.IsElementaryAbelian p E := exc2t_isElementaryAbelian hE
  have hAC : E.map (graphFixedRootGroup t k σ.toRingHom).subtype ≤
      graphFixedRootGroup t k σ.toRingHom := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hAp : IsPGroup p (E.map (graphFixedRootGroup t k σ.toRingHom).subtype) :=
    (CFSG.IsElementaryAbelian.isPGroup p E).map _
  have hRC : S₀.map (graphFixedRootGroup t k σ.toRingHom).subtype ≤
      graphFixedRootGroup t k σ.toRingHom := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hR2 : IsPGroup 2 (S₀.map (graphFixedRootGroup t k σ.toRingHom).subtype) :=
    hS₀2.map _
  have hR1 : S₀.map (graphFixedRootGroup t k σ.toRingHom).subtype ≠ ⊥ := fun h => hS₀ (by
    apply Subgroup.map_injective (f := (graphFixedRootGroup t k σ.toRingHom).subtype)
      (fun x y hxy => Subtype.ext hxy)
    rw [h, Subgroup.map_bot])
  have hAR : E.map (graphFixedRootGroup t k σ.toRingHom).subtype ≤
      Subgroup.normalizer ((S₀.map (graphFixedRootGroup t k σ.toRingHom).subtype :
        Subgroup (ModGL t.tag k)) : Set (ModGL t.tag k)) :=
    (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map _)
  obtain ⟨x, hx, Q, Q', hQ, hQ', hQC, hQ'C, hCX, hnorm⟩ :=
    exc2t_radicals_of_normalizes t k p hp2 σ hσ _ hAC hAp _ hRC hR2 hR1 hAR
  refine exc2t_closure_top_of_conj E ⟨x, hx⟩
    (exc2t_closure_top_of_two_radicalsTwisted (graphFixedRootGroup t k σ.toRingHom)
      (E.map (MulAut.conj (⟨x, hx⟩ : graphFixedRootGroup t k σ.toRingHom)).toMonoidHom)
      Q Q' hQ hQ' hQC hQ'C ?_ ?_ hCX)
  · rintro e ⟨a, ha, rfl⟩
    exact (hnorm _ (Subgroup.mem_map_of_mem _ ha)).1
  · rintro e ⟨a, ha, rfl⟩
    exact (hnorm _ (Subgroup.mem_map_of_mem _ ha)).2

theorem not_uniqueFour_of_twistedChevalleyModel_two
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (t : TwistTag) {f : ℕ}
    (h : TwistedChevalleyModel G t (2 ^ f)) : ¬ uniqueFourUnique G := by
  obtain ⟨K, _, _, hK, σ₀, hσ₀, ⟨φ⟩⟩ := h
  haveI := hS.simple
  have := finite_modGL (τ := t.tag) (K := K)
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · subst h0
      have h1 : Nat.card K = 1 := by simpa using hK
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h0
  have hK2 : Nat.card K = 2 ^ (f * t.order) := by rw [hK, pow_mul]
  haveI : CharP K 2 := exc2t_charP_two (f := f * t.order)
    (by have := Nat.mul_pos hf t.order_pos; omega) hK2
  obtain ⟨σ, hσ, hord, -⟩ := finite_graph_field_parameter_fields t Nat.prime_two hf K hK
  have hσeq : σ₀ = σ.toRingHom := RingHom.ext fun c => (hσ₀ c).trans (hσ c).symm
  subst hσeq
  have hσo : σ ^ t.order = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one σ
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (2 ^ f) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hperf := finite_fixed_root_group_perfect t Nat.prime_two hf K hK σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup t K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := exc2t_derived_equiv _ _ hperf.2.2.1 hZ
  let e : G ≃* ↥(graphFixedRootGroup t K σ.toRingHom) := φ.trans ψ
  haveI : IsSimpleGroup ↥(graphFixedRootGroup t K σ.toRingHom) := MulEquiv.isSimpleGroup e.symm
  exact not_uniqueFour_of_closure hS (closure_hyp_of_mulEquiv e
    fun p hp hp2 E S₀ hE hS₀ hS₀2 hEN => by
      haveI : Fact p.Prime := ⟨hp⟩
      exact exc2t_closure_top_of_fixedRoot t K p hp2 σ hσo E S₀ hE hS₀ hS₀2 hEN)

end CFSG.LocalAnalysis.UniqueFourCatalog
