module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcOpp
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalTwisted
public import CFSG.LieType.Chevalley.FixedRootCentralizerGeneration
public import CFSG.LieType.Chevalley.GraphFixedParabolicNormalizer
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.LieType.Chevalley.GraphFixedRootBruhat
public import CFSG.LieType.Chevalley.GraphFixedParabolicIntersection

public section

namespace CFSG.StandardType

namespace GGOppRadExc

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical

section General

variable {G : Type*} [Group G]

theorem eq_map_conj_of_optimal_prime [Finite G] {p : ℕ} [Fact p.Prime] {C P Q R : Subgroup G}
    (hQp : IsPGroup p Q) (hQC : Q ≤ C) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hRad : CFSG.GroupTheory.IsRadicalPGroup p C R) {g : G} (hg : g ∈ C)
    (hN : ∀ x ∈ C, x ∈ Subgroup.normalizer (R : Set G) → g⁻¹ * x * g ∈ P)
    (hRQ : ∀ q ∈ R, g⁻¹ * q * g ∈ Q) : R = Q.map (MulAut.conj g).toMonoidHom := by
  set R' := R.map (MulAut.conj g⁻¹).toMonoidHom with hR'def
  have hgN : g⁻¹ ∈ Subgroup.normalizer (C : Set G) := Subgroup.le_normalizer (inv_mem hg)
  have hR'rad : CFSG.GroupTheory.IsRadicalPGroup p C R' :=
    hRad.map_mulAut (MulAut.conj g⁻¹) (Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN)
  have hR'Q : R' ≤ Q := by
    rintro _ ⟨q, hq, rfl⟩
    have := hRQ q hq
    simpa [MulAut.conj_apply] using this
  have hN' : C ⊓ Subgroup.normalizer (R' : Set G) ≤ P := by
    intro x hx
    obtain ⟨hxC, hxN⟩ := Subgroup.mem_inf.mp hx
    have hgx : g * x * g⁻¹ ∈ Subgroup.normalizer (R : Set G) := by
      have h1 : R = R'.map (MulAut.conj g).toMonoidHom := by
        rw [hR'def, ← GGTwoSig.map_conj_mul, mul_inv_cancel, GGTwoSig.map_conj_one]
      rw [h1, ← GGTwoSig.map_conj_normalizer]
      exact ⟨x, hxN, rfl⟩
    have := hN _ (mul_mem (mul_mem hg hxC) (inv_mem hg)) hgx
    simpa [mul_assoc] using this
  have hRQ' : R' = Q := by
    refine eq_of_inf_normalizer_le hQp hR'Q ?_
    have hle : Q ⊓ (C ⊓ Subgroup.normalizer (R' : Set G)) ≤
        pCoreOf p (C ⊓ Subgroup.normalizer (R' : Set G)) :=
      le_pCoreOf_of_le_normalizer p inf_le_right (fun x hx => mem_normalizer_inf
        (hPQ (hN' hx)) (Subgroup.le_normalizer hx)) (hQp.to_le inf_le_left)
    have hR'eq : pCoreOf p (C ⊓ Subgroup.normalizer (R' : Set G)) = R' := hR'rad
    rw [hR'eq] at hle
    intro x hx
    obtain ⟨hxQ, hxN⟩ := Subgroup.mem_inf.mp hx
    exact hle (Subgroup.mem_inf.mpr ⟨hxQ, Subgroup.mem_inf.mpr ⟨hQC hxQ, hxN⟩⟩)
  rw [← hRQ', hR'def, ← GGTwoSig.map_conj_mul, mul_inv_cancel, GGTwoSig.map_conj_one]

end General

variable {t : TwistTag} {K : Type} [Field K]

open CFSG.Blueprint CFSG.Blueprint.Chevalley RootWeightSpace RootWeight in
open scoped RealInnerProductSpace in
theorem exists_optimal_radical_fixed_prime [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (σ : K ≃+* K) (hσ : σ ^ t.order = 1) {R : Subgroup (ModGL t.tag K)}
    (hRG : R ≤ graphFixedRootGroup t K σ.toRingHom) (hRp : IsPGroup p R) (hR : R ≠ ⊥) :
    ∃ g ∈ graphFixedRootGroup t K σ.toRingHom, ∃ J : Set (Fin t.foldedTag.rank),
      (∀ x ∈ graphFixedRootGroup t K σ.toRingHom,
        x ∈ Subgroup.normalizer (R : Set (ModGL t.tag K)) →
          g⁻¹ * x * g ∈ graphFixedParabolic t K σ.toRingHom J) ∧
      ∀ q ∈ R, g⁻¹ * q * g ∈ graphFixedParabolicRadical t K σ.toRingHom J := by
  obtain ⟨g, hg, l, hl, M, hM0, hP, hraise⟩ : ∃ g ∈ graphFixedRootGroup t K σ.toRingHom,
      ∃ l ∈ (RootWeightDatum.fixed t σ hσ).dominant, ∃ M : ℝ, 0 < M ∧
        (∀ x ∈ graphFixedRootGroup t K σ.toRingHom,
          x ∈ Subgroup.normalizer (R : Set (ModGL t.tag K)) →
          g⁻¹ * x * g ∈
            graphFixedParabolic t K σ.toRingHom ((RootWeightDatum.fixed t σ hσ).face l)) ∧
        ∀ q ∈ R, LabelRaises (latticeGrade (τ := t.tag) l.1) M
          (((g⁻¹ * q * g : ModGL t.tag K) : Module.End K (RootModule t.tag K)) -
            (1 : Module.End K (RootModule t.tag K))) :=
    exists_optimal_parabolic_prime p (RootWeightDatum.fixed t σ hσ) hRG hRp hR
  set J := (RootWeightDatum.fixed t σ hσ).face l with hJ
  refine ⟨g, hg, J, hP, fun q hq => ?_⟩
  obtain ⟨hl', hA⟩ := fixed_dominant_unfold t σ hσ hl
  obtain ⟨qm, ⟨hu, hm, hy⟩, -⟩ :=
    (diagram_fixed_parabolic_root_radical_Levi_factors t K σ J).2.2.2.2.2.2.2.2.2.2.2.1 _
      (hP q (hRG hq) (Subgroup.le_normalizer hq))
  have h := hraise q hq
  rw [hy] at h
  have hm1 := eq_one_of_labelRaises_mul hl' hA (Subgroup.mem_inf.1 hu).1
    (Subgroup.mem_inf.1 hm).1 hM0 h
  rw [hy, hm1, mul_one]
  exact hu

theorem pCoreOf_graphFixedParabolic_prime [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    (σ : K ≃+* K) (J : Set (Fin t.foldedTag.rank)) :
    pCoreOf r (graphFixedParabolic t K σ.toRingHom J) =
      graphFixedParabolicRadical t K σ.toRingHom J := by
  have := finite_modGL (τ := t.tag) (K := K)
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hLP, huniq, -, -, -, -, hfin, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
  obtain ⟨-, -, -, -, hwA⟩ := diagram_fixed_parabolic_intersection t K σ J
  obtain ⟨wA, ⟨hwA1, hwA2⟩, -⟩ := (diagram_fixed_parabolic_intersection t K σ J).2.2.2.1
  obtain ⟨-, hnMP, -, hnV⟩ := hwA wA hwA1 hwA2
  set A := t.orbitUnion J with hA
  set P := graphFixedParabolic t K σ.toRingHom J with hPdef
  set Q := graphFixedParabolicRadical t K σ.toRingHom J with hQdef
  set L := graphFixedParabolicLevi t K σ.toRingHom J with hLdef
  set C₀ := graphFixedRootGroup t K σ.toRingHom with hC₀
  set U₀ := graphFixedPosUnipotent t K σ.toRingHom with hU₀
  set O := pCoreOf r P with hOdef
  have hO2 : IsPGroup r O := pCoreOf_isPGroup r P
  have hPO : P ≤ Subgroup.normalizer (O : Set (ModGL t.tag K)) := le_normalizer_pCoreOf r P
  have hPQ : P ≤ Subgroup.normalizer (Q : Set (ModGL t.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm
  have hQO : Q ≤ O := le_pCoreOf_of_le_normalizer r hQP hPQ (hfin r)
  refine le_antisymm ?_ hQO
  obtain ⟨w₀, hmax, -⟩ := weyl_longest_element t.tag
  obtain ⟨⟨S, hS⟩, -⟩ := exceptional_fixed_Sylow_opposition t K r σ w₀ hmax
  have hPC : P ≤ C₀ := graphFixedParabolic_le t K σ.toRingHom J
  have hU₀P : U₀ ≤ P := graphFixedPosUnipotent_le_graphFixedRootBorel.trans le_sup_left
  have hU₀C : U₀ ≤ C₀ := hU₀P.trans hPC
  have hU₀2 : IsPGroup r U₀ := by
    have h := S.isPGroup'
    rw [hS] at h
    exact h.of_equiv (Subgroup.subgroupOfEquivOfLe hU₀C)
  have hOU2 : IsPGroup r (O ⊔ U₀ : Subgroup (ModGL t.tag K)) :=
    IsPGroup.to_sup_of_normal_left' hO2 hU₀2 (hU₀P.trans hPO)
  have hOUC : O ⊔ U₀ ≤ C₀ := sup_le ((pCoreOf_le r P).trans hPC) hU₀C
  have hmax' := S.is_maximal' (Q := (O ⊔ U₀).subgroupOf C₀) hOU2.comap_subtype (by
    rw [hS]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)))
  rw [hS] at hmax'
  have hOU : O ≤ U₀ := by
    intro x hx
    have hxC : x ∈ C₀ := hOUC (Subgroup.mem_sup_left hx)
    have : (⟨x, hxC⟩ : C₀) ∈ (O ⊔ U₀).subgroupOf C₀ :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hx)
    rw [hmax'] at this
    exact Subgroup.mem_subgroupOf.mp this
  have hOUa : O ≤ posUnipotent t.tag K := fun x hx => (Subgroup.mem_inf.mp (hOU hx)).1
  set n := canonicalRep (coxeterSystem t.tag) K wA with hn
  have hnM : n ∈ parabolicLevi t.tag K A := (Subgroup.mem_inf.mp hnMP).1
  have hnP : n ∈ P := (Subgroup.mem_inf.mp hnMP).2
  have hnL : n ∈ L := Subgroup.mem_inf.mpr ⟨hnM, hPC hnP⟩
  have hOL : O ⊓ L = ⊥ := by
    have hV : ∀ z ∈ O, z ∈ parabolicLevi t.tag K A → z ∈ parabolicLeviUnipotent t.tag K A := by
      intro z hzO hzM
      obtain ⟨q, hq, v, hv, rfl⟩ := exists_mul_of_mem_posUnipotent A (hOUa hzO)
      have hqM : q ∈ parabolicLevi t.tag K A := by
        have : q = q * v * v⁻¹ := by group
        rw [this]
        exact mul_mem hzM (inv_mem (parabolicLeviUnipotent_le_parabolicLevi A hv))
      have hq1 : q ∈ parabolicRadical t.tag K A ⊓ parabolicLevi t.tag K A :=
        Subgroup.mem_inf.mpr ⟨hq, hqM⟩
      rw [parabolicRadical_inf_parabolicLevi, Subgroup.mem_bot] at hq1
      rw [hq1, one_mul]
      exact hv
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨hyO, hyL⟩ := Subgroup.mem_inf.mp hy
    have hyM : y ∈ parabolicLevi t.tag K A := (Subgroup.mem_inf.mp hyL).1
    have hy' : n⁻¹ * y * n ∈ parabolicLeviUnipotent t.tag K A := by
      refine hV _ ?_ (mul_mem (mul_mem (inv_mem hnM) hyM) hnM)
      have := (Subgroup.mem_normalizer_iff.mp (hPO (inv_mem hnP)) y).mp hyO
      rwa [inv_inv] at this
    have hyN : y ∈ negUnipotent t.tag K := by
      have hmem : (MulAut.conj n).toMonoidHom (n⁻¹ * y * n) ∈
          (parabolicLeviUnipotent t.tag K A).map (MulAut.conj n).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy'
      rw [hnV] at hmem
      have e : (MulAut.conj n).toMonoidHom (n⁻¹ * y * n) = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e] at hmem
      refine rootSpan_le_negUnipotent (fun α hα => ?_) hmem
      obtain ⟨β, hβ, rfl⟩ := hα
      exact ⟨IsRoot.neg hβ.1.1, by rw [height_neg]; have := hβ.2.2; omega⟩
    have h1 : y ∈ posUnipotent t.tag K ⊓ negUnipotent t.tag K :=
      Subgroup.mem_inf.mpr ⟨hOUa hyO, hyN⟩
    rwa [CFSG.LieType.Chevalley.posUnipotent_inf_negUnipotent] at h1
  intro x hx
  obtain ⟨⟨q, m⟩, ⟨hq, hm, rfl⟩, -⟩ := huniq x ((pCoreOf_le r P) hx)
  have hmO : m ∈ O := by
    have : m = q⁻¹ * (q * m) := by group
    rw [this]
    exact mul_mem (inv_mem (hQO hq)) hx
  have hm1 : m ∈ O ⊓ L := Subgroup.mem_inf.mpr ⟨hmO, hm⟩
  rw [hOL, Subgroup.mem_bot] at hm1
  rw [hm1, mul_one]
  exact hq

theorem pCoreOf_graphFixedParabolic [Finite K] [CharP K 2] (σ : K ≃+* K)
    (J : Set (Fin t.foldedTag.rank)) :
    pCoreOf 2 (graphFixedParabolic t K σ.toRingHom J) =
      graphFixedParabolicRadical t K σ.toRingHom J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact pCoreOf_graphFixedParabolic_prime 2 σ J

theorem isRadicalPGroup_graphFixedParabolicRadical_prime [Finite K] (r : ℕ) [Fact r.Prime]
    [CharP K r] (σ : K ≃+* K) (J : Set (Fin t.foldedTag.rank)) :
    CFSG.GroupTheory.IsRadicalPGroup r (graphFixedRootGroup t K σ.toRingHom)
      (graphFixedParabolicRadical t K σ.toRingHom J) := by
  unfold CFSG.GroupTheory.IsRadicalPGroup
  rw [diagram_fixed_parabolic_root_radical_normalizers, pCoreOf_graphFixedParabolic_prime]

theorem graphFixedParabolicRadical_univ (σ : K ≃+* K) :
    graphFixedParabolicRadical t K σ.toRingHom Set.univ = ⊥ := by
  have hA : t.orbitUnion Set.univ = Set.univ :=
    Set.eq_univ_of_forall fun i => mem_orbitUnion_iff_orbitIndex.mpr (Set.mem_univ _)
  rw [graphFixedParabolicRadical, hA, parabolicRadical_univ, bot_inf_eq]

theorem exists_eq_map_conj_graphFixedParabolicRadical_prime [Finite K] (r : ℕ) [Fact r.Prime]
    [CharP K r] (σ : K ≃+* K) (hσ : σ ^ t.order = 1) {R : Subgroup (ModGL t.tag K)}
    (hR : R ≠ ⊥)
    (hRad : CFSG.GroupTheory.IsRadicalPGroup r (graphFixedRootGroup t K σ.toRingHom) R) :
    ∃ g ∈ graphFixedRootGroup t K σ.toRingHom, ∃ J : Set (Fin t.foldedTag.rank),
      R = (graphFixedParabolicRadical t K σ.toRingHom J).map (MulAut.conj g).toMonoidHom := by
  have := finite_modGL (τ := t.tag) (K := K)
  obtain ⟨g, hg, J, hN, hQ⟩ := exists_optimal_radical_fixed_prime r σ hσ hRad.le hRad.isPGroup hR
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, -, -, -, -, -, -, hfin, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
  exact ⟨g, hg, J, eq_map_conj_of_optimal_prime (hfin r)
    (hQP.trans (graphFixedParabolic_le t K σ.toRingHom J))
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm) hRad hg hN hQ⟩

theorem exists_eq_map_conj_graphFixedParabolicRadical [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ ^ t.order = 1) {R : Subgroup (ModGL t.tag K)} (hR : R ≠ ⊥)
    (hRad : GGRadicalTwo (graphFixedRootGroup t K σ.toRingHom) R) :
    ∃ g ∈ graphFixedRootGroup t K σ.toRingHom, ∃ J : Set (Fin t.foldedTag.rank),
      R = (graphFixedParabolicRadical t K σ.toRingHom J).map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_eq_map_conj_graphFixedParabolicRadical_prime 2 σ hσ hR hRad

end GGOppRadExc

end CFSG.StandardType
