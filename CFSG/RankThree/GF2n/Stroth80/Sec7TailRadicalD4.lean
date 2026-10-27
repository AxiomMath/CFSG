module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailRadicalSection
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLeviQuotient
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseOneLie
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4LeParab
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Levi
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.Chevalley.EvenTrialityElementaryNine
public import CFSG.Quasithin.SteinbergCDRankOneLeviOddCyclic
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec78NormZ0
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssemblyFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarFrattini
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace RadD4


section Levi

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem graphFixedParabolicLeviUnipotent_empty :
    graphFixedParabolicLeviUnipotent TwistTag.D4 K σ.toRingHom ∅ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, -⟩
  have hV : parabolicLeviUnipotent TwistTag.D4.tag K (TwistTag.D4.orbitUnion ∅) = ⊥ := by
    rw [parabolicLeviUnipotent, CFSG.Quasithin.SteinbergCD.parabolicPosRoots_orbitUnion_empty]
    simp [rootSpan]
  rw [hV] at hx
  exact hx

theorem exists_levi_factor [CharP K 2] {e : ℕ} (h : CFSG.LocalAnalysis.GLTheoremA.TD4Le.Std e K σ)
    {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ) :
    ∃ L : Subgroup (ModGL TwistTag.D4.tag K),
      L ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom J ∧
      L ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
      L ⊓ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J = ⊥ ∧
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤ Subgroup.normalizer (L : Set _) ∧
      (∀ x ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J,
        ∃ q ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J,
          ∃ t ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom, ∃ l ∈ L, x = q * (t * l)) ∧
      (L = ⊥ ∨ ∃ (F : Type) (_ : Field F) (_ : Finite F) (s : ℕ), Nat.card F = 2 ^ s ∧
        Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)) := by
  rcases CFSG.LocalAnalysis.GLTheoremA.TD4Le.eq_empty_or_singleton_of_ne_univ hJ with
    rfl | ⟨a, rfl⟩
  ·
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hB, -⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ ∅
    refine ⟨⊥, bot_le, bot_le, bot_inf_eq _, fun t _ => ?_, fun x hx => ?_, Or.inl rfl⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro n
      simp only [SetLike.mem_coe, Subgroup.mem_bot]
      constructor
      · rintro rfl
        group
      · intro hn
        have e : n = t⁻¹ * (t * n * t⁻¹) * t := by group
        rw [e, hn]
        group
    · rw [graphFixedParabolic_empty] at hx
      have hx' : x ∈ (graphFixedRootBorel TwistTag.D4 K σ.toRingHom :
          Set (ModGL TwistTag.D4.tag K)) := hx
      rw [hB, graphFixedParabolicLeviUnipotent_empty] at hx'
      obtain ⟨q, hq, y, hy, rfl⟩ := hx'
      obtain ⟨t, ht, v, hv, rfl⟩ := hy
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hv
      exact ⟨q, hq, t, ht, 1, Subgroup.one_mem _, by rw [hv]⟩
  ·
    obtain ⟨-, -, -, -, -, -, hinf, -, hQP, hQnorm, hLP, -, -⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ {a}
    set M := (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range with hM
    set Q := graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {a} with hQ
    set H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom with hH
    have hML : M ≤ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom {a} :=
      CFSG.RankThree.PartTwo.Sec4.Res417Seven.range_le_graphFixedParabolicLevi _ a
    have hMP : M ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := hML.trans hLP
    have hMC : M ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun x hx => (hML hx).2
    have hHN : H ≤ Subgroup.normalizer (M : Set (ModGL TwistTag.D4.tag K)) :=
      CFSG.RankThree.PartTwo.Sec4.Res417Seven.graphFixedRootTorus_le_normalizer _ a
    have hHP : H ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} :=
      graphFixedRootTorus_le_graphFixedRootBorel.trans
        (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
    have hQN : H ⊔ M ≤ Subgroup.normalizer (Q : Set (ModGL TwistTag.D4.tag K)) :=
      (sup_le hHP hMP).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm)
    refine ⟨M, hMP, hMC, ?_, hHN, fun x hx => ?_, Or.inr ?_⟩
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxM, hxQ⟩ := Subgroup.mem_inf.1 hx
      have hxL := hML hxM
      rw [← hinf]
      exact Subgroup.mem_inf.2 ⟨hxQ, Subgroup.mem_inf.2 ⟨hxL.1,
        graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom hxL.2⟩⟩
    · have hx' : x ∈ ((Q ⊔ (H ⊔ M) : Subgroup (ModGL TwistTag.D4.tag K)) :
          Set (ModGL TwistTag.D4.tag K)) :=
        CFSG.RankThree.PartTwo.Sec4.Res417Seven.graphFixedParabolic_singleton_le_sup σ a hx
      rw [Subgroup.coe_mul_of_right_le_normalizer_left Q (H ⊔ M) hQN] at hx'
      obtain ⟨q, hq, n, hn, rfl⟩ := hx'
      have hn' : n ∈ ((H ⊔ M : Subgroup (ModGL TwistTag.D4.tag K)) :
          Set (ModGL TwistTag.D4.tag K)) := hn
      rw [Subgroup.coe_mul_of_left_le_normalizer_right H M hHN] at hn'
      obtain ⟨t, ht, l, hl, rfl⟩ := hn'
      exact ⟨q, hq, t, ht, l, hl, rfl⟩
    · have hinj : Function.Injective (orbitRankOneHom TwistTag.D4 K σ.toRingHom a) :=
        CFSG.RankThree.Chevalley.injective_of_ker_scalar_of_charTwo fun g hg =>
          eq_smul_one_of_mem_ker_orbitRankOneHom hg
      refine ⟨↥(orbitField TwistTag.D4 K σ.toRingHom a), inferInstance, inferInstance,
        e * (TwistTag.D4.orbit a).card, ?_, ⟨(MonoidHom.ofInjective hinj).symm⟩⟩
      rw [CFSG.LocalAnalysis.GLTheoremA.TD4Le.card_orbitField_std h a, ← pow_mul]

end Levi

section Reduction

theorem exists_mulEquiv_graphFixedRootGroupD4_of_lieModel {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (hX : CFSG.Blueprint.LieModel X .trialityD4 0 2 m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      CFSG.LocalAnalysis.GLTheoremA.TD4Le.Std m K σ ∧
        Nonempty (X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  rcases hX with ⟨hc, -⟩ | ⟨-, -, hmodel⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd hc (by decide)
  · obtain ⟨K, _, _, σ, hK, hσ, he⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hm hmodel.2
    exact ⟨K, inferInstance, inferInstance, σ, ⟨hm, hK, Or.inl hσ⟩, he⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem exists_conj_le_graphFixedParabolic {m : ℕ}
    (h : CFSG.LocalAnalysis.GLTheoremA.TD4Le.Std m K σ) {X : Type} [Group X]
    (e : X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) {U : Subgroup X} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) :
    ∃ ψ : X →* ModGL TwistTag.D4.tag K, Function.Injective ψ ∧
      ψ.range = graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
      ∃ J : Set (Fin TwistTag.D4.foldedTag.rank), J ≠ Set.univ ∧
        (Subgroup.normalizer (U : Set X)).map ψ ≤
          graphFixedParabolic TwistTag.D4 K σ.toRingHom J := by
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  have hT : U.map e.toMonoidHom ≠ ⊥ := fun hT => hU (by
    rw [← Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective]
    exact hT)
  have hT2 : IsPGroup 2 (U.map e.toMonoidHom) := hU2.map _
  obtain ⟨g, J, hJ, -, -, -, -, -, hN⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.TD4Le.borelTits_normalized σ h _ hT hT2
  set φ : X →* ↥C := (MulAut.conj g).toMonoidHom.comp e.toMonoidHom with hφ
  have hφs : Function.Surjective φ := (MulAut.conj g).surjective.comp e.surjective
  refine ⟨C.subtype.comp φ, C.subtype_injective.comp ((MulAut.conj g).injective.comp e.injective),
    ?_, J, hJ, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hφs, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · have hmap : (Subgroup.normalizer (U : Set X)).map φ =
        (Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup ↥C) : Set ↥C)).map
          (MulAut.conj g).toMonoidHom := by
      rw [hφ, ← Subgroup.map_map, Subgroup.map_equiv_normalizer_eq]
    rw [← Subgroup.map_map, hmap]
    refine (Subgroup.map_mono hN).trans ?_
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left

end Reduction

section Pullback

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem exists_pullback_data {m : ℕ} (h : CFSG.LocalAnalysis.GLTheoremA.TD4Le.Std m K σ)
    {X : Type} [Group X] {ψ : X →* ModGL TwistTag.D4.tag K} (hψ : Function.Injective ψ)
    (hψr : ψ.range = graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ) (U : Subgroup X)
    (hNJ : (Subgroup.normalizer (U : Set X)).map ψ ≤
      graphFixedParabolic TwistTag.D4 K σ.toRingHom J) :
    ∃ P R H L : Subgroup X, Subgroup.normalizer (U : Set X) ≤ P ∧ R ≤ P ∧
      (R.subgroupOf P).Normal ∧ IsPGroup 2 R ∧ H ≤ P ∧ L ≤ P ∧
      (∀ x ∈ P, ∃ q ∈ R, ∃ t ∈ H, ∃ l ∈ L, x = q * (t * l)) ∧
      H ≤ Subgroup.normalizer (L : Set X) ∧ (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) ∧
      L ⊓ R = ⊥ ∧
      (L = ⊥ ∨ ∃ (F : Type) (_ : Field F) (_ : Finite F) (s : ℕ), Nat.card F = 2 ^ s ∧
        Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)) := by
  obtain ⟨L, hLP, hLC, hLQ, hHN, hfac, hLiso⟩ := exists_levi_factor σ h hJ
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, -, -, -, -, -, -, hQ2, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ J
  set PJ := graphFixedParabolic TwistTag.D4 K σ.toRingHom J with hPJ
  set Q := graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J with hQ
  set H₁ := graphFixedRootTorus TwistTag.D4 K σ.toRingHom with hH₁
  have hQC : Q ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (graphFixedParabolicRadical_le_graphFixedPosUnipotent J).trans
      (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
  have hHC : H₁ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := inf_le_right
  have hHP : H₁ ≤ PJ := graphFixedRootTorus_le_graphFixedRootBorel.trans
    (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
  have hpre : ∀ {y : ModGL TwistTag.D4.tag K},
      y ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom → ∃ x, ψ x = y := fun hy => by
    rw [← hψr] at hy
    exact hy
  refine ⟨PJ.comap ψ, Q.comap ψ, H₁.comap ψ, L.comap ψ, Subgroup.map_le_iff_le_comap.1 hNJ,
    Subgroup.comap_mono hQP, ?_, hQ2 2 |>.comap_of_injective ψ hψ, Subgroup.comap_mono hHP,
    Subgroup.comap_mono hLP, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨fun r hr p => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hr ⊢
    have hpP : ψ (p : X) ∈ PJ := p.2
    have hn := (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm hpP
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hn _).1 hr
  ·
    intro x hx
    obtain ⟨q, hq, t, ht, l, hl, hxe⟩ := hfac _ hx
    obtain ⟨q', rfl⟩ := hpre (hQC hq)
    obtain ⟨t', rfl⟩ := hpre (hHC ht)
    obtain ⟨l', rfl⟩ := hpre (hLC hl)
    refine ⟨q', hq, t', ht, l', hl, hψ ?_⟩
    rw [hxe, map_mul, map_mul]
  ·
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro n
    simp only [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 (hHN ht) (ψ n)
  ·
    intro a ha b hb
    exact hψ (by rw [map_mul, map_mul]; exact graphFixedRootTorus_mul_comm ha hb)
  ·
    rw [← Subgroup.comap_inf, hLQ, MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff ψ).2 hψ]
  ·
    rcases hLiso with rfl | ⟨F, _, _, s, hF, ⟨eL⟩⟩
    · left
      rw [MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff ψ).2 hψ]
    · right
      have hLr : L ≤ ψ.range := hψr ▸ hLC
      have e₁ : ↥(L.comap ψ) ≃* ↥L :=
        ((L.comap ψ).equivMapOfInjective ψ hψ).trans
          (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hLr))
      exact ⟨F, inferInstance, inferInstance, s, hF, ⟨e₁.trans eL⟩⟩

end Pullback

end RadD4

open Subgroup CFSG CFSG.Open


theorem radicalTwoSubgroup_trialityD4 :
    ∀ (X : Type) [Group X] [Finite X],
      (∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .trialityD4 0 2 m) →
      ∀ U : Subgroup X, U ≠ ⊥ → IsPGroup 2 U →
        inSubgroup (pCore 2) (Subgroup.normalizer (U : Set X)) = U →
        ∀ S : Subgroup (↥(Subgroup.normalizer (U : Set X)) ⧸
            U.subgroupOf (Subgroup.normalizer (U : Set X))),
          S.Normal → IsQuasisimple S →
            ∃ (s : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 2 ≤ s ∧ Nat.card K = 2 ^ s ∧
              ∃ Z' : Subgroup S, Z' ≤ Subgroup.center S ∧ ∃ _ : Z'.Normal,
                Nonempty ((S ⧸ Z') ≃* StatedProj (StatedSL 2 K)) := by
  intro X _ _ hX U hU hU2 hrad S _ hSq
  obtain ⟨m, hm, hmodel⟩ := hX
  obtain ⟨K, _, _, σ, h, ⟨e⟩⟩ := RadD4.exists_mulEquiv_graphFixedRootGroupD4_of_lieModel hm hmodel
  haveI := h.charP_two
  obtain ⟨ψ, hψ, hψr, J, hJ, hNJ⟩ := RadD4.exists_conj_le_graphFixedParabolic σ h e hU hU2
  obtain ⟨P, R, H, L, hNP, hRP, hRn, hR2, hHP, hLP, hfac, hHN, hHc, hLR, hLiso⟩ :=
    RadD4.exists_pullback_data σ h hψ hψr hJ U hNJ
  haveI := hRn
  refine exists_statedProj_of_radical hrad hNP hRP hRn hR2 _
    (commutator_quotient_le_map_of_factor hRP hHP hLP hfac hHN hHc) ?_ S hSq
  rcases hLiso with rfl | ⟨F, _, _, s, hF, ⟨eL⟩⟩
  · left
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  · right
    obtain ⟨e₀⟩ := nonempty_mulEquiv_map_subgroupOf_of_inf_eq_bot hLP hLR
    exact ⟨F, inferInstance, inferInstance, s, hF, ⟨e₀.trans eL⟩⟩

end CFSG.RankThree.GF2n.Stroth80

end
