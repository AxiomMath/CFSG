module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeBOddIndex
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9TwE6Rat

public section

namespace CFSG.StandardType.TwE6ThreeB

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (d4Nodes)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section B2
open CFSG.Open CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.StandardType
  CFSG.StandardType.ExcThreeAtTwo

theorem ratComp_notExcThree_or_d4_E6
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) (hq2 : S.D.q = 2)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GGNotExcThreeOrder (ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∨
      (compRank (componentRoots (rootCharHom a) i) = 4 ∧
        (componentRoots (rootCharHom a) i).ncard = 24) := by
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · left
    by_cases hr3 : compRank (componentRoots (rootCharHom a) i) = 3
    · exact (not_a3Shape_of_three_E6 S h3L hTp i ⟨hr3, by rw [hA.2, hr3]⟩).elim
    · exact typeA_ggCQ_ne_three_two S hq2 hT hap h1 i hA hr3 hqs
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S
        Nat.prime_three h3L hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD | hE
    · exact (hA hA').elim
    · by_cases hr4 : compRank (componentRoots (rootCharHom a) i) = 4
      · exact Or.inr ⟨hr4, by rw [hD.2, hr4]⟩
      · left
        have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
        have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
          rw [hD.2, Nat.mul_assoc]
          have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
          have h20 : 20 ≤ compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1) :=
            le_trans (by norm_num : 20 ≤ 5 * 4) (Nat.mul_le_mul hr5 h4)
          omega
        by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)])
        · exact inner_big_ggCQ_ne S hq2 hT i (Or.inr (Or.inl rfl)) hinner h26
        · exact outerD_ggCQ_ne S hq2 hT hap h1 i hr5 hD.2 hinner
    · exact (false_of_e6Class_E S Nat.prime_three h3L hTp h1 i hE.1 hE.2).elim

end B2

section Assembly
open CFSG.Open CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.StandardType
  CFSG.StandardType.ExcThreeAtTwo TwE6UniqAbs

theorem kac_d4_only : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3 →
    ∀ x ∈ zlC ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ)
        ((m5 : ℕ) : ℤ),
      szF (zlC ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ)
        ((m5 : ℕ) : ℤ)) x = 24 →
      ∀ y ∈ zlC ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ)
          ((m5 : ℕ) : ℤ),
        cmpF (zlC ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ)
          ((m5 : ℕ) : ℤ)) y =
          cmpF (zlC ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ)
            ((m5 : ℕ) : ℤ)) x := by
  decide +kernel

theorem componentRoots_eq_kernelRoots_of_ncard_24
    {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hc : (componentRoots (rootCharHom a) i).ncard = 24) :
    componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) := by
  obtain ⟨-, w, m0, m1, m2, m3, m4, m5, -, hsum, -, hcl⟩ := kac_class_data h3 hap
  obtain ⟨x, hx, hrx, hnx, -, -⟩ := hcl i
  refine Set.Subset.antisymm (fun γ hγ => hγ.1) fun γ hγ => ?_
  obtain ⟨y, hy, hry, -, -, -⟩ := hcl ⟦⟨γ, hγ⟩⟧
  have hmem : γ ∈ componentRoots (rootCharHom a) ⟦⟨γ, hγ⟩⟧ := ⟨hγ, rfl⟩
  rw [hry, kac_d4_only m0 m1 m2 m3 m4 m5 hsum x hx (hnx ▸ hc) y hy, ← hrx] at hmem
  exact hmem

theorem ratComp_excThree_layer_E6
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hq2 : S.D.q = 2) (hAlg : S.IsAlgebraic) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hout : compRank (componentRoots (rootCharHom a) i) = 4 →
      (componentRoots (rootCharHom a) i).ncard = 24 →
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) →
      GGNotExcThreeOrder (ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    GGNotExcThreeOrder (ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∨
      (Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i) = ⊥ ∧
        ∀ x ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}, ∀ k : ℕ, x ^ (2 ^ k) = 1 →
          x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  rcases ratComp_notExcThree_or_d4_E6 S hq2 hT hap h1 i hqs with h | ⟨hr4, hc⟩
  · exact Or.inl h
  have h3 : ((3 : ℕ) : L) ≠ 0 := by
    rw [show ((3 : ℕ) : L) = 1 + 2 by norm_num, CharTwo.two_eq_zero, add_zero]
    exact one_ne_zero
  have hceq := componentRoots_eq_kernelRoots_of_ncard_24 h3 hap i hc
  have hall : (kernelRoots (rootCharHom a)).ncard = 24 := hceq ▸ hc
  have hker := rho_mem_kernelRoots_of_mem_torus S hT
  have hρΨ : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hceq] at hγ ⊢
    exact hker γ hγ
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
  have hs := componentOrbitLength_eq_one hfin hρΨ
  by_cases hin : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · rw [hs, hceq] at hin
    obtain ⟨-, -, -, hZ, h2, -⟩ :=
      twE6_threeB_rationalComponent_of_twistInner S hq2 hAlg hap h1 hT hall hin i
    exact Or.inr ⟨hZ, h2⟩
  · exact Or.inl (hout hr4 hc hin)

end Assembly

section Outer
open CFSG.Open CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType
  CFSG.StandardType.ExcThreeAtTwo CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.LocalAnalysis.GLTheoremA.RationalModel CFSG.LocalAnalysis.GLTheoremA.HStdExcl

theorem ggCQ_notExcThree_of_d4_not_inner_E6
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) (hq2 : S.D.q = 2)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24)
    (hinner : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    GGNotExcThreeOrder (ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    rw [show ((3 : ℕ) : L) = 1 + 2 by norm_num, CharTwo.two_eq_zero, add_zero]
    exact one_ne_zero
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  rcases hP with rfl | ⟨t, ht, rfl⟩
  · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext1 g
      rw [hΦ, one_mul, inv_one, mul_one]
    exact d4Class_ggCQ_E6_two S ⟨Fr, hFr, hΦ'⟩ hq2 hT hap h1 i hrank hcard hqs
  · obtain ⟨v, hv, hρ'⟩ := S.d4_pinnedT_of_prime Nat.prime_three h3L facts_E6
      kacCount_E6_four (by decide) (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT
      (rootDiagUnit_pow_eq_one_of_forall hap) i hrank hcard
    have hs := componentOrbitLength_eq_one hfin hρ'
    rw [hs, Function.iterate_one] at hinner
    have hsub : kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i :=
      (componentRoots_eq_kernelRoots_of_ncard_24 h3L hap i hcard).ge
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hq21 : S.D.q = 2 ^ 1 := by rw [hq2, pow_one]
    obtain ⟨⟨e⟩, hZ⟩ := d4t2out_rationalComponent_equiv (ℓ := 2) (f := 1) S
      ⟨t, ht, Fr, hFr, hΦ⟩ (by norm_num) hq21 (by norm_num) hT hap i v hv hsub hρ' hinner
    haveI := finite_rationalComponent S a i
    have hcardR : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) =
        CFSG.Open.orderTrialityD4 (2 ^ 1) := by
      have h := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds _ _ ⟨e⟩
      change _ = CFSG.Open.orderTrialityD4 (TauCeti.PrimePower.card _) at h
      rw [h, TauCeti.PrimePower.card_def]
    have hquot : ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i) =
        Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      Nat.card_congr
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv
    rw [hquot, hcardR]
    unfold CFSG.Open.orderTrialityD4 GGNotExcThreeOrder
    norm_num

theorem ratComp_excThree_layer_E6'
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hq2 : S.D.q = 2) (hAlg : S.IsAlgebraic) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GGNotExcThreeOrder (ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∨
      (Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i) = ⊥ ∧
        ∀ x ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}, ∀ k : ℕ, x ^ (2 ^ k) = 1 →
          x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  ratComp_excThree_layer_E6 S hq2 hAlg hT hap h1 i hqs fun hr hc hnin =>
    ggCQ_notExcThree_of_d4_not_inner_E6 S hq2 hT hap h1 i hqs hr hc hnin

end Outer

end CFSG.StandardType.TwE6ThreeB

end
