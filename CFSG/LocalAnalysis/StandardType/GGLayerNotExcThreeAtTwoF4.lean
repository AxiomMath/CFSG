module

public import Certificates.Certificate13659
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsBasic
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerCover
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmall
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.LocalAnalysis.StandardType.GGExcSmallCompOrder
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.RankThree.PartOne.KE.SLnShape
import Certificates.Certificate10
import Certificates.Certificate10050
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate13660
import Certificates.Certificate1952
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate8117
import Certificates.Certificate9

public section

namespace CFSG.StandardType.ExcThreeAtTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem ggNotExcThreeOrder_two_pow_mul_odd {e u : ℕ} (hu : Odd u) (h12 : e ≠ 12) (h6 : e ≠ 6)
    (h3 : e ≠ 3) : GGNotExcThreeOrder (2 ^ e * u) := by
  have key : ∀ a n : ℕ, Odd n → e ≠ a → 2 ^ e * u ≠ 2 ^ a * n := by
    intro a n hn hne heq
    exact hne (le_antisymm (ggAKFG_le_of_two_pow_dvd hn ⟨u, heq.symm⟩)
      (ggAKFG_le_of_two_pow_dvd hu ⟨n, heq⟩))
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact key 12 42525 ⟨21262, by norm_num⟩ h12 (by rw [h]; norm_num)
  · exact key 6 405 ⟨202, by norm_num⟩ h6 (by rw [h]; norm_num)
  · exact key 3 45 ⟨22, by norm_num⟩ h3 (by rw [h]; norm_num)

theorem odd_sum_mul_pow_of_even {Q : ℕ} (hQ : Even Q) (c : ℕ → ℕ) (hc : c 0 = 1) (N : ℕ) :
    Odd (∑ k ∈ Finset.range (N + 1), c k * Q ^ k) := by
  rw [Finset.sum_range_succ', hc, pow_zero, mul_one]
  have h2 : (2 : ℕ) ∣ ∑ k ∈ Finset.range N, c (k + 1) * Q ^ (k + 1) :=
    Finset.dvd_sum fun k _ =>
      Dvd.dvd.mul_left (dvd_pow (even_iff_two_dvd.mp hQ) (Nat.succ_ne_zero k)) _
  exact (even_iff_two_dvd.mpr h2).add_one

theorem ggCQ_top_subgroup {G : Type*} [Group G] (S : Subgroup G) :
    ggCQ (⊤ : Subgroup ↥S) = ggCQ S :=
  ggCQ_congr Subgroup.topEquiv

section HalfRoots


private theorem ncard_eq_two_mul_ncard_posRoots {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) (hfin : Ψ.Finite) : Ψ.ncard = 2 * (posRoots Ψ).ncard := by
  classical
  have hu : Ψ = posRoots Ψ ∪ negRoots Ψ := by
    ext α
    exact ⟨fun hα => (mem_posRoots_or_mem_negRoots hΨ hα).elim Or.inl Or.inr,
      fun h => h.elim (fun h => h.1) fun h => ((mem_negRoots_iff hΨ).1 h).1⟩
  have hdisj : Disjoint (posRoots Ψ) (negRoots Ψ) :=
    Set.disjoint_left.2 fun α h1 h2 => not_mem_negRoots_of_mem_posRoots h1 h2
  have himg : negRoots Ψ = (fun α : Fin τ.rank → ℤ => -α) '' posRoots Ψ := by
    ext α
    refine ⟨fun h => ⟨-α, h, by simp⟩, ?_⟩
    rintro ⟨β, hβ, rfl⟩
    change -(-β) ∈ posRoots Ψ
    rw [neg_neg]
    exact hβ
  have hfp : (posRoots Ψ).Finite := hfin.subset fun α hα => hα.1
  have hfn : (negRoots Ψ).Finite := by rw [himg]; exact hfp.image _
  conv_lhs => rw [hu]
  rw [Set.ncard_union_eq hdisj hfp hfn, himg, Set.ncard_image_of_injective _ neg_injective]
  ring

end HalfRoots

section RootSpan


theorem exists_odd_ggCQ_componentRootSpan {τ : Tag} {K : Type} [Field K] [Finite K]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) {s : ℕ} (hs : 1 ≤ s) (hK : Nat.card K = 2 ^ s) :
    ∃ u : ℕ, Odd u ∧ ggCQ (componentRootSpan K χ i) =
      2 ^ (s * (posRoots (componentRoots χ i)).ncard) * u := by
  obtain ⟨d, c, -, hc0, -, -, hcard⟩ :=
    SmallCompOrder.exists_card_componentRootSpan_counts (K := K) i
  obtain ⟨m, hm⟩ := SmallCompOrder.card_center_dvd_card_componentTorus (K := K) (χ := χ) i
  have hZpos : 0 < Nat.card (Subgroup.center (componentRootSpan K χ i)) := Nat.card_pos
  have hS := card_eq_ggCQ_mul (componentRootSpan K χ i)
  have hQ2 : Even (2 ^ s) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hQeven : Even (Nat.card K) := hK ▸ hQ2
  have hTodd : Odd (Nat.card (componentTorus K χ i)) := by
    by_contra hT
    have h2 : 2 ∣ Nat.card (componentTorus K χ i) :=
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hT)
    have h2' := SmallCompOrder.prime_dvd_sub_one_of_dvd_card_componentTorus (K := K) i
      Nat.prime_two h2
    rw [hK] at h2'
    exact (Nat.not_even_iff_odd.mpr (Nat.Even.sub_odd Nat.one_le_two_pow hQ2 odd_one))
      (even_iff_two_dvd.mpr h2')
  have hmodd : Odd m := (Nat.odd_mul.mp (hm ▸ hTodd)).2
  have hggCQ : ggCQ (componentRootSpan K χ i) = m * Nat.card K ^
      (posRoots (componentRoots χ i)).ncard *
        ∑ k ∈ Finset.range ((posRoots (componentRoots χ i)).ncard + 1),
          c k * Nat.card K ^ k := by
    refine Nat.eq_of_mul_eq_mul_right hZpos ?_
    rw [← hS, hcard, hm]
    ring
  refine ⟨m * ∑ k ∈ Finset.range ((posRoots (componentRoots χ i)).ncard + 1),
    c k * Nat.card K ^ k, hmodd.mul (odd_sum_mul_pow_of_even hQeven c hc0 _), ?_⟩
  rw [hggCQ, hK, ← pow_mul]
  ring

theorem isPerfect_componentRootSpan_f4_card_eighteen {K : Type} [Field K] [Finite K]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) (hcard : (componentRoots χ i).ncard = 18) {s : ℕ} (hs : 1 ≤ s)
    (hK : Nat.card K = 2 ^ s) : Group.IsPerfect (componentRootSpan K χ i) := by
  classical
  by_cases hs2 : 2 ≤ s
  · have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs2
    obtain ⟨a, ha0, ha⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card K hK4
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.isPerfect_componentRootSpan_of_sq_ne_one
      (t := Units.mk0 a ha0) (fun h => ha (by simpa using congrArg Units.val h)) i
  · have hK2 : Nat.card K = 2 := by
      obtain rfl : s = 1 := by omega
      simpa using hK
    by_cases hA2 : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α ∧
        iform α α = iform δ δ ∧ iform α δ ≠ 0
    · exact isPerfect_componentRootSpan_F4_two (eq_zero_or_one_of_card_two hK2) i hA2
    · exfalso
      obtain ⟨α₀, hα₀⟩ : (componentRoots χ i).Nonempty :=
        Set.nonempty_of_ncard_ne_zero (by omega)
      have hbig : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α := by
        by_contra hbig
        push Not at hbig
        have hsub : componentRoots χ i ⊆ {α₀, -α₀} := fun δ hδ => by
          by_cases h : δ = α₀
          · simp [h]
          · simp [hbig α₀ hα₀ δ hδ h]
        have h2 : ({α₀, -α₀} : Set (Fin Tag.F4.rank → ℤ)).ncard ≤ 2 :=
          (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
        have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans h2
        omega
      push Not at hA2
      obtain ⟨s', l, -, -, -, hΨ⟩ := eq_b2Block_of_noA2 i hbig hA2
      have h8 : (componentRoots χ i).ncard ≤ 8 := by
        have e : ({s', -s', l, -l, s' + l, -(s' + l), 2 • s' + l, -(2 • s' + l)} :
            Set (Fin Tag.F4.rank → ℤ)) = ↑([s', -s', l, -l, s' + l, -(s' + l), 2 • s' + l,
              -(2 • s' + l)] : List (Fin Tag.F4.rank → ℤ)).toFinset := by
          ext x
          simp
        rw [hΨ, e, Set.ncard_coe_finset]
        exact (List.toFinset_card_le _).trans (by simp)
      omega

end RootSpan

section Main


theorem bc3Class_ggCQ_F4_two {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀)
    (_hFr : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr))
    (hq2 : S.D.q = 2) {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.F4 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 3)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 18)
    (_hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GGNotExcThreeOrder (ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
    by_cases hin : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · exact hin
    · have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
        unfold twistKind
        rw [if_neg hin, if_neg (by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega),
          if_neg (fun h => by omega),
          if_neg (fun h => by have := h.2; rw [hrank, hcard] at this; omega)]
      exact twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hkind
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨σ, hfin, hcardσ, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  haveI := hfin
  rw [hq2] at hcardσ
  have hperf :=
    isPerfect_componentRootSpan_f4_card_eighteen i hcard (Nat.succ_le_of_lt hs0) hcardσ
  have hN : (posRoots (componentRoots (rootCharHom a) i)).ncard = 9 := by
    have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
    have hfinΨ : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot Tag.F4).subset fun β hβ => hΨ.isRoot β hβ
    have := ncard_eq_two_mul_ncard_posRoots hΨ hfinΨ
    omega
  obtain ⟨u, hu, hCQ⟩ := exists_odd_ggCQ_componentRootSpan i (Nat.succ_le_of_lt hs0) hcardσ
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperf)) hf1
  have h := ggCQ_map_of_perfect f hker (Group.IsPerfect.top_iff.mpr hperf)
  rw [← MonoidHom.range_eq_map, hRf, ggCQ_top_subgroup] at h
  rw [h, hCQ, hN]
  exact ggNotExcThreeOrder_two_pow_mul_odd hu (by omega) (by omega) (by omega)

end Main

end CFSG.StandardType.ExcThreeAtTwo
