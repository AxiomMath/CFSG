module

public import CFSG.LocalAnalysis.StandardType.GGResMaxRankModel
public import CFSG.LocalAnalysis.StandardType.GGMaxRankE8Typed
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.LocalAnalysis.StandardType.GGExcMaxToral
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
import CFSG.RankThree.PartOne.K133H.WeylKey
import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE8
public import Certificates.Certificate13691
import CFSG.LieType.AlgebraicGroups.ToralCentralizerIdentity

public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.CGT.PushingUpLit.BHSSym.Coxeter
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.RatLayer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplitConj
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASuConj
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralChain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.LieType.Chevalley.SignKernelPositiveRepresentatives
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGLangWSLGamma
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFam
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RLangLabel
public import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.RankThree.Classical2.SLnConjLemmas
public import CFSG.RankThree.Classical2.SLnFrobeniusFormFixed

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryBasic
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylTorusAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylOuterTransport
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcD4Layer
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGMaxRankE8Core : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), Nat.card K = 2 ^ n →
    ∀ (A J : Subgroup (adjointGroup .E8 K)) (s : adjointGroup .E8 K),
      IsElemAbelian 3 A → 3 ^ 8 ≤ Nat.card A → s ∈ A → s ≠ 1 →
      IsComponentOf J (Subgroup.centralizer ({s} : Set (adjointGroup .E8 K))) →
      ((GGHasLabel ⟨.A, 8, n⟩ (↥J ⧸ Subgroup.center ↥J) ∧ 3 ∣ 2 ^ n - 1) ∨
        (GGHasLabel ⟨.twA, 8, n⟩ (↥J ⧸ Subgroup.center ↥J) ∧ 3 ∣ 2 ^ n + 1)) →
      ∃ eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J A),
        ∀ i, GGIsReflection 3 ((eJ ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J A)) : MulAut ↥A)

theorem ggMaxRankE8_exists_actual_rationalComponent
    (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (hK : Nat.card K = 2 ^ n)
    (A J : Subgroup (adjointGroup .E8 K)) (s : adjointGroup .E8 K)
    (hA : IsElemAbelian 3 A) (hAcard : 3 ^ 8 ≤ Nat.card A)
    (hsA : s ∈ A) (hs1 : s ≠ 1)
    (hJ : IsComponentOf J (Subgroup.centralizer ({s} : Set (adjointGroup .E8 K)))) :
    ∃ (S : LangSetup .E8 (AlgebraicClosure K) 5)
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (ι : adjointGroup .E8 K →* ModGL .E8 (AlgebraicClosure K))
      (w : WeylGroup .E8) (a : Fin (Tag.E8).rank → (AlgebraicClosure K)ˣ),
      (∀ c, Fr c = c ^ (2 ^ n)) ∧
      S.D.Φ = Units.map (entrywiseHom Fr) ∧
      S.D.q = 2 ^ n ∧
      S.D.n = canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w ∧
      (3 ∣ 2 ^ n - 1 → w = 1) ∧
      (3 ∣ 2 ^ n + 1 → ∀ u : Fin (Tag.E8).rank → ℤ, w • u = -u) ∧
      Function.Injective ι ∧
      ι.range = S.Γ ∧
      (∀ x : adjointGroup .E8 K,
        ι x = S.D.g0⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) * S.D.g0) ∧
      (∀ x : ModGL .E8 (AlgebraicClosure K),
        x ∈ A.map ι ↔ x ∈ S.D.torus ∧ x ^ 3 = 1) ∧
      ι s = rootDiagUnit .E8 a ∧
      (∀ i, a i ^ 3 = 1) ∧
      (∃ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
          J.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  let L := AlgebraicClosure K
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨Fr, hFr, D, hΦ, hqK, ⟨w, hw, _hshape, hsign1, hsign2⟩, _hmem, hiff, _hcardA⟩ :=
    ExcMaxToral.adjointMaxElemToral_E8_three (K := K) n hK A hA hAcard
  have hFr' : ∀ c : L, Fr c = c ^ (2 ^ n) := by
    intro c
    rw [hFr c, hK]
  have hq2 : D.q = 2 ^ n := hqK.trans hK
  have hperf : Group.IsPerfect ↥(adjointGroup .E8 K) :=
    CFSG.LieType.Steinberg.Adjoint.isPerfect_e8 (K := K)
  have hperf' : commutator ↥(adjointGroup .E8 K) = ⊤ := hperf.commutator_eq_top
  let ι₀ : adjointGroup .E8 K →* ModGL .E8 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .E8 K).subtype
  have hι₀ : Function.Injective ι₀ :=
    (baseChangeGL_injective (algebraMap K L)).comp (Subgroup.subtype_injective _)
  have hd : LangDescent D 5 ι₀ :=
    langDescent_untw (K := K) (L := L) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hFr D hΦ
      Nat.prime_five (by norm_num) hperf'
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    constructor
    · rw [hqK, Nat.card_eq_fintype_card]
      exact FiniteField.isPrimePow_card K
    · rw [hqK, ← map_natCast (algebraMap K L), Nat.card_eq_fintype_card,
        FiniteField.cast_card_eq_zero K, map_zero]
  have hpq : ¬ 5 ∣ D.q := by
    rw [hqK, hK]
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0; norm_num
    · intro h
      have h52 : (5 : ℕ) ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h
      norm_num at h52
  obtain ⟨S, hSD, -⟩ :=
    exists_langSetup_of_descent_nosylow (τ := .E8) (L := L) frobeniusOnRoots_proved D
      Nat.prime_five (Or.inl le_rfl) hqpow hpq ι₀ hι₀ hd
  have hSΓ : S.Γ = D.Γ := by
    change S.D.Γ = D.Γ
    rw [hSD]
  let ι : adjointGroup .E8 K →* ModGL .E8 L :=
    (MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀
  have hι_inj : Function.Injective ι :=
    (MulAut.conj D.g0⁻¹).injective.comp hι₀
  have hι_apply : ∀ x : adjointGroup .E8 K,
      ι x = D.g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E8 K) * D.g0 := by
    intro x
    simp [ι, ι₀, MulAut.conj_apply]
  have hι_range : ι.range = D.Γ := by
    rw [hd.Γ_eq]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨ι₀ x, ⟨x, rfl⟩, ?_⟩
      rfl
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  have hAimage : ∀ x : ModGL .E8 L, x ∈ A.map ι ↔ x ∈ D.torus ∧ x ^ 3 = 1 := by
    intro x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hiff _).mpr ⟨a, ha, (hι_apply a).symm⟩
    · rintro ⟨hxT, hx3⟩
      obtain ⟨a, ha, hax⟩ := (hiff x).mp ⟨hxT, hx3⟩
      exact ⟨a, ha, (hι_apply a).trans hax⟩
  have hιsT : ι s ∈ D.torus := ((hAimage (ι s)).mp ⟨s, hsA, rfl⟩).1
  obtain ⟨a, ha_eq⟩ :=
    exists_rootDiagUnit_eq_of_mem_torusGroup (τ := .E8) (K := L)
      (mem_twistedTorusOf.1 hιsT).1
  have hιs3 : (ι s) ^ 3 = 1 := ((hAimage (ι s)).mp ⟨s, hsA, rfl⟩).2
  have hroot3 : (rootDiagUnit .E8 a) ^ 3 = 1 := by rw [← ha_eq]; exact hιs3
  have ha3 : a ^ 3 = 1 :=
    rootDiagUnit_injective (τ := .E8) (K := L) (by
      have hmap : rootDiagUnit .E8 (a ^ 3) = (rootDiagUnit .E8 a) ^ 3 :=
        map_pow (rootDiagUnitHom .E8 L) a 3
      rw [hmap, hroot3, rootDiagUnit_one])
  have hap : ∀ i, a i ^ 3 = 1 := fun i => by
    have := congrFun ha3 i
    simpa using this
  have ha_ne : rootDiagUnit .E8 a ≠ 1 := by
    rw [← ha_eq]
    intro h
    exact hs1 (hι_inj (h.trans (map_one ι).symm))
  have hcompMap : IsComponentOf (J.map ι)
      ((Subgroup.centralizer ({s} : Set (adjointGroup .E8 K))).map ι) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ ι hι_inj
  have hcompD : IsComponentOf (J.map ι)
      (D.Γ ⊓ Subgroup.centralizer ({rootDiagUnit .E8 a} : Set (ModGL .E8 L))) := by
    have hcent := CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_of_injective
      hι_inj s
    rw [hcent, hι_range] at hcompMap
    simpa [ha_eq] using hcompMap
  have hcompS : IsComponentOf (J.map ι)
      (S.Γ ⊓ Subgroup.centralizer ({rootDiagUnit .E8 a} : Set (ModGL .E8 L))) := by
    rw [hSΓ]
    exact hcompD
  have hcompOpen : CFSG.Open.IsComponentOf (J.map ι)
      (S.Γ ⊓ Subgroup.centralizer ({rootDiagUnit .E8 a} : Set (ModGL .E8 L))) :=
    (isComponentOf_iff_open).mp hcompS
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    intro h
    have h2 : ((3 : ℕ) : L) = 1 := by
      have h3eq : ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 := by norm_num
      rw [h3eq, CharP.cast_eq_zero L 2, zero_add]
    rw [h2] at h
    exact one_ne_zero h
  obtain ⟨i, hq, heq⟩ :=
    CFSG.StandardType.LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2
      S (by decide) Nat.prime_three h3L (by rw [hSD, ← ha_eq]; exact hιsT) hap ha_ne hcompOpen
  refine ⟨S, Fr, ι, w, a, hFr', ?_, ?_, ?_, hsign1, hsign2, hι_inj, ?_, ?_, ?_, ?_, hap, ?_⟩
  · rw [hSD]; exact hΦ
  · rw [hSD]; exact hq2
  · rw [hSD]; exact hw
  · rw [hSΓ]; exact hι_range
  · intro x; rw [hSD]; exact hι_apply x
  · intro x; rw [hSD]; exact hAimage x
  · exact ha_eq
  · exact ⟨i, hq, heq⟩

private theorem maxRankE8_normalizer_action
    {G : Type} [Group G] {L : Type} [Field L]
    (ι : G →* ModGL .E8 L) (hι : ι.range ≤ adjointGroup .E8 L)
    (A J : Subgroup G) (s : G) (hsA : s ∈ A)
    (hAJ : ∀ x ∈ A, ι x ∈ torusGroup .E8 L)
    (hJ : J ≤ Subgroup.centralizer ({s} : Set G))
    (a : Fin Tag.E8.rank → Lˣ) (hs : ι s = rootDiagUnit .E8 a)
    (h3 : ∀ i, a i ^ 3 = 1)
    (g : G) (hgJ : g ∈ J) (hgN : g ∈ Subgroup.normalizer (A : Set G)) :
    ∃ v : WeylGroup .E8, v ∈ kernelWeylGroup (rootCharHom a) ∧
      ∀ x ∈ A, ι (g * x * g⁻¹) =
        canonicalRep (coxeterSystem .E8) L v * ι x * (canonicalRep (coxeterSystem .E8) L v)⁻¹ := by
  classical
  have hVH : (A.map ι : Set (ModGL .E8 L)) ⊆ torusGroup .E8 L := by
    rintro y ⟨x, hx, rfl⟩
    exact hAJ x hx
  have hgN' : ι g ∈ Subgroup.normalizer (A.map ι : Set (ModGL .E8 L)) :=
    Subgroup.le_normalizer_map (H := A) ι (Subgroup.mem_map_of_mem ι hgN)
  have hg : ι g ∈ adjointGroup .E8 L ⊓ Subgroup.normalizer (A.map ι : Set (ModGL .E8 L)) :=
    Subgroup.mem_inf.mpr ⟨hι ⟨g, rfl⟩, hgN'⟩
  obtain ⟨v, hv⟩ :=
    CFSG.RankThree.PartOne.K133H.exists_conj_eq_canonicalRep_of_mem_normalizer
      (V := (A.map ι : Set (ModGL .E8 L))) hVH hg
  refine ⟨v, ?_, ?_⟩
  ·
    have hgs : g * s * g⁻¹ = s := by
      have hc := (Subgroup.mem_centralizer_iff.1 (hJ hgJ)) s (Set.mem_singleton s)
      rw [← hc]
      group
    have h1 : ι s =
        canonicalRep (coxeterSystem .E8) L v * ι s *
          (canonicalRep (coxeterSystem .E8) L v)⁻¹ := by
      have h := hv (ι s) (Subgroup.mem_map_of_mem ι hsA)
      calc
        ι s = ι (g * s * g⁻¹) := by rw [hgs]
        _ = ι g * ι s * (ι g)⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = _ := h
    have hconj : rootDiagUnit .E8 a * canonicalRep (coxeterSystem .E8) L v *
        (rootDiagUnit .E8 a)⁻¹ = canonicalRep (coxeterSystem .E8) L v := by
      rw [← hs]
      calc
        ι s * canonicalRep (coxeterSystem .E8) L v * (ι s)⁻¹ =
            (canonicalRep (coxeterSystem .E8) L v * ι s *
              (canonicalRep (coxeterSystem .E8) L v)⁻¹) *
              canonicalRep (coxeterSystem .E8) L v * (ι s)⁻¹ := by
          nth_rewrite 1 [h1]
          rfl
        _ = canonicalRep (coxeterSystem .E8) L v := by group
    have hstab : v ∈ rootCharStabilizerSubgroup a :=
      (conj_canonicalRep_eq_iff a v).1 hconj
    have hker : v ∈ kernelReflectionGroup a := by
      rwa [CFSG.HardMathSupport.Timmesfeld.Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_three a h3] at hstab
    rwa [kernelReflectionGroup_eq_kernelWeylGroup_rootCharHom a] at hker
  · intro x hx
    calc
      ι (g * x * g⁻¹) = ι g * ι x * (ι g)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = _ := hv (ι x) (Subgroup.mem_map_of_mem ι hx)

namespace MaxRankE8Label

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType
open CFSG.StandardType.TableCRes
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag)

private theorem componentLabel_tag_ne_B {r N e : ℕ} {k : TwistKind} :
    (componentLabel r N k e).tag ≠ .B := by
  cases k <;> unfold componentLabel <;> split_ifs <;> simp

private theorem componentLabel_tag_ne_C {r N e : ℕ} {k : TwistKind} :
    (componentLabel r N k e).tag ≠ .C := by
  cases k <;> unfold componentLabel <;> split_ifs <;> simp

private theorem componentLabel_eq_A_imp {r N e n : ℕ} {k : TwistKind}
    (h : componentLabel r N k e = (⟨.A, 8, n⟩ : LargeEvenLabel)) :
    r = 8 ∧ N = 72 := by
  cases k with
  | inner =>
    dsimp only [componentLabel] at h
    by_cases hN : N = r * (r + 1)
    · rw [if_pos hN] at h
      cases h
      exact ⟨rfl, by omega⟩
    · rw [if_neg hN] at h
      by_cases hD : N = 2 * r * (r - 1)
      · rw [if_pos hD] at h
        cases h
      · rw [if_neg hD] at h
        by_cases h6 : r = 6
        · rw [if_pos h6] at h
          cases h
        · rw [if_neg h6] at h
          by_cases h7 : r = 7
          · rw [if_pos h7] at h
            cases h
          · rw [if_neg h7] at h
            cases h
  | suN =>
    dsimp only [componentLabel] at h
    cases h
  | twoD =>
    dsimp only [componentLabel] at h
    cases h
  | exc =>
    dsimp only [componentLabel] at h
    split_ifs at h <;> cases h

private theorem componentLabel_eq_twA_imp {r N e n : ℕ} {k : TwistKind}
    (h : componentLabel r N k e = (⟨.twA, 8, n⟩ : LargeEvenLabel)) :
    r = 8 ∧ k = .suN := by
  cases k with
  | inner =>
    dsimp only [componentLabel] at h
    split_ifs at h <;> cases h
  | suN =>
    dsimp only [componentLabel] at h
    cases h
    exact ⟨rfl, rfl⟩
  | twoD =>
    dsimp only [componentLabel] at h
    cases h
  | exc =>
    dsimp only [componentLabel] at h
    split_ifs at h <;> cases h

private theorem twistKindOf_eq_suN_imp {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (Ψ : Set (Fin τ.rank → ℤ)) (h : twistKindOf ρ Ψ = .suN) :
    2 ≤ compRank Ψ ∧ Ψ.ncard = compRank Ψ * (compRank Ψ + 1) := by
  unfold twistKindOf at h
  by_cases h1 : twistInner Ψ
      ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ Ψ])
  · rw [if_pos h1] at h
    cases h
  · rw [if_neg h1] at h
    by_cases h2 : (compRank Ψ = 6 ∧ Ψ.ncard = 72) ∨
        (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧
          ¬ twistInner Ψ
            ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[2 * componentOrbitLength ρ Ψ]))
    · rw [if_pos h2] at h
      cases h
    · rw [if_neg h2] at h
      by_cases h3 : 4 ≤ compRank Ψ ∧ Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1)
      · rw [if_pos h3] at h
        cases h
      · rw [if_neg h3] at h
        by_cases h4 : 2 ≤ compRank Ψ ∧ Ψ.ncard = compRank Ψ * (compRank Ψ + 1)
        · rw [if_pos h4] at h
          exact h4
        · rw [if_neg h4] at h
          cases h

private theorem labelIso_A_eq {r N e n : ℕ} {k : TwistKind}
    (h : GGLabelIso (componentLabel r N k e) (⟨.A, 8, n⟩ : LargeEvenLabel)) :
    componentLabel r N k e = ⟨.A, 8, n⟩ := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h.1 with hB | hC
    · exact (componentLabel_tag_ne_B hB).elim
    · exact (componentLabel_tag_ne_C hC).elim
  · have hr := congrArg LargeEvenLabel.rank h.2
    simp at hr
  · have htag := congrArg LargeEvenLabel.tag h.2
    cases htag
  · have htag := congrArg LargeEvenLabel.tag h.2
    cases htag
  · have htag := congrArg LargeEvenLabel.tag h.2
    cases htag
  · have hr := congrArg LargeEvenLabel.rank h.2
    simp at hr
  · have htag := congrArg LargeEvenLabel.tag h.1
    cases htag

private theorem labelIso_twA_eq {r N e n : ℕ} {k : TwistKind}
    (h : GGLabelIso (componentLabel r N k e) (⟨.twA, 8, n⟩ : LargeEvenLabel)) :
    componentLabel r N k e = ⟨.twA, 8, n⟩ := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h.1 with hB | hC
    · exact (componentLabel_tag_ne_B hB).elim
    · exact (componentLabel_tag_ne_C hC).elim
  · have htag := congrArg LargeEvenLabel.tag h.2
    cases htag
  · have htag := congrArg LargeEvenLabel.tag h.2
    cases htag
  · have hr := congrArg LargeEvenLabel.rank h.2
    simp at hr
  · have htag := congrArg LargeEvenLabel.tag h.2
    cases htag
  · have htag := congrArg LargeEvenLabel.tag h.2
    cases htag
  · have htag := congrArg LargeEvenLabel.tag h.1
    cases htag

private theorem LabAt_eq_A_imp {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {f n : ℕ}
    {Ψ : Set (Fin τ.rank → ℤ)}
    (h : GGLabelIso (LabAt ρ f Ψ) (⟨.A, 8, n⟩ : LargeEvenLabel)) :
    compRank Ψ = 8 ∧ Ψ.ncard = 72 := by
  have h' : GGLabelIso
      (componentLabel (compRank Ψ) Ψ.ncard (twistKindOf ρ Ψ)
        (componentOrbitLength ρ Ψ * f)) (⟨.A, 8, n⟩ : LargeEvenLabel) := by
    simpa only [LabAt] using h
  exact componentLabel_eq_A_imp (labelIso_A_eq h')

private theorem LabAt_eq_twA_imp {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {f n : ℕ}
    {Ψ : Set (Fin τ.rank → ℤ)}
    (h : GGLabelIso (LabAt ρ f Ψ) (⟨.twA, 8, n⟩ : LargeEvenLabel)) :
    compRank Ψ = 8 ∧ Ψ.ncard = 72 := by
  have h' : GGLabelIso
      (componentLabel (compRank Ψ) Ψ.ncard (twistKindOf ρ Ψ)
        (componentOrbitLength ρ Ψ * f)) (⟨.twA, 8, n⟩ : LargeEvenLabel) := by
    simpa only [LabAt] using h
  obtain ⟨hr, hk⟩ := componentLabel_eq_twA_imp (labelIso_twA_eq h')
  have hshape := twistKindOf_eq_suN_imp ρ Ψ hk
  exact ⟨hr, by rw [hshape.2, hr]⟩

section Main

theorem compRank_eq_eight_ncard_eq_72_of_label
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup .E8 L p₀)
    {a : Fin Tag.E8.rank → Lˣ}
    (hT : rootDiagUnit .E8 a ∈ S.D.torus)
    (h3 : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit .E8 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {n : ℕ} (hn : 1 ≤ n)
    (hLab : GGHasLabel (⟨.A, 8, n⟩ : LargeEvenLabel)
        (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∨
      GGHasLabel (⟨.twA, 8, n⟩ : LargeEvenLabel)
        (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    compRank (componentRoots (rootCharHom a) i) = 8 ∧
      (componentRoots (rootCharHom a) i).ncard = 72 ∧
      kernelRoots (rootCharHom a) = componentRoots (rootCharHom a) i := by
  classical
  let a' : PUnit.{1} → Fin Tag.E8.rank → Lˣ := fun _ => a
  have hT' : ∀ u, rootDiagUnit .E8 (a' u) ∈ S.D.torus := fun _ => hT
  have hap' : ∀ u j, a' u j ^ 3 = 1 := fun _ j => h3 j
  have hrange : (Set.range fun u : PUnit.{1} => rootDiagUnit .E8 (a' u)) =
      {rootDiagUnit .E8 a} := by
    ext z
    simp [a']
  have hK : CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (S.Γ ⊓ Subgroup.centralizer
        (Set.range fun u : PUnit.{1} => rootDiagUnit .E8 (a' u))) := by
    rw [hrange]
    exact CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.isComponentOf_rationalComponent
      S hT i hQS
  obtain ⟨i', hi'⟩ := exists_componentRoots_eq (kernelRoots_famChar_punit_eq a).symm i
  have hspan : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan .E8 L (famOrbit S.ρ a' i') := by
    have hforb : famOrbit S.ρ a' i' = rationalRoots S.ρ (rootCharHom a) i := by
      ext γ
      simp only [famOrbit, rationalRoots, Set.mem_setOf_eq]
      rw [hi']
    rw [hforb]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  obtain ⟨f, -, hfq⟩ := CFSG.HardMathSupport.Dickson.Sec6.ssTw_exists_f S (ℓ := 2)
  have hlab := tc_langLabel (p := 3) langFamilyCompLabel_holds (Or.inr rfl) S
    (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2) hfq a' hT' hap' hK i' hspan
  have hlab' : GGCompLabelAt (LabAt S.ρ f (componentRoots (rootCharHom a) i))
      (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    rw [hi']
    exact hlab
  have hnA : LargeEvenInLambda2 (⟨.A, 8, n⟩ : LargeEvenLabel) := by
    simp [LargeEvenInLambda2, hn]
  have hntwA : LargeEvenInLambda2 (⟨.twA, 8, n⟩ : LargeEvenLabel) := by
    simp [LargeEvenInLambda2, hn]
  have hiso : GGLabelIso (LabAt S.ρ f (componentRoots (rootCharHom a) i))
        (⟨.A, 8, n⟩ : LargeEvenLabel) ∨
      GGLabelIso (LabAt S.ρ f (componentRoots (rootCharHom a) i))
        (⟨.twA, 8, n⟩ : LargeEvenLabel) := by
    rcases hLab with hA | htA
    · exact Or.inl (ggLabelRigidInput_holds _ _ _ hlab'.1 hnA hlab'.2.2.1 hA)
    · exact Or.inr (ggLabelRigidInput_holds _ _ _ hlab'.1 hntwA hlab'.2.2.1 htA)
  have hrN : compRank (componentRoots (rootCharHom a) i) = 8 ∧
      (componentRoots (rootCharHom a) i).ncard = 72 := by
    rcases hiso with hiso | hiso
    · exact LabAt_eq_A_imp hiso
    · exact LabAt_eq_twA_imp hiso
  refine ⟨hrN.1, hrN.2, ?_⟩
  apply Set.Subset.antisymm
  · intro β hβ
    have hrat : β ∈ ratClosure (componentRoots (rootCharHom a) i) := by
      rw [ratClosure_eq_of_compRank_eq (τ := .E8) hrN.1]
      exact hβ.1
    exact mem_componentRoots_of_mem_ratClosure hrat hβ
  · intro β hβ
    exact hβ.1

end Main

end MaxRankE8Label

namespace MaxRankE8FixedCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.StandardType.LangRat
open scoped MatrixGroups

theorem frame_ker_ne_top {τ : Tag} {L : Type} [Field L] {ν : ℕ} (hν : 2 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) : ψ.ker ≠ ⊤ := by
  intro htop
  have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
  obtain ⟨ε, hε⟩ := hψ.transv _ _ h01
  have hmem : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [MonoidHom.mem_ker, hε, mul_one, ← pinnedX_zero τ L (σ _ _)] at hmem
  exact Units.ne_zero ε (pinnedX_injective τ L (σ _ _) hmem)

theorem odd_card_ker_of_frame {τ : Tag} {L : Type} [Field L] [CharP L 2] {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hker : ψ.ker ≠ ⊤) : Odd (Nat.card ψ.ker) := by
  have hle : ψ.ker ≤ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hker (fun Y => ?_)
    rw [MonoidHom.mem_ker.mp hX, one_mul, mul_one]
  exact Odd.of_dvd_nat
    (finite_odd_card_center_specialLinearGroup (Ω := L) (n := ν) (by omega)).2
    (Subgroup.card_dvd_of_le hle)

theorem map_eqLocus_le_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom a) i = frameRoots σ)
    (hkercenter : ψ.ker ≤ Subgroup.center SL(ν, L)) (hodd : Odd (Nat.card ψ.ker))
    (F' : SL(ν, L) →* SL(ν, L)) (hcomm : ∀ X, S.D.step (ψ X) = ψ (F' X))
    (hperf : Group.IsPerfect (F'.eqLocus (MonoidHom.id _)))
    {g : ModGL τ L} (hg : g ∈ rootSpan τ L (frameRoots σ))
    (hgfix : S.D.step g = g) (hg2 : g ^ 2 = 1) :
    g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  have hgRange : g ∈ ψ.range := by rw [hψ.range]; exact hg
  obtain ⟨y, hyψ, hy2⟩ := CFSG.Alternating.Multipliers.exists_lift_sq_eq_one hkercenter hodd hgRange hg2
  have hyΦ : F' y = y := by
    refine CFSG.Alternating.Multipliers.eq_of_sq_eq_one (f := ψ) hkercenter hodd ?_ ?_ ?_
    · rw [← hcomm y]
      simpa [hyψ] using hgfix
    · rw [← map_pow, hy2, map_one]
    · exact hy2
  set C : Subgroup (SL(ν, L)) := F'.eqLocus (MonoidHom.id _) with hC
  have hyC : y ∈ C := hyΦ
  have hCmodel : ∀ c : C, ψ (c : SL(ν, L)) ∈ S.D.model := by
    intro c
    have h1 : ψ (c : SL(ν, L)) ∈ adjointGroup τ L :=
      hψ.range_le_adjointGroup ⟨c, rfl⟩
    have h2 : S.D.n * S.D.Φ (ψ (c : SL(ν, L))) * S.D.n⁻¹ = ψ (c : SL(ν, L)) := by
      change S.D.step (ψ (c : SL(ν, L))) = ψ (c : SL(ν, L))
      rw [hcomm]
      exact congrArg ψ c.2
    exact S.D.mem_model.mpr ⟨h1, h2⟩
  have hCΓ : ∀ c : C, ψ (c : SL(ν, L)) ∈ S.Γ :=
    map_mem_commutator_of_perfect hperf (ψ.comp C.subtype) S.D.model hCmodel
  have hCspan : ∀ c : C, ψ (c : SL(ν, L)) ∈
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    intro c
    refine rootSpan_mono (S := frameRoots σ) ?_ ?_
    · intro γ hγ
      rw [← hΨ] at hγ
      exact ⟨0, γ, hγ, by simp⟩
    · rw [← hψ.range]
      exact ⟨c, rfl⟩
  have hCrat : ∀ c : C, ψ (c : SL(ν, L)) ∈
      rationalSpan S.ρ S.Γ (rootCharHom a) i := fun c =>
    Subgroup.mem_inf.2 ⟨hCspan c, hCΓ c⟩
  have hgmem : ψ y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    map_mem_commutator_of_perfect hperf (ψ.comp C.subtype)
      (rationalSpan S.ρ S.Γ (rootCharHom a) i) hCrat ⟨y, hyC⟩
  simpa [rationalComponent, MonoidHom.comp_apply, hyψ] using hgmem

theorem exists_split_source_perfect
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π x) (π y))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {k' : Type} [Field k'] [Finite k'] [Algebra k' L] [IsAlgClosure k' L]
    {r e : ℕ} (hr : r.Prime) [CharP L r] (he : 0 < e) (hq : S.D.q = r ^ e) :
    ∃ F' : SL(ν, L) →* SL(ν, L),
      (∀ X, S.D.step (ψ X) = ψ (F' X)) ∧
        Group.IsPerfect (F'.eqLocus (MonoidHom.id _)) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r e
  have hσc : ∀ c, σQ c = c ^ (r ^ e) := fun c => by
    have h1 : σQ c = iterateFrobenius L r e c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  have hσc' : ∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i))) := by
    intro c
    rw [hs1, Nat.mul_one]
    exact hσc c
  obtain ⟨B, hstd⟩ := split_exists_pin (S := S) hν hψ π hπ hq hσc'
  have hstd1 : ∀ X : SL(ν, L),
      ψ B * S.D.step (ψ X) * (ψ B)⁻¹ = ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) := by
    intro X
    have h := hstd X
    rw [hs1] at h
    simpa [iterHom_eq_iterate] using h
  have hB : ∀ X : SL(ν, L),
      S.D.step (ψ X) = ψ (B⁻¹ * Matrix.SpecialLinearGroup.map σQ.toRingHom X * B) := by
    intro X
    calc S.D.step (ψ X)
        = (ψ B)⁻¹ * (ψ B * S.D.step (ψ X) * (ψ B)⁻¹) * ψ B := by group
      _ = (ψ B)⁻¹ * ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) * ψ B := by
            rw [hstd1 X]
      _ = ψ (B⁻¹ * Matrix.SpecialLinearGroup.map σQ.toRingHom X * B) := by
            rw [map_mul, map_mul, map_inv]
  let A : GL (Fin ν) L := Matrix.SpecialLinearGroup.toGL B⁻¹
  let F' : SL(ν, L) →* SL(ν, L) :=
    (conjSLn A).comp (Matrix.SpecialLinearGroup.map σQ.toRingHom)
  have hF' : ∀ X, F' X = B⁻¹ * Matrix.SpecialLinearGroup.map σQ.toRingHom X * B := by
    intro X
    change conjSLn (Matrix.SpecialLinearGroup.toGL B⁻¹)
      (Matrix.SpecialLinearGroup.map σQ.toRingHom X) =
        B⁻¹ * Matrix.SpecialLinearGroup.map σQ.toRingHom X * B
    rw [conjSLn_toGL]
    simp
  refine ⟨F', ?_, ?_⟩
  · intro X
    rw [hF' X]
    exact hB X
  · have hQ := isQuasisimple_eqLocus_conjSLn_frobenius_split (k' := k') (Ω := L)
      (n := ν) (ℓ := r) (f := e) hr he (by omega) (Or.inl (by omega)) σQ.toRingHom hσc A
    simpa [F'] using hQ.2.1

theorem exists_unitary_source_perfect
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {k' : Type} [Field k'] [Finite k'] [Algebra k' L] [IsAlgClosure k' L]
    {r e : ℕ} (hr : r.Prime) [CharP L r] (he : 0 < e) (hq : S.D.q = r ^ e)
    (hνq : (ν, r ^ e) ≠ (3, 2)) :
    ∃ F' : SL(ν, L) →* SL(ν, L),
      (∀ X, S.D.step (ψ X) = ψ (F' X)) ∧
        Group.IsPerfect (F'.eqLocus (MonoidHom.id _)) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r e
  have hσc : ∀ c, σQ c = c ^ (r ^ e) := fun c => by
    have h1 : σQ c = iterateFrobenius L r e c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  have hσc' : ∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i))) := by
    intro c
    rw [hs1, Nat.mul_one]
    exact hσc c
  obtain ⟨B, hstd⟩ := unitary_exists_pin (S := S) hν hψ π hπ hq hσc'
  have hstd1 : ∀ X : SL(ν, L),
      ψ B * S.D.step (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
    intro X
    have h := hstd X
    rw [hs1] at h
    simpa [iterHom_eq_iterate] using h
  have hB : ∀ X : SL(ν, L),
      S.D.step (ψ X) = ψ (B⁻¹ * stdUnitary σQ.toRingHom X * B) := by
    intro X
    calc S.D.step (ψ X)
        = (ψ B)⁻¹ * (ψ B * S.D.step (ψ X) * (ψ B)⁻¹) * ψ B := by group
      _ = (ψ B)⁻¹ * ψ (stdUnitary σQ.toRingHom X) * ψ B := by
            rw [hstd1 X]
      _ = ψ (B⁻¹ * stdUnitary σQ.toRingHom X * B) := by
            rw [map_mul, map_mul, map_inv]
  let A : GL (Fin ν) L := Matrix.SpecialLinearGroup.toGL B⁻¹
  let F' : SL(ν, L) →* SL(ν, L) :=
    (conjSLn A).comp (invTransposeSL.comp (Matrix.SpecialLinearGroup.map σQ.toRingHom))
  have hF' : ∀ X, F' X = B⁻¹ * stdUnitary σQ.toRingHom X * B := by
    intro X
    change conjSLn (Matrix.SpecialLinearGroup.toGL B⁻¹) (stdUnitary σQ.toRingHom X) =
      B⁻¹ * stdUnitary σQ.toRingHom X * B
    rw [conjSLn_toGL]
    simp
  refine ⟨F', ?_, ?_⟩
  · intro X
    rw [hF' X]
    exact hB X
  · have hQ := isQuasisimple_eqLocus_conjSLn_frobenius_unitary (k' := k') (Ω := L)
      (n := ν) (ℓ := r) (f := e) hr he hν hνq σQ.toRingHom hσc A
    simpa [F'] using hQ.2.1

theorem rootSL2_WSL_mem_rationalComponent_of_split_frame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π x) (π y))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {k' : Type} [Field k'] [Finite k'] [Algebra k' L] [IsAlgClosure k' L]
    {n : ℕ} (hn : 0 < n) (hq : S.D.q = 2 ^ n)
    {α : Fin τ.rank → ℤ} (hα : α ∈ frameRoots σ)
    (hρα : S.ρ α = α ∨ S.ρ α = -α) :
    rootSL2 τ L α WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  obtain ⟨F', hcomm, hperf⟩ :=
    exists_split_source_perfect (S := S) (i := i) (hν := hν) (hψ := hψ) (π := π)
      (hπ := hπ) (hs1 := hs1) (k' := k') (r := 2) (e := n) Nat.prime_two hn hq
  have hkerproper : ψ.ker ≠ ⊤ := frame_ker_ne_top (τ := τ) (L := L) (ν := ν) (by omega) hψ
  have hkercenter : ψ.ker ≤ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hkerproper (fun Y => ?_)
    rw [MonoidHom.mem_ker.mp hX, one_mul, mul_one]
  have hodd : Odd (Nat.card ψ.ker) :=
    odd_card_ker_of_frame (hν := hν) hψ hkerproper
  set g : ModGL τ L := rootSL2 τ L α WSL with hg
  have hαroot : IsRoot τ α := hψ.frameRoots_isRoot α hα
  have hgframe : g ∈ rootSpan τ L (frameRoots σ) := by
    refine rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (L := L) hαroot WSL)
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact hα
    · obtain ⟨x, y, hxy, rfl⟩ := hα
      exact ⟨y, x, hxy.symm, (hψ.neg x y).symm⟩
  have hmodel := rootSL2_WSL_mem_model_of_rho S hαroot hρα
  have hgfix : S.D.step g = g := (S.D.mem_model.mp hmodel).2
  have hg2 : g ^ 2 = 1 := by
    rw [pow_two]
    exact rootSL2_WSL_mul_self (L := L) α
  exact map_eqLocus_le_rationalComponent S i hψ hΨ hkercenter hodd F' hcomm hperf
    hgframe hgfix hg2

theorem rootSL2_WSL_mem_rationalComponent_of_unitary_frame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {k' : Type} [Field k'] [Finite k'] [Algebra k' L] [IsAlgClosure k' L]
    {n : ℕ} (hn : 0 < n) (hq : S.D.q = 2 ^ n)
    (hνq : (ν, 2 ^ n) ≠ (3, 2))
    {α : Fin τ.rank → ℤ} (hα : α ∈ frameRoots σ)
    (hρα : S.ρ α = α ∨ S.ρ α = -α) :
    rootSL2 τ L α WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  obtain ⟨F', hcomm, hperf⟩ :=
    exists_unitary_source_perfect (S := S) (i := i) (hν := hν) (hψ := hψ) (π := π)
      (hπ := hπ) (hs1 := hs1) (k' := k') (r := 2) (e := n) Nat.prime_two hn hq hνq
  have hkerproper : ψ.ker ≠ ⊤ := frame_ker_ne_top (τ := τ) (L := L) (ν := ν) (by omega) hψ
  have hkercenter : ψ.ker ≤ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hkerproper (fun Y => ?_)
    rw [MonoidHom.mem_ker.mp hX, one_mul, mul_one]
  have hodd : Odd (Nat.card ψ.ker) :=
    odd_card_ker_of_frame (hν := hν) hψ hkerproper
  set g : ModGL τ L := rootSL2 τ L α WSL with hg
  have hαroot : IsRoot τ α := hψ.frameRoots_isRoot α hα
  have hgframe : g ∈ rootSpan τ L (frameRoots σ) := by
    refine rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (L := L) hαroot WSL)
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact hα
    · obtain ⟨x, y, hxy, rfl⟩ := hα
      exact ⟨y, x, hxy.symm, (hψ.neg x y).symm⟩
  have hmodel := rootSL2_WSL_mem_model_of_rho S hαroot hρα
  have hgfix : S.D.step g = g := (S.D.mem_model.mp hmodel).2
  have hg2 : g ^ 2 = 1 := by
    rw [pow_two]
    exact rootSL2_WSL_mul_self (L := L) α
  exact map_eqLocus_le_rationalComponent S i hψ hΨ hkercenter hodd F' hcomm hperf
    hgframe hgfix hg2

end MaxRankE8FixedCover

namespace MaxRankE8Weyl

open CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Permutation.SymmetricCoxeter
open scoped MatrixGroups

variable
  {L : Type} [Field L] {ψ : SL(9, L) →* ModGL .E8 L}
  {σ : Fin 9 → Fin 9 → Fin Tag.E8.rank → ℤ}

private theorem e8_symmetrizer_self (i : Fin Tag.E8.rank) :
    (Tag.symmetrizer .E8) i i = 1 := by
  simp [Tag.symmetrizer]

private theorem e8_iform_self {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot .E8 β) :
    iform β β = 2 :=
  SimplyLacedCover.iform_self_eq_two e8_symmetrizer_self hβ

private theorem frame_iform_self (hψ : IsSLFrame ψ σ) {a b : Fin 9} (hab : a ≠ b) :
    iform (σ a b) (σ a b) = 2 :=
  e8_iform_self (hψ.isRoot a b hab)

private theorem frame_iform_adj (hψ : IsSLFrame ψ σ) (i j : Fin 8)
    (hij : (j : ℕ) = (i : ℕ) + 1) :
    iform (σ i.castSucc i.succ) (σ j.castSucc j.succ) = -1 := by
  have hnorm : ∀ a b : Fin 9, a ≠ b → iform (σ a b) (σ a b) = 2 * (1 : ℤ) := by
    intro a b hab
    rw [frame_iform_self hψ hab]
    norm_num
  have hcast : j.castSucc = i.succ := Fin.ext (by simp [hij])
  rw [hcast]
  rw [hψ.iform_eq hnorm i.castSucc i.succ i.succ j.succ]
  simp [framePairForm, Fin.ext_iff]
  omega

private theorem frame_iform_orth (hψ : IsSLFrame ψ σ) {i j : Fin 8}
    (hij : (i : ℕ) + 2 ≤ j) :
    iform (σ i.castSucc i.succ) (σ j.castSucc j.succ) = 0 := by
  have hnorm : ∀ a b : Fin 9, a ≠ b → iform (σ a b) (σ a b) = 2 * (1 : ℤ) := by
    intro a b hab
    rw [frame_iform_self hψ hab]
    norm_num
  rw [hψ.iform_eq hnorm i.castSucc i.succ j.castSucc j.succ]
  simp [framePairForm, Fin.ext_iff]
  omega

private theorem isAChain_beta (hψ : IsSLFrame ψ σ) :
    IsAChain (fun i : Fin 8 => σ i.castSucc i.succ) where
  isRoot i := hψ.isRoot i.castSucc i.succ (Fin.castSucc_lt_succ.ne)
  adj i j hij := frame_iform_adj hψ i j hij
  orth i j hij := frame_iform_orth hψ hij

private theorem rootReflection_mem_closure_of_chain (hψ : IsSLFrame ψ σ) :
    ∀ a b : Fin 9, a ≠ b →
      rootReflection (σ a b) ∈
        Subgroup.closure (rootReflection ''
          Set.range (fun i : Fin 8 => σ i.castSucc i.succ)) := by
  let β : Fin 8 → Fin Tag.E8.rank → ℤ := fun i => σ i.castSucc i.succ
  let K : Subgroup (WeylGroup .E8) :=
    Subgroup.closure (rootReflection '' Set.range β)
  have hβmem : ∀ i : Fin 8, rootReflection (β i) ∈ K := fun i =>
    Subgroup.subset_closure ⟨β i, ⟨i, rfl⟩, rfl⟩
  have hnorm : ∀ a b : Fin 9, a ≠ b → iform (σ a b) (σ a b) = 2 * (1 : ℤ) := by
    intro a b hab
    rw [frame_iform_self hψ hab]
    norm_num
  have key : ∀ d : ℕ, ∀ a b : Fin 9, (b : ℕ) = (a : ℕ) + d + 1 →
      rootReflection (σ a b) ∈ K := by
    intro d
    induction d with
    | zero =>
        intro a b hb
        have ha : (a : ℕ) < 8 := by omega
        have hb' : b = (⟨a.val + 1, by omega⟩ : Fin 9) := Fin.ext (by simp [hb])
        have hβeq : β ⟨a.val, ha⟩ = σ a b := by
          unfold β
          rw [hb', show (⟨a.val, ha⟩ : Fin 8).castSucc = a from Fin.ext rfl]
          congr 1
        rw [← hβeq]
        exact hβmem _
    | succ d ih =>
        intro a b hb
        have ha8 : (a : ℕ) < 8 := by omega
        let c : Fin 9 := ⟨a.val + 1, by omega⟩
        have hac : a ≠ c := by
          intro h
          have := congrArg Fin.val h
          simp [c] at this
        have hcb : c ≠ b := by
          intro h
          have := congrArg Fin.val h
          simp [c] at this
          omega
        have hab : a ≠ b := by
          intro h
          have := congrArg Fin.val h
          omega
        have hdist : (b : ℕ) = (c : ℕ) + d + 1 := by
          simp [c]
          omega
        have hrec := ih c b hdist
        have hβeq : β ⟨a.val, ha8⟩ = σ a c := by
          unfold β
          rw [show (⟨a.val, ha8⟩ : Fin 8).castSucc = a from Fin.ext rfl]
          rfl
        have hiform : iform (σ a c) (σ c b) = -1 := by
          rw [hψ.iform_eq hnorm a c c b]
          simp [framePairForm, Fin.ext_iff]
          omega
        have hpair : IsA2Pair (σ a c) (σ c b) :=
          ⟨hψ.isRoot a c hac, hψ.isRoot c b hcb, by
            rw [hψ.add a c b]
            exact hψ.isRoot a b hab, by
            rw [frame_iform_self hψ hcb, frame_iform_self hψ hac], by
            rw [hiform, frame_iform_self hψ hac]
            norm_num⟩
        have hconj := hpair.rootReflection_fst_snd_fst
        rw [← hψ.add a c b, ← hconj]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _
          (by rw [← hβeq]; exact hβmem _) hrec) (by rw [← hβeq]; exact hβmem _)
  intro a b hab
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact key (b.val - a.val - 1) a b (by omega)
  · have hrec := key (a.val - b.val - 1) b a (by omega)
    rw [hψ.neg b a, rootReflection_neg (hψ.isRoot b a (by omega))]
    exact hrec

theorem closure_rootReflection_frameRoots_eq_adjacent (hψ : IsSLFrame ψ σ) :
    Subgroup.closure (rootReflection '' frameRoots σ) =
      Subgroup.closure (rootReflection ''
        Set.range (fun i : Fin 8 => σ i.castSucc i.succ)) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨x, ⟨a, b, hab, rfl⟩, rfl⟩
    exact rootReflection_mem_closure_of_chain hψ a b hab
  · rw [Subgroup.closure_le]
    rintro y ⟨x, ⟨i, rfl⟩, hxy⟩
    rw [← hxy]
    exact Subgroup.subset_closure ⟨(fun i : Fin 8 => σ i.castSucc i.succ) i,
      ⟨i.castSucc, i.succ, Fin.castSucc_lt_succ.ne, rfl⟩, rfl⟩

private theorem rootReflection_adj_ne {β : Fin 8 → Fin Tag.E8.rank → ℤ}
    (hβ : IsAChain β) {i j : Fin 8} (hij : (j : ℕ) = (i : ℕ) + 1) :
    rootReflection (β i) ≠ rootReflection (β j) := by
  intro h
  have h1 : rootReflection (β j) • β i = rootReflection (β i) • β i := by rw [h]
  have hnormj : iform (β j) (β j) = 2 := e8_iform_self (hβ.isRoot j)
  have hcp : corootPair (β j) (β i) = iform (β j) (β i) := by
    rw [corootPair, hnormj]
    omega
  rw [rootReflection_smul (hβ.isRoot j), hcp, iform_comm, hβ.adj i j hij,
    rootReflection_smul_self (hβ.isRoot i)] at h1
  have hβj : β j = (-2 : ℤ) • β i := by
    funext k
    have hk := congrFun h1 k
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at hk
    show β j k = -2 * β i k
    linarith
  have hcontr := (hβ.isRoot j).eq_one_or_neg_one_of_eq_smul hβj
  omega

private theorem rootReflection_orth_ne {β : Fin 8 → Fin Tag.E8.rank → ℤ}
    (hβ : IsAChain β) {i j : Fin 8} (hij : (i : ℕ) + 2 ≤ j) :
    rootReflection (β i) ≠ rootReflection (β j) := by
  intro h
  have h1 : rootReflection (β j) • β i = rootReflection (β i) • β i := by rw [h]
  have hzeroij : iform (β j) (β i) = 0 := by
    rw [iform_comm]
    exact hβ.orth i j hij
  rw [rootReflection_smul_of_iform_eq_zero (hβ.isRoot j) hzeroij,
    rootReflection_smul_self (hβ.isRoot i)] at h1
  have hzero : β i = 0 := by
    funext k
    have hk := congrFun h1 k
    simp only [Pi.neg_apply] at hk
    show β i k = 0
    linarith
  exact (hβ.isRoot i).ne_zero hzero

private theorem isCoxeterA_rootReflection_chain {β : Fin 8 → Fin Tag.E8.rank → ℤ}
    (hβ : IsAChain β) :
    IsCoxeterA 8 (fun i : ℕ => if h : i < 8 then rootReflection (β ⟨i, h⟩) else 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [dif_pos hi]
    exact rootReflection_mul_self (hβ.isRoot _)
  · intro i hi
    have hi' : i < 8 := by omega
    rw [dif_pos hi', dif_pos hi]
    have hA2 : IsA2Pair (β ⟨i, hi'⟩) (β ⟨i + 1, hi⟩) :=
      ⟨hβ.isRoot _, hβ.isRoot _, by
        exact SimplyLacedCover.isRoot_add e8_symmetrizer_self (hβ.isRoot _) (hβ.isRoot _)
          (hβ.adj _ _ rfl), by
        rw [e8_iform_self (hβ.isRoot _), e8_iform_self (hβ.isRoot _)], by
        rw [hβ.adj _ _ rfl, e8_iform_self (hβ.isRoot _)]
        norm_num⟩
    exact hA2.rootReflection_fst_snd_fst.trans hA2.rootReflection_snd_fst_snd.symm
  · intro i j hij hj
    have hi' : i < 8 := by omega
    rw [dif_pos hi', dif_pos hj]
    exact (rootReflection_commute (hβ.isRoot ⟨i, hi'⟩) (hβ.isRoot ⟨j, hj⟩)
      (hβ.orth ⟨i, hi'⟩ ⟨j, hj⟩ hij)).eq

theorem exists_coxeterA8_equiv_kernelWeylGroup
    (hψ : IsSLFrame ψ σ)
    {M : Type} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* M}
    (hker : kernelRoots χ = frameRoots σ) :
    ∃ e : (CoxeterMatrix.A 8).Group ≃* kernelWeylGroup χ,
      ∀ i : Fin 8,
        ((e ((CoxeterMatrix.A 8).simple i) : kernelWeylGroup χ) : WeylGroup .E8) =
          rootReflection (σ i.castSucc i.succ) := by
  let β : Fin 8 → Fin Tag.E8.rank → ℤ := fun i => σ i.castSucc i.succ
  let r : ℕ → WeylGroup .E8 :=
    fun i => if h : i < 8 then rootReflection (β ⟨i, h⟩) else 1
  have hβ : IsAChain β := isAChain_beta hψ
  have hcox : IsCoxeterA 8 r := isCoxeterA_rootReflection_chain hβ
  have h01 : r 0 ≠ r 1 := by
    change (if h : 0 < 8 then rootReflection (β ⟨0, h⟩) else 1) ≠
      (if h : 1 < 8 then rootReflection (β ⟨1, h⟩) else 1)
    rw [dif_pos (by norm_num : 0 < 8), dif_pos (by norm_num : 1 < 8)]
    exact rootReflection_adj_ne hβ (i := ⟨0, by norm_num⟩) (j := ⟨1, by norm_num⟩) rfl
  have h02 : r 0 ≠ r 2 := by
    change (if h : 0 < 8 then rootReflection (β ⟨0, h⟩) else 1) ≠
      (if h : 2 < 8 then rootReflection (β ⟨2, h⟩) else 1)
    rw [dif_pos (by norm_num : 0 < 8), dif_pos (by norm_num : 2 < 8)]
    exact rootReflection_orth_ne hβ (i := ⟨0, by norm_num⟩) (j := ⟨2, by norm_num⟩) (by norm_num)
  obtain ⟨eK, heK⟩ := CFSG.CGT.PushingUpLit.BHSSym.exists_mulEquiv_closure
    (n := 8) (by norm_num) (x := r) hcox h01 (fun _ => h02)
  have hrange : r '' Set.Iio 8 = rootReflection '' Set.range β := by
    ext w
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' : i < 8 := hi
      refine ⟨β ⟨i, hi'⟩, ⟨⟨i, hi'⟩, rfl⟩, ?_⟩
      change rootReflection (β ⟨i, hi'⟩) = r i
      simp only [r, dif_pos hi']
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      refine ⟨i.val, i.2, ?_⟩
      change r i.val = rootReflection (β i)
      simp only [r, dif_pos i.2]
  have hclosureFrame : Subgroup.closure (rootReflection '' Set.range β) =
      Subgroup.closure (rootReflection '' frameRoots σ) :=
    (closure_rootReflection_frameRoots_eq_adjacent hψ).symm
  have hclosure : Subgroup.closure (r '' Set.Iio 8) = kernelWeylGroup χ := by
    rw [hrange, hclosureFrame, kernelWeylGroup_eq_closure, hker]
  let eK' : Equiv.Perm (Fin 9) ≃* kernelWeylGroup χ :=
    eK.trans (MulEquiv.subgroupCongr hclosure)
  obtain ⟨eA, heA⟩ := CFSG.StandardType.ggCoxeterA_mulEquivPerm 8
  refine ⟨eA.trans eK', ?_⟩
  intro i
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, heA i]
  have hswap : adjSwap 8 (i : ℕ) = Equiv.swap i.castSucc i.succ := by
    rw [adjSwap_of_lt i.2]
    rfl
  have hval : ((eK (Equiv.swap i.castSucc i.succ) :
        ↥(Subgroup.closure (r '' Set.Iio 8))) : WeylGroup .E8) = r i.val := by
    rw [← hswap]
    exact heK i.val i.2
  change ((eK' (Equiv.swap i.castSucc i.succ) : kernelWeylGroup χ) : WeylGroup .E8) =
    rootReflection (σ i.castSucc i.succ)
  rw [show ((eK' (Equiv.swap i.castSucc i.succ) : kernelWeylGroup χ) : WeylGroup .E8) =
      ((eK (Equiv.swap i.castSucc i.succ) :
        ↥(Subgroup.closure (r '' Set.Iio 8))) : WeylGroup .E8) from rfl]
  rw [hval]
  simp only [r, dif_pos i.2]
  congr 1

end MaxRankE8Weyl

open CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

private theorem maxRankE8_exists_frame_nine
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E8 L p₀) {a : Fin Tag.E8.rank → Lˣ}
    (hL3 : (3 : L) ≠ 0) (h3 : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 8)
    (hn : (componentRoots (rootCharHom a) i).ncard = 72) :
    ∃ (ψ : SL(9, L) →* ModGL .E8 L) (σ : Fin 9 → Fin 9 → Fin Tag.E8.rank → ℤ),
      IsSLFrame ψ σ ∧ componentRoots (rootCharHom a) i = frameRoots σ := by
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S Nat.prime_three hL3
      (rootDiagUnit_pow_eq_one_of_forall h3) i (by omega) (by rw [hn, hr])
  have hcount : ν * (ν - 1) = 72 := by
    rw [← kd147c_frameRoots_ncard hψ hκ hnorm, ← hΨ, hn]
  have hν9 : ν = 9 := by
    have hsub : ν - 1 + 1 = ν := by omega
    by_cases hle : ν ≤ 9
    · by_cases hlt : ν ≤ 8
      · nlinarith
      · omega
    · have hge : 10 ≤ ν := by omega
      nlinarith
  subst ν
  exact ⟨ψ, σ, hψ, hΨ⟩

theorem ggMaxRankE8_exists_actual_frame_nine
    (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (hK : Nat.card K = 2 ^ n)
    (A J : Subgroup (adjointGroup .E8 K)) (s : adjointGroup .E8 K)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : 3 ^ 8 ≤ Nat.card A)
    (hsA : s ∈ A) (hs1 : s ≠ 1)
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({s} : Set (adjointGroup .E8 K))))
    (hLab : GGHasLabel ⟨.A, 8, n⟩ (↥J ⧸ Subgroup.center ↥J) ∨
      GGHasLabel ⟨.twA, 8, n⟩ (↥J ⧸ Subgroup.center ↥J)) :
    ∃ (S : LangSetup .E8 (AlgebraicClosure K) 5)
      (ι : adjointGroup .E8 K →* ModGL .E8 (AlgebraicClosure K))
      (a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
      (i : KernelComponent (rootCharHom a))
      (ψ : SL(9, AlgebraicClosure K) →* ModGL .E8 (AlgebraicClosure K))
      (σ : Fin 9 → Fin 9 → Fin Tag.E8.rank → ℤ),
      S.D.q = 2 ^ n ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ y, y ∈ A.map ι ↔ y ∈ S.D.torus ∧ y ^ 3 = 1) ∧
      ι s = rootDiagUnit .E8 a ∧
      J.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      IsSLFrame ψ σ ∧ componentRoots (rootCharHom a) i = frameRoots σ ∧
      kernelRoots (rootCharHom a) = frameRoots σ ∧
      ((∀ γ, IsRoot .E8 γ → S.ρ γ = γ) ∨
        (∀ γ, IsRoot .E8 γ → S.ρ γ = -γ)) := by
  classical
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨S, Fr, ι, w, a, hFr, hΦ, hq, hn, hsign1, hsign2, hι,
      hrange, hconj, hAimage, hs, ha3, i, hqs, hJi⟩ :=
    ggMaxRankE8_exists_actual_rationalComponent K n hK A J s hA hcard hsA hs1 hJ
  have hT : rootDiagUnit .E8 a ∈ S.D.torus := by
    rw [← hs]
    exact ((hAimage (ι s)).mp (Subgroup.mem_map_of_mem ι hsA)).1
  have h1 : rootDiagUnit .E8 a ≠ 1 := by
    rw [← hs]
    intro h
    exact hs1 (hι (h.trans (map_one ι).symm))
  have hn1 : 1 ≤ n := by
    haveI : Fintype K := Fintype.ofFinite K
    have ht : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hK, hn0] at ht
    norm_num at ht
  let eJ := (J.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hJi)
  have hLab' : GGHasLabel ⟨.A, 8, n⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∨
      GGHasLabel ⟨.twA, 8, n⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
    rcases hLab with h | h
    · exact Or.inl (ggHasLabel_quotCenter_of_mulEquiv eJ h)
    · exact Or.inr (ggHasLabel_quotCenter_of_mulEquiv eJ h)
  obtain ⟨hr, hN, hkernel⟩ :=
    MaxRankE8Label.compRank_eq_eight_ncard_eq_72_of_label
      S hT ha3 h1 i hqs hn1 hLab'
  have hL3 : (3 : AlgebraicClosure K) ≠ 0 := by
    have hthree : (3 : AlgebraicClosure K) = 1 := by
      have htwo := CharP.cast_eq_zero (AlgebraicClosure K) 2
      linear_combination htwo
    rw [hthree]
    exact one_ne_zero
  obtain ⟨ψ, σ, hψ, hΨ⟩ := maxRankE8_exists_frame_nine S hL3 ha3 i hr hN
  have hmod : (2 ^ n : ℕ) % 3 = 1 ∨ (2 ^ n : ℕ) % 3 = 2 := by
    have hnot : ¬ 3 ∣ 2 ^ n := fun h => by
      have h32 := Nat.prime_three.dvd_of_dvd_pow h
      norm_num at h32
    have hnot0 : (2 ^ n : ℕ) % 3 ≠ 0 := by
      simpa [Nat.dvd_iff_mod_eq_zero] using hnot
    have hlt := Nat.mod_lt (2 ^ n) (by norm_num : 0 < 3)
    omega
  have hsign : (∀ γ, IsRoot .E8 γ → S.ρ γ = γ) ∨
      (∀ γ, IsRoot .E8 γ → S.ρ γ = -γ) := by
    rcases hmod with hplus | hminus
    · have hd : 3 ∣ 2 ^ n - 1 := by
        have hmodeq : 1 ≡ 2 ^ n [MOD 3] := by
          show 1 % 3 = (2 ^ n) % 3
          norm_num [hplus]
        exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmodeq
      have hw := hsign1 hd
      left
      intro γ hγ
      rw [S.rho_eq_smul_of_frob (fun c => by rw [hq]; exact hFr c) hΦ hn hγ, hw]
      simp
    · have hd : 3 ∣ 2 ^ n + 1 := by
        rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
        simp [hminus]
      right
      intro γ hγ
      rw [S.rho_eq_smul_of_frob (fun c => by rw [hq]; exact hFr c) hΦ hn hγ]
      exact hsign2 hd γ
  exact ⟨S, ι, a, i, ψ, σ, hq, hι, hrange, hAimage, hs, hJi, hψ, hΨ,
    hkernel.trans hΨ, hsign⟩
theorem ggMaxRankE8_exists_actual_frame_involutions
    (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (hK : Nat.card K = 2 ^ n)
    (A J : Subgroup (adjointGroup .E8 K)) (s : adjointGroup .E8 K)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : 3 ^ 8 ≤ Nat.card A)
    (hsA : s ∈ A) (hs1 : s ≠ 1)
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({s} : Set (adjointGroup .E8 K))))
    (hLab : GGHasLabel ⟨.A, 8, n⟩ (↥J ⧸ Subgroup.center ↥J) ∨
      GGHasLabel ⟨.twA, 8, n⟩ (↥J ⧸ Subgroup.center ↥J)) :
    ∃ (S : LangSetup .E8 (AlgebraicClosure K) 5)
      (ι : adjointGroup .E8 K →* ModGL .E8 (AlgebraicClosure K))
      (a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
      (i : KernelComponent (rootCharHom a))
      (ψ : SL(9, AlgebraicClosure K) →* ModGL .E8 (AlgebraicClosure K))
      (σ : Fin 9 → Fin 9 → Fin Tag.E8.rank → ℤ),
      S.D.q = 2 ^ n ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ y, y ∈ A.map ι ↔ y ∈ S.D.torus ∧ y ^ 3 = 1) ∧
      ι s = rootDiagUnit .E8 a ∧
      J.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      IsSLFrame ψ σ ∧ componentRoots (rootCharHom a) i = frameRoots σ ∧
      kernelRoots (rootCharHom a) = frameRoots σ ∧
      (∀ α ∈ frameRoots σ, rootSL2 .E8 (AlgebraicClosure K) α WSL ∈ J.map ι) := by
  classical
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨S, ι, a, i, ψ, σ, hq, hι, hrange, hAimage, hs, hJi, hψ, hΨ, hkernel, hsign⟩ :=
    ggMaxRankE8_exists_actual_frame_nine K n hK A J s hA hcard hsA hs1 hJ hLab
  have hn1 : 0 < n := by
    have ht : 1 < Nat.card K := by
      haveI : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    by_contra h
    have h0 : n = 0 := by omega
    rw [hK, h0] at ht
    norm_num at ht
  have hfinite : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot .E8).subset fun α hα => hα.1.1
  have hstable : ∀ α ∈ componentRoots (rootCharHom a) i,
      S.ρ α ∈ componentRoots (rootCharHom a) i := by
    intro α hα
    rcases hsign with hp | hm
    · rw [hp α hα.1.1]
      exact hα
    · rw [hm α hα.1.1]
      exact (isRootComponent_componentRoots i).neg_mem α hα
  have horbit : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one hfinite hstable
  refine ⟨S, ι, a, i, ψ, σ, hq, hι, hrange, hAimage, hs, hJi, hψ, hΨ, hkernel, ?_⟩
  intro α hα
  rw [hJi]
  rcases hsign with hp | hm
  · have hπ : ∀ x y : Fin 9, x ≠ y →
        (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)] (σ x y) = σ ((1 : Equiv.Perm (Fin 9)) x) ((1 : Equiv.Perm (Fin 9)) y) := by
      intro x y hxy
      rw [horbit, Function.iterate_one, hp _ (hψ.isRoot x y hxy)]
      rfl
    exact MaxRankE8FixedCover.rootSL2_WSL_mem_rationalComponent_of_split_frame
      (k' := K) S i (by norm_num) hψ hΨ 1 hπ horbit hn1 hq hα
      (Or.inl (hp α (hψ.frameRoots_isRoot α hα)))
  · have hπ : ∀ x y : Fin 9, x ≠ y →
        (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)] (σ x y) = σ ((1 : Equiv.Perm (Fin 9)) y) ((1 : Equiv.Perm (Fin 9)) x) := by
      intro x y hxy
      rw [horbit, Function.iterate_one, hm _ (hψ.isRoot x y hxy)]
      exact (hψ.neg x y).symm
    exact MaxRankE8FixedCover.rootSL2_WSL_mem_rationalComponent_of_unitary_frame
      (k' := K) S i (by norm_num) hψ hΨ 1 hπ horbit hn1 hq (by simp) hα
      (Or.inr (hm α (hψ.frameRoots_isRoot α hα)))

namespace MaxRankE8Action

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
open CFSG.StandardType.ExcFrames CFSG.StandardType.TableBExc.E6Three
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint
open Multiplicative

abbrev E8TorsionCoord : Type := Multiplicative (Fin Tag.E8.rank → ZMod 3)

@[expose] noncomputable def frameDiagHom {L : Type} [Field L] (ζ : Lˣ) (hζ : ζ ^ 3 = 1) :
    E8TorsionCoord →* ModGL .E8 L where
  toFun x := frameDiag ζ hζ (toAdd x)
  map_one' := by rw [toAdd_one, frameDiag_zero]
  map_mul' x y := by rw [toAdd_mul, frameDiag_add]

@[simp] theorem frameDiagHom_apply {L : Type} [Field L] (ζ : Lˣ) (hζ : ζ ^ 3 = 1)
    (x : E8TorsionCoord) :
    frameDiagHom ζ hζ x = frameDiag ζ hζ (toAdd x) := rfl

theorem isUnit_det_symmetrizedCartan_E8_zmod_three :
    IsUnit (((Tag.E8).symmetrizedCartan.det : ℤ) : ZMod 3) := by
  rw [det_symmetrizedCartan_E8]
  exact isUnit_one

theorem frameDiagHom_injective {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) : Function.Injective (frameDiagHom ζ hζ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x y hxy
  exact toAdd.injective
    (frameDiag_injective (τ := .E8) hζo hζ isUnit_det_symmetrizedCartan_E8_zmod_three hxy)

theorem range_frameDiagHom {L : Type} [Field L] [IsAlgClosed L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) :
    Set.range (frameDiagHom (L := L) ζ hζ) = splitPow .E8 L 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact frameDiag_mem (fun a => rootDiagUnit_mem_torusGroup a) ζ hζ (toAdd x)
  · intro hy
    obtain ⟨s, hs⟩ := exists_frameDiag_of_mem (τ := .E8) hζo hζ
      isUnit_det_symmetrizedCartan_E8_zmod_three hy
    exact ⟨ofAdd s, by simp [hs]⟩

section Generic

variable {G : Type} [Group G] {L : Type} [Field L] [IsAlgClosed L]
  {ι : G →* ModGL .E8 L} (hι : Function.Injective ι)
  {A : Subgroup G}
  (hAimage : ∀ y : ModGL .E8 L, y ∈ A.map ι ↔ y ∈ torusGroup .E8 L ∧ y ^ 3 = 1)
  {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)

noncomputable def frameDiagMapToMap :
    E8TorsionCoord →* ↥(A.map ι) :=
  (frameDiagHom ζ hζ).codRestrict (A.map ι) fun x => by
    rw [hAimage]
    refine ⟨?_, frameDiag_pow ζ hζ (toAdd x)⟩
    change rootDiagUnit .E8 (zetaVec ζ hζ (frameCoord .E8 3 (toAdd x))) ∈ torusGroup .E8 L
    exact rootDiagUnit_mem_torusGroup _

include hζo in
theorem frameDiagMapToMap_injective :
    Function.Injective (frameDiagMapToMap hAimage hζ) := by
  intro x y hxy
  exact frameDiagHom_injective hζ hζo (congrArg Subtype.val hxy)

include hζo in
theorem frameDiagMapToMap_surjective :
    Function.Surjective (frameDiagMapToMap hAimage hζ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro y
  have hy : (y : ModGL .E8 L) ∈ torusGroup .E8 L ∧ (y : ModGL .E8 L) ^ 3 = 1 :=
    (hAimage (y : ModGL .E8 L)).mp y.2
  obtain ⟨s, hs⟩ := exists_frameDiag_of_mem (τ := .E8) hζo hζ
    isUnit_det_symmetrizedCartan_E8_zmod_three hy
  refine ⟨ofAdd s, ?_⟩
  apply Subtype.ext
  change frameDiag ζ hζ (toAdd (ofAdd s)) = (y : ModGL .E8 L)
  simpa using hs

noncomputable def frameDiagEquivMap :
    E8TorsionCoord ≃* ↥(A.map ι) :=
  MulEquiv.ofBijective (frameDiagMapToMap hAimage hζ)
    ⟨frameDiagMapToMap_injective hAimage hζ hζo,
      frameDiagMapToMap_surjective hAimage hζ hζo⟩

noncomputable def frameDiagTorsionEquiv (hι : Function.Injective ι) : E8TorsionCoord ≃* A :=
  (frameDiagEquivMap hAimage hζ hζo).trans (Subgroup.equivMapOfInjective A ι hι).symm

theorem frameDiagTorsionEquiv_apply (x : E8TorsionCoord) :
    ι (frameDiagTorsionEquiv hAimage hζ hζo hι x) = frameDiag ζ hζ (toAdd x) := by
  change ι ((Subgroup.equivMapOfInjective A ι hι).symm
    (frameDiagEquivMap hAimage hζ hζo x) : G) = _
  have h := congrArg Subtype.val ((Subgroup.equivMapOfInjective A ι hι).apply_symm_apply
    (frameDiagEquivMap hAimage hζ hζo x))
  exact h

end Generic

theorem monomial_conj_frameDiag {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    {m : ModGL .E8 L} (hm : m ∈ monomialSubgroup .E8 L) {w : WeylGroup .E8}
    (hmw : MapsRootLines m w) (s : Fin Tag.E8.rank → ZMod 3) :
    m * frameDiag ζ hζ s * m⁻¹ =
      frameDiag ζ hζ (TableBExc.torusAct .E8 3 w s) := by
  rw [frameDiag, monomial_conj_rootDiagUnit_weylTuple hm hmw, weylTuple_zetaVec,
    adAct_frameCoord, frameDiag]

theorem monomial_conj_frameDiagHom {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    {m : ModGL .E8 L} (hm : m ∈ monomialSubgroup .E8 L) {w : WeylGroup .E8}
    (hmw : MapsRootLines m w) (x : E8TorsionCoord) :
    m * frameDiagHom ζ hζ x * m⁻¹ =
      frameDiagHom ζ hζ ((ExcWeylOuter.torusMulAut .E8 3) w x) := by
  rw [← ofAdd_toAdd x, frameDiagHom_apply, frameDiagHom_apply, ExcWeylOuter.torusMulAut_apply, toAdd_ofAdd]
  exact monomial_conj_frameDiag hζ hm hmw (toAdd x)

theorem canonicalRep_conj_frameDiagHom {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (w : WeylGroup .E8) (x : E8TorsionCoord) :
    canonicalRep (coxeterSystem .E8) L w * frameDiagHom ζ hζ x *
        (canonicalRep (coxeterSystem .E8) L w)⁻¹ =
      frameDiagHom ζ hζ ((ExcWeylOuter.torusMulAut .E8 3) w x) :=
  monomial_conj_frameDiagHom hζ (canonicalRep_mem_monomialSubgroup L w)
    (mapsRootLines_canonicalRep w) x

theorem rootSL2_WSL_mem_monomialSubgroup_E8 {L : Type} [Field L]
    {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot .E8 β) :
    rootSL2 .E8 L β WSL ∈ monomialSubgroup .E8 L :=
  CFSG.ClassicalInvolution.ModelFacts.Levi.rootSL2_WSL_mem_monomialSubgroup
    (τ := .E8) (K := L) hβ

theorem mapsRootLines_rootSL2_WSL_E8 {L : Type} [Field L]
    {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot .E8 β) :
    MapsRootLines (rootSL2 .E8 L β WSL) (rootReflection β) :=
  CFSG.ClassicalInvolution.ModelFacts.Levi.mapsRootLines_rootSL2_WSL
    (τ := .E8) (K := L) hβ

theorem rootSL2_WSL_conj_frameDiagHom {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot .E8 β) (x : E8TorsionCoord) :
    rootSL2 .E8 L β WSL * frameDiagHom ζ hζ x * (rootSL2 .E8 L β WSL)⁻¹ =
      frameDiagHom ζ hζ
        ((ExcWeylOuter.torusMulAut .E8 3) (rootReflection β) x) :=
  monomial_conj_frameDiagHom hζ (rootSL2_WSL_mem_monomialSubgroup_E8 hβ)
    (mapsRootLines_rootSL2_WSL_E8 hβ) x

end MaxRankE8Action

namespace MaxRankE8Automizer

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.StandardType

@[expose] noncomputable def e8TorusMulAut {G : Type} [Group G] {A : Subgroup G}
    (Θ : Multiplicative (Fin Tag.E8.rank → ZMod 3) ≃* ↥A)
    (W : Subgroup (WeylGroup .E8)) : W →* MulAut ↥A :=
  (MulAut.congr Θ).toMonoidHom.comp
    ((ExcWeylOuter.torusMulAut .E8 3).comp W.subtype)

theorem e8TorusMulAut_injective {G : Type} [Group G] {A : Subgroup G}
    (Θ : Multiplicative (Fin Tag.E8.rank → ZMod 3) ≃* ↥A)
    (W : Subgroup (WeylGroup .E8)) :
    Function.Injective (e8TorusMulAut Θ W) := by
  intro w w' h
  have h' : ExcWeylOuter.torusMulAut .E8 3 (w : WeylGroup .E8) =
      ExcWeylOuter.torusMulAut .E8 3 (w' : WeylGroup .E8) :=
    (MulAut.congr Θ).injective (by
      simpa [e8TorusMulAut, MonoidHom.comp_apply] using h)
  exact Subtype.ext
    ((ExcWeylOuter.torusMulAut_injective (τ := .E8) (p := 3) (by norm_num)) h')

theorem e8TorusMulAut_rootReflection_isReflection
    {G : Type} [Group G] {A : Subgroup G}
    (Θ : Multiplicative (Fin Tag.E8.rank → ZMod 3) ≃* ↥A)
    {W : Subgroup (WeylGroup .E8)} {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot .E8 β)
    (hβW : rootReflection β ∈ W) :
    GGIsReflection 3 (e8TorusMulAut Θ W ⟨rootReflection β, hβW⟩) := by
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hβ
  let s : MulAut (Multiplicative (Fin Tag.E8.rank → ZMod 3)) :=
    ExcWeylOuter.torusMulAut .E8 3 (rootReflection β)
  have hroot : rootReflection β = w * simple .E8 j * w⁻¹ := rootReflection_eq_conj hw
  have hs_eq : s = ExcWeylOuter.torusMulAut .E8 3 w *
      ExcWeylOuter.torusMulAut .E8 3 (simple .E8 j) *
      (ExcWeylOuter.torusMulAut .E8 3 w)⁻¹ := by
    simp only [s, hroot, map_mul, map_inv]
  have hsq : s ^ 2 = 1 := by
    change (ExcWeylOuter.torusMulAut .E8 3 (rootReflection β)) ^ 2 = 1
    rw [pow_two, ← map_mul, rootReflection_mul_self hβ, map_one]
  have hfix : Nat.card {f : Multiplicative (Fin Tag.E8.rank → ZMod 3) // s f = f} * 3 =
      Nat.card (Multiplicative (Fin Tag.E8.rank → ZMod 3)) := by
    rw [hs_eq, natCard_fix_conj_mulAut,
      ExcWeylOuter.torusMulAut_simple TableBExc.Three.cartan_symm_E8 j]
    exact card_fix_torusReflAut (p := 3) (by norm_num) (by norm_num)
      (CFSG.RankThree.CentralCover.cartanFunctional .E8 3 j) (Pi.single j 1)
      (CFSG.RankThree.CentralCover.cartanFunctional_single j)
  simpa [e8TorusMulAut, s, MulAut.congr_apply, MonoidHom.comp_apply] using
    ggIsReflection_congr Θ hsq hfix

theorem range_le_ggAutomizer_of_simple_mem {G : Type} [Group G] {A J : Subgroup G}
    {W : Subgroup (WeylGroup .E8)} (eW : (CoxeterMatrix.A 8).Group ≃* W)
    (ρ : W →* MulAut ↥A)
    (hmem : ∀ i : Fin 8,
      ρ (eW ((CoxeterMatrix.A 8).simple i)) ∈ ggAutomizer J A) :
    ρ.range ≤ ggAutomizer J A := by
  have hgen : Subgroup.closure (Set.range ((CoxeterMatrix.A 8).simple)) = ⊤ := by
    rw [← CoxeterMatrix.toCoxeterSystem_simple]
    exact (CoxeterMatrix.A 8).toCoxeterSystem.subgroup_closure_range_simple
  have hrange : ρ.range = Subgroup.closure (Set.range fun i : Fin 8 =>
      ρ (eW ((CoxeterMatrix.A 8).simple i))) := by
    have hcomp : (ρ.comp eW.toMonoidHom).range = ρ.range := by
      rw [MonoidHom.range_comp,
        show eW.toMonoidHom.range = ⊤ from MulEquiv.range_eq_top eW, Subgroup.map_top]
    rw [← hcomp, MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure]
    congr 1
    rw [← Set.range_comp']
    rfl
  rw [hrange]
  exact (Subgroup.closure_le (ggAutomizer J A)).mpr fun x hx => by
    obtain ⟨i, rfl⟩ := hx
    exact hmem i

theorem exists_eJ_of_injective_range {G : Type} [Group G] {A J : Subgroup G} {p : ℕ}
    {W : Subgroup (WeylGroup .E8)} (eW : (CoxeterMatrix.A 8).Group ≃* W)
    (ρ : W →* MulAut ↥A) (hρ : Function.Injective ρ)
    (hmem : ∀ i : Fin 8, ρ (eW ((CoxeterMatrix.A 8).simple i)) ∈ ggAutomizer J A)
    (hupper : ggAutomizer J A ≤ ρ.range)
    (hrefl : ∀ i : Fin 8, GGIsReflection p (ρ (eW ((CoxeterMatrix.A 8).simple i)))) :
    ∃ eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J A),
      (∀ u : (CoxeterMatrix.A 8).Group,
        ((eJ u : ↥(ggAutomizer J A)) : MulAut ↥A) = ρ (eW u)) ∧
      ∀ i : Fin 8, GGIsReflection p
        ((eJ ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J A)) : MulAut ↥A) := by
  have hle : ρ.range ≤ ggAutomizer J A := range_le_ggAutomizer_of_simple_mem eW ρ hmem
  have hEq : ρ.range = ggAutomizer J A := le_antisymm hle hupper
  let eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J A) :=
    (eW.trans (MonoidHom.ofInjective hρ)).trans (MulEquiv.subgroupCongr hEq)
  have hcoe : ∀ u : (CoxeterMatrix.A 8).Group,
      ((eJ u : ↥(ggAutomizer J A)) : MulAut ↥A) = ρ (eW u) := by
    intro u
    change (((MulEquiv.subgroupCongr hEq) ((MonoidHom.ofInjective hρ) (eW u)) :
      ↥(ggAutomizer J A)) : MulAut ↥A) = ρ (eW u)
    rw [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  refine ⟨eJ, hcoe, ?_⟩
  intro i
  rw [hcoe ((CoxeterMatrix.A 8).simple i)]
  exact hrefl i

theorem ggAutomizer_le_range_of_forall_conjAut {G : Type} [Group G] {A J : Subgroup G}
    {W : Subgroup (WeylGroup .E8)} (ρ : W →* MulAut ↥A)
    (h : ∀ (g : G) (hgJ : g ∈ J) (hgN : g ∈ Subgroup.normalizer (A : Set G)),
      ∃ w : W, ggConjAut A hgN = ρ w) :
    ggAutomizer J A ≤ ρ.range := by
  change Subgroup.closure (ggInduced J A) ≤ ρ.range
  refine (Subgroup.closure_le (ρ.range)).mpr ?_
  rintro φ ⟨g, hgJ, hgN, hφ⟩
  obtain ⟨w, hw⟩ := h g hgJ hgN
  have hφ' : φ = ggConjAut A hgN := MulEquiv.ext fun b => Subtype.ext (hφ b)
  rw [hφ', hw]
  exact MonoidHom.mem_range.mpr ⟨w, rfl⟩

end MaxRankE8Automizer

namespace MaxRankE8Action
theorem exists_actual_action {G H : Type} [Group G] [Group H]
    (ι : G →* H) (hι : Function.Injective ι) (A J : Subgroup G)
    {V : Type} [Group V] (Θ : V ≃* A) (ρ : MulAut V)
    (m : H) (hm : m ∈ J.map ι)
    (hact : ∀ v, m * ι (Θ v) * m⁻¹ = ι (Θ (ρ v))) :
    ∃ (g : G) (hgJ : g ∈ J) (hgN : g ∈ Subgroup.normalizer (A : Set G)),
      ggConjAut A hgN = MulAut.congr Θ ρ := by
  obtain ⟨g, hgJ, rfl⟩ := hm
  have hgact : ∀ v, g * (Θ v : G) * g⁻¹ = (Θ (ρ v) : G) := by
    intro v
    apply hι
    simpa only [map_mul, map_inv] using hact v
  have hgN : g ∈ Subgroup.normalizer (A : Set G) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      let v := Θ.symm ⟨x, hx⟩
      have he : (Θ v : G) = x := congrArg Subtype.val (Θ.apply_symm_apply ⟨x, hx⟩)
      rw [← he, hgact]
      exact (Θ (ρ v)).property
    · intro hx
      let v := ρ.symm (Θ.symm ⟨g * x * g⁻¹, hx⟩)
      have he : (Θ (ρ v) : G) = g * x * g⁻¹ := by
        simp only [v, MulEquiv.apply_symm_apply]
      have he' : (Θ v : G) = x := by
        have h := (hgact v).trans he
        exact mul_left_cancel (mul_right_cancel h)
      rw [← he']
      exact (Θ v).property
  refine ⟨g, hgJ, hgN, ?_⟩
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  change g * (b : G) * g⁻¹ = (Θ (ρ (Θ.symm b)) : G)
  have h := hgact (Θ.symm b)
  simpa only [Θ.apply_symm_apply] using h

theorem ggConjAut_eq_of_action {G H : Type} [Group G] [Group H]
    (ι : G →* H) (hι : Function.Injective ι) (A : Subgroup G)
    {V : Type} [Group V] (Θ : V ≃* A) (ρ : MulAut V)
    (g : G) (hgN : g ∈ Subgroup.normalizer (A : Set G))
    (hact : ∀ v, ι (g * (Θ v : G) * g⁻¹) = ι (Θ (ρ v))) :
    ggConjAut A hgN = MulAut.congr Θ ρ := by
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  apply hι
  change ι (g * (b : G) * g⁻¹) = ι (Θ (ρ (Θ.symm b)))
  simpa only [Θ.apply_symm_apply] using hact (Θ.symm b)

theorem map_eq_range_of_card {G H V : Type} [Group G] [Group H] [Group V] [Finite V]
    (ι : G →* H) (hι : Function.Injective ι) (A : Subgroup G)
    (χ : V →* H) (hχ : Function.Injective χ)
    (hle : A.map ι ≤ χ.range) (hcard : Nat.card V ≤ Nat.card A) :
    A.map ι = χ.range := by
  haveI : Finite χ.range := Finite.of_equiv V (MonoidHom.ofInjective hχ).toEquiv
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [← Nat.card_congr (MonoidHom.ofInjective hχ).toEquiv,
    Subgroup.card_map_of_injective hι]
  exact hcard

end MaxRankE8Action

open MaxRankE8Action MaxRankE8Automizer MaxRankE8Weyl

theorem ggMaxRankE8Core_holds : GGMaxRankE8Core := by
  classical
  intro K _ _ _ n hK A J s hA hcard hsA hs1 hJ hLab
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨S, ι, a, i, ψ, σ, hq, hι, hrange, hAimage, hs, hJi, hψ, hΨ, hkernel, hinvol⟩ :=
    ggMaxRankE8_exists_actual_frame_involutions K n hK A J s hA hcard hsA hs1 hJ
      (hLab.imp And.left And.left)
  have h3 : ∀ j, a j ^ 3 = 1 := by
    have hpow : (rootDiagUnit .E8 a) ^ 3 = 1 := by
      rw [← hs, ← map_pow, hA.2 s hsA, map_one]
    have hp : a ^ 3 = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective (by
      rw [← rootDiagUnit_pow, hpow, rootDiagUnit_one])
    intro j
    exact congrFun hp j
  have ha : a ≠ 1 := by
    intro ha
    have he : ι s = ι 1 := by rw [hs, ha, rootDiagUnit_one, map_one]
    exact hs1 (hι he)
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 1 := by
    by_contra h
    apply ha
    funext j
    exact not_not.mp (not_exists.mp h j)
  let ζ := a j
  have hζ : ζ ^ 3 = 1 := h3 j
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ hj
  let χ := frameDiagHom ζ hζ
  have hχ : Function.Injective χ := frameDiagHom_injective hζ hζo
  have hle : A.map ι ≤ χ.range := by
    intro y hy
    have ht := (hAimage y).mp hy
    have ht' : y ∈ ExcFrames.splitPow .E8 (AlgebraicClosure K) 3 :=
      ⟨(CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.mp ht.1).1, ht.2⟩
    rw [← range_frameDiagHom hζ hζo] at ht'
    exact ht'
  have hVcard : Nat.card E8TorsionCoord = 3 ^ 8 := by
    change Nat.card (Fin 8 → ZMod 3) = 3 ^ 8
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hEq : A.map ι = χ.range :=
    map_eq_range_of_card ι hι A χ hχ hle (by rw [hVcard]; exact hcard)
  have hAfull : ∀ y, y ∈ A.map ι ↔ y ∈ torusGroup .E8 (AlgebraicClosure K) ∧ y ^ 3 = 1 := by
    intro y
    rw [hEq]
    exact Set.ext_iff.mp (range_frameDiagHom hζ hζo) y
  let Θ : E8TorsionCoord ≃* A := frameDiagTorsionEquiv hAfull hζ hζo hι
  have hΘ : ∀ v, ι (Θ v) = χ v := fun v =>
    frameDiagTorsionEquiv_apply hι hAfull hζ hζo v
  obtain ⟨eW, heW⟩ := exists_coxeterA8_equiv_kernelWeylGroup hψ hkernel
  let W := kernelWeylGroup (rootCharHom a)
  let ρ : W →* MulAut A := e8TorusMulAut Θ W
  have hιC : ι.range ≤ adjointGroup .E8 (AlgebraicClosure K) := by
    rw [hrange]
    exact (Subgroup.commutator_le_self S.D.model).trans inf_le_left
  have hAT : ∀ x ∈ A, ι x ∈ torusGroup .E8 (AlgebraicClosure K) := fun x hx =>
    ((hAfull (ι x)).mp (Subgroup.mem_map_of_mem ι hx)).1
  have hupper : ggAutomizer J A ≤ ρ.range := by
    apply ggAutomizer_le_range_of_forall_conjAut ρ
    intro g hgJ hgN
    obtain ⟨w, hw, hact⟩ := maxRankE8_normalizer_action ι hιC A J s hsA hAT hJ.1 a hs h3 g hgJ hgN
    refine ⟨⟨w, hw⟩, ?_⟩
    change ggConjAut A hgN = MulAut.congr Θ (ExcWeylOuter.torusMulAut .E8 3 w)
    apply ggConjAut_eq_of_action ι hι A Θ _ g hgN
    intro v
    rw [hact (Θ v) (Θ v).property, hΘ, hΘ]
    exact canonicalRep_conj_frameDiagHom hζ w v
  have hmem : ∀ k : Fin 8, ρ (eW ((CoxeterMatrix.A 8).simple k)) ∈ ggAutomizer J A := by
    intro k
    have hneq : k.castSucc ≠ k.succ := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
    have hβ := hψ.isRoot k.castSucc k.succ hneq
    have hβmem : σ k.castSucc k.succ ∈ CFSG.HardMathSupport.Timmesfeld.CrossChar.frameRoots σ := ⟨k.castSucc, k.succ, hneq, rfl⟩
    obtain ⟨g, hgJ, hgN, hact⟩ := exists_actual_action ι hι A J Θ
      (ExcWeylOuter.torusMulAut .E8 3 (rootReflection (σ k.castSucc k.succ)))
      (rootSL2 .E8 (AlgebraicClosure K) (σ k.castSucc k.succ) WSL) (hinvol _ hβmem)
      (fun v => by rw [hΘ, hΘ]; exact rootSL2_WSL_conj_frameDiagHom hζ hβ v)
    have heq : ρ (eW ((CoxeterMatrix.A 8).simple k)) = ggConjAut A hgN := by
      rw [hact]
      change MulAut.congr Θ (ExcWeylOuter.torusMulAut .E8 3
        ((eW ((CoxeterMatrix.A 8).simple k) : W) : WeylGroup .E8)) = _
      rw [heW k]
    rw [heq]
    exact ggConjAut_mem_ggAutomizer hgJ hgN
  have hrefl : ∀ k : Fin 8, GGIsReflection 3 (ρ (eW ((CoxeterMatrix.A 8).simple k))) := by
    intro k
    have hneq : k.castSucc ≠ k.succ := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
    have hβ := hψ.isRoot k.castSucc k.succ hneq
    have hwmem : rootReflection (σ k.castSucc k.succ) ∈ W := by
      rw [← heW k]
      exact (eW ((CoxeterMatrix.A 8).simple k)).property
    have heq : eW ((CoxeterMatrix.A 8).simple k) =
        (⟨rootReflection (σ k.castSucc k.succ), hwmem⟩ : W) := Subtype.ext (heW k)
    rw [heq]
    exact e8TorusMulAut_rootReflection_isReflection Θ hβ hwmem
  obtain ⟨eJ, -, hsimple⟩ := exists_eJ_of_injective_range eW ρ
    (e8TorusMulAut_injective Θ W) hmem hupper hrefl
  exact ⟨eJ, hsimple⟩

end CFSG.StandardType

end
