module

public import CFSG.LocalAnalysis.StandardType.GGB36Defs
public import CFSG.LocalAnalysis.StandardType.GGKacExcB2
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGB36LemmaRT
public import CFSG.LocalAnalysis.StandardType.GGKacTable
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutThreeRank
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.CGT.Timmesfeld75.MultPrime
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec5Nine
public import CFSG.CGT.Timmesfeld75.Sec5Ten
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.GH74.GLS.Balance.PStarComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.CGT.Timmesfeld75

@[expose] def GGE6CoverThreeLocalRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (lab : LargeEvenLabel), LargeEvenInLambda2 lab → lab.tag = .E6 →
    3 ∣ 2 ^ lab.n - 1 → GGHasLabel lab (X ⧸ Subgroup.center X) → commutator X = ⊤ →
    3 ∣ Nat.card (Subgroup.center X) → 6 ≤ LargeEvenTwoLocalRank 3 X

private theorem ltqE6h_card_le_of_isCyclic_exp {G : Type*} [Group G] {p : ℕ} {S : Subgroup G}
    (hp : 0 < p) (hc : IsCyclic S) (he : ∀ y ∈ S, y ^ p = 1) : Nat.card S ≤ p := by
  obtain ⟨e, he'⟩ := hc.exists_generator
  rw [← orderOf_eq_card_of_forall_mem_zpowers he']
  exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using he _ e.2)))

private theorem ltqE6h_conj_injective {S : Type*} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro x
  have h := congrArg (fun α : MulAut S => α x) ((MonoidHom.mem_ker).mp hg)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc x * g = g * x * g⁻¹ * g := by rw [h]
    _ = g * x := by group

private theorem ltqE6h_mulAut_card_le_of_normalForm {C Q : Type} [Group C] [Group Q] [Finite C]
    (hZ : Subgroup.center C = ⊥) (Θ : MulAut C →* Q) (hsurj : Function.Surjective Θ)
    (hker : Θ.ker = (MulAut.conj : C →* MulAut C).range) (hcyc : IsCyclic Q)
    (hAut : ∀ F : Subgroup C, IsElemAbelian 3 F → Nat.card F ≤ 9)
    (E : Subgroup (MulAut C)) (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 3 := by
  classical
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) := ltqE6h_conj_injective hZ
  have hS : IsElemAbelian 3 (E ⊓ Θ.ker) := CFSG.Open.IsElemAbelian.mono hE inf_le_left
  have hle : E ⊓ Θ.ker ≤ (MulAut.conj : C →* MulAut C).range := by
    rw [← hker]; exact inf_le_right
  have hT : IsElemAbelian 3 ((E ⊓ Θ.ker).comap (MulAut.conj : C →* MulAut C)) :=
    CFSG.Open.IsElemAbelian.comap hS hinj
  have hmap : ((E ⊓ Θ.ker).comap (MulAut.conj : C →* MulAut C)).map
      (MulAut.conj : C →* MulAut C) = E ⊓ Θ.ker :=
    Subgroup.map_comap_eq_self hle
  have hkerbound : Nat.card (E ⊓ Θ.ker : Subgroup (MulAut C)) ≤ 9 := by
    have hcard : Nat.card ((E ⊓ Θ.ker).comap (MulAut.conj : C →* MulAut C) : Subgroup C) =
        Nat.card (E ⊓ Θ.ker : Subgroup (MulAut C)) := by
      calc Nat.card ((E ⊓ Θ.ker).comap (MulAut.conj : C →* MulAut C) : Subgroup C)
          = Nat.card (((E ⊓ Θ.ker).comap (MulAut.conj : C →* MulAut C)).map
              (MulAut.conj : C →* MulAut C)) :=
            (Subgroup.card_map_of_injective (f := MulAut.conj) hinj).symm
        _ = Nat.card (E ⊓ Θ.ker : Subgroup (MulAut C)) := by rw [hmap]
    rw [← hcard]
    exact hAut _ hT
  have himg : IsElemAbelian 3 (E.map Θ) := CFSG.Open.IsElemAbelian.map hE Θ
  haveI : IsCyclic Q := hcyc
  haveI : IsCyclic (⊤ : Subgroup Q) :=
    isCyclic_of_surjective (Subgroup.topEquiv (G := Q)).symm.toMonoidHom
      (Subgroup.topEquiv (G := Q)).symm.surjective
  have hcycS : IsCyclic (E.map Θ) := Subgroup.isCyclic_of_le le_top
  have himgcard : Nat.card (E.map Θ : Subgroup Q) ≤ 3 :=
    ltqE6h_card_le_of_isCyclic_exp (by norm_num) hcycS (fun y hy => himg.2 y hy)
  have hkercard : Nat.card ((Θ.comp E.subtype).ker : Subgroup E) =
      Nat.card (E ⊓ Θ.ker : Subgroup (MulAut C)) := by
    have hker_eq : (Θ.comp E.subtype).ker = (E ⊓ Θ.ker).subgroupOf E := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf, Subgroup.coe_subtype]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : (Θ.comp E.subtype).range = E.map Θ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardE : Nat.card E =
      Nat.card (E ⊓ Θ.ker : Subgroup (MulAut C)) * Nat.card (E.map Θ : Subgroup Q) := by
    have h := Subgroup.card_ker_mul_card_range (Θ.comp E.subtype)
    rw [hkercard, hrange] at h
    exact h.symm
  calc Nat.card E = Nat.card (E ⊓ Θ.ker : Subgroup (MulAut C)) * Nat.card (E.map Θ : Subgroup Q) :=
        hcardE
    _ ≤ 9 * 3 := Nat.mul_le_mul hkerbound himgcard
    _ = 3 ^ 3 := by norm_num

theorem ggTriD4AutThreeBound
    {J : Type} [Group J] [Finite J] (hperf : commutator J = ⊤)
    {n : ℕ} (hlab : GGHasLabel ⟨.triD4, 0, n⟩ (J ⧸ Subgroup.center J)) :
    ∀ E : Subgroup (MulAut J), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3 := by
  intro E hE
  unfold GGHasLabel at hlab
  dsimp only [LargeEvenRawDatum] at hlab
  unfold LargeEvenRecipeTwisted at hlab
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hlab
  haveI : Fintype K := Fintype.ofFinite K
  have hKge : 2 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card (α := K)
    omega
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hK1 : Nat.card K = 1 := by
      rw [hn0] at hKcard
      simpa using hKcard
    omega
  have htw : TwistedChevalleyModel
      (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) .D4
      (2 ^ n) :=
    twistedChevalleyModel_largeEven .D4 hKcard
  obtain ⟨K', hK'f, hK'fin, σ', hK'card, hσ', ⟨e'⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hn htw
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, hcyc, -, -, hZ, -⟩ :=
    CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form hn K' hK'card σ' hσ'
  have hb := ltqE6h_mulAut_card_le_of_normalForm hZ Θ hsurj hker hcyc
    (fun F hF =>
      CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof.card_le_nine_of_graphFixedRootGroup
        hn hK'card hσ' F hF)
    (E.map (ggInducedAut (e.trans e')))
    (CFSG.Open.IsElemAbelian.map hE (ggInducedAut (e.trans e')))
  have hinj : Function.Injective (ggInducedAut (e.trans e')) :=
    ggInducedAut_injective_of_perfect hperf _
  have hcard : Nat.card (E.map (ggInducedAut (e.trans e'))) = Nat.card E :=
    Subgroup.card_map_of_injective hinj
  rwa [hcard] at hb

private noncomputable def ltqE6h_largeEvenProj_statedProj (K : Type) [Field K] :
    LargeEvenProj (LargeEvenSLGroup (Fin 3) K) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) :=
  QuotientGroup.congr ((LargeEvenScalars (Fin 3) K).subgroupOf (LargeEvenSLGroup (Fin 3) K))
    ((CFSG.Open.StatedScalars (Fin 3) K).subgroupOf (CFSG.Open.StatedSL 3 K))
    (MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL 3)) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ((MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL 3)) y : GL (Fin 3) K) ∈
        CFSG.Open.StatedScalars (Fin 3) K
      rw [MulEquiv.subgroupCongr_apply]
      change (y : GL (Fin 3) K) ∈ LargeEvenScalars (Fin 3) K at hy
      exact hy
    · intro hx
      change (x : GL (Fin 3) K) ∈ CFSG.Open.StatedScalars (Fin 3) K at hx
      refine ⟨⟨(x : GL (Fin 3) K), ?_⟩, ?_, ?_⟩
      · rw [largeEvenSLGroup_eq_statedSL 3]; exact x.2
      · change (x : GL (Fin 3) K) ∈ LargeEvenScalars (Fin 3) K
        exact hx
      · ext; simp [MulEquiv.subgroupCongr_apply])

private theorem ltqE6h_aut_projectiveSL3_card_le {K : Type} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card Kˣ) :
    ∀ E : Subgroup (MulAut (projectiveSL 3 K)), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3 := by
  intro E hE
  have hR : standardAutGroup 3 K = ⊤ :=
    (automorphism_generation (K := K) (n := 3) le_rfl).1
  obtain ⟨-, -, hInorm, -, -, hcyc, -, hindex, -, -⟩ :=
    standard_outer_quotients (K := K) (n := 3)
  rw [hR] at hInorm hindex
  have hindex' : (semilinearAutGroup 3 K).index ≤ 2 := by
    rw [← Subgroup.relIndex_top_right]
    exact hindex
  have hEstd : E ≤ semilinearAutGroup 3 K := by
    intro x hx
    have hx2 : x ^ 2 ∈ semilinearAutGroup 3 K := by
      have h0 : (semilinearAutGroup 3 K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      rcases (show (semilinearAutGroup 3 K).index = 1 ∨ (semilinearAutGroup 3 K).index = 2 by
        omega) with h1 | h2
      · rw [Subgroup.index_eq_one.1 h1]; trivial
      · exact Subgroup.sq_mem_of_index_two h2 x
    have hodd : 2 * ((3 + 1) / 2) = 3 + 1 := by norm_num
    have hxe : x = (x ^ 2) ^ ((3 + 1) / 2) := by
      rw [← pow_mul, hodd, pow_succ, hE.2 x hx, one_mul]
    rw [hxe]
    exact pow_mem hx2 _
  have hSE : IsElemAbelian 3 (E ⊓ linearAutGroup 3 K) :=
    CFSG.Open.IsElemAbelian.mono hE inf_le_left
  have hcardSE : Nat.card (E ⊓ linearAutGroup 3 K :
      Subgroup (MulAut (projectiveSL 3 K))) ≤ 3 ^ 2 := by
    obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 (CFSG.Open.IsElemAbelian.isPGroup hSE)
    have hrle : r ≤ 2 := by
      have h1 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) inf_le_right hSE hr
      have h2 : CFSG.Open.pRank 3 (linearAutGroup 3 K) ≤ 2 := by
        simpa using pRank_linearAutGroup_le (K := K) (n := 3) le_rfl Nat.prime_three
          (by norm_num) h3
      exact h1.trans h2
    rw [hr]
    exact Nat.pow_le_pow_right (by norm_num) hrle
  have hInormal : (linearAutGroup 3 K).Normal :=
    ⟨fun a ha g => by
      have := hInorm.conj_mem ⟨a, trivial⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨g, trivial⟩
      exact Subgroup.mem_subgroupOf.1 this⟩
  set N := (linearAutGroup 3 K).subgroupOf (semilinearAutGroup 3 K)
  obtain ⟨g, hg, hgen⟩ := hcyc
  have hQcyc : IsCyclic (semilinearAutGroup 3 K ⧸ N) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hg⟩, fun q => ?_⟩⟩
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hgen x hx
    refine ⟨-k, ?_⟩
    change ((QuotientGroup.mk ⟨g, hg⟩ : semilinearAutGroup 3 K ⧸ N) ^ (-k)) =
      QuotientGroup.mk _
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [_root_.zpow_neg] using hk
  let ψ : E →* semilinearAutGroup 3 K ⧸ N :=
    (QuotientGroup.mk' N).comp (Subgroup.inclusion hEstd)
  have hker : ψ.ker = (E ⊓ linearAutGroup 3 K).subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · rintro hx
      exact ⟨x.2, hx⟩
    · rintro ⟨-, hx⟩
      exact hx
  have hkercard : Nat.card ψ.ker = Nat.card (E ⊓ linearAutGroup 3 K :
      Subgroup (MulAut (projectiveSL 3 K))) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrangecard : Nat.card ψ.range ≤ 3 := by
    have hexp : Monoid.exponent ψ.range ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun y => by
        obtain ⟨x, hx⟩ := y.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hx, ← map_pow,
          show x ^ 3 = 1 from Subtype.ext (hE.2 x x.2), map_one]
        rfl
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num) hexp
  have hcardE : Nat.card E = Nat.card (E ⊓ linearAutGroup 3 K :
      Subgroup (MulAut (projectiveSL 3 K))) * Nat.card ψ.range := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hkercard] at h
    exact h.symm
  calc Nat.card E = Nat.card (E ⊓ linearAutGroup 3 K :
        Subgroup (MulAut (projectiveSL 3 K))) * Nat.card ψ.range := hcardE
    _ ≤ 3 ^ 2 * 3 := Nat.mul_le_mul hcardSE hrangecard
    _ = 3 ^ 3 := by norm_num

private theorem ltqE6h_aut_A2 {J : Type} [Group J] [Finite J] (hperf : commutator J = ⊤)
    {m : ℕ} (h3 : 3 ∣ 2 ^ m - 1)
    (hlab : GGHasLabel ⟨.A, 2, m⟩ (J ⧸ Subgroup.center J)) :
    ∀ E : Subgroup (MulAut J), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3 := by
  intro E hE
  unfold GGHasLabel at hlab
  dsimp only [LargeEvenRawDatum] at hlab
  unfold LargeEvenRecipeLinear at hlab
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hlab
  have h3K : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hKcard]
    exact h3
  let θ : J ⧸ Subgroup.center J ≃* projectiveSL 3 K :=
    e.trans ((ltqE6h_largeEvenProj_statedProj K).trans
      (projectiveSLMulEquivStatedProj 3 K).symm)
  have hb := ltqE6h_aut_projectiveSL3_card_le h3K
    (E.map (ggInducedAut θ)) (CFSG.Open.IsElemAbelian.map hE (ggInducedAut θ))
  have hinj : Function.Injective (ggInducedAut θ) :=
    ggInducedAut_injective_of_perfect hperf θ
  have hcard : Nat.card (E.map (ggInducedAut θ)) = Nat.card E :=
    Subgroup.card_map_of_injective hinj
  rwa [hcard] at hb

theorem ggE6TorusLiftFiveRank
    {X : Type} [Group X] [Finite X] (hperf : commutator X = ⊤) {lab : LargeEvenLabel}
    (htag : lab.tag = .E6) (h3 : 3 ∣ 2 ^ lab.n - 1)
    (hlab : GGHasLabel lab (X ⧸ Subgroup.center X)) :
    5 ≤ LargeEvenTwoLocalRank 3 X := by
  have hmain := largeEvenLabelAll_torusLift_E6_three htag h3
    (fun R _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R)) hlab
  obtain ⟨R, hRgrp, I, F, ⟨θ⟩, hlift⟩ := largeEvenRawDatum_exists hmain
  let ψ : X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    refine ⟨x, ?_⟩
    show θ (QuotientGroup.mk' (Subgroup.center X) x) = r
    rw [hx]
    exact hq
  have hker_le : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : θ (QuotientGroup.mk' (Subgroup.center X) x) = 1 := by simpa [ψ] using hx
    have hx'' : QuotientGroup.mk' (Subgroup.center X) x = 1 := θ.injective (by simpa using hx')
    exact (QuotientGroup.eq_one_iff x).mp hx''
  obtain ⟨U, E, hU, hU2, hEU, hE, hEcard, -⟩ := hlift X ψ hψ hker_le hperf
  have hTL : IsTwoLocal (Subgroup.normalizer (U : Set X)) := ⟨U, hU, hU2, rfl⟩
  have h5 : 5 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (U : Set X)) := by
    have := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hEU hE hEcard
    simpa using this
  exact TableB.le_twoLocalRank (p := 3) (by norm_num) hTL h5

private theorem ltqE6h_false_of_E6_hard
    (hβ : GGE6CoverThreeLocalRank)
    {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNDatumB 3 (3 ^ 6) (fun _ _ => True) A Ab σ J) (hk : GGTPNKernel A σ J)
    {labJ labX : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hΛX : LargeEvenInLambda2 labX)
    (hcase : labJ = ⟨.triD4, 0, labX.n⟩ ∨ labJ = ⟨.A, 2, 3 * labX.n⟩)
    (htagX : labX.tag = .E6) (h3 : 3 ∣ 2 ^ labX.n - 1)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) : False := by
  obtain ⟨hlocCore, hflat, -, hrank, hnum, hself, honly, hmarked⟩ := hd.1
  obtain ⟨hAbA, hσAb, -, hkerAb⟩ := hflat
  have hnormA : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := hlocCore.2.2.2.2
  have hperfJ : commutator ↥J = ⊤ := hlocCore.2.2.2.1.2.2.1
  have hAbab : IsElemAbelian 3 Ab := by
    obtain ⟨hc, hp⟩ := hlocCore.1
    haveI : IsMulCommutative A := hc
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
    · apply Subtype.ext
      exact Subgroup.mul_comm_of_mem_isMulCommutative A (hAbA u.2) (hAbA v.2)
    · exact hp z (hAbA hz)
  have hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J := fun a ha j hj => hnormA a (hAbA ha) j hj
  have hAut : ∀ E : Subgroup (MulAut ↥J), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3 := by
    intro E hE
    rcases hcase with hcase | hcase
    · exact ggTriD4AutThreeBound hperfJ (hcase ▸ hhJ) E hE
    · have h3' : 3 ∣ 2 ^ (3 * labX.n) - 1 := by
        have h : 3 ∣ (2 ^ labX.n) ^ 3 - 1 :=
          h3.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ labX.n) 3)
        have he : (2 ^ labX.n) ^ 3 - 1 = 2 ^ (3 * labX.n) - 1 := by
          rw [mul_comm 3, pow_mul]
        rwa [he] at h
      exact ltqE6h_aut_A2 hperfJ h3' (hcase ▸ hhJ) E hE
  have hbound : Nat.card Ab ≤ 3 ^ 4 := by
    have h := B36.card_le_of_kernel_le_zpowers (p := 3) (by norm_num) hAbab hσAb hnorm hkerAb
      (k := 3) hAut
    simpa using h
  have hAb4 : 3 ^ 4 ≤ Nat.card Ab := by
    have h : 3 ^ 2 * 3 ^ 4 ≤ 3 ^ 2 * Nat.card Ab := by
      calc 3 ^ 2 * 3 ^ 4 = 3 ^ 6 := by norm_num
        _ ≤ 3 ^ 2 * Nat.card Ab := hnum.2
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  have hAbcard : Nat.card Ab = 3 ^ 4 := le_antisymm hbound hAb4
  obtain ⟨m, hmcard, hmrank⟩ := hrank
  have hm : m = 4 := by
    have h : 3 ^ m = 3 ^ 4 := hmcard.symm.trans hAbcard
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
  rw [hm] at hmrank
  have hperfX : commutator X = ⊤ := hmarked.1
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center X)
  · have h6 := hβ X labX hΛX htagX h3 hhX hperfX hZ
    rw [if_pos hZ] at hmrank
    omega
  · have h5 := ggE6TorusLiftFiveRank hperfX htagX h3 hhX
    rw [if_neg hZ] at hmrank
    omega

private theorem ltqE6h_iso_twE6 {l : LargeEvenLabel}
    (h : GGLabelIso ⟨.twE6, 0, 1⟩ l) : l = ⟨.twE6, 0, 1⟩ := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private local instance (priority := high) ltqE6hDecEqLabel : DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) ltqE6hDecEqOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) ltqE6hDecEqDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) ltqE6hDecEqIso (l l' : LargeEvenLabel) :
    Decidable (GGLabelIso l l') := by
  unfold GGLabelIso
  infer_instance

private theorem ltqE6h_fin :
    ∀ D' ∈ ggKacTable .E6 true 3 1, ∀ o' ∈ D'.orbits, o'.qs = true →
      GGLabelIso ⟨.twA, 4, 1⟩ o'.lab →
        ∃ o ∈ D'.orbits, o.lab = ⟨.A, 1, 1⟩ ∧ o.qs = false := by
  decide

private theorem ltqE6h_false_of_twE6
    (hBS : GGK0ExcBS)
    {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNDatumB 3 (3 ^ 6) (fun _ _ => True) A Ab σ J) (hk : GGTPNKernel A σ J)
    (hhJ : GGHasLabel ⟨.twA, 4, 1⟩ (↥J ⧸ Subgroup.center ↥J))
    (hhX : GGHasLabel ⟨.twE6, 0, 1⟩ (X ⧸ Subgroup.center X)) : False := by
  obtain ⟨hlocCore, hflat, -, -, -, hself, honly, hmarked⟩ := hd.1
  have hσA : σ ∈ A := hlocCore.2.1
  have hAab : IsElemAbelian 3 A := hlocCore.1
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    have hsub : ggFixSub σ = ggAutFixedSubgroup σ := by
      ext x
      simp [ggFixSub, ggAutFixedSubgroup]
    rw [hsub]
    exact hlocCore.2.2.2.1
  obtain ⟨hcomm, lab', hlab', hraw⟩ := hmarked
  have hhaslab' : GGHasLabel lab' (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim (fun θ _ => ⟨θ⟩)) hraw
  have hΛX : LargeEvenInLambda2 ⟨.twE6, 0, 1⟩ := ⟨le_rfl, rfl⟩
  have hrigid : GGLabelIso ⟨.twE6, 0, 1⟩ lab' :=
    ggLabelRigidInput_holds ⟨.twE6, 0, 1⟩ lab' (X ⧸ Subgroup.center X) hΛX hlab' hhX hhaslab'
  have hlab'_eq : lab' = ⟨.twE6, 0, 1⟩ := ltqE6h_iso_twE6 hrigid
  rw [hlab'_eq] at hraw
  have hExcPair : GGKacExcPair ⟨.twE6, 0, 1⟩ 3 :=
    ⟨Nat.prime_three, by norm_num, Or.inr (by norm_num), Or.inr (Or.inl rfl)⟩
  have hBS' := hBS 3 ⟨.twE6, 0, 1⟩ hΛX hExcPair
  have hmain := hBS' _ hraw
  obtain ⟨R, hRgrp, I, F, hQBS⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨hQmark, hBSconcl⟩ := hQBS
  obtain ⟨hsimple, hna, θ, htrue, hhalf, hInd⟩ := hQmark
  let ψ : X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    refine ⟨x, ?_⟩
    show θ (QuotientGroup.mk' (Subgroup.center X) x) = r
    rw [hx]
    exact hq
  have hker_le : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : θ (QuotientGroup.mk' (Subgroup.center X) x) = 1 := by simpa [ψ] using hx
    have hx'' : QuotientGroup.mk' (Subgroup.center X) x = 1 := θ.injective (by simpa using hx')
    exact (QuotientGroup.eq_one_iff x).mp hx''
  have hσ3 : σ ^ 3 = 1 := hlocCore.1.2 σ hσA
  have hInd'' : ∃ φ ∈ I, ∀ l : X, φ (ψ l) = ψ (σ l) := by
    refine ⟨ggInducedAut θ σ, hInd σ hσA, fun l => ?_⟩
    exact ggInducedAut_apply θ σ l
  obtain ⟨D, hValid, ha, hb, hc, hd, hcomp, hsigma⟩ :=
    hBSconcl X ψ hψ hker_le hcomm σ hσ3 hInd''
  obtain ⟨o, ho, hoqs, hodvd, hΛo, holab⟩ := ha J hJfix
  have hΛJ : LargeEvenInLambda2 ⟨.twA, 4, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have hiso : GGLabelIso ⟨.twA, 4, 1⟩ o.lab :=
    ggLabelRigidInput_holds ⟨.twA, 4, 1⟩ o.lab (↥J ⧸ Subgroup.center ↥J) hΛJ hΛo hhJ holab
  obtain ⟨T, tw, hT, hmem⟩ := hValid
  simp only [ggKacTypeOfLabel] at hT
  cases hT
  obtain ⟨o', ho', ho'lab, ho'qs⟩ := ltqE6h_fin D hmem o ho hoqs hiso
  have hInd' : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : X, φ (ψ l) = ψ (a l) := by
    intro a ha
    refine ⟨ggInducedAut θ a, hInd a ha, ?_⟩
    intro l
    change ggInducedAut θ a (θ (l : X ⧸ Subgroup.center X)) =
      θ ((a l : X) : X ⧸ Subgroup.center X)
    exact ggInducedAut_apply θ a l
  obtain ⟨t, ht3, htfix, htcent, htnotin⟩ :=
    hsigma o' ho' ⟨ho'lab, ho'qs⟩ A hσA hAab hInd'
  have hconjA : (MulAut.conj t : MulAut X) ∈ A := hself t htfix ht3
  have hconjJ : ∀ j ∈ J, (MulAut.conj t : MulAut X) j = j := by
    intro j hj
    have h := htcent J hJfix j hj
    show t * j * t⁻¹ = j
    rw [h]; group
  exact htnotin (hk (MulAut.conj t) hconjA hconjJ)

theorem ggTablePKnownRK_b36JExc_E6Hard
    (hBS : GGK0ExcBS) (hβ : GGE6CoverThreeLocalRank) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeB36J p n labJ labX ∧
      ((labX.tag = .E6 ∧ 3 ∣ 2 ^ labX.n - 1 ∧
          (labJ = ⟨.triD4, 0, labX.n⟩ ∨ labJ = ⟨.A, 2, 3 * labX.n⟩)) ∨
        (labX = ⟨.twE6, 0, 1⟩ ∧ labJ = ⟨.twA, 4, 1⟩)) := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hcases⟩ := hr
  obtain ⟨hp3, hn, labL, htagL, hJlabel⟩ := hreg
  subst hp3
  subst hn
  rcases hcases with ⟨htagX, h3X, hcaseJ⟩ | ⟨hlabX, hlabJ⟩
  · exact (ltqE6h_false_of_E6_hard hβ hd hk hΛJ hΛX hcaseJ htagX h3X hhJ hhX).elim
  · subst hlabX
    subst hlabJ
    exact (ltqE6h_false_of_twE6 hBS hd hk hhJ hhX).elim

end CFSG.StandardType

end
