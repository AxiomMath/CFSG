module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FLinearField
import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6Noninner
import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoFrame
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesReps
import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6Field
import CFSG.Timmesfeld.RankTwo.LevisExtras
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8ExcRank
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverE6RankTw
import CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FLift
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Chevalley
open CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LieType.SeitzGeneration.ExcHigh (frameRoot)


theorem uc22s2114r4f_twistedE6_restrict_order {K : Type} [Field K] [Finite K]
    (σ δ : K ≃+* K) (hσ : ∀ x, σ (σ x) = x) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hδ : orderOf δ = r) :
    orderOf (fixSubfieldRestrict δ σ) = r := by
  have : Fact r.Prime := ⟨hr⟩
  have hδr : δ ^ r = 1 := hδ ▸ pow_orderOf_eq_one δ
  have hδ1 : δ ≠ 1 := fun h => hr.ne_one (by rw [h, orderOf_one] at hδ; exact hδ.symm)
  apply orderOf_eq_prime (fixSubfieldRestrict_pow_eq_one σ hδr)
  intro hfix
  apply hδ1
  apply CFSG.StandardType.RootDetectTwE6.eq_one_of_fixed_of_pow_eq_one
    σ.toRingHom hσ (apply_apply_comm_of_finite δ σ) _ (hr.odd_of_ne_two hr2) hδr
  intro x hx
  have h := DFunLike.congr_fun hfix (⟨x, hx⟩ : fixSubfield σ)
  exact congrArg Subtype.val h


theorem uc22s2114r4f_twistedE6_root_frame {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) :
    ∃ j : Fin 4 → SpecialLinearGroup (Fin 2) (fixSubfield σ) →* twistedE6RootGroup K σ,
      (∀ i, Function.Injective (j i)) ∧
      (∀ i l, i ≠ l → ∀ A B, Commute (j i A) (j l B)) ∧
      ∀ i (δ : K ≃+* K) (A : SpecialLinearGroup (Fin 2) (fixSubfield σ)),
        fieldActor σ δ (j i A) =
          j i (SpecialLinearGroup.map (fixSubfieldRestrict δ σ).toRingHom A) := by
  have hroot : ∀ i, IsRoot TwistTag.E6.tag (frameRoot i) := fun i =>
    RootOps.isRootB_iff.1 (e6_four_roots_check.1 i)
  have hρ : ∀ i, permLattice TwistTag.E6.perm (frameRoot i) = frameRoot i := by
    decide +kernel
  let R : Fin 4 → SpecialLinearGroup (Fin 2) (fixSubfield σ) →* ModGL TwistTag.E6.tag K :=
    fun i => (rootSL2 TwistTag.E6.tag K (frameRoot i)).comp
      (SpecialLinearGroup.map (fixSubfield σ).subtype)
  have hmem : ∀ i A, R i A ∈ twistedE6RootGroup K σ := by
    intro i
    have hle : closure (Set.range (sl2Upper (fixSubfield σ)) ∪
        Set.range (sl2Lower (fixSubfield σ))) ≤ (twistedE6RootGroup K σ).comap (R i) := by
      apply (closure_le _).2
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change rootSL2 TwistTag.E6.tag K (frameRoot i)
          (SpecialLinearGroup.map (fixSubfield σ).subtype (uSL c)) ∈ twistedE6RootGroup K σ
        rw [E6GraphLevi.map_uSL, rootSL2_uSL_of_charTwo (hroot i)]
        exact CFSG.SeitzReduction.pinnedX_mem_graphFixedRootGroup_of_fixed σ.toRingHom
          (hroot i) (hρ i) c.2
      · change rootSL2 TwistTag.E6.tag K (frameRoot i)
          (SpecialLinearGroup.map (fixSubfield σ).subtype (vSL c)) ∈ twistedE6RootGroup K σ
        rw [E6GraphLevi.map_vSL, rootSL2_vSL_of_charTwo (hroot i)]
        exact CFSG.SeitzReduction.pinnedX_mem_graphFixedRootGroup_of_fixed σ.toRingHom
          (IsRoot.neg (hroot i)) (by rw [permLattice_neg, hρ]) c.2
    rw [sl2_closure_upper_lower] at hle
    exact fun A => hle (mem_top A)
  let j : Fin 4 → SpecialLinearGroup (Fin 2) (fixSubfield σ) →* twistedE6RootGroup K σ :=
    fun i => (R i).codRestrict _ (hmem i)
  have hj : ∀ i, Function.Injective (j i) := fun i A B h =>
    CFSG.RankThree.PartOne.KLAY.map_injective_SL2 (fixSubfield σ).subtype
      ((even_Chevalley_pinned_root_SL2_maps TwistTag.E6.tag K (hroot i)).1
        (congrArg Subtype.val h))
  have hc : ∀ i l, i ≠ l → ∀ A B, Commute (j i A) (j l B) := by
    intro i l hil A B
    obtain ⟨h0, hp, hm⟩ := e6_four_roots_check.2 i l hil
    have hnot : ∀ {v : Fin TwistTag.E6.tag.rank → ℤ},
        RootOps.isRootB TwistTag.E6.tag v = false → ¬ IsRoot TwistTag.E6.tag v :=
      fun hv hr => by rw [← RootOps.isRootB_iff, hv] at hr; exact Bool.false_ne_true hr
    exact Subtype.ext (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation
      TwistTag.E6.tag K (hroot i) (hroot l) h0 (hnot hp) (hnot hm)
      _ ⟨_, rfl⟩ _ ⟨_, rfl⟩)
  refine ⟨j, hj, hc, ?_⟩
  intro i δ A
  apply Subtype.ext
  change Units.map (entrywiseHom δ.toRingHom)
      (rootSL2 TwistTag.E6.tag K (frameRoot i)
        (SpecialLinearGroup.map (fixSubfield σ).subtype A)) = _
  rw [entrywise_rootSL2_of_field]
  change rootSL2 TwistTag.E6.tag K (frameRoot i)
      (SpecialLinearGroup.map δ.toRingHom (SpecialLinearGroup.map (fixSubfield σ).subtype A)) =
    rootSL2 TwistTag.E6.tag K (frameRoot i)
      (SpecialLinearGroup.map (fixSubfield σ).subtype
        (SpecialLinearGroup.map (fixSubfieldRestrict δ σ).toRingHom A))
  congr 1

theorem uc22s2114r4f_exists_fixed_three_twistedE6 {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ δ : K ≃+* K) :
    ∃ X : Subgroup (twistedE6RootGroup K σ), IsPGroup 3 X ∧ ¬ IsCyclic X ∧
      ∀ x ∈ X, fieldActor σ δ x = x := by
  obtain ⟨j, hj, hc, hfield⟩ := uc22s2114r4f_twistedE6_root_frame σ
  obtain ⟨X, hX, hcard, hXN⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6CartanRankFourAux.exists_elemAbelian_three_pow
      j hj hc
  have hfix : X ≤ fixSubgroup (fieldActor σ δ) := hXN _ fun i => by
    rw [mem_fixSubgroup, hfield,
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc.map_c3]
  exact ⟨X, hX.isPGroup, PartTwo.s16c7_not_isCyclic_of_elemAbelian Nat.prime_three
    hX (by rw [hcard]; norm_num), fun x hx => hfix hx⟩

theorem uc22s2114r4f_exists_fpf_twistedE6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (δ : K ≃+* K) (hδ : orderOf δ = r) :
    ∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* twistedE6RootGroup K σ, Function.Injective ι ∧
            ∀ a, fieldActor σ δ (ι a) = ι (κ a) := by
  have hk : Nat.card (fixSubfield σ) = 2 ^ f := card_eqLocusField_of_pow Nat.prime_two hf hK hσ
  have hσσ : ∀ c, σ (σ c) = c :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.theta_theta_of_card (θ := σ.toRingHom) hK hσ
  have hδk := uc22s2114r4f_twistedE6_restrict_order σ δ hσσ hr (by omega) hδ
  obtain ⟨q, hq, hq7, hqr, -, -, Q, _, _, hQ, τ, hτ, jQ, hjQ, hδQ⟩ :=
    uc22s2114r4f_exists_fpf_nonsplit_sl2 hf hk hr hr5 (fixSubfieldRestrict δ σ) hδk
  obtain ⟨j, hj, hc, hfield⟩ := uc22s2114r4f_twistedE6_root_frame σ
  let ρ := (j 0).noncommCoprod (j 1) (hc 0 1 (by decide))
  have hρ : Function.Injective ρ :=
    CFSG.Timmesfeld.LevisExtras.injective_noncommCoprod (hj 0) (hj 1) (hc 0 1 (by decide))
  let A := Q × Q
  let κ : A →* A := τ.prodMap τ
  have hAp : IsPGroup q A := IsPGroup.of_card (n := 2) (by
    change Nat.card (Q × Q) = q ^ 2
    rw [Nat.card_prod, hQ]
    ring)
  have hAc : ¬ IsCyclic A := by
    intro hc
    have h := (Group.isCyclic_prod_iff.1 hc).2.2
    simp only [hQ] at h
    exact hq.ne_one (Nat.coprime_self q |>.1 h)
  have hκ : ∀ a : A, κ a = a → a = 1 := fun a ha =>
    Prod.ext (hτ a.1 (congrArg Prod.fst ha)) (hτ a.2 (congrArg Prod.snd ha))
  let ι : A →* twistedE6RootGroup K σ := ρ.comp (jQ.prodMap jQ)
  have hι : Function.Injective ι := hρ.comp (by
    intro a b hab
    exact Prod.ext (hjQ (congrArg Prod.fst hab)) (hjQ (congrArg Prod.snd hab)))
  refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, ?_⟩
  intro a
  change fieldActor σ δ (j 0 (jQ a.1) * j 1 (jQ a.2)) =
    j 0 (jQ (τ a.1)) * j 1 (jQ (τ a.2))
  rw [map_mul, hfield, hfield, hδQ, hδQ]

theorem uc22s2114r4f_twistedE6_field_descent {Y : Type} [Group Y] [Finite Y] {f r : ℕ}
    (hY : LieModel Y .twistedE6 0 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      ∃ σ : K ≃+* K, Nat.card K = (2 ^ f) ^ 2 ∧ (∀ c, σ c = c ^ 2 ^ f) ∧
        ∃ δ : K ≃+* K, orderOf δ = r ∧
          ∃ e : Y ≃* twistedE6RootGroup K σ, ∀ x, e (θ x) = fieldActor σ δ (e x) := by
  obtain ⟨-, hchev⟩ := (LieModel.chevalleyExceptional_iff (by decide)).1 hY
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e0⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hchev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (by
    rw [hK, ← pow_mul] : Nat.card K = 2 ^ (f * 2))
  let α : MulAut (twistedE6RootGroup K σ) := MulAut.congr e0 θ
  have hα : orderOf α = r :=
    (orderOf_injective (MulAut.congr e0).toMonoidHom (MulAut.congr e0).injective θ).trans hθ
  have hαout : α ∉ (MulAut.conj : twistedE6RootGroup K σ →*
      MulAut (twistedE6RootGroup K σ)).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e0.symm x, (MulAut.congr e0).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e0.apply_symm_apply, hx]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, -, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two
      hY.admissible.2.1 K hK σ hσ
  let αB : (⊤ : Subgroup (MulAut (twistedE6RootGroup K σ))) := ⟨α, mem_top _⟩
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm f 2]
  obtain ⟨hδ, hrf, ⟨ψ, hψ⟩, -⟩ :=
    twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial Nat.prime_two
      hY.admissible.2.1 K hK' σ hσ Θ hΘ hr (by omega) ⊤ le_top αB hαout
      (by simpa [αB] using hα)
  refine ⟨hrf, K, inferInstance, inferInstance, inferInstance, σ, hK, hσ, Θ α, hδ,
    e0.trans ψ, ?_⟩
  intro x
  have h := congrArg (fun η : MulAut (twistedE6RootGroup K σ) => η (ψ (e0 x))) hψ
  change ψ (α (ψ.symm (ψ (e0 x)))) = fieldActor σ (Θ α) (ψ (e0 x)) at h
  rw [MulEquiv.symm_apply_apply] at h
  change ψ (e0 (θ (e0.symm (e0 x)))) = _ at h
  rw [MulEquiv.symm_apply_apply] at h
  exact h

theorem uc22s2114r4f_fieldSubgroups_of_twistedE6 {Y : Type} [Group Y] [Finite Y] {f r : ℕ}
    (hY : LieModel Y .twistedE6 0 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧
    (∃ X : Subgroup Y, IsPGroup 3 X ∧ ¬ IsCyclic X ∧ ∀ x ∈ X, θ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* Y, Function.Injective ι ∧ ∀ a, θ (ι a) = ι (κ a)) := by
  obtain ⟨hrf, K, _, _, _, σ, hK, hσ, δ, hδ, e, he⟩ :=
    uc22s2114r4f_twistedE6_field_descent hY hr hr5 θ hθ hout
  have hε : ∀ x, θ (e.symm x) = e.symm (fieldActor σ δ x) := by
    intro x
    apply e.injective
    simpa only [MulEquiv.apply_symm_apply] using he (e.symm x)
  refine ⟨hrf, ?_, ?_⟩
  · obtain ⟨X, hXp, hXc, hfix⟩ := uc22s2114r4f_exists_fixed_three_twistedE6 σ δ
    let j : X →* Y := e.symm.toMonoidHom.comp X.subtype
    have hj : Function.Injective j := e.symm.injective.comp X.subtype_injective
    let η := MonoidHom.ofInjective hj
    refine ⟨j.range, hXp.of_equiv η, fun hc => hXc (η.isCyclic.2 hc), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hε x).trans (congrArg e.symm (hfix x x.2))
  · obtain ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hσι⟩ :=
      uc22s2114r4f_exists_fpf_twistedE6 hY.admissible.2.1 hK σ hσ hr hr5 δ hδ
    refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ,
      e.symm.toMonoidHom.comp ι, e.symm.injective.comp hι, ?_⟩
    intro a
    exact (hε (ι a)).trans (congrArg e.symm (hσι a))

theorem uc22s2114r4f_four_le_pRank_three_twistedE6 {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {f : ℕ}
    (hX : LieModel (BarInf L) .twistedE6 0 2 f) : 4 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨-, hchev⟩ := (LieModel.chevalleyExceptional_iff (by decide)).1 hX
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e0⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hchev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (by
    rw [hK, ← pow_mul] : Nat.card K = 2 ^ (f * 2))
  have hcl := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two
    hX.admissible.2.1 K hK σ.toRingHom hσ).2.2.1
  have h3 : (3 : fixSubfield σ) ≠ 0 := by
    intro h
    have h2 : (2 : fixSubfield σ) = 0 := CharTwo.two_eq_zero
    have h1 : (1 : fixSubfield σ) = 0 := by linear_combination h - h2
    exact one_ne_zero h1
  obtain ⟨h, w, hcomm, hord, hinv, hfix⟩ :=
    CFSG.AGLEmbedding.KFactProofs.CoverE6.exists_inverter_data_twisted
      (fixSubfield σ).subtype σ.toRingHom (fun c => c.2) hcl h3
  let e := eb.symm.trans e0
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (center (Bar2 L)))
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)]
  exact CFSG.AGLEmbedding.KFactProofs.CoverE6.four_le_pRank_of_inverter_data π
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (fun y hy => by
      have hπ : π y = 1 := MonoidHom.mem_ker.1 hy
      apply (QuotientGroup.eq_one_iff (N := center (Bar2 L)) y).1
      apply e.injective
      exact hπ.trans (map_one e).symm)
    h w hcomm hord hinv hfix

section Multiplier


theorem uc22s2114r4f_card_center_twistedE6_dvd_three {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f)
    (hX : LieModel (BarInf L) .twistedE6 0 2 f) : Nat.card (center (Bar2 L)) ∣ 3 := by
  have hm : TwistedChevalleyModel (BarInf L) .E6 (2 ^ f) :=
    (hX.chevalleyExceptionalModel (by decide)).2
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
  have hq3 : 3 ≤ 2 ^ f := (by norm_num : 3 ≤ 2 ^ 3).trans
    (Nat.pow_le_pow_right (by norm_num) hf)
  obtain ⟨em⟩ := (CFSG.LieType.Steinberg.CentralExt.GriessExceptional.twistedE6_hopfMultiplier
    hq3 hK hσ).2
  have hcardM : Nat.card (griessHopfMultiplier
      (DerivedCentralQuotient (twistedFixedGroup .E6 K σ))) = Nat.gcd 3 (2 ^ f + 1) :=
    (Nat.card_congr em.toEquiv).trans (by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod])
  have hcard : Nat.card (griessHopfMultiplier (BarInf L)) = Nat.gcd 3 (2 ^ f + 1) :=
    (Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv).trans hcardM
  have : Finite (griessHopfMultiplier (BarInf L)) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact Nat.gcd_ne_zero_left (by decide))
  have hq : CFSG.IsQuasisimple (Bar2 L) :=
    ⟨⟨hL.2.2.1⟩, hL.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2⟩
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hq eb.symm
  rw [hcard] at hd
  exact hd.trans (Nat.gcd_dvd_left _ _)

theorem uc22s2114r4f_not_dvd_radical_twistedE6 {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f)
    (hX : LieModel (BarInf L) .twistedE6 0 2 f) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    ¬ q ∣ Nat.card (CFSG.solvableRadical L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [uc22s2114r3f_card_solvableRadical hL]
  intro h
  rcases hq.dvd_mul.1 h with h2 | h3
  · obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 L)).exists_card_eq
    rw [ha] at h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2))
  · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1
      (h3.trans (uc22s2114r4f_card_center_twistedE6_dvd_three hL hf hX)))

theorem uc22s2114r4f_fieldDataBody_twistedE6 {G : Type} [Group G] [Finite G]
    {D : Data G} (hSg : UC6S846.SigmaStd D) {L : Subgroup G} (hL : L ∈ calC D.M)
    {f : ℕ} (hX : LieModel (BarInf L) .twistedE6 0 2 f) {b : G}
    (hbL : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hbr : orderOf b = r) (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    (¬ r ∣ Nat.card (CFSG.solvableRadical L)) ∧
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ D.sig ∧
      ∃ X : Subgroup (BarInf L), IsPGroup p X ∧ ¬ IsCyclic X ∧
        ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ¬ q ∣ Nat.card (CFSG.solvableRadical L) ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) := by
  have : Fact r.Prime := ⟨hr⟩
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have hb : (⟨b, hbL⟩ : normalizer (L : Set G)) ^ r = 1 :=
      Subtype.ext (hbr ▸ pow_orderOf_eq_one b)
    rw [hb, map_one]
  have hθ1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1 := fun h1 => hin ⟨1, by rw [map_one, h1]⟩
  obtain ⟨hrf, ⟨X, hXp, hXc, hXfix⟩, ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩ :=
    uc22s2114r4f_fieldSubgroups_of_twistedE6 hX hr hr5 (inducedBarInfAutHom L ⟨b, hbL⟩)
      (orderOf_eq_prime hθr hθ1) hin
  have hf : 3 ≤ f := by
    have := Nat.le_of_dvd (by have := hX.admissible.2.1; omega : 0 < f) hrf
    omega
  exact ⟨uc22s2114r4f_not_dvd_radical_twistedE6 hL hf hX hr (by omega) (by omega),
    ⟨3, Nat.prime_three, by norm_num, hSg.four_mem 3 Nat.prime_three (by norm_num)
      ((uc22s2114r4f_four_le_pRank_three_twistedE6 hL hX).trans
        (CFSG.SectionRank.pRank_mono (by norm_num) hL.1.le)), X, hXp, hXc, hXfix⟩,
    ⟨q, hq, hq7, hqr, uc22s2114r4f_not_dvd_radical_twistedE6 hL hf hX hq (by omega) (by omega),
      A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩

end Multiplier

end CFSG.LocalAnalysis.UniquenessCase.UC22
