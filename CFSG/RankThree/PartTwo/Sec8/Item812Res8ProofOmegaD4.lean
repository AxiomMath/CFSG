module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofGammaInner
public import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofArith
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofTransport
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4
import CFSG.RankThree.PartTwo.KFacts.K71Item89

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projSL)

namespace Item812Res8

theorem autFix_conj_eq_centralizer {M : Type*} [Group M] (w : M) :
    Sec4.autFix (MulAut.conj w) = Subgroup.centralizer ({w} : Set M) := by
  ext z
  rw [Sec4.mem_autFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc z * w = w * z * w⁻¹ * w := by rw [h]
      _ = w * z := by group
  · intro h
    rw [← h]
    group

noncomputable def perfectResidualCongr {A B : Type*} [Group A] [Group B] (φ : A ≃* B) :
    perfectResidual A ≃* perfectResidual B :=
  ((perfectResidual A).equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (KFacts.perfectResidual_map_mulEquiv φ))

noncomputable def inSubgroupPerfectResidualEquiv {H : Type} [Group H] (C : Subgroup H) :
    inSubgroup perfectResidual C ≃* perfectResidual C :=
  ((perfectResidual C).equivMapOfInjective C.subtype C.subtype_injective).symm

end Item812Res8


@[expose] def KF89D4FixInv : Prop :=
  ∀ (m : ℕ), Odd m → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ m) ^ 3 → (∀ c, σ c = c ^ 2 ^ m) →
    ∀ (τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      τ ^ 3 = 1 → ¬ IsInnerAut τ → τ w = w → w ^ 3 = 1 →
      Nonempty (perfectResidual
          (Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ≃*
        projSL 2 (GaloisField 2 (3 * m))) →
        ∃ v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          v ≠ 1 ∧ v ^ 2 = 1 ∧ τ v = v ∧ v * w = w * v


namespace Item812Res8

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {d : G}

theorem not_outer_of_trialityD4_odd {m : ℕ} (hodd : Odd m)
    (hL : IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) m)
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (hres : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) L)) =
      2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1)) :
    ¬ InducesOuterTheta d L := by
  intro hout
  obtain ⟨hm1, K, _, _, σ, hK, hσ, ⟨E⟩⟩ := Item812Res7.exists_trialityD4_model hL
  set τ := inducedAutHom L E ⟨d, hdN⟩ with hτ
  have hτ3 : τ ^ 3 = 1 := inducedAutHom_pow_eq_one L E hdN hd3
  have hτin : ¬ IsInnerAut τ := (not_isInnerAut_inducedAutHom_iff L E hdN).mpr hout
  have hCτ : barCentralizer (Subgroup.zpowers d) L ≃* Sec4.autFix τ :=
    (MulEquiv.subgroupCongr (barCentralizer_zpowers_eq_autFix hdN)).trans
      (autFixCongrEquiv E _).symm
  have hq := two_le_two_pow hm1
  by_cases hstd : Sec4.IsStdGraphFieldConj σ τ
  · obtain ⟨β, hβ⟩ := hstd
    obtain ⟨k, _, _, hk, ⟨φ⟩⟩ :=
      isoGTwoEven_barCentralizer_of_conj_fieldActor hm1 hK hσ E hdN β hβ
    exact card_perfectResidual_g2_ne hm1 hk
      ((card_inSubgroup_perfectResidual_eq φ).symm.trans hres)
  · rcases inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds m hodd K σ
      hK hσ τ hτ3 hτin with hs | ⟨-, -, -, -, -, -, hP⟩
    · exact hstd hs
    · exact false_of_card_dvd hres
        (card_of_isoPGUThree hm1 (Item82OneProof.isoPGUThree_of_mulEquiv hCτ hP))
        (not_dvd_unitary hq)

end Item812Res8

open Item812Res8

theorem pair89OmegaD4_of (h45 : Sec4.Item4_5) (hS : Item86ResProof.KF86D4ShiftConj)
    (hV : KF89D4FixInv) : Pair89OmegaD4 := by
  intro G _ _ A c L a b X n h p hp m hodd hD
  classical
  obtain ⟨e, Le⟩ := p
  obtain ⟨heA, he1, hLe, ⟨x, hxA, hxk⟩, -, ⟨d, m', hdm⟩⟩ := hp
  have hAel := h.mem_partTwoF.1
  have h3 : ∀ u ∈ A, u ^ 3 = 1 := hAel.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using h3 u u.2)⟩
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hz e heA)
  have hAN : A ≤ Subgroup.normalizer (Le : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp (h3 e heA) he1
      hA3 hAe Le hLe
  have hdA := hdm.1
  have hxN := hAN hxA
  have hdN := hAN hdA
  have hd3 := h3 d hdA
  have hx3 := h3 x hxA
  have hm1 : 1 ≤ m := hodd.pos
  have hm'1 : 1 ≤ m' := Item86ResProof.one_le_of_isGammaIndex hdm
  have hmm : m' = m := Item86ResProof.eq_of_isGammaType hm'1 hm1
    (Item86ResProof.isGammaType_of_isGammaIndex hdm) (Or.inr (Or.inl hD))
  subst hmm
  have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq hdN
    ⟨1, by rw [pow_one]; exact hd3⟩
  obtain ⟨-, -, -, hcase⟩ := Item87Proof.isGammaIndex_cases hdm
  obtain ⟨ι⟩ : Nonempty (imageModTheta Le
      (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer {d})) ≃*
        projSL 2 (GaloisField 2 (3 * m'))) := by
    rcases hcase with ⟨hRee, -⟩ | ⟨-, hι⟩
    · exact ((Item86ResProof.sigF4_of_reeF4 hm'1 hRee).false_of_sigD4
        (Item86ResProof.sigD4_of_isoTrialityD4 hm'1 hD) hm'1).elim
    · exact hι
  have hres : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) Le)) =
      2 ^ (3 * m') * ((2 ^ (3 * m')) ^ 2 - 1) := by
    rw [← himg, Nat.card_congr ι.toEquiv]
    exact Item87Proof.card_projSL_two_three hm'1
  obtain ⟨-, K, _, _, σ, hK, hσ, ⟨E⟩⟩ := Item812Res7.exists_trialityD4_model hD
  have hinj := Item812Res7.conj_injective_of_center_trivial
    (exceptional_fixed_center_trivial TwistTag.D4 K σ)
  have hxout : InducesOuterTheta x Le := by
    rcases hxk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
  have hτ3 : inducedAutHom Le E ⟨x, hxN⟩ ^ 3 = 1 := inducedAutHom_pow_eq_one Le E hxN hx3
  have hτin : ¬ IsInnerAut (inducedAutHom Le E ⟨x, hxN⟩) :=
    (not_isInnerAut_inducedAutHom_iff Le E hxN).mpr hxout
  have hdin : ¬ InducesOuterTheta d Le := not_outer_of_trialityD4_odd hodd hD hdN hd3 hres
  have hdinn : IsInnerAut (inducedAutHom Le E ⟨d, hdN⟩) := by
    by_contra hni
    exact hdin ((not_isInnerAut_inducedAutHom_iff Le E hdN).mp hni)
  obtain ⟨w, hw⟩ := hdinn
  have hxd' : (⟨x, hxN⟩ : Subgroup.normalizer (Le : Set G)) * ⟨d, hdN⟩ = ⟨d, hdN⟩ * ⟨x, hxN⟩ :=
    Subtype.ext (hcomm x hxA d hdA)
  have hττc : inducedAutHom Le E ⟨x, hxN⟩ * MulAut.conj w =
      MulAut.conj w * inducedAutHom Le E ⟨x, hxN⟩ := by
    have h1 := congrArg (inducedAutHom Le E) hxd'
    rw [map_mul, map_mul, ← hw] at h1
    exact h1
  have hw3 : w ^ 3 = 1 := by
    apply hinj
    rw [map_pow MulAut.conj w 3, hw, map_one]
    exact inducedAutHom_pow_eq_one Le E hdN hd3
  have hCw : barCentralizer (Subgroup.zpowers d) Le ≃*
      Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    ((MulEquiv.subgroupCongr (barCentralizer_zpowers_eq_autFix hdN)).trans
      (autFixCongrEquiv E _).symm).trans
      (MulEquiv.subgroupCongr (by
        rw [show MulAut.congr E (thetaQuotMulAut Le (compAction Le ⟨d, hdN⟩)) =
          inducedAutHom Le E ⟨d, hdN⟩ from rfl, ← hw]
        exact autFix_conj_eq_centralizer w))
  have hres' : Nonempty (perfectResidual
      (Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ≃*
        projSL 2 (GaloisField 2 (3 * m'))) := by
    refine ⟨(perfectResidualCongr hCw).symm.trans ?_⟩
    refine (inSubgroupPerfectResidualEquiv _).symm.trans ?_
    exact (MulEquiv.subgroupCongr himg.symm).trans ι
  have hw1 : w ≠ 1 := by
    rintro rfl
    have hC : barCentralizer (Subgroup.zpowers d) Le = ⊤ := by
      rw [barCentralizer_zpowers_eq_autFix hdN]
      refine eq_top_iff.mpr fun z _ => ?_
      rw [Sec4.mem_autFix]
      have h1 : MulAut.congr E (thetaQuotMulAut Le (compAction Le ⟨d, hdN⟩)) = 1 := by
        rw [show MulAut.congr E (thetaQuotMulAut Le (compAction Le ⟨d, hdN⟩)) =
          inducedAutHom Le E ⟨d, hdN⟩ from rfl, ← hw, map_one]
      have h2 : thetaQuotMulAut Le (compAction Le ⟨d, hdN⟩) = 1 := by
        apply (MulAut.congr E).injective
        rw [h1, map_one]
      rw [h2]
      rfl
    have hperf : Group.IsPerfect (Le ⧸ aschbacherSolvableCore 3 Le) :=
      (Sec6.isQuasisimple_of_mem_thetaComponentsAt hLe).1
    have hcard : Nat.card (Le ⧸ aschbacherSolvableCore 3 Le) =
        2 ^ (3 * m') * ((2 ^ (3 * m')) ^ 2 - 1) := by
      rw [← hres, hC, inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        KFacts.perfectResidual_eq_top_of_isPerfect
          (hperf.ofSurjective (f := (Subgroup.topEquiv).symm.toMonoidHom)
            (MulEquiv.surjective _)),
        Subgroup.card_top, Subgroup.card_top]
    have hodd2 : Odd ((2 ^ (3 * m')) ^ 2 - 1) := by
      have h1 : 1 ≤ (2 ^ (3 * m')) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      have h2 : Even ((2 ^ (3 * m')) ^ 2) := by
        rw [← pow_mul]
        exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      exact Nat.Even.sub_odd h1 h2 odd_one
    exact (Item86ResProof.sigD4_of_isoTrialityD4 hm'1 hD).profile.ne_of_ne hodd2
      (by omega) hcard
  obtain ⟨v, hv1, hv2, hτv, hvw⟩ := hV m' hodd K σ hK hσ _ w hτ3 hτin
    (Item812Res7.apply_eq_of_commute_conj hinj hττc) hw3 hres'
  have hclass : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (Le : Set G)),
      Sec4.IsStdGraphFieldConj σ (inducedAutHom Le E ⟨y, hy⟩) →
        IsoGTwoEven (barCentralizer (Subgroup.zpowers y) Le) m' := by
    rintro y hy ⟨β, hβ⟩
    exact isoGTwoEven_barCentralizer_of_conj_fieldActor hm'1 hK hσ E hy β hβ
  have hgf : ∀ y ∈ A, InducesOuterTheta y Le →
      KFacts.InducesStdKind Le y .field ∨ KFacts.InducesStdKind Le y .graphField :=
    fun y hy hyout => Or.inr (KFacts.InducesStdKind.triality m' hm'1 _ hK σ hσ
      (KFacts.inducesKindTriality_graphField hm'1 hK hσ Le (h3 y hy) hyout E))
  rcases Item812Res7.isStdGraphFieldConj_or_shift hS hK hσ hτ3 hτin (orderOf_eq_prime hw3 hw1)
    (Item812Res7.apply_eq_of_commute_conj hinj hττc) hv1 hv2 hτv hvw with hstd | ⟨ε, -, hstd⟩
  · exact ⟨x, hxA, hxk, hclass x hxN hstd⟩
  · have hεA : x * d ^ ε ∈ A := A.mul_mem hxA (A.zpow_mem hdA ε)
    have hεN : x * d ^ ε ∈ Subgroup.normalizer (Le : Set G) := hAN hεA
    have hind : inducedAutHom Le E ⟨x * d ^ ε, hεN⟩ =
        inducedAutHom Le E ⟨x, hxN⟩ * MulAut.conj w ^ ε := by
      have h1 : (⟨x * d ^ ε, hεN⟩ : Subgroup.normalizer (Le : Set G)) =
          ⟨x, hxN⟩ * ⟨d, hdN⟩ ^ ε := Subtype.ext (by simp)
      rw [h1, map_mul, map_zpow, ← hw]
    have hstd' : Sec4.IsStdGraphFieldConj σ (inducedAutHom Le E ⟨x * d ^ ε, hεN⟩) := by
      rw [hind]
      exact hstd
    have hεout : InducesOuterTheta (x * d ^ ε) Le :=
      (not_isInnerAut_inducedAutHom_iff Le E hεN).mp
        (not_isInnerAut_of_isStdGraphFieldConj hm'1 hK hσ hstd')
    exact ⟨x * d ^ ε, hεA, hgf _ hεA hεout, hclass _ hεN hstd'⟩

end CFSG.RankThree.PartTwo.Sec8
