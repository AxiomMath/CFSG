module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofOmega
public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofOmegaD4
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofArith
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofTransport
import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofD4Even
import CFSG.RankThree.PartTwo.KFacts.K71Item89

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projSL)


namespace Item812Res11

theorem d4_trichotomy {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {α γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hα3 : α ^ 3 = 1)
    (hα : ¬ IsInnerAut α) (hγ3 : γ ^ 3 = 1) :
    IsInnerAut γ ∨ IsInnerAut (γ * α⁻¹) ∨ IsInnerAut (γ * α) := by
  classical
  have hpart : ∀ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      (MulAut.conj g * fieldActor σ δ) ^ 3 = 1 → δ ^ 3 = 1 := by
    intro g δ h3
    rw [conj_mul_pow_three] at h3
    apply (isInnerAut_fieldActor_iff hf hK hσ).mp
    have e : fieldActor (t := TwistTag.D4) σ (δ ^ 3) =
        (MulAut.conj (g * fieldActor σ δ g * fieldActor σ δ (fieldActor σ δ g)))⁻¹ := by
      rw [← eq_inv_of_mul_eq_one_right h3]
      exact map_pow (fieldActorHom (t := TwistTag.D4) σ) δ 3
    rw [e, ← map_inv]
    exact ⟨_, rfl⟩
  obtain ⟨g, δ, rfl⟩ := exists_conj_mul_fieldActor hf hK hσ α
  obtain ⟨h, ε, rfl⟩ := exists_conj_mul_fieldActor hf hK hσ γ
  have hδ3 := hpart g δ hα3
  have hε3 := hpart h ε hγ3
  by_cases hε1 : ε = 1
  · left
    rw [hε1, fieldActor_one, mul_one]
    exact ⟨h, rfl⟩
  right
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    rw [fieldActor_one, mul_one] at hα
    exact hα ⟨g, rfl⟩
  have hδo : orderOf δ = 3 := orderOf_eq_prime hδ3 hδ1
  have hεo : orderOf ε = 3 := orderOf_eq_prime hε3 hε1
  have hK' : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, hδf⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) hK' hδo
  obtain ⟨-, hεf⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) hK' hεo
  have h3 : 3 * f / 3 = f := by omega
  have h23 : 2 * (3 * f) / 3 = 2 * f := by omega
  rw [h3, h23] at hδf hεf
  have : Fintype K := Fintype.ofFinite K
  have hpn : ∀ (c : K) (a b : ℕ), a + b = 3 * f → (c ^ 2 ^ a) ^ 2 ^ b = c := by
    intro c a b hab
    rw [← pow_mul, ← pow_add, hab, ← hK', Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hcases : ε = δ ∨ ε * δ = 1 := by
    rcases hδf with h1 | h1 <;> rcases hεf with h2 | h2
    · left
      ext c
      rw [h1, h2]
    · right
      ext c
      rw [RingAut.mul_apply, h1, h2, RingAut.one_apply, hpn c f (2 * f) (by omega)]
    · right
      ext c
      rw [RingAut.mul_apply, h1, h2, RingAut.one_apply, hpn c (2 * f) f (by omega)]
    · left
      ext c
      rw [h1, h2]
  rcases hcases with heq | hinv
  · left
    subst heq
    refine ⟨h * g⁻¹, ?_⟩
    rw [map_mul, map_inv]
    group
  · right
    refine ⟨h * fieldActor σ ε g, ?_⟩
    have e1 : fieldActor (t := TwistTag.D4) σ ε * MulAut.conj g =
        MulAut.conj (fieldActor σ ε g) * fieldActor σ ε := by
      rw [← mul_mulAutConj_mul_inv, inv_mul_cancel_right]
    have e2 : fieldActor (t := TwistTag.D4) σ ε * fieldActor σ δ = 1 := by
      rw [← fieldActor_mul, hinv, fieldActor_one]
    rw [map_mul]
    symm
    calc MulAut.conj h * fieldActor σ ε * (MulAut.conj g * fieldActor σ δ) =
        MulAut.conj h * (fieldActor σ ε * MulAut.conj g) * fieldActor σ δ := by
          simp only [mul_assoc]
      _ = MulAut.conj h * (MulAut.conj (fieldActor σ ε g) * fieldActor σ ε) *
          fieldActor σ δ := by rw [e1]
      _ = MulAut.conj h * MulAut.conj (fieldActor σ ε g) *
          (fieldActor σ ε * fieldActor σ δ) := by simp only [mul_assoc]
      _ = MulAut.conj h * MulAut.conj (fieldActor σ ε g) := by rw [e2, mul_one]

end Item812Res11


@[expose] def KF89D4FixInvEven : Prop :=
  ∀ (m : ℕ), Even m → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ m) ^ 3 → (∀ c, σ c = c ^ 2 ^ m) →
    ∀ (τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      τ ^ 3 = 1 → ¬ IsInnerAut τ → τ w = w → w ^ 3 = 1 →
      Nonempty (perfectResidual
          (Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ≃*
        projSL 2 (GaloisField 2 (3 * m))) →
        ∃ v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          v ≠ 1 ∧ v ^ 2 = 1 ∧ τ v = v ∧ v * w = w * v

namespace Item812Res11

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {d : G}

open Item812Res8 in
theorem not_outer_of_trialityD4 {m : ℕ}
    (hL : IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) m)
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (hres : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) L)) =
      2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1)) :
    ¬ InducesOuterTheta d L := by
  intro hout
  have hEv : KF89D4SecondCentEven := kF89D4SecondCentEven_of_y0 kF89D4SecondCentY0Even_holds
  obtain ⟨hm1, K, _, _, σ, hK, hσ, ⟨E⟩⟩ := Item812Res7.exists_trialityD4_model hL
  set τ := inducedAutHom L E ⟨d, hdN⟩ with hτ
  have hτ3 : τ ^ 3 = 1 := inducedAutHom_pow_eq_one L E hdN hd3
  have hτin : ¬ IsInnerAut τ := (not_isInnerAut_inducedAutHom_iff L E hdN).mpr hout
  have hCτ : barCentralizer (Subgroup.zpowers d) L ≃* Sec4.autFix τ :=
    (MulEquiv.subgroupCongr (Sec4.barCentralizer_zpowers_eq_autFix hdN)).trans
      (Sec4.autFixCongrEquiv E _).symm
  have hq := two_le_two_pow hm1
  by_cases hstd : Sec4.IsStdGraphFieldConj σ τ
  · obtain ⟨β, hβ⟩ := hstd
    obtain ⟨k, _, _, hk, ⟨φ⟩⟩ :=
      isoGTwoEven_barCentralizer_of_conj_fieldActor hm1 hK hσ E hdN β hβ
    exact card_perfectResidual_g2_ne hm1 hk
      ((card_inSubgroup_perfectResidual_eq φ).symm.trans hres)
  · rcases Nat.even_or_odd m with hev | hodd
    · have hP := hEv m hev hm1 K σ hK hσ τ hτ3 hτin hstd
      exact false_of_card_dvd hres
        (card_of_isoPGLThree hm1 (isoPGLThree_of_mulEquiv hCτ hP)) (not_dvd_linear hq)
    · rcases inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds m hodd K σ
        hK hσ τ hτ3 hτin with
        hs | ⟨-, -, -, -, -, -, hP⟩
      · exact hstd hs
      · exact false_of_card_dvd hres
          (card_of_isoPGUThree hm1 (Item82OneProof.isoPGUThree_of_mulEquiv hCτ hP))
          (not_dvd_unitary hq)

end Item812Res11

open Item812Res11 Item812Res8

theorem kF89OmegaFixInvD4_of (h45 : Sec4.Item4_5) (hFix : KF89D4FixInv)
    (hEven : KF89D4FixInvEven) : KF89OmegaFixInvD4 := by
  intro G _ _ A c L a b X n h p hp hDm w hw hwe
  classical
  obtain ⟨m, hD⟩ := hDm
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
  obtain ⟨hm1, K, _, _, σ, hK, hσ, ⟨E⟩⟩ := Item812Res7.exists_trialityD4_model hD
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hinj := Item812Res7.conj_injective_of_center_trivial hZ
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
  have hxout : InducesOuterTheta x Le := by
    rcases hxk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
  set ρ : A →* MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (inducedAutHom Le E).comp (Subgroup.inclusion hAN) with hρ
  have hρapply : ∀ y : A, ρ y = inducedAutHom Le E ⟨y, hAN y.2⟩ := fun y => rfl
  have hτ3 : ρ ⟨x, hxA⟩ ^ 3 = 1 := inducedAutHom_pow_eq_one Le E hxN hx3
  have hτin : ¬ IsInnerAut (ρ ⟨x, hxA⟩) := (not_isInnerAut_inducedAutHom_iff Le E hxN).mpr hxout
  have hdin : ¬ InducesOuterTheta d Le := not_outer_of_trialityD4 hD hdN hd3 hres
  have hdinn : IsInnerAut (inducedAutHom Le E ⟨d, hdN⟩) := by
    by_contra hni
    exact hdin ((not_isInnerAut_inducedAutHom_iff Le E hdN).mp hni)
  obtain ⟨w₀, hw₀⟩ := hdinn
  have hxd' : (⟨x, hxN⟩ : Subgroup.normalizer (Le : Set G)) * ⟨d, hdN⟩ = ⟨d, hdN⟩ * ⟨x, hxN⟩ :=
    Subtype.ext (hcomm x hxA d hdA)
  have hττc : ρ ⟨x, hxA⟩ * MulAut.conj w₀ = MulAut.conj w₀ * ρ ⟨x, hxA⟩ := by
    have h1 := congrArg (inducedAutHom Le E) hxd'
    rw [map_mul, map_mul, ← hw₀] at h1
    exact h1
  have hw₀3 : w₀ ^ 3 = 1 := by
    apply hinj
    rw [map_pow MulAut.conj w₀ 3, hw₀, map_one]
    exact inducedAutHom_pow_eq_one Le E hdN hd3
  have hCw : barCentralizer (Subgroup.zpowers d) Le ≃*
      Subgroup.centralizer ({w₀} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    ((MulEquiv.subgroupCongr (Sec4.barCentralizer_zpowers_eq_autFix hdN)).trans
      (Sec4.autFixCongrEquiv E _).symm).trans
      (MulEquiv.subgroupCongr (by
        rw [show MulAut.congr E (thetaQuotMulAut Le (compAction Le ⟨d, hdN⟩)) =
          inducedAutHom Le E ⟨d, hdN⟩ from rfl, ← hw₀]
        exact autFix_conj_eq_centralizer w₀))
  have hres' : Nonempty (perfectResidual
      (Subgroup.centralizer ({w₀} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ≃*
        projSL 2 (GaloisField 2 (3 * m'))) := by
    refine ⟨(perfectResidualCongr hCw).symm.trans ?_⟩
    refine (inSubgroupPerfectResidualEquiv _).symm.trans ?_
    exact (MulEquiv.subgroupCongr himg.symm).trans ι
  have hw₀1 : w₀ ≠ 1 := by
    rintro rfl
    apply hdin
    have h1 : inducedAutHom Le E ⟨d, hdN⟩ = 1 := by rw [← hw₀, map_one]
    exfalso
    have hC : barCentralizer (Subgroup.zpowers d) Le = ⊤ := by
      rw [Sec4.barCentralizer_zpowers_eq_autFix hdN]
      refine eq_top_iff.mpr fun z _ => ?_
      rw [Sec4.mem_autFix]
      have h2 : thetaQuotMulAut Le (compAction Le ⟨d, hdN⟩) = 1 := by
        apply (MulAut.congr E).injective
        rw [show MulAut.congr E (thetaQuotMulAut Le (compAction Le ⟨d, hdN⟩)) =
          inducedAutHom Le E ⟨d, hdN⟩ from rfl, h1, map_one]
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
  have hτw₀ : ρ ⟨x, hxA⟩ w₀ = w₀ := Item812Res7.apply_eq_of_commute_conj hinj hττc
  obtain ⟨v, hv1, hv2, hτv, hvw⟩ : ∃ v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      v ≠ 1 ∧ v ^ 2 = 1 ∧ ρ ⟨x, hxA⟩ v = v ∧ v * w₀ = w₀ * v := by
    rcases Nat.even_or_odd m' with hev | hodd
    · exact hEven m' hev K σ hK hσ _ w₀ hτ3 hτin hτw₀ hw₀3 hres'
    · exact hFix m' hodd K σ hK hσ _ w₀ hτ3 hτin hτw₀ hw₀3 hres'
  have hekr : ρ ⟨e, heA⟩ = 1 := by
    rw [hρapply, inducedAutHom_apply]
    have h1 : compAction Le ⟨e, hAN heA⟩ = 1 := by
      refine MulEquiv.ext fun z => Subtype.ext ?_
      change e * (z : G) * e⁻¹ = (z : G)
      have hze : (z : G) * e = e * z :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (le_centralizer_of_mem_thetaComponentsAt_three hLe z.2)
      rw [← hze, mul_inv_cancel_right]
    rw [h1, map_one, map_one]
  have hwA : w ∈ A := hw.1
  have hwkr : ρ ⟨w, hwA⟩ = 1 := by
    rw [hρapply, inducedAutHom_apply,
      Item812Res8.thetaQuotMulAut_eq_one_of_mem_sectionCentralizer hw (hAN hwA), map_one]
  have hR9 : Nat.card ρ.range ≤ 9 :=
    card_range_le_nine h.card_eq ρ (Subtype.ext (by simpa using h3 e heA))
      (fun h1 => he1 (by simpa using congrArg Subtype.val h1)) hekr hwkr
      (fun hmem => hwe (by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩))
  have hRc : ∀ β ∈ ρ.range, ∀ γ ∈ ρ.range, β * γ = γ * β := by
    rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
    rw [← map_mul, ← map_mul, hAel.1.is_comm.comm y y']
  have hR3 : ∀ β ∈ ρ.range, β ^ 3 = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, show y ^ 3 = 1 from Subtype.ext (by simpa using h3 y y.2), map_one]
  have htri : ∀ γ ∈ ρ.range, IsInnerAut γ ∨ IsInnerAut (γ * (ρ ⟨x, hxA⟩)⁻¹) ∨
      IsInnerAut (γ * ρ ⟨x, hxA⟩) := fun γ hγ =>
    d4_trichotomy hm1 hK hσ hτ3 hτin (hR3 γ hγ)
  have hw₀R : MulAut.conj w₀ ∈ ρ.range := ⟨⟨d, hdA⟩, by rw [hρapply, ← hw₀]⟩
  have hfix := fixed_of_trichotomy_conj hZ ρ.range hRc hR3 hR9 ⟨⟨x, hxA⟩, rfl⟩ hτin htri hw₀R
    hw₀1 hτv hvw
  refine ⟨E.symm v, ?_, fun u hu huA => ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hv2 hv1
  · have h1 : ρ ⟨u, huA⟩ v = v := hfix _ ⟨⟨u, huA⟩, rfl⟩
    rw [hρapply, inducedAutHom_apply, MulAut.congr_apply] at h1
    apply E.injective
    rw [MulEquiv.apply_symm_apply]
    have h2 : (⟨u, hAN huA⟩ : Subgroup.normalizer (Le : Set G)) = ⟨u, hu⟩ := rfl
    rw [h2] at h1
    exact h1

theorem kF89OmegaFixInvNonSp_of_d4 (h45 : Sec4.Item4_5)
    (hMinus : Sec11.KS11Lie4Proof.G2ThreeConjSL2Minus) (hFix : KF89D4FixInv)
    (hEven : KF89D4FixInvEven) (hRee : KF89OmegaFixInvRee) (hU : KF89OmegaFixInvUnitary) :
    KF89OmegaFixInvNonSp :=
  kF89OmegaFixInvNonSp_of_minus h45 hMinus (kF89OmegaFixInvD4_of h45 hFix hEven) hRee hU

end CFSG.RankThree.PartTwo.Sec8
