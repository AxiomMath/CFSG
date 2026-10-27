module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofOmegaD4
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofArith
import CFSG.RankThree.PartTwo.KFacts.K71Item89

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LieType.Ree
open CFSG.Assembly.RankThreeEven (projSL)

namespace Item812Res11

theorem trichotomy_of_normal_form {M : Type*} [Group M] {K : Type*} [Field K] [Finite K]
    {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hK : Nat.card K = p ^ n)
    (Φ : (K ≃+* K) →* MulAut M) (hdec : ∀ α : MulAut M, ∃ (g : M) (β : K ≃+* K),
      α = MulAut.conj g * Φ β)
    (hfaith : ∀ β : K ≃+* K, IsInnerAut (Φ β) → β = 1) {α γ : MulAut M} (hα3 : α ^ 3 = 1)
    (hα : ¬ IsInnerAut α) (hγ3 : γ ^ 3 = 1) :
    IsInnerAut γ ∨ IsInnerAut (γ * α⁻¹) ∨ IsInnerAut (γ * α) := by
  classical
  have hpart : ∀ (g : M) (δ : K ≃+* K), (MulAut.conj g * Φ δ) ^ 3 = 1 → δ ^ 3 = 1 := by
    intro g δ h3
    rw [conj_mul_pow_three] at h3
    apply hfaith
    rw [map_pow, eq_inv_of_mul_eq_one_right h3]
    exact ⟨_, map_inv MulAut.conj _⟩
  obtain ⟨g, δ, rfl⟩ := hdec α
  obtain ⟨h, ε, rfl⟩ := hdec γ
  have hδ3 := hpart g δ hα3
  have hε3 := hpart h ε hγ3
  by_cases hε1 : ε = 1
  · left
    rw [hε1, map_one, mul_one]
    exact ⟨h, rfl⟩
  right
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hα
    exact hα ⟨g, rfl⟩
  have hδo : orderOf δ = 3 := orderOf_eq_prime hδ3 hδ1
  have hεo : orderOf ε = 3 := orderOf_eq_prime hε3 hε1
  obtain ⟨⟨r, hr⟩, hδf⟩ := eq_frobenius_pow_of_orderOf_eq_three hp hn hK hδo
  obtain ⟨-, hεf⟩ := eq_frobenius_pow_of_orderOf_eq_three hp hn hK hεo
  have h3 : n / 3 = r := by omega
  have h23 : 2 * n / 3 = 2 * r := by omega
  rw [h3, h23] at hδf hεf
  have : Fintype K := Fintype.ofFinite K
  have hpn : ∀ (c : K) (a b : ℕ), a + b = n → (c ^ p ^ a) ^ p ^ b = c := by
    intro c a b hab
    rw [← pow_mul, ← pow_add, hab, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hcases : ε = δ ∨ ε * δ = 1 := by
    rcases hδf with h1 | h1 <;> rcases hεf with h2 | h2
    · left
      ext c
      rw [h1, h2]
    · right
      ext c
      rw [RingAut.mul_apply, h1, h2, RingAut.one_apply, hpn c r (2 * r) (by omega)]
    · right
      ext c
      rw [RingAut.mul_apply, h1, h2, RingAut.one_apply, hpn c (2 * r) r (by omega)]
    · left
      ext c
      rw [h1, h2]
  have e1 : Φ ε * MulAut.conj g = MulAut.conj (Φ ε g) * Φ ε := by
    rw [← mul_mulAutConj_mul_inv, inv_mul_cancel_right]
  rcases hcases with heq | hinv
  · left
    subst heq
    refine ⟨h * g⁻¹, ?_⟩
    rw [map_mul, map_inv]
    group
  · right
    refine ⟨h * Φ ε g, ?_⟩
    have e2 : Φ ε * Φ δ = 1 := by rw [← map_mul, hinv, map_one]
    rw [map_mul]
    symm
    calc MulAut.conj h * Φ ε * (MulAut.conj g * Φ δ) =
        MulAut.conj h * (Φ ε * MulAut.conj g) * Φ δ := by simp only [mul_assoc]
      _ = MulAut.conj h * (MulAut.conj (Φ ε g) * Φ ε) * Φ δ := by rw [e1]
      _ = MulAut.conj h * MulAut.conj (Φ ε g) * (Φ ε * Φ δ) := by simp only [mul_assoc]
      _ = MulAut.conj h * MulAut.conj (Φ ε g) := by rw [e2, mul_one]

end Item812Res11


@[expose] def KF89ReeFixInv : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
    Nat.card K = 2 ^ (2 * k + 1) →
    ∀ (τ : MulAut (ReeTag.F4.reeGamma K k)) (w : ReeTag.F4.reeGamma K k),
      τ ^ 3 = 1 → ¬ IsInnerAut τ → τ w = w → w ^ 3 = 1 →
      IsoSUThree (perfectResidual
          (Subgroup.centralizer ({w} : Set (ReeTag.F4.reeGamma K k)))) (2 ^ (2 * k + 1)) →
        ∃ v : ReeTag.F4.reeGamma K k, v ≠ 1 ∧ v ^ 2 = 1 ∧ τ v = v ∧ v * w = w * v


open Item812Res11 Item812Res8

theorem kF89OmegaFixInvRee_of (h45 : Sec4.Item4_5) (hFix : KF89ReeFixInv) :
    KF89OmegaFixInvRee := by
  intro G _ _ A c L a b X n h p hp hRm w hw hwe
  classical
  obtain ⟨m, hRee⟩ := hRm
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
  have hm'1 : 1 ≤ m' := Item86ResProof.one_le_of_isGammaIndex hdm
  obtain ⟨-, -, -, hcase⟩ := Item87Proof.isGammaIndex_cases hdm
  have hF4 := Item86ResProof.sigF4_of_reeF4 (X := Le ⧸ aschbacherSolvableCore 3 Le) hm'1
  obtain ⟨hRee', hSU⟩ : IsGammaTypeRee (Le ⧸ aschbacherSolvableCore 3 Le) m' ∧
      IsoSUThree (imageModTheta Le
        (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G))))
        (2 ^ (3 * m')) := by
    rcases hcase with hR | ⟨hL2, -⟩
    · exact hR
    · exfalso
      have hm1 : 1 ≤ m := by
        obtain ⟨k, -, hkm, -⟩ := hRee
        omega
      have hFm := Item86ResProof.sigF4_of_reeF4 hm1 hRee
      rcases hL2 with hD | hG | hPSU | hS | hSp
      · exact hFm.false_of_sigD4 (Item86ResProof.sigD4_of_isoTrialityD4 hm'1 hD) hm1
      · exact hFm.false_of_sigG2 (Item86ResProof.sigG2_of_isoGTwo hm'1 hG) hm1
      · obtain ⟨e₂⟩ := hPSU
        exact hFm.false_of_sigU (Item86ResProof.sigU_of_unitarySig
          (Item86ResProof.unitarySig_of_projSU (by omega) e₂)) hm1
      · exact hFm.false_of_sigU (Item86ResProof.sigU_of_unitarySig
          (Item86ResProof.unitarySig_of_isoSUThree (by omega) hS)) hm1
      · obtain ⟨e₂⟩ := hSp
        exact hFm.false_of_sigSp4 (Item86ResProof.sigSp4_of_projSp hm'1 e₂) hm1
  have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq hdN
    ⟨1, by rw [pow_one]; exact hd3⟩
  obtain ⟨k, hk, hkm, ⟨e₀⟩⟩ := hRee'
  have hR := (Sec4.Census.bridgeExceptional46).reeF4 k hk
  obtain ⟨-, k', hk'1, hkk', K, _, _, _, hK, ⟨e₁⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
  set E := e₀.trans e₁ with hE
  have hZ := ReeTag.large_Ree_fixed_group_center_trivial k' K hK
  have hinj := Item812Res7.conj_injective_of_center_trivial hZ
  have hK3m : 2 * k' + 1 = 3 * m' := by omega
  have hxout : InducesOuterTheta x Le := by
    rcases hxk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
  set ρ : A →* MulAut (ReeTag.F4.reeGamma K k') :=
    (inducedAutHom Le E).comp (Subgroup.inclusion hAN) with hρ
  have hρapply : ∀ y : A, ρ y = inducedAutHom Le E ⟨y, hAN y.2⟩ := fun y => rfl
  have hτ3 : ρ ⟨x, hxA⟩ ^ 3 = 1 := inducedAutHom_pow_eq_one Le E hxN hx3
  have hτin : ¬ IsInnerAut (ρ ⟨x, hxA⟩) := (not_isInnerAut_inducedAutHom_iff Le E hxN).mpr hxout
  have hdin : ¬ InducesOuterTheta d Le := by
    intro hout
    obtain ⟨bb, k'', _, _, _, hk'', hrel, ⟨φ⟩⟩ :=
      exists_barCentralizer_mulEquiv_reeGamma' hk'1 hK E hd3 hout
    have hb : 2 * bb + 1 = m' := by omega
    have hC := Item86ResProof.card_of_mulEquiv_reeGamma bb k'' hk'' φ
    rw [hb, Item86ResProof.ordTwistedF4_eq_factored' (two_le_two_pow hm'1)] at hC
    have hdvd := card_inSubgroup_perfectResidual_dvd (barCentralizer (Subgroup.zpowers d) Le)
    rw [← himg, card_of_isoSUThree hSU, hC, mul_comm 3 m', pow_mul] at hdvd
    exact not_dvd_ree (two_le_two_pow hm'1) hdvd
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
      Subgroup.centralizer ({w₀} : Set (ReeTag.F4.reeGamma K k')) :=
    ((MulEquiv.subgroupCongr (Sec4.barCentralizer_zpowers_eq_autFix hdN)).trans
      (Sec4.autFixCongrEquiv E _).symm).trans
      (MulEquiv.subgroupCongr (by
        rw [show MulAut.congr E (thetaQuotMulAut Le (compAction Le ⟨d, hdN⟩)) =
          inducedAutHom Le E ⟨d, hdN⟩ from rfl, ← hw₀]
        exact autFix_conj_eq_centralizer w₀))
  have hres' : IsoSUThree (perfectResidual
      (Subgroup.centralizer ({w₀} : Set (ReeTag.F4.reeGamma K k')))) (2 ^ (2 * k' + 1)) := by
    obtain ⟨F, _, _, hF, ⟨ψ⟩⟩ := hSU
    refine ⟨F, inferInstance, inferInstance, by rw [hF, hK3m], ⟨?_⟩⟩
    refine (perfectResidualCongr hCw).symm.trans ?_
    refine (inSubgroupPerfectResidualEquiv _).symm.trans ?_
    rw [hK3m]
    exact (MulEquiv.subgroupCongr himg.symm).trans ψ
  have hw₀1 : w₀ ≠ 1 := by
    rintro rfl
    have h1 : inducedAutHom Le E ⟨d, hdN⟩ = 1 := by rw [← hw₀, map_one]
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
        (2 ^ (3 * m')) ^ 3 * (((2 ^ (3 * m')) ^ 2 - 1) * ((2 ^ (3 * m')) ^ 3 + 1)) := by
      rw [← mul_assoc, ← card_of_isoSUThree hSU, himg, hC, inSubgroup,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        KFacts.perfectResidual_eq_top_of_isPerfect
          (hperf.ofSurjective (f := (Subgroup.topEquiv).symm.toMonoidHom)
            (MulEquiv.surjective _)),
        Subgroup.card_top, Subgroup.card_top]
    have hodd2 : Odd (((2 ^ (3 * m')) ^ 2 - 1) * ((2 ^ (3 * m')) ^ 3 + 1)) := by
      have h1 : 1 ≤ (2 ^ (3 * m')) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      have h2 : Even ((2 ^ (3 * m')) ^ 2) := by
        rw [← pow_mul]
        exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      have h3 : Even ((2 ^ (3 * m')) ^ 3) := by
        rw [← pow_mul]
        exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      exact Nat.odd_mul.mpr ⟨Nat.Even.sub_odd h1 h2 odd_one, h3.add_one⟩
    exact (hF4 ⟨k, hk, hkm, ⟨e₀⟩⟩).profile.ne_of_ne hodd2 (a := 3 * m' * 3) (by omega)
      (by rw [hcard, ← pow_mul])
  have hτw₀ : ρ ⟨x, hxA⟩ w₀ = w₀ := Item812Res7.apply_eq_of_commute_conj hinj hττc
  obtain ⟨v, hv1, hv2, hτv, hvw⟩ := hFix k' hk'1 K hK _ w₀ hτ3 hτin hτw₀ hw₀3 hres'
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
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
        exact ⟨j, by simpa using congrArg Subtype.val hj⟩))
  have hRc : ∀ β ∈ ρ.range, ∀ γ ∈ ρ.range, β * γ = γ * β := by
    rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
    rw [← map_mul, ← map_mul, hAel.1.is_comm.comm y y']
  have hR3 : ∀ β ∈ ρ.range, β ^ 3 = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, show y ^ 3 = 1 from Subtype.ext (by simpa using h3 y y.2), map_one]
  obtain ⟨hdec, hfaith⟩ := KFacts.largeRee_automorphism_normal_form hk'1 hK
  have htri : ∀ γ ∈ ρ.range, IsInnerAut γ ∨ IsInnerAut (γ * (ρ ⟨x, hxA⟩)⁻¹) ∨
      IsInnerAut (γ * ρ ⟨x, hxA⟩) := fun γ hγ =>
    trichotomy_of_normal_form Nat.prime_two (by omega) hK (ReeTag.F4.reeGammaFieldAutHom K k')
      hdec hfaith hτ3 hτin (hR3 γ hγ)
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

theorem kF89OmegaFixInvNonSp_of_ree (h45 : Sec4.Item4_5)
    (hMinus : Sec11.KS11Lie4Proof.G2ThreeConjSL2Minus) (hFix : KF89D4FixInv)
    (hEven : KF89D4FixInvEven) (hRee : KF89ReeFixInv) (hU : KF89OmegaFixInvUnitary) :
    KF89OmegaFixInvNonSp :=
  kF89OmegaFixInvNonSp_of_d4 h45 hMinus hFix hEven (kF89OmegaFixInvRee_of h45 hRee) hU

end CFSG.RankThree.PartTwo.Sec8
