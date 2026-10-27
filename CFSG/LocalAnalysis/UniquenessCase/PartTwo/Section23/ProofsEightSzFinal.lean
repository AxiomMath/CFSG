module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightSzContext
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightSzTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightSzBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightSzLow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightSzPrime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem orderOf_mul_conj_commutator_ne_two_pow {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (S : Sylow 2 X) (θ : MulAut X)
    (hθS : ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X))
    (hfp : ∀ x ∈ Subgroup.normalizer ((S : Subgroup X) : Set X),
      θ x * x⁻¹ ∈ (S : Subgroup X) → x ∈ (S : Subgroup X))
    {d : X} (hdN : d ∈ Subgroup.normalizer ((S : Subgroup X) : Set X))
    (hdS : d ∉ (S : Subgroup X)) :
    ∀ n : ℕ, orderOf (θ * MulAut.conj d * θ⁻¹ * (MulAut.conj d)⁻¹) ≠ 2 ^ n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj_inj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    P22y.conj_injective_of_center_eq_bot hZ
  have hSmap : (S : Subgroup X).map (θ : X ≃* X).toMonoidHom = (S : Subgroup X) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro - ⟨s, hs, rfl⟩; exact hθS s hs
    · rw [Subgroup.card_map_of_injective (θ : X ≃* X).injective]
  have hθdN : θ d ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
    have hmem : θ d ∈
        (Subgroup.normalizer ((S : Subgroup X) : Set X)).map (θ : X ≃* X).toMonoidHom :=
      Subgroup.mem_map_of_mem (θ : X ≃* X).toMonoidHom hdN
    have hnorm : (Subgroup.normalizer ((S : Subgroup X) : Set X)).map
        (θ : X ≃* X).toMonoidHom = Subgroup.normalizer ((S : Subgroup X) : Set X) := by
      rw [Subgroup.map_equiv_normalizer_eq, hSmap]
    rwa [hnorm] at hmem
  let y : X := θ d * d⁻¹
  have hyN : y ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) :=
    (Subgroup.normalizer ((S : Subgroup X) : Set X)).mul_mem hθdN
      ((Subgroup.normalizer ((S : Subgroup X) : Set X)).inv_mem hdN)
  have hinv : (MulAut.conj d)⁻¹ = MulAut.conj d⁻¹ :=
    (map_inv (MulAut.conj : X →* MulAut X) d).symm
  have heq : θ * MulAut.conj d * θ⁻¹ * (MulAut.conj d)⁻¹ = MulAut.conj y := by
    rw [hinv]
    ext z
    simp [y, MulAut.conj_apply, mul_assoc]
  intro n hord
  have hyord : orderOf y = 2 ^ n := by
    rwa [← orderOf_injective (MulAut.conj : X →* MulAut X) hconj_inj y, ← heq]
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.iff_card.mpr ⟨n, by rw [Nat.card_zpowers, hyord]⟩
  have hyS : y ∈ (S : Subgroup X) := by
    have hmem : y ∈ Subgroup.zpowers y ⊓ Subgroup.normalizer ((S : Subgroup X) : Set X) :=
      ⟨Subgroup.mem_zpowers y, hyN⟩
    have hinf : Subgroup.zpowers y ⊓ Subgroup.normalizer ((S : Subgroup X) : Set X) =
        Subgroup.zpowers y ⊓ (S : Subgroup X) := by
      simpa only [Sylow.coe_coe] using IsPGroup.inf_normalizer_sylow hy2 S
    rw [hinf] at hmem
    exact hmem.2
  exact hdS (hfp d hdN (by simpa [y] using hyS))

private theorem Ctx23L.exists_b_sylow_of_sz {D : Data G} {Ch : Choice2011 G}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch)
    (h54 : S23_5_4 D Ch) (h215 : S21_5 D Ch) (h2115 : S21_15N D Ch) (hBor : KBor)
    (hCentSz : KCentSz) (hsig : D.sig.Nonempty) (h1930 : H1930 D) (c₁ : Ctx23L D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ} (hSz : IsSz (Bar2 K) a)
    (hne : conjClosure D.M K ≠ K) :
    ∃ (b : G) (S : Sylow 2 (xbar K)) (hbK : b ∈ Subgroup.normalizer (K : Set G)),
      b ∈ c₁.B0 ∧ b ∈ c₁.L0 ∧ b ∉ Subgroup.centralizer (D.Z : Set G) ∧
      (S : Subgroup (xbar K)) = sylowImage D K ∧
      (∀ y ∈ (S : Subgroup (xbar K)),
        inducedQuotInfAut K b hbK y ∈ (S : Subgroup (xbar K))) ∧
      (∀ y ∈ Subgroup.normalizer ((S : Subgroup (xbar K)) : Set (xbar K)),
        inducedQuotInfAut K b hbK y * y⁻¹ ∈ (S : Subgroup (xbar K)) →
          y ∈ (S : Subgroup (xbar K))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hm2, hP1⟩ := c₁.exists_mem_B0_not_mem_centralizer_Z hE h207 h52 h53 h1930
  have hne1 : 2 ^ CFSG.Open.pRank 2 D.Z - 1 ≠ 1 := by
    have h4 : 4 ≤ 2 ^ CFSG.Open.pRank 2 D.Z := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ CFSG.Open.pRank 2 D.Z := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne1
  obtain ⟨b, hb0, -, hbZ⟩ := hP1 r hr hrdvd
  have hbL0 : b ∈ c₁.L0 := c₁.hB0.1 hb0
  have hbK : b ∈ Subgroup.normalizer (K : Set G) :=
    c₁.B0_le_normalizer_of_mem_calC h215 h1930 hK hb0
  have hsz := c₁.szPrime_of_ne hE h207 h52 h53 h54 h215 h2115 hBor hCentSz hsig h1930
    hK hSz hne
  obtain ⟨S, hScoe, hSinv⟩ :=
    exists_sylow_normalized hBor h215 h1930 c₁ hK (Or.inr hSz) hb0 hbK
  refine ⟨b, S, hbK, hb0, hbL0, hbZ, hScoe, hSinv, ?_⟩
  intro y hyN hymod
  rw [hScoe] at hyN hymod ⊢
  exact hsz.2.2 b hb0 hbK hbZ y hyN hymod

theorem Ctx23L.false_of_szTorus_low {D : Data G} {Ch : Choice2011 G}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch)
    (h54 : S23_5_4 D Ch) (h215 : S21_5 D Ch) (h2115 : S21_15N D Ch) (hBor : KBor)
    (hCentSz : KCentSz) (hsig : D.sig.Nonempty) (h1930 : H1930 D) (c₁ : Ctx23L D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ} (hSz : IsSz (Bar2 K) a)
    (hne : conjClosure D.M K ≠ K) {x : G} (hxK : x ∈ Subgroup.normalizer (K : Set G))
    {d : xbar K} (hdN : d ∈ Subgroup.normalizer ((sylowImage D K : Set (xbar K))))
    (hdS : d ∉ sylowImage D K)
    (hθx : inducedQuotInfAut K x hxK = MulAut.conj d)
    (hx : ∀ b ∈ c₁.L0, b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 c₁.L0) :
    False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, S, hbK, -, hbL0, -, hScoe, hSinv, hfp⟩ :=
    c₁.exists_b_sylow_of_sz hE h207 h52 h53 h54 h215 h2115 hBor hCentSz hsig h1930 hK hSz hne
  have hcomm_mem : b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 c₁.L0 := hx b hbL0
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c₁.L0) := uc22main1_isPGroup_pCoreOf c₁.L0
  obtain ⟨k, hk⟩ := hO2.exists_orderOf_dvd_pow
    (⟨b * x * b⁻¹ * x⁻¹, hcomm_mem⟩ : ↥(CFSG.Open.pCoreOf 2 c₁.L0))
  have hcommK : b * x * b⁻¹ * x⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
    have hb' : b⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normalizer (K : Set G)).inv_mem hbK
    have hx' : x⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normalizer (K : Set G)).inv_mem hxK
    exact (Subgroup.normalizer (K : Set G)).mul_mem
      ((Subgroup.normalizer (K : Set G)).mul_mem
        ((Subgroup.normalizer (K : Set G)).mul_mem hbK hxK) hb') hx'
  have hθcomm : inducedQuotInfAut K (b * x * b⁻¹ * x⁻¹) hcommK =
      inducedQuotInfAut K b hbK * MulAut.conj d *
        (inducedQuotInfAut K b hbK)⁻¹ * (MulAut.conj d)⁻¹ := by
    rw [← hθx]
    change inducedQuotInfAutHom K ⟨b * x * b⁻¹ * x⁻¹, hcommK⟩ =
      inducedQuotInfAutHom K ⟨b, hbK⟩ * inducedQuotInfAutHom K ⟨x, hxK⟩ *
        (inducedQuotInfAutHom K ⟨b, hbK⟩)⁻¹ * (inducedQuotInfAutHom K ⟨x, hxK⟩)⁻¹
    rw [show (⟨b * x * b⁻¹ * x⁻¹, hcommK⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨b, hbK⟩ * ⟨x, hxK⟩ * ⟨b, hbK⟩⁻¹ * ⟨x, hxK⟩⁻¹ from Subtype.ext rfl]
    simp only [map_mul, map_inv]
  have hdvdθ : orderOf (inducedQuotInfAut K (b * x * b⁻¹ * x⁻¹) hcommK) ∣ 2 ^ k := by
    refine (orderOf_inducedQuotInfAut_dvd K hcommK).trans ?_
    simpa using hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdθ
  have hZ : Subgroup.center (xbar K) = ⊥ := by
    have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
    obtain ⟨e⟩ := uc22p21k_quotCenter_equiv (center_barInf_eq_bot hq)
    exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e (center_barInf_eq_bot hq)
  exact orderOf_mul_conj_commutator_ne_two_pow hZ S (inducedQuotInfAut K b hbK) hSinv hfp
    (by rwa [hScoe]) (by rwa [hScoe]) m (hθcomm ▸ hm)

theorem s23_8_Sz_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h208 : S20_8 D) (h2010 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M)
    (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch) (h54 : S23_5_4 D Ch) (h215 : S21_5 D Ch)
    (h2115 : S21_15N D Ch) (hBor : KBor) (hCentSz : KCentSz) (hAut : KSzTwoAut)
    (hsig : D.sig.Nonempty) (hLow : S23_8_SzLow D Ch) : S23_8_Sz D Ch := by
  intro h1930 c K hK a hSz
  by_cases hEq : conjClosure D.M K = K
  · exact uc22p21j_normal_of_conjClosure_eq hK.1.le hEq.symm
  · exfalso
    obtain ⟨ha_eq, ha_prime, -⟩ :=
      c.szPrime_of_ne hE h207 h52 h53 h54 h215 h2115 hBor hCentSz hsig h1930 hK hSz hEq
    obtain ⟨r, hr, hrdvd, A, hAcard, hAne, -, hAM, hAT, hAK, hTorus⟩ :=
      c.exists_szTorus h2115 hsig h1930 kSzBorel_holds hAut hK hSz hEq
    obtain ⟨L₁, hL₁, -, hcomm⟩ :=
      hLow h1930 c K hK a hSz hEq ha_eq ha_prime r hr hrdvd A hAcard hAM hAT hAK
    obtain ⟨c₁, hc₁L0, -⟩ :=
      exists_ctx23L_of_mem_calLLow D Ch h1930 h208 h2010 hCh c.hTI hL₁
    obtain ⟨x, hxA, hxne⟩ := (Subgroup.bot_or_exists_ne_one A).resolve_left hAne
    have hxK : x ∈ Subgroup.normalizer (K : Set G) := hAK hxA
    obtain ⟨d, hdN, hdS, hθx⟩ := hTorus x hxA hxK hxne
    have hxcomm : ∀ b ∈ c₁.L0, b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 c₁.L0 := by
      intro b hb
      rw [hc₁L0] at hb ⊢
      exact hcomm x hxA b hb
    exact c₁.false_of_szTorus_low hE h207 h52 h53 h54 h215 h2115 hBor hCentSz hsig h1930
      hK hSz hEq hxK hdN hdS hθx hxcomm

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
