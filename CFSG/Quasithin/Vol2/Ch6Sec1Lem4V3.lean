module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V1
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4VIn
public import CFSG.Quasithin.Background.SQTKQuotTwo
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CenterlessCover

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem kg614FiveL2_of (hcat : CatalogStepFact) : KG614FiveL2 := by
  intro Γ _ _ H K T X hyp hL2
  classical
  obtain ⟨hH, hK, hKq, -, hT2, hTK, hTs, -, hXO, hX5, hXn, hTX, hXK, hXinn, hXnt⟩ := hyp
  obtain ⟨p, f, hp, hp2, hf, hPSL⟩ := hL2
  obtain ⟨hadm, F, _, _, hFcard, ⟨ϕ'⟩⟩ := hPSL
  have : Fact p.Prime := ⟨hp⟩
  let ϕ : ModO2 K ⧸ Subgroup.center (ModO2 K) ≃* PSL2 F :=
    ϕ'.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hKo : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, by omega, hFcard⟩
  have hcard : 3 < Nat.card F := by
    obtain ⟨-, -, -, h22, h23⟩ := hadm
    have h2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    rw [hFcard]
    have h2' : p ^ f ≠ 2 := fun h => h22 (by rw [h])
    have h3' : p ^ f ≠ 3 := fun h => h23 (by rw [h])
    omega
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (PGammaL2 F) :=
    Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right)) (by
      intro x y hxy
      exact SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  have hperf : commutator (ModO2 K) = ⊤ := by
    have := hKq.1
    exact Group.IsPerfect.commutator_eq_top
  let Ψ : MulAut (ModO2 K ⧸ Subgroup.center (ModO2 K)) ≃* PGammaL2 F :=
    (MulAut.congr ϕ).trans (pGammaL2EquivMulAut614 F hKo hcard hFcard).symm
  set σ : ↥(Subgroup.normalizer (K : Set Γ)) →* PGammaL2 F :=
    Ψ.toMonoidHom.comp ((quotCenterAut614 (ModO2 K)).comp (actModO2_614 K)) with hσ
  set N := pGammaL2PSLRange F with hN
  have hσK : ∀ k (hk : k ∈ K), σ ⟨k, Subgroup.le_normalizer hk⟩ =
      iotaPSL614 F (ϕ (((⟨k, hk⟩ : ↥K) : ModO2 K) : ModO2 K ⧸ Subgroup.center (ModO2 K))) := by
    intro k hk
    show Ψ (quotCenterAut614 (ModO2 K) (actModO2_614 K ⟨k, Subgroup.le_normalizer hk⟩)) = _
    rw [actModO2_614_of_mem K hk, quotCenterAut614_conj]
    show (pGammaL2EquivMulAut614 F hKo hcard hFcard).symm (MulAut.congr ϕ (MulAut.conj _)) = _
    rw [mulAut_congr_conj614, pGammaL2EquivMulAut614_symm_conj]
  have hσKN : ∀ k (hk : k ∈ K), σ ⟨k, Subgroup.le_normalizer hk⟩ ∈ N := fun k hk => by
    rw [hσK k hk]
    exact ⟨_, rfl⟩
  have hCN : centralizerMod (pCoreOf 2 K) H K ≤ Subgroup.normalizer (K : Set Γ) := by
    have key : ∀ c ∈ centralizerMod (pCoreOf 2 K) H K, ∀ u ∈ K, c * u * c⁻¹ ∈ K := by
      intro c hc u hu
      have h1 := CFSG.LieType.BorelTits.pCoreOf_le 2 K (hc.2.2 u hu)
      have e : c * u * c⁻¹ = (c * u * c⁻¹ * u⁻¹) * u := by group
      rw [e]
      exact K.mul_mem h1 hu
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key c hc h, fun hh => ?_⟩
    have := key c⁻¹ (Subgroup.inv_mem _ hc) _ hh
    simpa [mul_assoc] using this
  have hσC : ∀ c (hc : c ∈ centralizerMod (pCoreOf 2 K) H K), σ ⟨c, hCN hc⟩ = 1 := by
    intro c hc
    have h1 : actModO2_614 K ⟨c, hCN hc⟩ = 1 := actModO2_614_eq_one K fun u hu => hc.2.2 u hu
    show Ψ (quotCenterAut614 (ModO2 K) (actModO2_614 K ⟨c, hCN hc⟩)) = 1
    rw [h1, map_one, map_one]
  have hXN : ∀ x (hx : x ∈ X), σ ⟨x, hXK hx⟩ ∈ N := by
    intro x hx
    have hx' := hXinn hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K _ hCN] at hx'
    obtain ⟨k, hk, c, hc, hkc⟩ := hx'
    have e : (⟨x, hXK hx⟩ : ↥(Subgroup.normalizer (K : Set Γ))) =
        ⟨k, Subgroup.le_normalizer hk⟩ * ⟨c, hCN hc⟩ := Subtype.ext hkc.symm
    rw [e, map_mul, hσC c hc, mul_one]
    exact hσKN k hk
  have hX1 : ∃ x, ∃ hx : x ∈ X, σ ⟨x, hXK hx⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hXnt
    refine commutator_le_pCoreOf_of_actModO2_614 hXK fun x hx => ?_
    have h2 : quotCenterAut614 (ModO2 K) (actModO2_614 K ⟨x, hXK hx⟩) = 1 :=
      Ψ.injective (by rw [map_one]; exact hcon x hx)
    exact eq_one_of_quotCenterAut614_eq_one hperf h2
  obtain ⟨y, hy5, hyN, hXy, hTy, hker⟩ := exists_zpowers_five614 (N := N) σ hXK hTK
    inf_le_left (hT2.to_le inf_le_right) hXn hX5 hXO hTX hXN hX1
    (fun V hV hVe => card_le_four_of_isElemAbelian614 hKo hcard V hV hVe)
    (fun _ _ _ hy hu hg hy5 hu2 hyu hgu =>
      mem_normalizer_of_commute614 hKo hy hu hg hy5 hu2 hyu hgu)
  set τK : ↥K →* PGammaL2 F :=
    σ.comp (Subgroup.inclusion (Subgroup.le_normalizer : K ≤ Subgroup.normalizer (K : Set Γ)))
    with hτK
  have hτKrange : τK.range = N := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨⟨k, hk⟩, rfl⟩
      exact hσKN k hk
    · rintro _ ⟨s, rfl⟩
      obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (ϕ.symm s)
      obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨⟨k, hk⟩, ?_⟩
      show σ ⟨k, Subgroup.le_normalizer hk⟩ = _
      rw [hσK k hk, hq, MulEquiv.apply_symm_apply]
  set D := ((T ⊓ K).subgroupOf K).map τK with hD
  have hDs : IsSylowTwoOf D N := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨hτKrange ▸ Subgroup.map_le_range _ _, ?_, ?_⟩
    · exact ((hT2.to_le inf_le_left).of_equiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).symm).map τK
    · rw [← hτKrange]
      set ρ := τK.rangeRestrict
      have hsub : D.subgroupOf τK.range = ((T ⊓ K).subgroupOf K).map ρ := by
        ext ⟨φ, hφ⟩
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
        constructor
        · rintro ⟨x, hx, he⟩
          exact ⟨x, hx, Subtype.ext he⟩
        · rintro ⟨x, hx, he⟩
          exact ⟨x, hx, congrArg Subtype.val he⟩
      intro h2
      apply hTs.2.2
      have h3 : D.relIndex τK.range ∣ (T ⊓ K).relIndex K := by
        show (D.subgroupOf τK.range).index ∣ ((T ⊓ K).subgroupOf K).index
        rw [hsub]
        exact Subgroup.index_map_dvd _ (MonoidHom.rangeRestrict_surjective τK)
      exact h2.trans h3
  have hDy : D ≤ Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F)) := by
    rintro _ ⟨⟨k, hk⟩, hkT, rfl⟩
    exact hTy k hkT.1
  by_cases hp35 : p = 3 ∨ p = 5
  · exfalso
    have hq : Nat.card F = 5 ∨ Nat.card F = 9 ∨ Nat.card F = 25 := by
      rw [hFcard]
      rcases hp35 with rfl | rfl <;> rcases hf with rfl | rfl
      · rw [hFcard] at hcard
        norm_num at hcard
      all_goals norm_num
    exact false_of_le_normalizer_five614 hKo hcard hq hDs hyN hy5 hDy
  obtain ⟨r, hrD, hry⟩ := exists_inv_of_isSylowTwoOf614 hKo hcard hDs hyN hy5 hDy
  obtain ⟨⟨s, hsK⟩, hsTK, rfl⟩ := hrD
  have hsT : s ∈ T := hsTK.1
  have hXK' : X ≤ K := by
    refine le_of_mul_conj_mem614 (P := X ⊓ T) hXK (hT2.to_le inf_le_right) hXO hsK
      fun x hx => ?_
    have hsx : s * x * s⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hTX hsT) x).mp hx
    have hw : x * (s * x * s⁻¹) ∈ X := X.mul_mem hx hsx
    refine hker _ hw ?_
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hXy x hx)
    have e1 : σ ⟨x * (s * x * s⁻¹), hXK hw⟩ =
        σ ⟨x, hXK hx⟩ * (τK ⟨s, hsK⟩ * σ ⟨x, hXK hx⟩ * (τK ⟨s, hsK⟩)⁻¹) := by
      show _ = σ _ * (σ ⟨s, Subgroup.le_normalizer hsK⟩ * σ _ *
        (σ ⟨s, Subgroup.le_normalizer hsK⟩)⁻¹)
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [e1, ← hi, ← conj_zpow, hry, inv_zpow, mul_inv_cancel]
  have hp7 : 7 ≤ p := by
    by_contra h
    push Not at h
    have h2 := hp.two_le
    interval_cases p
    · exact hp2 rfl
    · exact hp35 (Or.inl rfl)
    · norm_num at hp
    · exact hp35 (Or.inr rfl)
    · norm_num at hp
  have hF7 : 7 ≤ Nat.card F := by
    rw [hFcard]
    exact hp7.trans (Nat.le_self_pow (by omega) p)
  have hSQ : SQTKGroup (ModO2 K) := by
    have h1 := InternalSec.sqtkGroup_subgroup hH (K.subgroupOf H)
    have h2 : SQTKGroup ↥K :=
      sqtkGroup_of_mulEquiv614 h1 (Subgroup.subgroupOfEquivOfLe (le_of_mem_cComp hK))
    exact sqtkGroup_quotient_of_isPGroup_two h2 (CFSG.pCore 2 ↥K) CFSG.pCore_isPGroup
  have hZodd := odd_card_center_modO2_614 K
  have hZcop : Nat.Coprime (Nat.card (Subgroup.center (ModO2 K))) (Nat.card F) := by
    rw [hFcard]
    rcases hcat (ModO2 K) hKq hSQ hZodd with h | h <;> rw [h]
    · exact Nat.coprime_one_left _
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes (by norm_num) hp).mpr (by omega))
  have hGWq : CFSG.GorensteinWalter.IsQuasisimple (ModO2 K) := by
    refine ⟨?_, hperf, hKq.2.1⟩
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    obtain ⟨a, b, hab⟩ := hKq.2.2
    apply hab
    have h1 : ∀ q : ModO2 K ⧸ Subgroup.center (ModO2 K), q = 1 := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [Subsingleton.elim g 1]
      rfl
    rw [h1 a, h1 b]
  have hZ := center_eq_bot_of_quasisimple_psl2_quotient_coprime hGWq F hKo hF7 hZodd hZcop ⟨ϕ⟩
  unfold Five614Concl
  refine Or.inr (Or.inl ⟨hXK', Or.inl ⟨p, f, hp, hp2, by omega, by omega, ?_⟩⟩)
  exact ⟨hadm, F, inferInstance, inferInstance, hFcard,
    ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans ϕ'⟩⟩

theorem kg614Five_of_L2 (hlist : A23SQTKListFact) (hcat : CatalogStepFact) (h3 : KG614FiveL3)
    (hc : KG614FiveChar2) (hs : KG614FiveSpor) : KG614Five :=
  kg614Five_of hlist (kg614FiveL2_of hcat) h3 hc hs

end CFSG.Quasithin.H13
