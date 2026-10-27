module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieG2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieRows
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieArithSp4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieArithF4
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27Exc

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

section F4


theorem f4Excl429 (k : Type) [Field k] [Finite k] [CharP k ReeTag.F4.prime] (b : ℕ)
    (hk : Nat.card k = 2 ^ (2 * b + 1)) (G : Type) [Group G] [Finite G] (C J : Subgroup G)
    (hC : Nonempty (C ≃* ReeTag.F4.reeGamma k b)) (hJC : J ≤ C) (hJperf : Group.IsPerfect J)
    (hsub : (J.subgroupOf C).IsSubnormal) (htype : IsType429 (J ⧸ CFSG.pCore 2 J)) : False := by
  obtain ⟨eC⟩ := hC
  haveI := hJperf
  obtain ⟨E, hEJ, -, hE3, hE9, -⟩ := exists_e9_of_type429 htype
  obtain ⟨k₀, hk₀E, hk₀1, hk₀3⟩ := exists_ne_one_pow_three hE3 hE9
  have hk₀J : k₀ ∈ J := hEJ hk₀E
  have hJnt : J ≠ ⊥ := fun hb => hk₀1 ((Subgroup.mem_bot).mp (hb ▸ hk₀J))
  have hk₀1' : (⟨k₀, hk₀J⟩ : J) ≠ 1 := fun h => hk₀1 (congrArg Subtype.val h)
  have hk₀3' : (⟨k₀, hk₀J⟩ : J) ^ 3 = 1 := Subtype.ext (by simpa using hk₀3)
  obtain ⟨hQperf, hQnt⟩ := quot_pCore_facts hk₀1' hk₀3'
  haveI := hQnt
  have hcardC : Nat.card C = CFSG.Open.ordTwistedF4 (2 ^ (2 * b + 1)) :=
    Sec8.Item86ResProof.card_of_mulEquiv_reeGamma b k hk eC
  have hQJ : Nat.card (J ⧸ CFSG.pCore 2 J) ∣ Nat.card J := by
    haveI : (CFSG.pCore 2 J).Normal := CFSG.pCore_normal
    exact Subgroup.card_quotient_dvd_card _
  have hJCd : Nat.card J ∣ Nat.card C := Subgroup.card_dvd_of_le hJC
  rcases Nat.eq_zero_or_pos b with rfl | hb
  ·
    have hdvd : Nat.card (J ⧸ CFSG.pCore 2 J) ∣ 35942400 := by
      have := hQJ.trans hJCd
      rw [hcardC] at this
      simpa [CFSG.Open.ordTwistedF4] using this
    rcases card_of_isType429 htype with ⟨p, e, hp, hp3, he, ⟨hq, hc⟩ | ⟨hq, hc, hsol⟩⟩ |
      hc | hc | hc | hc
    · exact f4two_L3 hdvd (Nat.le_trans hp.two_le (Nat.le_self_pow (by omega) p)) hq hc
    · have h2 := f4two_U3 hdvd (Nat.le_trans hp.two_le (Nat.le_self_pow (by omega) p)) hq hc
      exact Group.IsPerfect.not_isSolvable _ (hsol h2)
    all_goals
      rw [hc] at hdvd
      norm_num at hdvd
  ·
    haveI hCs : IsSimpleGroup (ReeTag.F4.reeGamma k b) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hk
    have hCs' : IsSimpleGroup C := eC.isSimpleGroup
    have hJC' : J = C := eq_of_subnormal_of_le_simple hJC le_rfl hsub hCs' hJnt
    haveI hJs : IsSimpleGroup J := by
      rw [hJC']
      exact hCs'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hN : CFSG.pCore 2 J = ⊥ := by
      haveI : (CFSG.pCore 2 J).Normal := CFSG.pCore_normal
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 J) with h | h
      · exact h
      · exfalso
        have hkN : (⟨k₀, hk₀J⟩ : J) ∈ CFSG.pCore 2 J := h ▸ Subgroup.mem_top _
        exact hk₀1' (eq_one_of_isPGroup_two_of_pow_three CFSG.pCore_isPGroup hkN hk₀3')
    have hcardQ : Nat.card (J ⧸ CFSG.pCore 2 J) = CFSG.Open.ordTwistedF4 (2 ^ (2 * b + 1)) := by
      have e1 : (J ⧸ CFSG.pCore 2 J) ≃* J :=
        (QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot
      rw [Nat.card_congr e1.toEquiv, ← hcardC]
      exact congrArg (fun H : Subgroup G => Nat.card H) hJC'
    have hbig : 604800 < CFSG.Open.ordTwistedF4 (2 ^ (2 * b + 1)) := by
      have h8 : 8 ≤ 2 ^ (2 * b + 1) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      unfold CFSG.Open.ordTwistedF4
      set x := 2 ^ (2 * b + 1) with hx
      have h12 : 8 ^ 12 ≤ x ^ 12 := Nat.pow_le_pow_left h8 12
      have h6 : 1 ≤ x ^ 6 + 1 := by omega
      have h4 : 1 ≤ x ^ 4 - 1 := by
        have : 8 ^ 4 ≤ x ^ 4 := Nat.pow_le_pow_left h8 4
        omega
      have h3 : 1 ≤ x ^ 3 + 1 := by omega
      have h1 : 1 ≤ x - 1 := by omega
      have hprod : 1 ≤ (x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1) :=
        Nat.one_le_iff_ne_zero.mpr (by positivity)
      calc 604800 < 8 ^ 12 := by norm_num
        _ ≤ x ^ 12 := h12
        _ = x ^ 12 * 1 := (mul_one _).symm
        _ ≤ x ^ 12 * ((x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1)) :=
          Nat.mul_le_mul_left _ hprod
        _ = x ^ 12 * (x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1) := by ring
    rcases card_of_isType429 htype with ⟨p, e, hp, hp3, he, ⟨hq, hc⟩ | ⟨hq, hc, -⟩⟩ |
      hc | hc | hc | hc
    · exact f4_mul_three_ne_L3 (by omega) hp hp3 he (hcardQ ▸ hc)
    · exact f4_mul_three_ne_U3 (by omega) hp hp3 he (hcardQ ▸ hc)
    all_goals omega

theorem noCfgS429_of_reeGamma {S : Type} [Group S] [Finite S] {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (τ : S ≃* ReeTag.F4.reeGamma K a) : NoCfgS429 S := by
  intro A σ J hc
  haveI := hc.isPerfect
  have hσ3 := cfgS429_pow_three hc
  obtain ⟨E, hEJ, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_type429 hc.isType
  have hfix : ∀ k ∈ J, σ k = k := fun k hk => Sec4.mem_autFix.mp (hc.le_autFix hk)
  have hZ : ∀ s : ReeTag.F4.reeGamma K a, (∀ t, s * t = t * s) → s = 1 := by
    intro s hs
    refine
      CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.eq_one_of_conj_eq_one hK ?_
    ext t
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [hs t, mul_inv_cancel_right]
  obtain ⟨-, -, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  set α := MulAut.congr τ σ with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hσ3, map_one]
  by_cases hin : IsInnerAut α
  ·
    refine false_of_fix_e9_of_mulEquiv τ
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut _).range ?_ (fun s => ⟨s, rfl⟩) hZ hin
      hσ3 hc.ne_one hEJ hEc hE3 hE9 hfix hEZ
    intro B hB h3B hcB
    exact card_le_nine_inn (fun E hE h27 =>
      CFSG.HardMathSupport.Dickson.Sec6.I1431.noE27_reeGamma a K hK ⟨E, hE, h27⟩) hZ hB h3B hcB
  ·
    set p := Ψ.symm α with hp
    have hαp : α = MulAut.conj p.left * ReeTag.F4.reeGammaFieldAut K a p.right := by
      rw [← hΨ]
      exact (Ψ.apply_symm_apply α).symm
    have hF1 : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := by
      have h1 := hΨ 1 1
      rw [show (⟨1, 1⟩ : ReeTag.F4.reeGamma K a ⋊[ReeTag.F4.reeGammaFieldAutHom K a] (K ≃+* K)) = 1
        from rfl, map_one, map_one, one_mul] at h1
      exact h1.symm
    have hβ3 : p.right ^ 3 = 1 := by
      have h1 : p ^ 3 = 1 := by
        apply Ψ.injective
        rw [map_pow, hp, Ψ.apply_symm_apply, hα3, map_one]
      have h2 := congrArg (SemidirectProduct.rightHom) h1
      rwa [map_pow, map_one] at h2
    have hβ1 : p.right ≠ 1 := by
      intro h1
      apply hin
      rw [hαp, h1, hF1, mul_one]
      exact ⟨p.left, rfl⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hβ : orderOf p.right = 3 := orderOf_eq_prime hβ3 hβ1
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK Nat.prime_three
      p.right hβ α hα3 ⟨p.left, hαp⟩
    obtain ⟨b, -, hkcard, himg⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.largeRee_fixed_data_of_odd hK Nat.prime_three
        (by norm_num) p.right hβ
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP (fixSubfield p.right) ReeTag.F4.prime := by
      have := Fintype.ofFinite (fixSubfield p.right)
      exact charP_of_card_eq_prime_pow (f := 2 * b + 1)
        (by rw [← Nat.card_eq_fintype_card, hkcard]; rfl)
    set γ := ReeTag.F4.reeGammaFieldAut K a p.right with hγ
    have eγ : Sec4.autFix γ ≃* ReeTag.F4.reeGamma (fixSubfield p.right) b :=
      (((MulEquiv.subgroupCongr (show Sec4.autFix γ = γ.toMonoidHom.eqLocus (MonoidHom.id _)
          from rfl)).trans
        ((γ.toMonoidHom.eqLocus (MonoidHom.id _)).equivMapOfInjective _
          (Subgroup.subtype_injective _))).trans (MulEquiv.subgroupCongr himg)).trans
        ((ReeTag.F4.reeGamma (fixSubfield p.right) b).equivMapOfInjective _
          (baseChangeGL_injective (fixSubfield p.right).subtype)).symm
    have eα : Sec4.autFix α ≃* ReeTag.F4.reeGamma (fixSubfield p.right) b := by
      rw [hg]
      exact (autFixConjEquiv (MulAut.conj g) γ).trans eγ
    exact f4Excl429 (fixSubfield p.right) b hkcard S (Sec4.autFix σ) J
      ⟨(Sec4.autFixCongrEquiv τ σ).symm.trans eα⟩ hc.le_autFix hc.isPerfect hc.isSubnormal
      hc.isType

theorem seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowSOf429 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group := by
  intro m hm
  refine rowSOf429_of_noCfg fun S _ _ hs hna ⟨e⟩ => ?_
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hm e
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e'⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
  exact noCfgS429_of_reeGamma ha hK e'

end F4

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
