module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowCover
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieD4
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27Exc
public import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.Assembly.RankThreeEven (projSU)


section Orders

theorem padicValNat_ordTwistedF4_two_pow {e : ℕ} (he : 1 ≤ e) :
    padicValNat 2 (CFSG.Open.ordTwistedF4 (2 ^ e)) = 12 * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Even (2 ^ e) := (Nat.even_pow' (by omega)).mpr even_two
  have h1 : Odd ((2 ^ e) ^ 6 + 1) := ((Nat.even_pow' (by norm_num)).mpr hq).add_one
  have h2 : Odd ((2 ^ e) ^ 4 - 1) := CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)
  have h3 : Odd ((2 ^ e) ^ 3 + 1) := ((Nat.even_pow' (by norm_num)).mpr hq).add_one
  have h4 : Odd (2 ^ e - 1) := by
    have := CFSG.Timmesfeld.Orders.odd_pow_sub_one (f := e) (a := 1) (by omega) (by norm_num)
    rwa [pow_one] at this
  have hodd := h1.mul (h2.mul (h3.mul h4))
  rw [CFSG.Open.ordTwistedF4, mul_assoc, mul_assoc, mul_assoc,
    padicValNat.mul (by positivity) hodd.pos.ne',
    padicValNat.eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero, ← pow_mul,
    padicValNat.prime_pow, mul_comm]

end Orders

section F4


theorem false_of_f4_cover (k : Type) [Field k] [Finite k] [CharP k ReeTag.F4.prime] (b : ℕ)
    (hk : Nat.card k = 2 ^ (2 * b + 1)) {G : Type} [Group G] {C Y : Subgroup G}
    (eC : C ≃* ReeTag.F4.reeGamma k b) (hYC : Y ≤ C) [Group.IsPerfect Y]
    (hsub : (Y.subgroupOf C).IsSubnormal) {m : ℕ} (hmo : Odd m) (hm1 : 1 < m)
    (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardC : Nat.card C = CFSG.Open.ordTwistedF4 (2 ^ (2 * b + 1)) :=
    Sec8.Item86ResProof.card_of_mulEquiv_reeGamma b k hk eC
  have hU := padicValNat_card_projSU (by omega : 1 ≤ m)
  have hU1 := one_lt_card_projSU (by omega : 1 ≤ m)
  have hdU : Nat.card (projSU 3 2 m) ∣ Nat.card Y := Subgroup.card_dvd_of_surjective hπ
  have hdY : Nat.card Y ∣ Nat.card C := Subgroup.card_dvd_of_le hYC
  rcases Nat.eq_zero_or_pos b with rfl | hb
  ·
    have h := hdU.trans hdY
    rw [hcardC] at h
    have h2 : 2 ^ (3 * m) ∣ Nat.card (projSU 3 2 m) := hU ▸ pow_padicValNat_dvd
    have hm3 : m = 3 := by
      by_contra hne
      have hm5 : 5 ≤ m := by
        obtain ⟨j, rfl⟩ := hmo
        omega
      have h15 : 2 ^ 15 ∣ 2 ^ (3 * m) := pow_dvd_pow 2 (by omega)
      have := (h15.trans h2).trans h
      norm_num [CFSG.Open.ordTwistedF4] at this
    subst hm3
    rw [CFSG.PGLModel.card_projSU_three_eight] at h
    norm_num [CFSG.Open.ordTwistedF4] at h
  ·
    haveI : IsSimpleGroup (ReeTag.F4.reeGamma k b) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hk
    haveI hCs : IsSimpleGroup C := eC.isSimpleGroup
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hCs hsub with h | h
    ·
      have hY1 : Y = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have : (⟨y, hYC hy⟩ : C) ∈ Y.subgroupOf C := hy
        rw [h, Subgroup.mem_bot] at this
        rw [Subgroup.mem_bot]
        exact congrArg Subtype.val this
      rw [hY1, Subgroup.card_bot] at hdU
      have := Nat.le_of_dvd (by norm_num) hdU
      omega
    ·
      have hYeq : Y = C := by
        refine le_antisymm hYC fun y hy => ?_
        have : (⟨y, hy⟩ : C) ∈ Y.subgroupOf C := by
          rw [h]
          exact Subgroup.mem_top _
        exact this
      have eY : Y ≃* C := MulEquiv.subgroupCongr hYeq
      haveI : IsSimpleGroup Y := eY.isSimpleGroup
      have hcY := card_eq_of_isSimpleGroup_surj π hπ hU1
      have hv := padicValNat_ordTwistedF4_two_pow (by omega : 1 ≤ 2 * b + 1)
      rw [← hcardC, ← Nat.card_congr eY.toEquiv, hcY, hU] at hv
      obtain ⟨j, rfl⟩ := hmo
      omega

theorem rowU3_F4 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : ReeTitsModel S .twistedF4 2 f) {σ : MulAut S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    {Y : Subgroup S} (hYC : Y ≤ Sec4.autFix σ) [Group.IsPerfect Y]
    (hsub : (Y.subgroupOf (Sec4.autFix σ)).IsSubnormal) {m : ℕ} (hmo : Odd m) (hm1 : 1 < m)
    (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) : False := by
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨τ⟩⟩ := Sec4.exists_mulEquiv_reeGamma hm
  obtain ⟨E, hEY, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_cover hmo hm1 π hπ hker
  have hfix : ∀ k ∈ Y, σ k = k := fun k hk => Sec4.mem_autFix.mp (hYC hk)
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
    refine RonanK429Lie.false_of_fix_e9_of_mulEquiv τ
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut _).range ?_ (fun s => ⟨s, rfl⟩) hZ hin
      hσ3 hσ1 hEY hEc hE3 hE9 hfix hEZ
    intro B hB h3B hcB
    exact RonanK429Lie.card_le_nine_inn (fun E hE h27 =>
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
      exact (RonanK429Lie.autFixConjEquiv (MulAut.conj g) γ).trans eγ
    exact false_of_f4_cover (fixSubfield p.right) b hkcard
      ((Sec4.autFixCongrEquiv τ σ).symm.trans eα) hYC hsub hmo hm1 π hπ

end F4

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
