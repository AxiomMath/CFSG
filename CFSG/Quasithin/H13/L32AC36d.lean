module

public import CFSG.Quasithin.Background.SmithB45MatMain
public import CFSG.Quasithin.EmptyFaithful.LRed5Plumb
public import CFSG.Quasithin.H13.L32AC36c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Mathieu
  CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.Family
open CFSG.Quasithin CFSG.Quasithin.B45Mat

section Code

variable {V : Type} [CommGroup V] [Finite V]

theorem code22_of_qhat
    (hIrr : MathieuSmallIrr22) (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) (hT : B45TypeSpor .M22 ↥L)
    (h2 : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) :
    (MathieuCode22 L ⊤ ⊥ ∧ ((2 : ℚ) : WithTop ℚ) ≤ qOf G) ∨
      (MathieuCocode22 L ⊤ ⊥ ∧ ((2 : ℚ) : WithTop ℚ) < qOf G) := by
  obtain ⟨hZ, ⟨θ⟩⟩ := hT
  have θ' : ↥L ≃* S22 := θ
  obtain ⟨hnt, hirr, hLG, hGN⟩ := b4Hyp_facts hHyp
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr' : IsIrrOn L := ⟨hnt, hirr⟩
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp h2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  have hAidx := B45Exc.index_le_sq_of_offender2 A hAV
  have e := cqEquiv hZ θ'
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hV30 : Nat.card V ≤ 2 ^ 30 := by
    rcases out2_dichotomy_gen hW hHyp.2.2.1.1 hirr' (hA.1.trans hGN) hA.isElemAbelian2 e
      m22_center_eq_bot' m22_mulAut_card (k := 3 + 1) (p := 11) (by norm_num)
      (fun ψ hψ hψ2 => m22_outer_gen ψ hψ2 hψ) with hAL | ⟨hdisp, hcardE⟩
    · have hcardA : Nat.card A ≤ 2 ^ 4 :=
        card_le_two_pow_of_le hW hirr' hAL hA.isElemAbelian2 e m22_rank_le
      obtain ⟨⟨b, hbA⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.ne_bot
      have := card_le_of_offender_mem θ' m22_gen3 hirr hA.isElemAbelian2 hAV hcardA hbA
        (hAL hbA) (fun h => hb1 (Subtype.ext h))
      calc Nat.card V ≤ 2 ^ (6 * 4) := this
        _ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    · rw [orderOf_two_zmod_11] at hdisp
      have hE0el : IsElemAbelian2 (A ⊓ L) :=
        ⟨fun a ha b hb => hA.isElemAbelian2.1 a ha.1 b hb.1, fun a ha => hA.isElemAbelian2.2 a ha.1⟩
      have hE0card : Nat.card ↥(A ⊓ L) ≤ 2 ^ 4 :=
        card_le_two_pow_of_le hW hirr' inf_le_right hE0el e m22_rank_le
      have hA4 : 4 ≤ Nat.card A := by
        by_contra hlt
        push Not at hlt
        have hc := B45Mat.card_eq_two_pow_rk hA.isElemAbelian2
        have hA2 : Nat.card A ≤ 2 := by
          rw [hc] at hlt ⊢
          have : rk ↥A < 2 := by
            by_contra h
            push Not at h
            have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
            omega
          calc 2 ^ rk ↥A ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 2 := by norm_num
        have h1 : (fixV A).index ≤ 2 ^ 2 := hAidx.trans (Nat.pow_le_pow_left hA2 2)
        have h2 : (fixV A).index ^ (3 + 1) ≤ (2 ^ 2) ^ (3 + 1) := Nat.pow_le_pow_left h1 _
        have h3 := hdisp.trans h2
        norm_num at h3
      have hE02 : 2 ≤ Nat.card ↥(A ⊓ L) := by omega
      obtain ⟨b, hb, hb1⟩ := exists_ne_one_of_two_le hE02
      have hcardA : Nat.card A ≤ 2 ^ 5 := by
        calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L) := hcardE
          _ ≤ 2 * 2 ^ 4 := Nat.mul_le_mul le_rfl hE0card
          _ = 2 ^ 5 := by norm_num
      exact card_le_of_offender_mem θ' m22_gen3 hirr hA.isElemAbelian2 hAV hcardA hb.1 hb.2 hb1
  have hLG' : IsOver L G := ⟨hLG, hGN⟩
  rcases hIrr V hW L ⟨θ⟩ hirr hV30 with hc | hc
  · exact Or.inl ⟨hc, two_le_qOf_code22 hLG' hc⟩
  · exact Or.inr ⟨hc, two_lt_qOf_cocode22 hLG' hc⟩

end Code

section NoFF

open CFSG.Open (pCoreOf)
open CFSG.LieType.BorelTits CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

theorem noFaithfulFF_m22 (h56 : AsB56) {X K T : Subgroup G}
    (hK : K ∈ cComp X) (hKnorm : (K.subgroupOf X).Normal) (hXeq : X = K ⊔ T) (hTX : T ≤ X)
    (hT2 : IsPGroup 2 T) (hsqtk : SQTKGroup ↥X) (hM : IsSporadic .M22 (KBar K)) :
    HasNoFaithfulFFModulesMod X (pCoreOf 2 X) := by
  intro W _ _ hW ρ hker hff
  have hKX : K ≤ X := le_of_mem_cComp hK
  set Γ := ρ.range with hΓ
  set Lg := (K.subgroupOf X).map ρ with hL
  obtain ⟨e⟩ := LRed5.kbar_equiv_image hK ρ hker
  obtain ⟨eM⟩ := hM
  have hsM : IsSimpleGroup ↥NativeSporadic.M22 := fam_m22_simplicity.2.2
  have eL : ↥Lg ≃* ↥NativeSporadic.M22 := e.symm.trans eM
  have hLsimple : IsSimpleGroup ↥Lg := eL.isSimpleGroup
  have hcardL : Nat.card ↥Lg = 2 ^ 7 * 3465 := by
    rw [Nat.card_congr eL.toEquiv, card_M22]
    norm_num
  have hLΓ : Lg ≤ Γ := Subgroup.map_le_range ρ _
  have hn : (Lg.subgroupOf Γ).Normal := by
    have hrs : Lg.subgroupOf Γ = (K.subgroupOf X).map ρ.rangeRestrict := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [hrs]
    exact hKnorm.map ρ.rangeRestrict ρ.rangeRestrict_surjective
  set T₀ := (T.subgroupOf X).map ρ with hT₀
  have hT₀2 : IsPGroup 2 T₀ := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm).map ρ
  have hT₀Γ : T₀ ≤ Γ := Subgroup.map_le_range ρ _
  have hΓeq : Γ = Lg ⊔ T₀ := by
    have h1 : (K.subgroupOf X) ⊔ (T.subgroupOf X) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKX hTX, ← hXeq]
      exact Subgroup.subgroupOf_self _
    rw [hΓ, MonoidHom.range_eq_map, ← h1, Subgroup.map_sup]
  have hO2 : pCoreOf 2 Γ = ⊥ := LRed5.pCoreOf_range_eq_bot ρ hker
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hK)
  have hpKbar : Group.IsPerfect (KBar K) := inferInstance
  have hperfL : Group.IsPerfect ↥Lg :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hcenter : Subgroup.center ↥Lg = ⊥ := center_eq_bot_of_simple_perfect hperfL
  have hnc : ∃ a b : ↥Lg, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have htop : Subgroup.center ↥Lg = ⊤ :=
      eq_top_iff.2 fun x _ => Subgroup.mem_center_iff.2 fun y => hcon y x
    rw [hcenter] at htop
    have h1 : Nat.card ↥Lg = 1 := by
      rw [← Subgroup.card_top (G := ↥Lg), ← htop, Subgroup.card_bot]
    rw [hcardL] at h1
    norm_num at h1
  have hZ : ∀ x ∈ Lg, (∀ y ∈ Lg, x * y = y * x) → x = 1 := by
    intro x hx hxc
    have : (⟨x, hx⟩ : ↥Lg) ∈ Subgroup.center ↥Lg :=
      Subgroup.mem_center_iff.2 fun z => Subtype.ext (hxc z z.2).symm
    rw [hcenter, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hC := LRed5.centralizer_eq_bot_of_two_quotient hLΓ hn hZ hT₀Γ hT₀2 hΓeq hO2
  have hq : CFSG.IsQuasisimple ↥Lg := LRed5.isQuasisimple_of_simple_nonabelian hperfL hnc
  have hQ : G64.IsQuotientOfSQTKCat ↥Γ :=
    ⟨↥X, inferInstance, inferInstance, ρ.ker, inferInstance, SQTKGroup.isSQTKCat hsqtk,
      ⟨(QuotientGroup.quotientKerEquivRange ρ).symm⟩⟩
  have hoff : ∃ A : Subgroup (MulAut W), IsFFStarOffender Γ A := B6.exists_isFFStarOffender hff
  have hV : ∀ v : W, v * v = 1 := fun v => by rw [← sq]; exact hW v
  exact false_of_ff_card h56 hV hQ hLΓ hn hC hq (m := 3465) (by decide) (by decide) hcardL hoff

end NoFF

end CFSG.Quasithin.H13.L32A.C
