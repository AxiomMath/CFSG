module

public import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha
import CFSG.RankThree.PartTwo.Sec13.Item13Theta

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Alpha131Pair {G : Type} [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  c ∈ L ∧ Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 ∧
    ∃ y : L ⧸ aschbacherSolvableCore 3 L, MulAut.conj y ∈ Sec4.autThetaQuot A L ∧
      ∃ β ∈ Sec4.autThetaQuot A L, β y ≠ y

@[expose] def KS131AlphaCentralNoPair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → A ⊓ L ≤ Subgroup.zpowers c → ¬ Alpha131Pair A c L →
    thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
        (Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L)) ≠ ⊥

namespace Item131bProof

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem thetaQuotMulAut_normalizer_mk {h : G} (hN : h ∈ Subgroup.normalizer (L : Set G)) (l : L) :
    Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨h, hN⟩)
        (l : L ⧸ aschbacherSolvableCore 3 L) =
      ((L.normalizerMonoidHom ⟨h, hN⟩ l : L) : L ⧸ aschbacherSolvableCore 3 L) :=
  Sec4.thetaQuotMulAut_mk _ l

theorem mem_autThetaQuot_centralizer_of_pair (hD : Sec13Data G A c L) (hP : Alpha131Pair A c L)
    {t : MulAut (L ⧸ aschbacherSolvableCore 3 L)}
    (ht : t ∈ Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L)
    (htB : ∀ b ∈ Sec4.autThetaQuot A L, t * b = b * t) :
    t ∈ Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L := by
  obtain ⟨hcL, hZ3, y, hyB, β, hβB, hβy⟩ := hP
  set cb : L ⧸ aschbacherSolvableCore 3 L :=
    ((⟨c, hcL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) with hcb
  have hc3 : c ^ 3 = 1 := by rw [← hD.orderOf_eq]; exact pow_orderOf_eq_one c
  have hcbZ : cb ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    refine Subgroup.mem_center_iff.mpr fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H l =>
      have h1 : (l : G) * c = c * l :=
        Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer l.2)
      rw [hcb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext h1
  have hcb1 : cb ≠ 1 := by
    intro h1
    rw [hcb, QuotientGroup.eq_one_iff] at h1
    exact hD.ne_one (eq_one_of_mem_inSubgroup_theta_of_pow_three ⟨_, h1, rfl⟩ hc3)
  have hcb3 : cb ^ 3 = 1 := by
    rw [hcb, ← QuotientGroup.mk_pow]
    have : (⟨c, hcL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, QuotientGroup.mk_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = Subgroup.zpowers cb := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcbZ) ?_).symm
    rw [hZ3, Nat.card_zpowers, orderOf_eq_prime hcb3 hcb1]
  have hBc : ∀ b ∈ Sec4.autThetaQuot A L, b cb = cb := by
    intro b hb
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hb
    rw [hcb, thetaQuotMulAut_normalizer_mk]
    congr 1
    apply Subtype.ext
    change a * c * a⁻¹ = c
    rw [hD.commute haA hD.mem_A, mul_inv_cancel_right]
  have hBZ : ∀ b ∈ Sec4.autThetaQuot A L,
      ∀ z ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L), b z = z := by
    intro b hb z hz
    rw [hZ] at hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [map_zpow, hBc b hb]
  have hcent : ∀ σ : MulAut (L ⧸ aschbacherSolvableCore 3 L),
      σ * MulAut.conj y = MulAut.conj y * σ →
      y⁻¹ * σ y ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    intro σ hσ
    refine Subgroup.mem_center_iff.mpr fun w => ?_
    have h1 := congrArg (fun f : MulAut (L ⧸ aschbacherSolvableCore 3 L) => f (σ.symm w)) hσ
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.apply_symm_apply, map_mul,
      map_inv] at h1
    calc w * (y⁻¹ * σ y) = y⁻¹ * (y * w * y⁻¹) * σ y := by group
      _ = y⁻¹ * (σ y * w * (σ y)⁻¹) * σ y := by rw [h1]
      _ = y⁻¹ * σ y * w := by group
  have hβc : β * MulAut.conj y = MulAut.conj y * β :=
    autThetaQuot_commute (fun x hx z hz => hD.commute hx hz) hβB hyB
  set u := y⁻¹ * β y with hu
  have huZ : u ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := hcent β hβc
  have hu1 : u ≠ 1 := fun h => hβy (by
    have : β y = y * u := by rw [hu]; group
    rw [this, h, mul_one])
  set z := y⁻¹ * t y with hz
  have hzZ : z ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := hcent t (htB _ hyB)
  have htu : t u = u := by
    have h1 : t (β y) = β (t y) := by
      have := congrArg (fun f : MulAut (L ⧸ aschbacherSolvableCore 3 L) => f y) (htB β hβB)
      simpa only [MulAut.mul_apply] using this
    have hβy' : β y = y * u := by rw [hu]; group
    have hty : t y = y * z := by rw [hz]; group
    have hL : t (β y) = y * z * t u := by rw [hβy', map_mul, hty]
    have hR : β (t y) = y * u * z := by rw [hty, map_mul, hβy', hBZ β hβB z hzZ]
    have h2 : y * z * t u = y * u * z := by rw [← hL, ← hR, h1]
    have hcomm : u * z = z * u := Subgroup.mem_center_iff.mp hzZ u
    calc t u = (y * z)⁻¹ * (y * z * t u) := by group
      _ = (y * z)⁻¹ * (y * u * z) := by rw [h2]
      _ = z⁻¹ * (u * z) := by group
      _ = u := by rw [hcomm]; group
  have htc : t cb = cb := by
    have hu' : u ∈ Subgroup.zpowers cb := hZ ▸ huZ
    have hzp : Subgroup.zpowers u = Subgroup.zpowers cb := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu') ?_
      have hu3 : u ^ 3 = 1 := by
        have h := orderOf_dvd_of_mem_zpowers hu'
        rw [orderOf_eq_prime hcb3 hcb1] at h
        exact orderOf_dvd_iff_pow_eq_one.mp h
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hcb3 hcb1,
        orderOf_eq_prime hu3 hu1]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ Subgroup.mem_zpowers cb)
    rw [← hk, map_zpow, htu]
  obtain ⟨h, hN, hH, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp ht
  refine Sec4.mem_autThetaQuot_iff.mpr ⟨h, hN, ?_, rfl⟩
  rw [hcb, thetaQuotMulAut_normalizer_mk] at htc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp hH c).mp (Subgroup.mem_zpowers c))
  have hmem := QuotientGroup.eq.mp htc
  have hθ : (h * c * h⁻¹)⁻¹ * c ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    ⟨_, hmem, by
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
        Sec4.normalizerMonoidHom_apply_coe]⟩
  have hcube : ((h * c * h⁻¹)⁻¹ * c) ^ 3 = 1 := by
    have hck : (c ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
    have hcomm : Commute ((c ^ k)⁻¹) c := (Commute.zpow_left (Commute.refl c) k).inv_left
    rw [← hk, hcomm.mul_pow, inv_pow, hck, inv_one, one_mul, hc3]
  have h1 := eq_one_of_mem_inSubgroup_theta_of_pow_three hθ hcube
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2 : h * c * h⁻¹ = c := by
    calc h * c * h⁻¹ = h * c * h⁻¹ * ((h * c * h⁻¹)⁻¹ * c) := by rw [h1, mul_one]
      _ = c := by group
  calc h * c = h * c * h⁻¹ * h := by group
    _ = c * h := by rw [h2]

end Item131bProof

open Item131bProof

theorem ks131AlphaInvolutionCentral_of_noPair (h : KS131AlphaCentralNoPair) :
    KS131AlphaInvolutionCentral := by
  intro G _ _ A c L hD hAL hα t ht _
  by_cases hP : Alpha131Pair A c L
  · refine mem_autThetaQuot_centralizer_of_pair hD hP t.2 fun b hb => ?_
    have hbX : b ∈ Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L :=
      autThetaQuot_mono (hD.A_le_centralizer.trans (centralizer_le_normalizer_zpowers c)) L hb
    set b' : Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L := ⟨b, hbX⟩
    by_cases hb1 : b' = 1
    · have : b = 1 := congrArg Subtype.val hb1
      rw [this, mul_one, one_mul]
    · have hb' : b' ∈ (Sec4.autThetaQuot A L).subgroupOf
          (Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L) :=
        Subgroup.mem_subgroupOf.mpr hb
      have htC : t ∈ Subgroup.centralizer ({b'} : Set _) := by
        have h1 : t ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b'} : Set _)) :=
          by
            simp only [thetaT, Subgroup.mem_iInf] at ht
            exact ht b' hb' hb1
        exact Subgroup.map_subtype_le _ h1
      have h2 := Subgroup.mem_centralizer_singleton_iff.mp htC
      have h3 := congrArg Subtype.val h2
      simpa only [Subgroup.coe_mul] using h3
  · exact absurd hα (h G A c L hD hAL hP)

theorem ks131AlphaCentralNoPair_of (h : KS131AlphaInvolutionCentral) :
    KS131AlphaCentralNoPair := by
  intro G _ _ A c L hD hAL _ hα
  apply hD.mem_lA.2.2.2
  exact thetaAlpha_subgroupOf_eq_bot_of_le (autThetaQuot_mono hD.A_le_centralizer L)
    (autThetaQuot_mono (centralizer_le_normalizer_zpowers c) L)
    (autThetaQuot_centralizer_normal c L)
    (fun β hβ => autThetaQuot_pow_three hD.isElemAbelian.2 hβ)
    (fun β hβ γ hγ => autThetaQuot_commute (fun x hx y hy => hD.commute hx hy) hβ hγ)
    (fun x hx => sq_mem_autThetaQuot_centralizer hD.orderOf_eq L hx) hα
    (h G A c L hD hAL hα)

end CFSG.RankThree.PartTwo.Sec13
