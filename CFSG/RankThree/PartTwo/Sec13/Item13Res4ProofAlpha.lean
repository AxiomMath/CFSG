module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res4ProofCensus
public import CFSG.RankThree.PartTwo.Sec13.Item131bProofAlpha
import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res4Proof

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem exists_mem_of_invariant (hD : Sec13Data G A c L)
    {Y : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    (hY : ∀ β ∈ Sec4.autThetaQuot A L, ∀ y ∈ Y, β y ∈ Y) (h3 : 3 ∣ Nat.card Y) :
    ∃ z ∈ A, ∃ hz : z ∈ L, orderOf z = 3 ∧
      ((⟨z, hz⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈ Y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 L with hθ
  set ρ := QuotientGroup.mk' θ with hρ
  set Yh : Subgroup L := Y.comap ρ with hYh
  set W : Subgroup G := Yh.map L.subtype with hW
  have hW3 : 3 ∣ Nat.card W := by
    rw [hW, Subgroup.card_map_of_injective L.subtype_injective]
    exact h3.trans (Subgroup.card_dvd_of_surjective
      (ρ.subgroupComap_surjective _ (QuotientGroup.mk'_surjective θ)))
  have hAW : ∀ a ∈ A, ∀ w ∈ W, a * w * a⁻¹ ∈ W := by
    intro a ha w hw
    obtain ⟨l, hl, rfl⟩ := hw
    have haN : a ∈ Subgroup.normalizer (L : Set G) := hD.le_normalizer ha
    set σ := L.normalizerMonoidHom ⟨a, haN⟩ with hσ
    refine ⟨σ l, ?_, rfl⟩
    change ρ (σ l) ∈ Y
    have hmap : ρ (σ l) = Sec4.thetaQuotMulAut L σ (ρ l) := rfl
    rw [hmap]
    exact hY _ (Sec4.mem_autThetaQuot_iff.mpr ⟨a, haN, ha, rfl⟩) _ hl
  have hAe := hD.isElemAbelian
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  let _ : MulAction A W :=
    { smul := fun a w => ⟨(a : G) * w * (a : G)⁻¹, hAW a a.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ((1 : A) : G) * (w : G) * ((1 : A) : G)⁻¹ = (w : G)
        simp)
      mul_smul := fun a₁ a₂ w => Subtype.ext (by
        show ((a₁ * a₂ : A) : G) * (w : G) * ((a₁ * a₂ : A) : G)⁻¹ =
          (a₁ : G) * ((a₂ : G) * (w : G) * (a₂ : G)⁻¹) * (a₁ : G)⁻¹
        simp [mul_assoc]) }
  have hsmul : ∀ (a : A) (w : W), ((a • w : W) : G) = (a : G) * w * (a : G)⁻¹ := fun _ _ => rfl
  set F : Subgroup G := W ⊓ Subgroup.centralizer (A : Set G) with hF
  have hfix : Nat.card (MulAction.fixedPoints A W) = Nat.card F := by
    refine Nat.card_congr
      { toFun := fun w => ⟨(w.1 : G), w.1.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
        invFun := fun f => ⟨⟨f.1, f.2.1⟩, fun a => Subtype.ext ?_⟩
        left_inv := fun w => rfl
        right_inv := fun f => rfl }
    · have h1 := congrArg Subtype.val (w.2 ⟨a, ha⟩)
      rw [hsmul] at h1
      calc a * (w.1 : G) = a * (w.1 : G) * a⁻¹ * a := by group
        _ = (w.1 : G) * a := by rw [h1]
    · rw [hsmul]
      have h1 := Subgroup.mem_centralizer_iff.mp f.2.2 a a.2
      change (a : G) * f.1 * (a : G)⁻¹ = f.1
      rw [h1, mul_inv_cancel_right]
  have hF3 : 3 ∣ Nat.card F := by
    have hmod := hAp.card_modEq_card_fixedPoints W
    rw [hfix] at hmod
    exact (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hW3)))
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := F) 3 hF3
  have hzW : (z : G) ∈ W := z.2.1
  have hzA' : ∀ a ∈ A, a * (z : G) = (z : G) * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp z.2.2 a ha
  have hz3 : (z : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hzo : orderOf (z : G) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hsup := isElemAbelian_sup hAe (isElemAbelian_zpowers hz3) (by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (hzA' x hx) k).eq)
  have hzA : (z : G) ∈ A := by
    rw [← hD.eq_of_le hsup le_sup_left]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨zl, hzl, hzle⟩ := hzW
  have hzL : (z : G) ∈ L := hzle ▸ zl.2
  refine ⟨z, hzA, hzL, hzo, ?_⟩
  have hzz : (⟨(z : G), hzL⟩ : L) = zl := Subtype.ext hzle.symm
  rw [hzz]
  exact hzl

theorem mem_map_of_fixed (hD : Sec13Data G A c L) {x : L ⧸ aschbacherSolvableCore 3 L}
    (hx3 : orderOf x = 3) (hfix : ∀ β ∈ Sec4.autThetaQuot A L, β x = x) :
    x ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
  have hY : ∀ β ∈ Sec4.autThetaQuot A L, ∀ y ∈ Subgroup.zpowers x,
      β y ∈ Subgroup.zpowers x := by
    intro β hβ y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [map_zpow, hfix β hβ]
    exact zpow_mem (Subgroup.mem_zpowers x) k
  have h3 : 3 ∣ Nat.card (Subgroup.zpowers x) := by rw [Nat.card_zpowers, hx3]
  obtain ⟨z, hzA, hzL, hzo, hzx⟩ := exists_mem_of_invariant hD hY h3
  set zb : L ⧸ aschbacherSolvableCore 3 L := ((⟨z, hzL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)
    with hzb
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hzb1 : zb ≠ 1 := by
    intro h1
    rw [hzb, QuotientGroup.eq_one_iff] at h1
    have hz1 : z = 1 := eq_one_of_mem_inSubgroup_theta_of_pow_three ⟨_, h1, rfl⟩ hz3
    rw [hz1, orderOf_one] at hzo
    omega
  have hzb3 : zb ^ 3 = 1 := by
    rw [hzb, ← QuotientGroup.mk_pow]
    have : (⟨z, hzL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this, QuotientGroup.mk_one]
  have heq : Subgroup.zpowers zb = Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzx) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hx3, orderOf_eq_prime hzb3 hzb1]
  have hxz : x ∈ Subgroup.zpowers zb := heq ▸ Subgroup.mem_zpowers x
  have hzbZ : zb ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :=
    ⟨⟨z, hzL⟩, Subgroup.mem_subgroupOf.mpr hzA, rfl⟩
  exact Subgroup.zpowers_le.mpr hzbZ hxz

theorem map_le_center (hD : Sec13Data G A c L) (hAL : A ⊓ L ≤ Subgroup.zpowers c) :
    (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ≤
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro q
  induction q using QuotientGroup.induction_on with
  | H l =>
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have hac : (a : G) ∈ Subgroup.zpowers c := hAL ⟨haA, a.2⟩
    have hlc : Commute (l : G) c :=
      Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer l.2)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hac
    have hcomm : (l : G) * a = a * l := by
      rw [← hk]
      exact (hlc.zpow_right k).eq
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hcomm

theorem card_map_dvd_three (hD : Sec13Data G A c L) (hAL : A ⊓ L ≤ Subgroup.zpowers c) :
    Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) ∣ 3 := by
  have h1 := Subgroup.card_map_dvd (A.subgroupOf L) (QuotientGroup.mk' (aschbacherSolvableCore 3 L))
  have h2 : Nat.card (A.subgroupOf L) = Nat.card (A ⊓ L : Subgroup G) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective L.subtype_injective]
  have h3 : Nat.card (A ⊓ L : Subgroup G) ∣ 3 := by
    rw [← hD.card_zpowers]
    exact Subgroup.card_dvd_of_le hAL
  exact h1.trans (h2 ▸ h3)

theorem mem_of_card_map_eq_three (hD : Sec13Data G A c L) (hAL : A ⊓ L ≤ Subgroup.zpowers c)
    (h : Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) = 3) :
    c ∈ L := by
  have hne : (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at h
    omega
  obtain ⟨⟨_, a, ha, rfl⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha1' : (a : G) ≠ 1 := by
    intro h1
    apply ha1
    have : a = 1 := Subtype.ext h1
    apply Subtype.ext
    simp [this]
  have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have hac : (a : G) ∈ Subgroup.zpowers c := hAL ⟨haA, a.2⟩
  have ha3 : (a : G) ^ 3 = 1 := hD.isElemAbelian.2 _ haA
  have heq : Subgroup.zpowers (a : G) = Subgroup.zpowers c := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hac) ?_
    rw [hD.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ha3 ha1']
  have hca : c ∈ Subgroup.zpowers (a : G) := heq ▸ Subgroup.mem_zpowers c
  exact Subgroup.zpowers_le.mpr a.2 hca

theorem isElemAbelian_autThetaQuot (hD : Sec13Data G A c L) :
    CFSG.Assembly.IsElemAbelian 3 (Sec4.autThetaQuot A L) ∧
      Nat.card (Sec4.autThetaQuot A L) = 9 := by
  refine ⟨⟨⟨⟨fun β γ => Subtype.ext
    (autThetaQuot_commute (fun x hx y hy => hD.commute hx hy) β.2 γ.2)⟩⟩,
    fun β hβ => autThetaQuot_pow_three hD.isElemAbelian.2 hβ⟩, ?_⟩
  have h := card_inf_mul_card_autThetaQuot hD.le_normalizer
  have hsc := hD.sectionCentralizer_eq
  rw [sectionCentralizer_eq_inf hD.le_normalizer] at hsc
  have heq : (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = Subgroup.zpowers c :=
    SetLike.coe_injective hsc
  have h3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 := by
    rw [heq, hD.card_zpowers]
  rw [h3, hD.card_eq] at h
  omega

theorem exists_isList46 (h46 : Sec4.Item4_6) (hD : Sec13Data G A c L) :
    ∃ (X' : Type) (_ : Group X') (_ : Finite X'),
      Sec4.IsList46 X' ∧ Nonempty (X' ≃* L ⧸ aschbacherSolvableCore 3 L) := by
  have hst := hD.toPartTwoStanding
  have hc1 := hD.ne_one
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsIn_iff.mp hD.mem_thetaComponentsAt
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have hcZ : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have hg : g ∈ C := hCt ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases hst.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h, Subgroup.mem_bot] at hcZ
      exact hc1 hcZ
    · obtain ⟨a, b, hab⟩ := hst.nonabelian
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hS4 : SectionFourHyp C := hst.toTheoremFourHyp.sectionFourHyp hCtop
  have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have h3C : 3 ∣ Nat.card (Subgroup.center C) := by
    have hz : (⟨c, hcC⟩ : C) ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)
    have hord : orderOf (⟨⟨c, hcC⟩, hz⟩ : Subgroup.center C) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hD.orderOf_eq]
    exact hord ▸ orderOf_dvd_natCard _
  set e₀ := Subgroup.subgroupOfEquivOfLe hLC with he₀
  exact ⟨_, inferInstance, inferInstance, h46 C hS4 h3C _ hL',
    ⟨QuotientGroup.congr _ _ e₀ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₀)⟩⟩

end Res4Proof

open Res4Proof

theorem ks131AlphaCentralNoPair_of_census (h46 : Sec4.Item4_6) (hK : KS131CentralCensus) :
    KS131AlphaCentralNoPair := by
  intro G _ _ A c L hD hAL hNP
  exfalso
  obtain ⟨X', _, _, hl, ⟨e⟩⟩ := exists_isList46 h46 hD
  obtain ⟨hBe, hB9⟩ := isElemAbelian_autThetaQuot hD
  refine hK.false_of_mulEquiv e hl
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) hBe hB9
    (map_le_center hD hAL) (card_map_dvd_three hD hAL)
    (fun x hx3 hfix => mem_map_of_fixed hD hx3 hfix) ?_
  intro hZ3 hC3 y hy β hβ
  by_contra hβy
  exact hNP ⟨mem_of_card_map_eq_three hD hAL hZ3, hC3, y, hy, β, hβ, hβy⟩

theorem ks131AlphaInvolutionCentral_of_census (h46 : Sec4.Item4_6) (hK : KS131CentralCensus) :
    KS131AlphaInvolutionCentral :=
  ks131AlphaInvolutionCentral_of_noPair (ks131AlphaCentralNoPair_of_census h46 hK)

theorem ks131AlphaCentralNoPair_of_kfacts (h46 : Sec4.Item4_6) (h1 : KS131ThreeFreeNoE9)
    (h2 : KS131CenterList46) (h3 : KS131CenterOuterE9) : KS131AlphaCentralNoPair :=
  ks131AlphaCentralNoPair_of_census h46 (ks131CentralCensus_of h1 h2 h3)

theorem ks131AlphaInvolutionCentral_of_kfacts (h46 : Sec4.Item4_6) (h1 : KS131ThreeFreeNoE9)
    (h2 : KS131CenterList46) (h3 : KS131CenterOuterE9) : KS131AlphaInvolutionCentral :=
  ks131AlphaInvolutionCentral_of_census h46 (ks131CentralCensus_of h1 h2 h3)

end CFSG.RankThree.PartTwo.Sec13
