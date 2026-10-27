module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res2ProofCube
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
public import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha
import CFSG.GroupTheory.SteinbergBSQuotientLifting

public section

namespace CFSG.RankThree.PartTwo.Sec13.Res2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem exists_cube_root_lift {H : Type*} [Group H] [Finite H] {Θ : Subgroup H} [Θ.Normal]
    (hΘ : ¬ 3 ∣ Nat.card Θ) {Y : Subgroup H} {e c h : H} (heY : e ∈ Y) (hcY : c ∈ Y)
    (hhY : h ∈ Y) (hcC : ∀ y ∈ Y, y * c = c * y) (he3 : e ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (hhe : h * e * h⁻¹ * e⁻¹ ∈ Θ) (hhc : h ^ 3 * c⁻¹ ∈ Θ) :
    ∃ x ∈ Y, x * e = e * x ∧ x ^ 3 = c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup Y := Θ.subgroupOf Y with hN
  have hN3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    apply hΘ
    refine h3.trans ?_
    have e1 : Nat.card N = Nat.card (Θ ⊓ Y : Subgroup H) := by
      rw [hN, ← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [e1]
    exact Subgroup.card_dvd_of_le inf_le_left
  set eY : Y := ⟨e, heY⟩ with heYdef
  set hY : Y := ⟨h, hhY⟩ with hhYdef
  have heY3 : eY ^ 3 = 1 := Subtype.ext (by simpa [heYdef] using he3)
  have hQ : IsPGroup 3 (Subgroup.zpowers eY) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, heY3, one_zpow]
  have hcommbar : QuotientGroup.mk' N hY * QuotientGroup.mk' N eY =
      QuotientGroup.mk' N eY * QuotientGroup.mk' N hY := by
    have h1 : hY * eY * hY⁻¹ * eY⁻¹ ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf]
      simpa [hhYdef, heYdef] using hhe
    have h2 : QuotientGroup.mk' N (hY * eY * hY⁻¹ * eY⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h1
    simp only [map_mul, map_inv] at h2
    calc QuotientGroup.mk' N hY * QuotientGroup.mk' N eY =
        (QuotientGroup.mk' N hY * QuotientGroup.mk' N eY * (QuotientGroup.mk' N hY)⁻¹ *
          (QuotientGroup.mk' N eY)⁻¹) * (QuotientGroup.mk' N eY * QuotientGroup.mk' N hY) := by
            group
      _ = _ := by rw [h2, one_mul]
  have hmem : QuotientGroup.mk' N hY ∈ Subgroup.centralizer
      (((Subgroup.zpowers eY).map (QuotientGroup.mk' N) : Subgroup (Y ⧸ N)) : Set (Y ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro q ⟨w, hw, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [map_zpow]
    exact (Commute.zpow_left hcommbar.symm n).eq
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hN3 hQ] at hmem
  obtain ⟨x₁, hx₁C, hx₁h⟩ := hmem
  have hx₁e : (x₁ : H) * e = e * x₁ := by
    have := Subgroup.mem_centralizer_iff.mp hx₁C eY (Subgroup.mem_zpowers eY)
    exact (congrArg Subtype.val this).symm
  have hx₁hΘ : (QuotientGroup.mk' Θ (x₁ : H)) = QuotientGroup.mk' Θ h := by
    have h1 : x₁⁻¹ * hY ∈ N := QuotientGroup.eq.mp hx₁h
    rw [hN, Subgroup.mem_subgroupOf] at h1
    exact QuotientGroup.eq.mpr (by simpa [hhYdef] using h1)
  set n₀ : H := (x₁ : H) ^ 3 * c⁻¹ with hn₀
  have hn₀Θ : n₀ ∈ Θ := by
    rw [← QuotientGroup.eq_one_iff (N := Θ)]
    change QuotientGroup.mk' Θ ((x₁ : H) ^ 3 * c⁻¹) = 1
    have h1 : QuotientGroup.mk' Θ (h ^ 3 * c⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hhc
    calc QuotientGroup.mk' Θ ((x₁ : H) ^ 3 * c⁻¹) =
        QuotientGroup.mk' Θ (x₁ : H) ^ 3 * (QuotientGroup.mk' Θ c)⁻¹ := by simp
      _ = QuotientGroup.mk' Θ h ^ 3 * (QuotientGroup.mk' Θ c)⁻¹ := by rw [hx₁hΘ]
      _ = QuotientGroup.mk' Θ (h ^ 3 * c⁻¹) := by simp
      _ = 1 := h1
  have hn₀Y : n₀ ∈ Y := mul_mem (pow_mem x₁.2 3) (inv_mem hcY)
  have hn₀c : n₀ * c = c * n₀ := hcC n₀ hn₀Y
  have hx₁3 : (x₁ : H) ^ 3 = n₀ * c := by rw [hn₀, inv_mul_cancel_right]
  set o := orderOf n₀ with ho
  have ho3 : ¬ 3 ∣ o := by
    intro h3
    apply hΘ
    refine h3.trans ?_
    have := orderOf_dvd_natCard (⟨n₀, hn₀Θ⟩ : Θ)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨t, hot, ht⟩ : ∃ t : ℕ, o ∣ t ∧ t % 3 = 1 := by
    have : o % 3 = 1 ∨ o % 3 = 2 := by omega
    rcases this with h1 | h2
    · exact ⟨o, dvd_refl o, h1⟩
    · exact ⟨2 * o, dvd_mul_left o 2, by omega⟩
  refine ⟨(x₁ : H) ^ t, pow_mem x₁.2 t, (Commute.pow_left hx₁e t).eq, ?_⟩
  have hcomm : Commute n₀ c := hn₀c
  have hn₀t : n₀ ^ t = 1 := orderOf_dvd_iff_pow_eq_one.mp hot
  have hct : c ^ t = c := by
    conv_lhs => rw [← Nat.div_add_mod t 3, ht, pow_add, pow_mul, hc3, one_pow, one_mul, pow_one]
  rw [← pow_mul, mul_comm, pow_mul, hx₁3, hcomm.mul_pow, hn₀t, one_mul, hct]

section G

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem bar_mem_not_mem_centralizer {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hD : Sec13Data G A c L) (D : SLTwoData (lBarA c L A) π p f K) (hcL : c ∈ L) {e : G}
    (heL : e ∈ L) (he3 : e ^ 3 = 1) (hec : e * c = c * e) (hecz : e ∉ Subgroup.zpowers c)
    {eb : lBarA c L A}
    (heb : (eb : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))) =
      QuotientGroup.mk' _ ⟨e, le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt heL⟩) :
    eb ∈ D.L₀ ∧ eb ^ 3 = 1 ∧ eb ∉ Subgroup.centralizer (D.L₀ : Set (lBarA c L A)) := by
  have hL := hD.mem_thetaComponentsAt
  have hLH : L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := le_normalizer_zpowers_of_mem hL
  set Hc := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHc
  set Θ := aschbacherSolvableCore 3 Hc with hΘ
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  have hΛL₀ : Λ ≤ D.L₀ := D.le_of_isPerfect (isPerfect_subgroupOf_lBar hD)
  set eH : Hc := ⟨e, hLH heL⟩ with heH
  set cH : Hc := ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ with hcH
  have hebΛ : eb ∈ Λ :=
    Subgroup.mem_subgroupOf.mpr ⟨eH, Subgroup.mem_subgroupOf.mpr heL, heb.symm⟩
  have heH3 : eH ^ 3 = 1 := Subtype.ext (by simpa [heH] using he3)
  have heb3 : eb ^ 3 = 1 := Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [heb, ← map_pow, heH3, map_one])
  have hc3 : c ^ 3 = 1 := by rw [← hD.orderOf_eq]; exact pow_orderOf_eq_one c
  have hcH3 : cH ^ 3 = 1 := Subtype.ext (by simpa [hcH] using hc3)
  set cb := mkC (L := L) hD.mem_A with hcb
  have hcbΛ : cb ∈ Λ :=
    Subgroup.mem_subgroupOf.mpr ⟨cH, Subgroup.mem_subgroupOf.mpr hcL, rfl⟩
  have hcbC : cb ∈ D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set (lBarA c L A)) :=
    ⟨hΛL₀ hcbΛ, Subgroup.center_le_centralizer _ (mkC_mem_center hD)⟩
  refine ⟨hΛL₀ hebΛ, heb3, fun hC => ?_⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
    (D.inf_centralizer_le_zpowers hcbC (mkC_ne_one hD) ⟨hΛL₀ hebΛ, hC⟩)
  apply hecz
  have h1 : QuotientGroup.mk' Θ (cH ^ j) = QuotientGroup.mk' Θ eH := by
    have := congrArg Subtype.val hj
    simp only [hcb, mkC, SubgroupClass.coe_zpow] at this
    rw [heb] at this
    simpa using this
  have h2 : (cH ^ j)⁻¹ * eH ∈ Θ := QuotientGroup.eq.mp h1
  have h3 : ((cH ^ j)⁻¹ * eH) ^ 3 = 1 := by
    have hcomm : Commute (cH ^ j)⁻¹ eH :=
      ((Commute.zpow_left (Subtype.ext hec.symm : cH * eH = eH * cH) j)).inv_left
    rw [hcomm.mul_pow, heH3, mul_one, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hcH3, one_zpow, inv_one]
  have h4 : (c ^ j)⁻¹ * e = 1 := by
    have := Sec13.eq_one_of_mem_inSubgroup_theta_of_pow_three (K := Hc) ⟨_, h2, rfl⟩
      (by simpa using congrArg Subtype.val h3)
    simpa [heH, hcH] using this
  have h6 : e = c ^ j := by
    rw [← mul_left_cancel_iff (a := (c ^ j)⁻¹), h4, inv_mul_cancel]
  rw [h6]
  exact Subgroup.zpow_mem_zpowers c j

theorem exists_cube_root_of_isSLThreePiTwo (hD : Sec13Data G A c L)
    (hSL : Sec4.IsSLThreePiTwo (lBarA c L A)) {e : G} (heL : e ∈ L) (he3 : e ^ 3 = 1)
    (hec : e * c = c * e) (hecz : e ∉ Subgroup.zpowers c) :
    ∃ x ∈ L ⊔ A, x * e = e * x ∧ x ^ 3 = c := by
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData hSL
  have hcL : c ∈ L := mem_of_isSLThreePiTwo slTwoCenter hD hSL
  have hL := hD.mem_thetaComponentsAt
  have hLH : L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := le_normalizer_zpowers_of_mem hL
  set Hc := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHc
  set Θ := aschbacherSolvableCore 3 Hc with hΘ
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := three_not_dvd_card_aschbacherSolvableCore
  set Y := (L ⊔ A).subgroupOf Hc with hY
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  have hΛL₀ : Λ ≤ D.L₀ := D.le_of_isPerfect (isPerfect_subgroupOf_lBar hD)
  set eH : Hc := ⟨e, hLH heL⟩ with heH
  set cH : Hc := ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ with hcH
  have heY : eH ∈ Y := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left heL)
  have hcY : cH ∈ Y := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hcL)
  set eb : lBarA c L A := ⟨QuotientGroup.mk' Θ eH, Subgroup.mem_map_of_mem _ heY⟩ with heb
  obtain ⟨hebL₀, heb3, hebC⟩ :=
    bar_mem_not_mem_centralizer hD D hcL heL he3 hec hecz (eb := eb) rfl
  have heH3 : eH ^ 3 = 1 := Subtype.ext (by simpa [heH] using he3)
  have hc3 : c ^ 3 = 1 := by rw [← hD.orderOf_eq]; exact pow_orderOf_eq_one c
  have hcH3 : cH ^ 3 = 1 := Subtype.ext (by simpa [hcH] using hc3)
  set cb := mkC (L := L) hD.mem_A with hcb
  have hcbΛ : cb ∈ Λ :=
    Subgroup.mem_subgroupOf.mpr ⟨cH, Subgroup.mem_subgroupOf.mpr hcL, rfl⟩
  have hcbC : cb ∈ D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set (lBarA c L A)) :=
    ⟨hΛL₀ hcbΛ, Subgroup.center_le_centralizer _ (mkC_mem_center hD)⟩
  obtain ⟨xb, hxbe, hxb3⟩ := sLTwoData_exists_cube_root D hebL₀ heb3 hebC hcbC
  obtain ⟨xbv, ⟨h, hhY, hxbv⟩⟩ := xb
  have hhe : h * eH * h⁻¹ * eH⁻¹ ∈ Θ := by
    have h1 : QuotientGroup.mk' Θ h * QuotientGroup.mk' Θ eH =
        QuotientGroup.mk' Θ eH * QuotientGroup.mk' Θ h := by
      have := congrArg Subtype.val hxbe
      simpa [heb, ← hxbv] using this
    rw [← QuotientGroup.eq_one_iff (N := Θ)]
    change QuotientGroup.mk' Θ (h * eH * h⁻¹ * eH⁻¹) = 1
    calc QuotientGroup.mk' Θ (h * eH * h⁻¹ * eH⁻¹) =
        QuotientGroup.mk' Θ h * QuotientGroup.mk' Θ eH * (QuotientGroup.mk' Θ h)⁻¹ *
          (QuotientGroup.mk' Θ eH)⁻¹ := by simp
      _ = QuotientGroup.mk' Θ eH * QuotientGroup.mk' Θ h * (QuotientGroup.mk' Θ h)⁻¹ *
          (QuotientGroup.mk' Θ eH)⁻¹ := by rw [h1]
      _ = 1 := by group
  have hhc : h ^ 3 * cH⁻¹ ∈ Θ := by
    have h1 := congrArg Subtype.val hxb3
    simp only [SubgroupClass.coe_pow, hcb, mkC] at h1
    rw [← hxbv] at h1
    rw [← QuotientGroup.eq_one_iff (N := Θ)]
    change QuotientGroup.mk' Θ (h ^ 3 * cH⁻¹) = 1
    rw [map_mul, map_pow, map_inv, h1, mul_inv_cancel]
  have hcC : ∀ y ∈ Y, y * cH = cH * y := by
    intro y hy
    have hyC : (y : G) ∈ Subgroup.centralizer ({c} : Set G) :=
      sup_le hD.le_centralizer hD.A_le_centralizer (Subgroup.mem_subgroupOf.mp hy)
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hyC)
  obtain ⟨x, hxY, hxe, hx3⟩ :=
    exists_cube_root_lift hΘ3 heY hcY hhY hcC heH3 hcH3 hhe hhc
  refine ⟨x, Subgroup.mem_subgroupOf.mp hxY, congrArg Subtype.val hxe, ?_⟩
  simpa [hcH] using congrArg Subtype.val hx3

end G

end CFSG.RankThree.PartTwo.Sec13.Res2Proof
