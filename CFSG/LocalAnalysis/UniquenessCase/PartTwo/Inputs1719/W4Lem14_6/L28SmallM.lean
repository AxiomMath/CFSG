module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.L28Module
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.OddOuter
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.Quasithin.Vol2.Ch10SecD12D
public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem rk_le_two_mul_rk_inf_fixV {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1)
    {V : Subgroup U} {b : MulAut U} (hb : b * b = 1) (hbV : ∀ v ∈ V, b v ∈ V) :
    rk ↥V ≤ 2 * rk ↥(V ⊓ fixV (Subgroup.zpowers b)) := by
  classical
  have hbb : ∀ u, b (b u) = u := fun u => by
    have := congrArg (fun φ : MulAut U => φ u) hb
    simpa using this
  let b' : MulAut ↥V :=
    { toFun := fun v => ⟨b v, hbV v v.2⟩
      invFun := fun v => ⟨b v, hbV v v.2⟩
      left_inv := fun v => Subtype.ext (hbb v)
      right_inv := fun v => Subtype.ext (hbb v)
      map_mul' := fun v w => Subtype.ext (map_mul b (v : U) (w : U)) }
  have hb' : b' * b' = 1 := by
    apply MulEquiv.ext
    intro v
    exact Subtype.ext (hbb v)
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hU v)
  have h1 := CFSG.Quasithin.E6.two_mul_rkIdx_fixV_le hV2 hb'
  have h2 := CFSG.Quasithin.rk_add_rkIdx (fixV (Subgroup.zpowers b'))
  have h3 : Nat.card ↥(fixV (Subgroup.zpowers b')) =
      Nat.card ↥(V ⊓ fixV (Subgroup.zpowers b)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : ↥V) : U), Subgroup.mem_inf.mpr ⟨(x : ↥V).2, ?_⟩⟩
        invFun := fun y => ⟨⟨(y : U), (Subgroup.mem_inf.mp y.2).1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · exact CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr
        (congrArg Subtype.val (CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mp x.2))
    · exact CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr
        (Subtype.ext (CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mp (Subgroup.mem_inf.mp y.2).2))
  have h4 : rk ↥(fixV (Subgroup.zpowers b')) = rk ↥(V ⊓ fixV (Subgroup.zpowers b)) := by
    unfold rk
    rw [h3]
  omega

theorem aParam_le_one_of_free_of_card_fixV {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) (N : Subgroup (MulAut U)) (hrk : rk U = 8)
    (hfree : ∀ t ∈ N, orderOf t = 2 → 2 * rkIdx (fixV (Subgroup.zpowers t)) = rk U)
    (hP : ∀ A : Subgroup (MulAut U), A ≤ N → IsElemAbelian2 A →
      ∃ P : Subgroup (MulAut U), A ≤ P ∧ P ≤ N ∧ IsElemAbelian2 P ∧ Nat.card P = 8 ∧
        Nat.card (fixV P) = 2) :
    E3.aParam N ≤ 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut U) :=
    Finite.of_injective (fun φ : MulAut U => (φ : U → U)) DFunLike.coe_injective
  have hfix4 : ∀ a ∈ N, orderOf a = 2 → rk ↥(fixV (Subgroup.zpowers a)) = 4 := by
    intro a haN ha
    have h1 := hfree a haN ha
    have h2 := CFSG.Quasithin.rk_add_rkIdx (fixV (Subgroup.zpowers a))
    omega
  have hpair : ∀ a ∈ N, orderOf a = 2 → ∀ b : MulAut U, b * b = 1 → a * b = b * a →
      4 ≤ Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ fixV (Subgroup.zpowers b)) := by
    intro a haN ha b hb hab
    have hV : ∀ v ∈ fixV (Subgroup.zpowers a), b v ∈ fixV (Subgroup.zpowers a) := by
      intro v hv
      rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply] at hv ⊢
      have h := congrArg (fun φ : MulAut U => φ v) hab
      simp only [MulAut.mul_apply] at h
      rw [h, hv]
    have h1 := rk_le_two_mul_rk_inf_fixV hU hb hV
    rw [hfix4 a haN ha] at h1
    rw [CFSG.Quasithin.card_eq_two_pow hU]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ rk ↥(fixV (Subgroup.zpowers a) ⊓ fixV (Subgroup.zpowers b)) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  refine CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty N 1 (fun A hA => ?_)
  obtain ⟨hAN, hAne, hAe, hAfix⟩ := hA
  obtain ⟨P, hAP, hPN, hPe, hP8, hPfix⟩ := hP A hAN hAe
  have hApg : IsPGroup 2 ↥A := CFSG.Quasithin.isPGroup_two_of_sq_eq_one
    (fun a : ↥A => Subtype.ext (by simpa using hAe.2 a a.2))
  have hfixB : ∀ B : Subgroup (MulAut U), B ≤ A → Nat.card ↥A ≤ 2 * Nat.card ↥B →
      fixV B = fixV A := fun B hBA hc => hAfix B hBA (by
        have := CFSG.Quasithin.Vol2.Ch10.SecD.mQuot_le_one_of_card_le hApg hBA hc
        omega)
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := hPe.1
  have hsq : ∀ x ∈ P, x * x = 1 := fun x hx => by rw [← sq]; exact hPe.2 x hx
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hAne (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx))
  have ha2 : orderOf a = 2 := orderOf_eq_prime (hAe.2 a haA) ha1
  have haN : a ∈ N := hAN haA
  have hza : Nat.card ↥(Subgroup.zpowers a) = 2 := by rw [Nat.card_zpowers, ha2]
  have hAdvd : Nat.card ↥A ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hP8]
    exact Subgroup.card_dvd_of_le hAP
  obtain ⟨k, hk, hkA⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hAdvd
  interval_cases k
  · exact hAne (Subgroup.eq_bot_of_card_eq A (by rw [hkA]; norm_num))
  ·
    have h := hfixB ⊥ bot_le (by rw [Subgroup.card_bot, hkA]; norm_num)
    rw [CFSG.Quasithin.B1.fixV_bot] at h
    apply ha1
    apply MulEquiv.ext
    intro u
    have hu : u ∈ fixV A := h ▸ Subgroup.mem_top u
    exact CFSG.Quasithin.mem_fixV.mp hu a haA
  ·
    have h1 := hfixB (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haA)
      (by rw [hkA, hza]; norm_num)
    obtain ⟨c, hcP, hcA⟩ : ∃ c ∈ P, c ∉ A := by
      by_contra hcon
      push Not at hcon
      have := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le (show P ≤ A from hcon))
      rw [hP8, hkA] at this
      norm_num at this
    have hcAc : ∀ d ∈ A, c * d = d * c := fun d hd => hcomm c hcP d (hAP hd)
    have hJ := CFSG.Quasithin.B1.card_sup_zpowers (hsq c hcP) hcAc hcA
    have hJP : Subgroup.zpowers c ⊔ A = P := Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hcP) hAP) (by rw [hJ, hP8, hkA]; norm_num)
    have h2 := hpair a haN ha2 c (hsq c hcP) (hcomm a (hAP haA) c hcP)
    rw [← hJP, CFSG.Quasithin.B1.fixV_sup, ← h1, inf_comm] at hPfix
    omega
  ·
    have hAP' : A = P := Subgroup.eq_of_le_of_card_ge hAP (by rw [hP8, hkA]; norm_num)
    obtain ⟨B, hB4, haB, hBA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
      (n := 2) (H := Subgroup.zpowers a) (L := A) (by rw [hza]; norm_num)
      (by rw [hkA]; norm_num) (Subgroup.zpowers_le.mpr haA)
    obtain ⟨b, hbB, hba⟩ : ∃ b ∈ B, b ∉ Subgroup.zpowers a := by
      by_contra hcon
      push Not at hcon
      have := Nat.le_of_dvd Nat.card_pos
        (Subgroup.card_dvd_of_le (show B ≤ Subgroup.zpowers a from hcon))
      rw [hza, hB4] at this
      norm_num at this
    have hbP : b ∈ P := hAP (hBA hbB)
    have hbc : ∀ d ∈ Subgroup.zpowers a, b * d = d * b := by
      intro d hd
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
      exact (Commute.zpow_right (show Commute b a from hcomm b hbP a (hAP haA)) j).eq
    have hJ := CFSG.Quasithin.B1.card_sup_zpowers (hsq b hbP) hbc hba
    have hJB : Subgroup.zpowers b ⊔ Subgroup.zpowers a = B := Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hbB) haB) (by rw [hJ, hB4, hza]; norm_num)
    have h1 := hfixB B hBA (by rw [hkA, hB4]; norm_num)
    rw [← hJB, CFSG.Quasithin.B1.fixV_sup] at h1
    have h2 := hpair a haN ha2 b (hsq b hbP) (hcomm a (hAP haA) b hbP)
    rw [← hAP', ← h1, inf_comm] at hPfix
    omega

theorem k_L28SmallM_holds : K_L28SmallM := by
  intro U _ _ hU N S hSN hnorm h3 hirr
  classical
  haveI : Finite (MulAut U) :=
    Finite.of_injective (fun φ : MulAut U => (φ : U → U)) DFunLike.coe_injective
  haveI : Finite ↥S := Subtype.finite
  have hZ : Subgroup.center ↥S = ⊥ := center_eq_bot_of_isL2_three h3
  have hout := odd_card_outer_of_isL2_three h3
  have hinS : ∀ t ∈ N, orderOf t = 2 → t ∈ S := fun t htN ht =>
    mem_of_orderOf_eq_two_of_odd_outer hU hSN hnorm hirr hZ hout htN ht
  have hfree : ∀ t ∈ N, orderOf t = 2 → 2 * rkIdx (fixV (Subgroup.zpowers t)) = rk U :=
    fun t htN ht => two_mul_rkIdx_fixV_eq_rk_of_isL2_three hU h3 hirr (hinS t htN ht) ht
  have h6 := six_le_rk_of_isL2_three hU h3
  have hP2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heven : Even (Nat.card ↥N) := by
    obtain ⟨θ⟩ := nonempty_mulEquiv_sl2_of_isL2_three h3
    obtain ⟨x, hx1, hx2⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.sl2_exists_involution θ
    have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    have h2S : 2 ∣ Nat.card ↥S := by
      rw [← hord]
      exact orderOf_dvd_natCard x
    exact even_iff_two_dvd.mpr (h2S.trans (Subgroup.card_dvd_of_le hSN))
  obtain ⟨t₀, ht₀N, ht₀, ht₀m⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam N heven
  have hm : 2 * E3.mParam N = rk U := by
    rw [← ht₀m]
    exact hfree t₀ ht₀N ht₀
  refine ⟨by omega, fun h5 => ?_⟩
  rcases rk_eq_six_or_eight_of_isL2_three hU h3 hirr (by omega) with h6' | h8
  · left
    have := hfree t₀ ht₀N ht₀
    exact ⟨h6', t₀, hinS t₀ ht₀N ht₀, ht₀, by omega⟩
  · right
    refine ⟨h8, aParam_le_one_of_free_of_card_fixV hU N h8 hfree ?_⟩
    intro A hAN hA
    have hAS : A ≤ S := by
      intro a ha
      by_cases ha1 : a = 1
      · rw [ha1]
        exact S.one_mem
      · exact hinS a (hAN ha) (orderOf_eq_prime (hA.2 a ha) ha1)
    obtain ⟨P, hAP, hPS, hPe, hP8, hPfix⟩ :=
      exists_card_fixV_eq_two_of_isL2_three hU h3 hirr h8 A hAS hA
    exact ⟨P, hAP, hPS.trans hSN, hPe, hP8, hPfix⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
