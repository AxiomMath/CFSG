module

public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.B.CTIB.HInner
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate16022
public import Certificates.Certificate3027
public import Certificates.Certificate16951

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B Native
open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem map_center_map_of_injective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) (K : Subgroup G) :
    ((Subgroup.center K).map K.subtype).map f =
      (Subgroup.center (K.map f)).map (K.map f).subtype := by
  ext x
  rw [CFSG.Monster.mem_map_center_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyK, hc⟩ := CFSG.Monster.mem_map_center_iff.1 hy
    refine ⟨⟨y, hyK, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hc z hz]
  · rintro ⟨⟨y, hy, rfl⟩, h⟩
    refine ⟨y, CFSG.Monster.mem_map_center_iff.2 ⟨hy, fun z hz => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact h (f z) ⟨z, hz, rfl⟩

theorem natCard_Sbp_eq :
    Nat.card Sbp = Nat.card Cbar :=
  Nat.card_congr (MulEquiv.inv' Cbar).toEquiv.symm

theorem natCard_Sbp_two_part :
    ∃ m : ℕ, Odd m ∧ Nat.card Sbp = 2 ^ 41 * m := by
  obtain ⟨m, hm, h⟩ := short_centralizer_quotient_sylow_two.2.1
  exact ⟨m, hm, natCard_Sbp_eq.trans h⟩

theorem factorization_natCard_Sbp :
    (Nat.card Sbp).factorization 2 = 41 := by
  obtain ⟨m, hm, h⟩ := natCard_Sbp_two_part
  rw [h, Nat.factorization_mul (by positivity) hm.pos.ne', Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat, smul_eq_mul, mul_one, add_zero]

theorem natCard_sylow_two
    (T : Sylow 2 Sbp) : Nat.card T = 2 ^ 41 := by
  rw [T.card_eq_multiplicity, factorization_natCard_Sbp]

theorem orderOf_xs : orderOf xs = 2 := orderOf_two_iff.2 ⟨xs_mul_self, xs_ne_one⟩

theorem exists_sylow_two_center_xs :
    ∃ T : Sylow 2 Sbp,
    (Subgroup.center (T : Subgroup Sbp)).map (T : Subgroup Sbp).subtype =
      Subgroup.zpowers xs := by
  have : Finite Cbar := Dyadic.finite_Cbar
  obtain ⟨P⟩ : Nonempty (Sylow 2 Jbar) := inferInstance
  obtain ⟨S₀, -, hZ⟩ := short_centralizer_quotient_sylow_two.1 P
  have hcard : Nat.card ((S₀ : Subgroup Cbar).map (MulEquiv.inv' Cbar).toMonoidHom) =
      2 ^ (Nat.card Sbp).factorization 2 := by
    rw [Subgroup.card_map_of_injective (MulEquiv.inv' Cbar).injective, S₀.card_eq_multiplicity,
      natCard_Sbp_eq]
  have hx : (MulEquiv.inv' Cbar).toMonoidHom xbar = xs := by
    show op xbar⁻¹ = op xbar
    rw [inv_eq_of_mul_eq_one_right xbar_mul_self]
  refine ⟨Sylow.ofCard _ hcard, ?_⟩
  rw [Sylow.coe_ofCard, ← map_center_map_of_injective (f := (MulEquiv.inv' Cbar).toMonoidHom)
    (MulEquiv.inv' Cbar).injective, hZ, MonoidHom.map_zpowers, hx]

theorem le_centralizer_of_center_eq {T : Subgroup Sbp} {z : Sbp}
    (h : (Subgroup.center T).map T.subtype = Subgroup.zpowers z) :
    T ≤ Subgroup.centralizer {z} := by
  intro y hy
  have hz : z ∈ (Subgroup.center T).map T.subtype := h ▸ Subgroup.mem_zpowers z
  exact Subgroup.mem_centralizer_singleton_iff.2 ((CFSG.Monster.mem_map_center_iff.1 hz).2 y hy)

theorem sylow_two_center
    (T : Sylow 2 Sbp) : ∃ z : Sbp, orderOf z = 2 ∧
    ((βr z) - 1).rank = 2048 ∧ IsConj z xs ∧
    (Subgroup.center (T : Subgroup Sbp)).map (T : Subgroup Sbp).subtype = Subgroup.zpowers z := by
  obtain ⟨T₀, hT₀⟩ := exists_sylow_two_center_xs
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Sbp T₀ T
  have hcoe : ((g • T₀ : Sylow 2 Sbp) : Subgroup Sbp) =
      (T₀ : Subgroup Sbp).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  have hconj : IsConj (g * xs * g⁻¹) xs := isConj_iff.2 ⟨g⁻¹, by group⟩
  refine ⟨g * xs * g⁻¹, ?_, by rw [rank_beta_conj hconj, rank_xs], hconj, ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_xs]
  · rw [hcoe, ← map_center_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, hT₀, MonoidHom.map_zpowers]
    rfl

theorem isConj_xs_of_le_centralizer
    {t : Sbp} (ht : orderOf t = 2) (T : Sylow 2 Sbp)
    (hT : (T : Subgroup Sbp) ≤ Subgroup.centralizer {t}) :
    t ∈ (Subgroup.center (T : Subgroup Sbp)).map (T : Subgroup Sbp).subtype ∧ IsConj t xs ∧
      ((βr t) - 1).rank = 2048 := by
  have hcent : (T : Subgroup Sbp) ≤ Subgroup.centralizer (Subgroup.zpowers t : Set Sbp) :=
    Subgroup.le_centralizer_iff.2 (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2
      fun h hh => Subgroup.mem_centralizer_singleton_iff.1 (hT hh)))
  have hp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hsup := T.is_maximal' (IsPGroup.to_sup_of_normal_right' T.isPGroup' hp
    (hcent.trans (Subgroup.centralizer_le_normalizer _))) le_sup_left
  have htT : t ∈ (T : Subgroup Sbp) := by
    rw [← hsup]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htZ : t ∈ (Subgroup.center (T : Subgroup Sbp)).map (T : Subgroup Sbp).subtype :=
    CFSG.Monster.mem_map_center_iff.2
      ⟨htT, fun y hy => Subgroup.mem_centralizer_singleton_iff.1 (hT hy)⟩
  obtain ⟨z, hz2, hzr, hzc, hZ⟩ := sylow_two_center T
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hZ ▸ htZ)
  have hmod : z ^ k = z ^ (k % 2) := by
    rw [← zpow_mod_orderOf z k, hz2, Nat.cast_ofNat]
  have htz : t = z := by
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [hmod, h, zpow_zero] at hk
      exact absurd hk.symm (orderOf_two_iff.1 ht).2
    · rw [hmod, h, zpow_one] at hk
      exact hk.symm
  subst htz
  exact ⟨htZ, hzc, hzr⟩

theorem native_sylow_two_center :
    (∃ m : ℕ, Odd m ∧ Nat.card Sbp = 2 ^ 41 * m) ∧
    (∃ T : Sylow 2 Sbp, (T : Subgroup Sbp) ≤ Subgroup.centralizer {xs} ∧
      (Subgroup.center (T : Subgroup Sbp)).map (T : Subgroup Sbp).subtype =
        Subgroup.zpowers xs) ∧
    (∀ T : Sylow 2 Sbp, Nat.card T = 2 ^ 41 ∧ ∃ z : Sbp, orderOf z = 2 ∧
      ((βr z) - 1).rank = 2048 ∧ IsConj z xs ∧
      (Subgroup.center (T : Subgroup Sbp)).map (T : Subgroup Sbp).subtype =
        Subgroup.zpowers z) ∧
    ∀ t : Sbp, orderOf t = 2 → ∀ T : Sylow 2 Sbp,
      (T : Subgroup Sbp) ≤ Subgroup.centralizer {t} →
      t ∈ (Subgroup.center (T : Subgroup Sbp)).map (T : Subgroup Sbp).subtype ∧
        IsConj t xs ∧ ((βr t) - 1).rank = 2048 := by
  obtain ⟨T₀, hT₀⟩ := exists_sylow_two_center_xs
  exact ⟨natCard_Sbp_two_part, ⟨T₀, le_centralizer_of_center_eq hT₀, hT₀⟩,
    fun T => ⟨natCard_sylow_two T, sylow_two_center T⟩,
    fun t ht T hT => isConj_xs_of_le_centralizer ht T hT⟩

theorem orderOf_rs1 :
    orderOf (rs 1) = 2 := by
  rw [rs1_eq]
  exact orderOf_two_iff.2 ⟨sq_qS_one (Or.inl rfl), qS_ne_one census_valid_one⟩

theorem rs3_commute_rs1 :
    Commute (rs 3) (rs 1) := by
  rw [rs3_eq, rs1_eq]
  show qS 7 * qS 1 = qS 1 * qS 7
  rw [qS_mul, qS_mul, show qmul gArr 7 1 = qmul gArr 1 7 by decide +kernel]

theorem liftWordS_mem_Jbar
    {w : List ℕ} (hw : ∀ l ∈ w, l < 2) : (liftWordS w).unop ∈ Jbar := by
  have h := (conj_liftWord w 1 id23 (by simp) (by simp [id23])
    (fun j hj => by rw [inv_one, one_mul, mul_one, id23_getD hj, qS_two_pow hj]) hw).2.2
  rwa [one_mul] at h

theorem conj_word_qS_one :
    (liftWordS [1, 0, 1, 0, 1, 0])⁻¹ * qS 1 * liftWordS [1, 0, 1, 0, 1, 0] = qS 5799405 := by
  rw [conj_qS (liftWordS_mem_Jbar (by decide)) (fun i hi => conj_liftWordS (by decide) hi) 1,
    show autApply gArr (autWord gArr genImgs [1, 0, 1, 0, 1, 0]) 1 = 5799405 by decide +kernel]

theorem conj_hs6_qS
    (n : ℕ) :
    (hs 6)⁻¹ * qS n * hs 6 = qS (autApply gArr liftImgs6.toArray n) :=
  conj_qS (hs_mem_Jbar (Or.inl rfl)) (fun i hi => by
    rw [conj_hs (Or.inl rfl) hi, liftImgsK, ite_eq_left rfl, Array.getD_eq_getD_getElem?,
      List.getElem?_toArray, List.getD_eq_getElem?_getD]) n

theorem rs5_commute :
    Commute (rs 5) (qS 5799405) := by
  have e : qS 5799405 * hs 6 = hs 6 * qS (autApply gArr liftImgs6.toArray 5799405) := by
    rw [← conj_hs6_qS]
    group
  show rs 5 * qS 5799405 = qS 5799405 * rs 5
  rw [show rs 5 = hs 6 * qS 61 from rfl, mul_assoc, qS_mul, ← mul_assoc, e, mul_assoc, qS_mul,
    show qmul gArr (autApply gArr liftImgs6.toArray 5799405) 61 = qmul gArr 61 5799405 by
      decide +kernel]

theorem exists_commute_isConj_rs1
    {i : ℕ} (hi : i ∈ [1, 0, 5, 3]) :
    ∃ y : Sbp, IsConj y (rs 1) ∧ Commute (rs i) y := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨rs 1, IsConj.refl _, Commute.refl _⟩
  · refine ⟨rs 1, IsConj.refl _, ?_⟩
    rw [rs0_eq, rs1_eq]
    exact xs_comm (qS_mem 1)
  · refine ⟨qS 5799405, ?_, rs5_commute⟩
    rw [rs1_eq, ← conj_word_qS_one]
    exact isConj_iff.2 ⟨liftWordS [1, 0, 1, 0, 1, 0], by group⟩
  · exact ⟨rs 1, IsConj.refl _, rs3_commute_rs1⟩

theorem native_involution_commutes_rank_1860 :
    ∀ t : Sbp, orderOf t = 2 → ∃ y : Sbp, orderOf y = 2 ∧ ((βr y) - 1).rank = 1860 ∧
      IsConj y labelS ∧ Commute t y := by
  intro t ht
  obtain ⟨i, ⟨hi, hti⟩, -⟩ := four_classes co2_involution_input ht
  obtain ⟨c, hc⟩ := isConj_iff.1 hti
  obtain ⟨y, hy, hcomm⟩ := exists_commute_isConj_rs1 hi
  have hy' : IsConj (c⁻¹ * y * c) (rs 1) := (isConj_iff.2 ⟨c, by group⟩).trans hy
  refine ⟨c⁻¹ * y * c, ?_, by rw [rank_beta_conj hy', rank_four.1], ?_, ?_⟩
  · obtain ⟨d, hd⟩ := isConj_iff.1 hy'
    rw [← orderOf_rs1, ← hd, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  · refine hy'.trans ?_
    rw [rs1_eq]
    exact (isConj_of_mem_jClass labelS_mem_jClass).symm
  · have ht' : t = c⁻¹ * rs i * c := by
      rw [← hc]
      group
    rw [ht']
    show c⁻¹ * rs i * c * (c⁻¹ * y * c) = c⁻¹ * y * c * (c⁻¹ * rs i * c)
    calc c⁻¹ * rs i * c * (c⁻¹ * y * c) = c⁻¹ * (rs i * y) * c := by group
      _ = c⁻¹ * (y * rs i) * c := by rw [hcomm.eq]
      _ = c⁻¹ * y * c * (c⁻¹ * rs i * c) := by group

theorem rank_iotaEquiv
    (X : NativeSporadic.B) :
    (X.val.val - 1).rank = ((βr (iotaEquiv X)) - 1).rank := by
  have h := rank_iotaEquiv_symm (iotaEquiv X)
  rwa [MulEquiv.symm_apply_apply] at h

theorem natCard_B_eq :
    Nat.card NativeSporadic.B = Nat.card Sbp :=
  Nat.card_congr iotaEquiv.toEquiv

theorem natCard_map_iotaS
    (T : Sylow 2 NativeSporadic.B) :
    Nat.card ((T : Subgroup NativeSporadic.B).map iotaS) = 2 ^ (Nat.card Sbp).factorization 2 := by
  have : Finite NativeSporadic.B := Finite.of_equiv Sbp iotaEquiv.symm.toEquiv
  rw [Subgroup.card_map_of_injective iotaS_spec.1, T.card_eq_multiplicity, natCard_B_eq]

theorem native_B_sylow_two_center :
    (∃ m : ℕ, Odd m ∧ Nat.card NativeSporadic.B = 2 ^ 41 * m) ∧
    (∀ T : Sylow 2 NativeSporadic.B, Nat.card T = 2 ^ 41 ∧ ∃ Z : NativeSporadic.B,
      orderOf Z = 2 ∧ (Z.val.val - 1).rank = 2048 ∧
      (Subgroup.center (T : Subgroup NativeSporadic.B)).map
        (T : Subgroup NativeSporadic.B).subtype = Subgroup.zpowers Z) ∧
    ∀ X : NativeSporadic.B, orderOf X = 2 → ∀ T : Sylow 2 NativeSporadic.B,
      (T : Subgroup NativeSporadic.B) ≤ Subgroup.centralizer {X} →
      (X.val.val - 1).rank = 2048 ∧ IsConj X (iotaEquiv.symm (rs 0)) := by
  refine ⟨?_, fun T => ?_, fun X hX T hT => ?_⟩
  · obtain ⟨m, hm, h⟩ := natCard_Sbp_two_part
    exact ⟨m, hm, natCard_B_eq.trans h⟩
  · let T' : Sylow 2 Sbp := Sylow.ofCard _ (natCard_map_iotaS T)
    have hT' : (T' : Subgroup Sbp) = (T : Subgroup NativeSporadic.B).map iotaS :=
      Sylow.coe_ofCard _ _
    obtain ⟨z, hz2, hzr, -, hZ⟩ := sylow_two_center T'
    refine ⟨?_, iotaEquiv.symm z, by rw [MulEquiv.orderOf_eq]; exact hz2,
      by rw [rank_iotaEquiv_symm]; exact hzr, ?_⟩
    · rw [← natCard_sylow_two T', hT', Subgroup.card_map_of_injective iotaS_spec.1]
    · apply Subgroup.map_injective (f := iotaS) iotaS_spec.1
      rw [map_center_map_of_injective iotaS_spec.1, ← hT', hZ, MonoidHom.map_zpowers,
        ← iotaEquiv_apply, MulEquiv.apply_symm_apply]
  · let T' : Sylow 2 Sbp := Sylow.ofCard _ (natCard_map_iotaS T)
    have hT' : (T' : Subgroup Sbp) = (T : Subgroup NativeSporadic.B).map iotaS :=
      Sylow.coe_ofCard _ _
    have hle : (T' : Subgroup Sbp) ≤ Subgroup.centralizer {iotaS X} := by
      rw [hT']
      rintro _ ⟨a, ha, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hT ha)]
    obtain ⟨-, hc, hr⟩ := isConj_xs_of_le_centralizer
      (by rw [orderOf_injective iotaS iotaS_spec.1]; exact hX) T' hle
    refine ⟨by rw [rank_iotaEquiv]; exact hr, ?_⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    refine isConj_iff.2 ⟨iotaEquiv.symm c, iotaEquiv.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      iotaEquiv_apply, hc, rs0_eq]

theorem native_B_involution_commutes_rank_1860 :
    ∀ X : NativeSporadic.B, orderOf X = 2 → ∃ Y : NativeSporadic.B, orderOf Y = 2 ∧
      (Y.val.val - 1).rank = 1860 ∧ Commute X Y := by
  intro X hX
  obtain ⟨y, hy2, hyr, -, hc⟩ :=
    native_involution_commutes_rank_1860 (iotaEquiv X) (by rw [MulEquiv.orderOf_eq]; exact hX)
  refine ⟨iotaEquiv.symm y, by rw [MulEquiv.orderOf_eq]; exact hy2,
    by rw [rank_iotaEquiv_symm]; exact hyr, iotaEquiv.injective ?_⟩
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
  exact hc

end CFSG.Monster.B.CTIB
