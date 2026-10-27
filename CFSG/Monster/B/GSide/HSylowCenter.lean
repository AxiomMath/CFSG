module

public import CFSG.Monster.B.GSide.HClasses
public import CFSG.Monster.B.TwoA.Sp8.Par1Center
public import CFSG.Monster.B.TwoA.Unitary.Stab891
public import CFSG.Monster.B.Cbar.SylowControl
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3059
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate3080
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate3050
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate16042
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA.Sp8

theorem wFix_sigPerp :
    wFix (bV.orthogonal sigLine : Set (Wv v0)) = ⊥ := by
  rw [eq_bot_iff]
  intro k hk
  rw [mem_wFix] at hk
  have hfix : ∀ x : Wv v0, wAct v0 k x = x := by
    intro x
    have hd : wAct v0 k x - x ∈ sigLine := by
      rw [← sigLine_orth_orth, LinearMap.BilinForm.mem_orthogonal_iff]
      intro h hh
      show bV h (wAct v0 k x - x) = 0
      have e1 : bV h (wAct v0 k x) = bV h x := by
        have := Unitary.bW_wAct k h x
        rwa [hk h hh] at this
      rw [map_sub, e1, sub_self]
    rcases mem_sigLine.1 hd with h0 | hσ
    · exact sub_eq_zero.1 h0
    · exfalso
      have hkx : wAct v0 k x = x + Unitary.sigmaW := by
        rw [← hσ]
        abel
      have hq := Unitary.qWv_wAct k x
      rw [hkx, QuadraticMap.map_add Unitary.qWv x Unitary.sigmaW, Unitary.qWv_sigmaW, add_zero,
        add_eq_left] at hq
      have hx : x ∈ bV.orthogonal sigLine := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro n hn
        rcases mem_sigLine.1 hn with rfl | rfl
        · exact LinearMap.map_zero₂ _ _
        · show QuadraticMap.polar Unitary.qWv Unitary.sigmaW x = 0
          rw [QuadraticMap.polar_comm]
          exact hq
      have h2 := hk x hx
      rw [hkx, add_eq_left] at h2
      exact sigmaW_ne_zero h2
  have hW : wAct v0 k = wAct v0 1 := by
    rw [wAct_one]
    exact LinearMap.ext hfix
  exact KvAct_injective_vMinus (congrArg MulOpposite.op hW)

theorem centralizer_N1_le
    {y : Dfull} (hy : y ∈ P1) (hc : ∀ n ∈ N1, y * n = n * y) :
    y ∈ N1 := by
  have hk : jhatToKv0 ⟨y, P1_le_Jhat hy⟩ ∈ wFix (bV.orthogonal sigLine : Set (Wv v0)) := by
    rw [mem_wFix]
    intro x hx
    obtain ⟨⟨e, heE⟩, rfl, he⟩ := exists_EU_of_mem hx
    have heN : e ∈ N1 := by
      rw [N1_eq_EU]
      exact he
    have h1 := psiW_conj (P1_le_Jhat hy) heE
    have h2 : (⟨y⁻¹ * e * y, conj_mem_Ehat (P1_le_Jhat hy) heE⟩ : Ehat) = ⟨e, heE⟩ := by
      apply Subtype.ext
      show y⁻¹ * e * y = e
      rw [mul_assoc, ← hc e heN, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h2] at h1
    exact h1.symm
  rw [wFix_sigPerp, Subgroup.mem_bot] at hk
  have h3 : p1Proj ⟨y, hy⟩ = 1 := Subtype.ext (by rw [coe_p1Proj]; exact hk)
  have h4 : (⟨y, hy⟩ : P1) ∈ p1Proj.ker := h3
  rw [ker_p1Proj, Subgroup.mem_subgroupOf] at h4
  exact h4

theorem mem_closure_of_centralizer_N1
    {y : Dfull} (hy : y ∈ P1)
    (hc : ∀ n ∈ N1, y * n = n * y) : y ∈ Subgroup.closure {xhat, cQ} := by
  rw [← EU_sigLine]
  exact (mem_center_N1 (centralizer_N1_le hy hc)).1 hc

@[expose] def iotaH :
    vStab cv0 →* Dfull := Shat.subtype.comp (vStab cv0).subtype

theorem iotaH_apply
    (y : vStab cv0) : iotaH y = ((y : Shat) : Dfull) := rfl

theorem iotaH_injective :
    Function.Injective iotaH := fun _ _ h =>
  Subtype.ext (Subtype.ext h)

@[expose] def AH :
    Subgroup (vStab cv0) := P1.comap iotaH

@[expose] def NH :
    Subgroup (vStab cv0) := N1.comap iotaH

theorem NH_le_AH :
    NH ≤ AH := fun _ h => N1_le_P1 h

theorem exists_iotaH_eq
    {d : Dfull} (hd : d ∈ P1) : ∃ y : vStab cv0, iotaH y = d := by
  have hE : d ∈ Eam := Pc_le_Eam 0 hd
  exact ⟨⟨⟨d, Eam_le_Shat hE⟩, mem_vStab_cv0.2 hE⟩, rfl⟩

theorem map_AH :
    AH.map iotaH = P1 := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hy
  · intro d hd
    obtain ⟨y, rfl⟩ := exists_iotaH_eq hd
    exact ⟨y, hd, rfl⟩

theorem map_NH :
    NH.map iotaH = N1 := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hy
  · intro d hd
    obtain ⟨y, rfl⟩ := exists_iotaH_eq (N1_le_P1 hd)
    exact ⟨y, hd, rfl⟩

theorem natCard_AH :
    Nat.card AH = 2 ^ 38 * 280665 := by
  rw [← Subgroup.card_map_of_injective iotaH_injective, map_AH, natCard_P1]
  norm_num

theorem natCard_NH :
    Nat.card NH = 2 ^ 22 := by
  rw [← Subgroup.card_map_of_injective iotaH_injective, map_NH, natCard_N1]

theorem natCard_H :
    Nat.card (vStab cv0) = 2 ^ 38 * 1113694156575 := by
  rw [natCard_vStab_eq]
  norm_num

theorem iotaH_cV0 :
    iotaH cV0 = cQ := by
  rw [iotaH_apply, coe_cV0, coe_clabelS, clabel_cv0]

theorem iotaH_lamW0H :
    iotaH lamW0H = cQ * xhat := clabel_cw0

theorem cV0_mem_NH : cV0 ∈ NH := by
  show iotaH cV0 ∈ N1
  rw [iotaH_cV0]
  exact Sp8.cQ_mem_N1

theorem lamW0H_mem_NH :
    lamW0H ∈ NH := by
  show iotaH lamW0H ∈ N1
  rw [iotaH_lamW0H]
  exact N1.mul_mem Sp8.cQ_mem_N1 xhat_mem_N1

theorem cV0_comm
    (y : vStab cv0) : y * cV0 = cV0 * y := by
  have h : cV0 ∈ Subgroup.center (vStab cv0) := by
    rw [center_vStab_cv0]
    exact Subgroup.mem_zpowers cV0
  exact (Subgroup.mem_center_iff.1 h y)

theorem cV0_mul_self :
    cV0 * cV0 = 1 := by
  rw [← pow_two, ← orderOf_cV0, pow_orderOf_eq_one]

theorem lamW0H_comm
    {y : vStab cv0} (hy : y ∈ AH) : y * lamW0H = lamW0H * y := by
  have hA : (y : Shat) ∈ cEdgeFix := mem_cEdgeFix_iff.2 hy
  have h := Subgroup.mem_center_iff.1 lamW0_mem_center ⟨y, hA⟩
  have h2 : (y : Shat) * clabelS cw0 = clabelS cw0 * (y : Shat) := congrArg Subtype.val h
  exact Subtype.ext h2

theorem factorization_two_mul {a m : ℕ} (hm : Odd m) : (2 ^ a * m).factorization 2 = a := by
  rw [Nat.factorization_mul (by positivity) hm.pos.ne', Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat, smul_eq_mul, mul_one, add_zero]

theorem factorization_natCard_H :
    (Nat.card (vStab cv0)).factorization 2 = 38 := by
  rw [natCard_H]
  exact factorization_two_mul (by decide)

theorem factorization_natCard_AH :
    (Nat.card AH).factorization 2 = 38 := by
  rw [natCard_AH]
  exact factorization_two_mul (by decide)

theorem natCard_sylow_two_H
    (T : Sylow 2 (vStab cv0)) : Nat.card T = 2 ^ 38 := by
  rw [T.card_eq_multiplicity, factorization_natCard_H]

theorem exists_sylow_two_AH :
    ∃ T₀ : Sylow 2 (vStab cv0), NH ≤ (T₀ : Subgroup (vStab cv0)) ∧
      (T₀ : Subgroup (vStab cv0)) ≤ AH := by
  have hp : IsPGroup 2 (NH.subgroupOf AH) := IsPGroup.of_card (n := 22) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe NH_le_AH).toEquiv, natCard_NH])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hcard : Nat.card ((Q : Subgroup AH).map AH.subtype) =
      2 ^ (Nat.card (vStab cv0)).factorization 2 := by
    rw [Subgroup.card_map_of_injective AH.subtype_injective, Q.card_eq_multiplicity,
      factorization_natCard_AH, factorization_natCard_H]
  refine ⟨Sylow.ofCard _ hcard, ?_, ?_⟩
  · intro y hy
    rw [Sylow.coe_ofCard]
    exact ⟨⟨y, NH_le_AH hy⟩, hQ hy, rfl⟩
  · rw [Sylow.coe_ofCard]
    rintro _ ⟨a, -, rfl⟩
    exact a.2

theorem mem_closure_xhat_cQ
    {d : Dfull} (hd : d ∈ Subgroup.closure {xhat, cQ}) :
    d = 1 ∨ d = cQ ∨ d = cQ * xhat ∨ d = xhat := by
  rw [← range_kleinHom] at hd
  obtain ⟨v, hv⟩ := hd
  have hv' : xhat ^ (Multiplicative.toAdd v).1.val * cQ ^ (Multiplicative.toAdd v).2.val = d :=
    hv
  have h01 : ∀ a : ZMod 2, a.val = 0 ∨ a.val = 1 := fun a => by
    have := ZMod.val_lt a
    omega
  rcases h01 (Multiplicative.toAdd v).1 with ha | ha <;>
    rcases h01 (Multiplicative.toAdd v).2 with hb | hb <;>
    simp only [ha, hb, pow_zero, pow_one, one_mul, mul_one] at hv'
  · exact Or.inl hv'.symm
  · exact Or.inr (Or.inl hv'.symm)
  · exact Or.inr (Or.inr (Or.inr hv'.symm))
  · exact Or.inr (Or.inr (Or.inl (by rw [← hv', xhat_comm_cQ])))

theorem iotaH_cV0_mul_lamW0H :
    iotaH (cV0 * lamW0H) = xhat := by
  rw [map_mul, iotaH_cV0, iotaH_lamW0H, ← mul_assoc, cQ_mul_self, one_mul]

theorem eq_four_of_iotaH_mem
    {z : vStab cv0} (h : iotaH z ∈ Subgroup.closure {xhat, cQ}) :
    z = 1 ∨ z = cV0 ∨ z = lamW0H ∨ z = cV0 * lamW0H := by
  rcases mem_closure_xhat_cQ h with h | h | h | h
  · exact Or.inl (iotaH_injective (h.trans (map_one iotaH).symm))
  · exact Or.inr (Or.inl (iotaH_injective (h.trans iotaH_cV0.symm)))
  · exact Or.inr (Or.inr (Or.inl (iotaH_injective (h.trans iotaH_lamW0H.symm))))
  · exact Or.inr (Or.inr (Or.inr (iotaH_injective (h.trans iotaH_cV0_mul_lamW0H.symm))))

theorem iotaH_comm_N1
    {T₀ : Subgroup (vStab cv0)} (hN : NH ≤ T₀) {z : vStab cv0}
    (hz : ∀ y ∈ T₀, y * z = z * y) : ∀ n ∈ N1, iotaH z * n = n * iotaH z := by
  intro n hn
  obtain ⟨m, rfl⟩ := exists_iotaH_eq (N1_le_P1 hn)
  rw [← map_mul, ← map_mul, hz m (hN hn)]

theorem eq_four_of_mem_center
    {T₀ : Subgroup (vStab cv0)} (hN : NH ≤ T₀) (hA : T₀ ≤ AH)
    {z : vStab cv0} (hz : z ∈ (Subgroup.center T₀).map T₀.subtype) :
    z = 1 ∨ z = cV0 ∨ z = lamW0H ∨ z = cV0 * lamW0H := by
  rw [mem_map_center_iff] at hz
  exact eq_four_of_iotaH_mem (mem_closure_of_centralizer_N1 (hA hz.1) (iotaH_comm_N1 hN hz.2))

theorem cV0_mem_center
    {T₀ : Subgroup (vStab cv0)} (hN : NH ≤ T₀) :
    cV0 ∈ (Subgroup.center T₀).map T₀.subtype := by
  rw [mem_map_center_iff]
  exact ⟨hN cV0_mem_NH, fun y _ => cV0_comm y⟩

theorem lamW0H_mem_center
    {T₀ : Subgroup (vStab cv0)} (hN : NH ≤ T₀) (hA : T₀ ≤ AH) :
    lamW0H ∈ (Subgroup.center T₀).map T₀.subtype := by
  rw [mem_map_center_iff]
  exact ⟨hN lamW0H_mem_NH, fun y hy => lamW0H_comm (hA hy)⟩

theorem center_sylow_two_AH
    {T₀ : Subgroup (vStab cv0)} (hN : NH ≤ T₀) (hA : T₀ ≤ AH) :
    ((Subgroup.center T₀).map T₀.subtype : Set (vStab cv0)) =
      {1, cV0, lamW0H, cV0 * lamW0H} := by
  ext z
  rw [SetLike.mem_coe]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨eq_four_of_mem_center hN hA, ?_⟩
  rintro (rfl | rfl | rfl | rfl)
  · exact Subgroup.one_mem _
  · exact cV0_mem_center hN
  · exact lamW0H_mem_center hN hA
  · exact Subgroup.mul_mem _ (cV0_mem_center hN) (lamW0H_mem_center hN hA)

section Generic

open scoped Pointwise

variable {G : Type*} [Group G]

theorem conj_eq_iff_gen (g x y : G) : g⁻¹ * x * g = y ↔ x = g * y * g⁻¹ := by
  constructor
  · rintro rfl
    group
  · rintro rfl
    group

theorem conj_eq_one_iff_gen (g x : G) : g⁻¹ * x * g = 1 ↔ x = 1 := by
  rw [conj_eq_iff_gen, mul_one, mul_inv_cancel]

theorem conj_eq_central_iff_gen {c : G} (hc : ∀ y, y * c = c * y) (g x : G) :
    g⁻¹ * x * g = c ↔ x = c := by
  rw [conj_eq_iff_gen, hc g, mul_inv_cancel_right]

theorem conj_eq_central_mul_iff_gen {c : G} (hc : ∀ y, y * c = c * y) (g x y : G) :
    g⁻¹ * x * g = c * y ↔ x = c * (g * y * g⁻¹) := by
  rw [conj_eq_iff_gen, ← mul_assoc, hc g]
  simp only [mul_assoc]

theorem conj_mem_four_iff_gen {c l : G} (hc : ∀ y, y * c = c * y) (g x : G) :
    g⁻¹ * x * g ∈ ({1, c, l, c * l} : Set G) ↔
      x ∈ ({1, c, g * l * g⁻¹, c * (g * l * g⁻¹)} : Set G) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact or_congr (conj_eq_one_iff_gen g x) (or_congr (conj_eq_central_iff_gen hc g x)
    (or_congr (conj_eq_iff_gen g x l) (conj_eq_central_mul_iff_gen hc g x l)))

theorem mem_smul_subgroup_iff_gen (K : Subgroup G) (g x : G) :
    x ∈ MulAut.conj g • K ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g⁻¹ * (g * y * g⁻¹) * g ∈ K
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
  · intro h
    exact ⟨g⁻¹ * x * g, h, by change g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩

theorem conj_comm_iff_gen (g x y : G) :
    y * x = x * y ↔ (g⁻¹ * y * g) * (g⁻¹ * x * g) = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by
  constructor
  · intro h
    calc (g⁻¹ * y * g) * (g⁻¹ * x * g) = g⁻¹ * (y * x) * g := by group
      _ = g⁻¹ * (x * y) * g := by rw [h]
      _ = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
  · intro h
    calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = x * y := by group

theorem mem_center_smul_iff_gen (K : Subgroup G) (g x : G) :
    x ∈ (Subgroup.center ↥(MulAut.conj g • K)).map (MulAut.conj g • K).subtype ↔
      g⁻¹ * x * g ∈ (Subgroup.center K).map K.subtype := by
  rw [mem_map_center_iff, mem_map_center_iff, mem_smul_subgroup_iff_gen]
  refine and_congr_right fun _ => ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · have hy' : g * y * g⁻¹ ∈ MulAut.conj g • K := by
      rw [mem_smul_subgroup_iff_gen]
      rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    have h1 := (conj_comm_iff_gen g x _).1 (h _ hy')
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
  · exact (conj_comm_iff_gen g x y).2 (h _ ((mem_smul_subgroup_iff_gen K g y).1 hy))

theorem center_sylow_eq_conj_gen [Finite G] {p : ℕ} [Fact p.Prime] (T₀ T : Sylow p G)
    {S : Set G}
    (hS : ((Subgroup.center (T₀ : Subgroup G)).map (T₀ : Subgroup G).subtype : Set G) = S) :
    ∃ g : G, ((Subgroup.center (T : Subgroup G)).map (T : Subgroup G).subtype : Set G) =
      {x | g⁻¹ * x * g ∈ S} := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G T₀ T
  refine ⟨g, ?_⟩
  rw [← hS, Sylow.coe_subgroup_smul]
  ext x
  exact mem_center_smul_iff_gen _ g x

end Generic

theorem native_H_sylow_two_center
    (T : Sylow 2 (vStab cv0)) :
    Nat.card T = 2 ^ 38 ∧ ∃ r ∈ RA,
      ((Subgroup.center (T : Subgroup (vStab cv0))).map (T : Subgroup (vStab cv0)).subtype :
        Set (vStab cv0)) = {1, cV0, r, cV0 * r} := by
  refine ⟨natCard_sylow_two_H T, exists_sylow_two_AH.elim fun T₀ hT₀ =>
    (center_sylow_eq_conj_gen T₀ T (center_sylow_two_AH hT₀.1 hT₀.2)).elim fun g hg =>
      ⟨g * lamW0H * g⁻¹, (mem_RA_iff_isConj _).2 (isConj_iff.2 ⟨g, rfl⟩),
        hg.trans (Set.ext fun x => conj_mem_four_iff_gen cV0_comm g x)⟩⟩

theorem mem_inf_centralizer_sylow_iff
    {T₀ : Sylow 2 (vStab cv0)}
    (hN : NH ≤ (T₀ : Subgroup (vStab cv0))) (hA : (T₀ : Subgroup (vStab cv0)) ≤ AH)
    (x : vStab cv0) :
    x ∈ (T₀ : Subgroup (vStab cv0)) ⊓ Subgroup.centralizer (T₀ : Set (vStab cv0)) ↔
      x ∈ ({1, cV0, lamW0H, cV0 * lamW0H} : Set (vStab cv0)) := by
  have e : (T₀ : Subgroup (vStab cv0)) ⊓ Subgroup.centralizer (T₀ : Set (vStab cv0)) =
      (Subgroup.center (T₀ : Subgroup (vStab cv0))).map (T₀ : Subgroup (vStab cv0)).subtype :=
    (map_center_eq_inf_centralizer _).symm
  rw [e, ← SetLike.mem_coe, center_sylow_two_AH hN hA]

theorem cV0_mul_cV0_mul
    (y : vStab cv0) : cV0 * (cV0 * y) = y := by
  rw [← mul_assoc, cV0_mul_self, one_mul]

theorem of_conj_mem_four
    {y : vStab cv0} (hy1 : y ≠ 1) {g : vStab cv0}
    (h : g * y * g⁻¹ ∈ ({1, cV0, lamW0H, cV0 * lamW0H} : Set (vStab cv0))) :
    y = cV0 ∨ y ∈ RA ∨ y ∈ RB := by
  have h' : g⁻¹⁻¹ * y * g⁻¹ ∈ ({1, cV0, lamW0H, cV0 * lamW0H} : Set (vStab cv0)) := by
    rwa [inv_inv]
  rw [conj_mem_four_iff_gen cV0_comm] at h'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h'
  rcases h' with h1 | h1 | h1 | h1
  · exact absurd h1 hy1
  · exact Or.inl h1
  · exact Or.inr (Or.inl ((mem_RA_iff_isConj y).2 (isConj_iff.2 ⟨g⁻¹, h1.symm⟩)))
  · refine Or.inr (Or.inr ?_)
    show cV0 * y ∈ RA
    rw [h1, cV0_mul_cV0_mul]
    exact (mem_RA_iff_isConj _).2 (isConj_iff.2 ⟨g⁻¹, rfl⟩)

theorem conj_mem_four_of
    {y : vStab cv0} (h : y = cV0 ∨ y ∈ RA ∨ y ∈ RB) :
    ∃ g : vStab cv0, g * y * g⁻¹ ∈ ({1, cV0, lamW0H, cV0 * lamW0H} : Set (vStab cv0)) := by
  have key : ∀ c : vStab cv0, y ∈ ({1, cV0, c * lamW0H * c⁻¹, cV0 * (c * lamW0H * c⁻¹)} :
      Set (vStab cv0)) → ∃ g : vStab cv0,
        g * y * g⁻¹ ∈ ({1, cV0, lamW0H, cV0 * lamW0H} : Set (vStab cv0)) := by
    intro c hc
    refine ⟨c⁻¹, ?_⟩
    rw [inv_inv]
    exact (conj_mem_four_iff_gen cV0_comm c y).2 hc
  rcases h with rfl | h | h
  · exact key 1 (Or.inr (Or.inl rfl))
  · obtain ⟨c, hc⟩ := isConj_iff.1 ((mem_RA_iff_isConj y).1 h)
    exact key c (Or.inr (Or.inr (Or.inl hc.symm)))
  · obtain ⟨c, hc⟩ := isConj_iff.1 ((mem_RA_iff_isConj _).1 (show cV0 * y ∈ RA from h))
    refine key c (Or.inr (Or.inr (Or.inr ?_)))
    show y = cV0 * (c * lamW0H * c⁻¹)
    rw [hc, cV0_mul_cV0_mul]

theorem odd_card_involution_class_iff
    {y : vStab cv0} (hy : orderOf y = 2) :
    Odd (Nat.card (ConjClasses.mk y).carrier) ↔ y = cV0 ∨ y ∈ RA ∨ y ∈ RB := by
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact absurd hy (by norm_num)
  refine exists_sylow_two_AH.elim fun T₀ hT₀ => ?_
  refine (Recog.odd_card_conjClass_iff T₀ ⟨1, by rw [hy, pow_one]⟩).trans ⟨fun h => ?_, fun h => ?_⟩
  · exact h.elim fun g hg =>
      of_conj_mem_four hy1 ((mem_inf_centralizer_sylow_iff hT₀.1 hT₀.2 _).1 hg)
  · exact (conj_mem_four_of h).elim fun g hg =>
      ⟨g, (mem_inf_centralizer_sylow_iff hT₀.1 hT₀.2 _).2 hg⟩

theorem mem_RA_or_RB_of_two_part
    {y : vStab cv0} (hy : orderOf y = 2) (hyc : y ≠ cV0)
    (h2 : 2 ^ 38 ∣ Nat.card (Subgroup.centralizer {y})) : y ∈ RA ∨ y ∈ RB := by
  have hodd : Odd (Nat.card (ConjClasses.mk y).carrier) := by
    rw [Recog.card_carrier_conjClasses]
    obtain ⟨m, hm⟩ := h2
    have h := (Subgroup.centralizer {y}).index_mul_card
    rw [natCard_H, hm] at h
    have h' : (Subgroup.centralizer {y}).index * m = 1113694156575 := by
      have h3 : 2 ^ 38 * ((Subgroup.centralizer {y}).index * m) = 2 ^ 38 * 1113694156575 := by
        rw [← h]
        ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h3
    exact Odd.of_dvd_nat (by decide) ⟨m, h'.symm⟩
  rcases (odd_card_involution_class_iff hy).1 hodd with h | h | h
  · exact absurd h hyc
  · exact Or.inl h
  · exact Or.inr h

end CFSG.Monster.B.GSide
