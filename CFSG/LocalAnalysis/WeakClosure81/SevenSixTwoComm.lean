module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp76 (V H E J A X : Subgroup G) [(J.subgroupOf X).Normal] : Prop where
  isElemAbelian : IsElemAbelian 2 V
  isTI : IsTI V
  isMulCommutative : IsMulCommutative E
  le_H : E ≤ H
  normal_E : (E.subgroupOf H).Normal
  omega_le_H : ∀ W ∈ omegaSet V H E, W ≤ H
  le_pCore : J ≤ pCoreOf 2 H
  normal_J : (J.subgroupOf H).Normal
  iSub_le : iSub V H E ≤ J
  le_X : J ≤ X
  X_le_H : X ≤ H
  A_le_normalizer : A ≤ Subgroup.normalizer (X : Set G)
  relIndex_odd : Odd (J.relIndex X)
  nilpotent : Group.IsNilpotent (↥X ⧸ J.subgroupOf X)
  faithful : ∀ a ∈ A, (∀ x ∈ X, ⁅a, x⁆ ∈ J) → a ∈ J
  generated : A = ⨆ U ∈ omegaSet V H E, ⨆ (_ : U ≤ A), U
  isPGroup : IsPGroup 2 A

@[expose] def dSetIn (V H E J A : Subgroup G) : Set G :=
  {d | ∃ U ∈ omegaSet V H E, U ≤ A ⊔ J ∧ d ∈ U ∧ d ∉ J}

theorem s762C_le_sup_zpowers_of_relIndex_eq_two {L K : Subgroup G} (hLK : L ≤ K)
    (h : L.relIndex K = 2) {a : G} (haK : a ∈ K) (haL : a ∉ L) :
    K ≤ L ⊔ Subgroup.zpowers a := by
  intro x hxK
  have hKindex : (L.subgroupOf K).index = 2 := h
  by_cases hxL : x ∈ L
  · exact Subgroup.mem_sup_left hxL
  · have hmul := Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf K) hKindex
      (a := (⟨x, hxK⟩ : K)) (b := (⟨a, haK⟩ : K))
    have hxa : x * a ∈ L := by
      have : (⟨x, hxK⟩ : K) * (⟨a, haK⟩ : K) ∈ L.subgroupOf K := by
        rw [hmul]
        exact ⟨fun hx' => absurd (Subgroup.mem_subgroupOf.mp hx') hxL,
          fun ha' => absurd (Subgroup.mem_subgroupOf.mp ha') haL⟩
      exact Subgroup.mem_subgroupOf.mp this
    have hmem : (x * a) * a⁻¹ ∈ L ⊔ Subgroup.zpowers a :=
      (L ⊔ Subgroup.zpowers a).mul_mem (Subgroup.mem_sup_left hxa)
        (Subgroup.mem_sup_right ((Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a)))
    rwa [show (x * a) * a⁻¹ = x by group] at hmem

private theorem s762C_zpow_eq_one_or_self_of_mul_self_eq_one {x : G} (hx : x * x = 1)
    (n : ℤ) : x ^ n = 1 ∨ x ^ n = x := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hx]
    rw [h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_one, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hx]
    rw [h2, one_zpow, one_mul]

private theorem s762C_mem_of_mul_self_eq_one {X J : Subgroup G} [(J.subgroupOf X).Normal]
    (hodd : Odd (J.relIndex X)) {s : G} (hsX : s ∈ X) (hs2 : s * s = 1) : s ∈ J := by
  let S : ↥X := ⟨s, hsX⟩
  have hS2 : S ^ 2 = 1 := by
    apply Subtype.ext
    show s ^ 2 = (1 : G)
    rw [pow_two, hs2]
  have hq2 : (QuotientGroup.mk' (J.subgroupOf X) S) ^ 2 = 1 := by
    rw [← map_pow, hS2, map_one]
  have hdiv2 : orderOf (QuotientGroup.mk' (J.subgroupOf X) S) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hq2
  have hdiv : orderOf (QuotientGroup.mk' (J.subgroupOf X) S) ∣ J.relIndex X := by
    change orderOf (QuotientGroup.mk' (J.subgroupOf X) S) ∣ (J.subgroupOf X).index
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hodd_t : Odd (orderOf (QuotientGroup.mk' (J.subgroupOf X) S)) :=
    hodd.of_dvd_nat hdiv
  have hone : orderOf (QuotientGroup.mk' (J.subgroupOf X) S) = 1 :=
    hodd_t.coprime_two_right.eq_one_of_dvd hdiv2
  have hS1 : S ∈ J.subgroupOf X :=
    (QuotientGroup.eq_one_iff S).mp (orderOf_eq_one_iff.mp hone)
  exact Subgroup.mem_subgroupOf.mp hS1

private theorem s762C_mem_of_mul_self_eq_one_of_quotient {X N : Subgroup G}
    (hXN : X ≤ N) (hNnorm : N ≤ Subgroup.normalizer (X : Set G)) {s w : G}
    (hsN : s ∈ N) (hwX : w ∈ X) (hs2 : s * s = 1) (hswN : s * w ∈ N)
    (hodd : Odd (orderOf (s * w))) : s ∈ X := by
  haveI : (X.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mpr hNnorm
  let S : ↥N := ⟨s, hsN⟩
  let W : ↥N := ⟨w, hXN hwX⟩
  let SW : ↥N := ⟨s * w, hswN⟩
  have hSW : SW = S * W := Subtype.ext rfl
  have hWmem : W ∈ X.subgroupOf N := Subgroup.mem_subgroupOf.mpr hwX
  have hWq : QuotientGroup.mk' (X.subgroupOf N) W = 1 :=
    (QuotientGroup.eq_one_iff W).mpr hWmem
  have hSq : QuotientGroup.mk' (X.subgroupOf N) SW =
      QuotientGroup.mk' (X.subgroupOf N) S := by
    rw [hSW, map_mul, hWq, mul_one]
  have hSWpow : SW ^ orderOf (s * w) = 1 := by
    rw [show orderOf (s * w) = orderOf SW from (Subgroup.orderOf_mk (s * w) hswN).symm]
    exact pow_orderOf_eq_one SW
  have hSpow : (QuotientGroup.mk' (X.subgroupOf N) S) ^ orderOf (s * w) = 1 := by
    rw [← hSq, ← map_pow, hSWpow, map_one]
  have hS2 : S ^ 2 = 1 := by
    apply Subtype.ext
    show s ^ 2 = (1 : G)
    rw [pow_two, hs2]
  have hSq2 : (QuotientGroup.mk' (X.subgroupOf N) S) ^ 2 = 1 := by
    rw [← map_pow, hS2, map_one]
  have hodd_t : Odd (orderOf (QuotientGroup.mk' (X.subgroupOf N) S)) :=
    hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hSpow)
  have hone : orderOf (QuotientGroup.mk' (X.subgroupOf N) S) = 1 :=
    hodd_t.coprime_two_right.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hSq2)
  have hSmem : S ∈ X.subgroupOf N :=
    (QuotientGroup.eq_one_iff S).mp (orderOf_eq_one_iff.mp hone)
  exact Subgroup.mem_subgroupOf.mp hSmem

variable {V H E J A X : Subgroup G} [(J.subgroupOf X).Normal]

theorem Hyp76.isPGroup_sup (h : Hyp76 V H E J A X) : IsPGroup 2 ↥(A ⊔ J) := by
  have hAH : A ≤ H := by
    rw [h.generated]
    exact iSup_le fun U => iSup_le fun hU => iSup_le fun _ => h.omega_le_H U hU
  have hJleH : J ≤ H := h.le_X.trans h.X_le_H
  have hHnormJ : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJleH h.normal_J
  have hAnormJ : A ≤ Subgroup.normalizer (J : Set G) := hAH.trans hHnormJ
  have hJ2 : IsPGroup 2 J :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).to_le h.le_pCore
  exact h.isPGroup.to_sup_of_normal_right' hJ2 hAnormJ

theorem Hyp76.sup_le_normalizer (h : Hyp76 V H E J A X) :
    A ⊔ J ≤ Subgroup.normalizer (X : Set G) :=
  sup_le h.A_le_normalizer (h.le_X.trans Subgroup.le_normalizer)

theorem Hyp76.faithful_sup (h : Hyp76 V H E J A X) :
    ∀ a ∈ A ⊔ J, (∀ x ∈ X, ⁅a, x⁆ ∈ J) → a ∈ J := by
  have hAH : A ≤ H := by
    rw [h.generated]
    exact iSup_le fun U => iSup_le fun hU => iSup_le fun _ => h.omega_le_H U hU
  have hJleH : J ≤ H := h.le_X.trans h.X_le_H
  have hHnormJ : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJleH h.normal_J
  have hAnormJ : A ≤ Subgroup.normalizer (J : Set G) := hAH.trans hHnormJ
  intro a ha hcomm
  have hcoe : ((A ⊔ J : Subgroup G) : Set G) = (A : Set G) * (J : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A J hAnormJ
  have ha' : a ∈ (A : Set G) * (J : Set G) := by rw [← hcoe]; exact ha
  rw [Set.mem_mul] at ha'
  obtain ⟨a₁, ha₁, j, hj, rfl⟩ := ha'
  have ha₁J : a₁ ∈ J := by
    apply h.faithful a₁ ha₁
    intro x hx
    have hxH : x ∈ H := h.X_le_H hx
    have hjx : ⁅j, x⁆ ∈ J := by
      have hmem : x * j⁻¹ * x⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp (hHnormJ hxH) j⁻¹).mp (J.inv_mem hj)
      have hprod : j * (x * j⁻¹ * x⁻¹) ∈ J := J.mul_mem hj hmem
      rwa [show j * (x * j⁻¹ * x⁻¹) = ⁅j, x⁆ by
        simp only [commutatorElement_def]; group] at hprod
    have hconj : a₁ * ⁅j, x⁆ * a₁⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hAnormJ ha₁) ⁅j, x⁆).mp hjx
    have hid : ⁅a₁, x⁆ = (a₁ * ⁅j, x⁆ * a₁⁻¹)⁻¹ * ⁅a₁ * j, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [hid]
    exact J.mul_mem (J.inv_mem hconj) (hcomm x hx)
  exact J.mul_mem ha₁J hj

theorem Hyp76.relIndex_eq_two (h : Hyp76 V H E J A X) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) (hUA : U ≤ A ⊔ J) :
    J.relIndex U = 2 ∧ (U ⊓ iSub V H E).relIndex U = 2 :=
  seven_six_one_relIndex_eq_two h.isElemAbelian h.isTI h.isMulCommutative h.le_H
    h.normal_E h.omega_le_H h.le_pCore h.normal_J h.iSub_le h.le_X h.X_le_H
    h.sup_le_normalizer h.relIndex_odd h.faithful_sup U hU hUA

theorem Hyp76.commute_of_le_sup (h : Hyp76 V H E J A X) {U U' : Subgroup G}
    (hU : U ∈ omegaSet V H E) (hU' : U' ∈ omegaSet V H E)
    (hUA : U ≤ A ⊔ J) (hU'A : U' ≤ A ⊔ J) : ∀ u ∈ U, ∀ u' ∈ U', u * u' = u' * u := by
  rcases commutator_eq_bot_or_exists_conj h.isElemAbelian h.isTI h.isMulCommutative hU hU' with
    hbot | ⟨y, hy, hy'⟩
  · intro u hu u' hu'
    have hle : U ≤ Subgroup.centralizer (U' : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    exact (Subgroup.mem_centralizer_iff.mp (hle hu) u' hu').symm
  · have hyH : y ∈ H :=
      (sup_le (h.omega_le_H U hU) (h.omega_le_H U' hU')) hy
    subst U'
    intro u hu u' hu'
    have hUOm : U ∈ omegaSet U H E := by rw [omegaSet_eq_of_mem hU]; exact hU
    have hOmH : ∀ W ∈ omegaSet U H E, W ≤ H := by
      intro W hW
      rw [omegaSet_eq_of_mem hU] at hW
      exact h.omega_le_H W hW
    have hP : IsPGroup 2 ↥(U ⊔ conjSubgroup U y ⊔ J) :=
      h.isPGroup_sup.to_le (sup_le (sup_le hUA hU'A) le_sup_right)
    exact seven_three_one (V := U) (H := H) (E := E) (J := J)
      (isElemAbelian_of_mem_omegaSet h.isElemAbelian hU) (isTI_of_mem_omegaSet hU h.isTI)
      h.isMulCommutative h.le_H h.normal_E hUOm hOmH h.le_pCore h.normal_J hyH hP u hu u' hu'

theorem Hyp76.commute_conj (h : Hyp76 V H E J A X) {U U' : Subgroup G}
    (hU : U ∈ omegaSet V H E) (hU' : U' ∈ omegaSet V H E)
    (hUA : U ≤ A ⊔ J) (hU'A : U' ≤ A ⊔ J) {d d' : G} (hd : d ∈ U) (hdJ : d ∉ J)
    (hd' : d' ∈ U') (hd'J : d' ∉ J) (hne : d⁻¹ * d' ∉ J) {x : G} (hx : x ∈ X) :
    ∀ u ∈ U, ∀ v ∈ conjSubgroup U' x, u * v = v * u := by
  have hxH : x ∈ H := h.X_le_H hx
  have hUH : U ≤ H := h.omega_le_H U hU
  have hU'H : U' ≤ H := h.omega_le_H U' hU'
  have hWOm : conjSubgroup U' x ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le_H h.normal_E hU' hxH
  have hWH : conjSubgroup U' x ≤ H := h.omega_le_H _ hWOm
  have hJleH : J ≤ H := h.le_X.trans h.X_le_H
  have hHnormJ : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJleH h.normal_J
  set W : Subgroup G := conjSubgroup U' x with hWdef
  set e : G := x⁻¹ * d' * x with hedef
  have heW : e ∈ W := by
    rw [hWdef, hedef, mem_conjSubgroup_iff]
    rw [show x * (x⁻¹ * d' * x) * x⁻¹ = d' by group]
    exact hd'
  have hWOm' : W ∈ omegaSet V H E := by rw [hWdef]; exact hWOm
  have hWH' : W ≤ H := by rw [hWdef]; exact hWH
  have hd2 : d * d = 1 :=
    elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.isElemAbelian hU) hd
  have hd'2 : d' * d' = 1 :=
    elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.isElemAbelian hU') hd'
  have he2 : e * e = 1 :=
    elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.isElemAbelian hWOm') heW
  have hdd' : d * d' = d' * d := h.commute_of_le_sup hU hU' hUA hU'A d hd d' hd'
  have hdN : d ∈ Subgroup.normalizer (X : Set G) := h.sup_le_normalizer (hUA hd)
  have hd'N : d' ∈ Subgroup.normalizer (X : Set G) := h.sup_le_normalizer (hU'A hd')
  set s : G := d * d' with hsdef
  set w : G := d'⁻¹ * x⁻¹ * d' * x with hwdef
  have hde : d * e = s * w := by rw [hsdef, hwdef, hedef]; group
  have hs2 : s * s = 1 := by
    rw [hsdef]
    calc (d * d') * (d * d') = d * (d' * d) * d' := by group
      _ = d * (d * d') * d' := by rw [← hdd']
      _ = (d * d) * (d' * d') := by group
      _ = 1 := by rw [hd2, hd'2, one_mul]
  have hwX : w ∈ X := by
    rw [hwdef]
    have hconj : d'⁻¹ * x⁻¹ * d' ∈ X := by
      have hmem := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (X : Set G)).inv_mem hd'N) x⁻¹).mp (X.inv_mem hx)
      simpa only [inv_inv] using hmem
    exact X.mul_mem hconj hx
  have hsN : s ∈ Subgroup.normalizer (X : Set G) := by
    rw [hsdef]; exact (Subgroup.normalizer (X : Set G)).mul_mem hdN hd'N
  have hxN : x ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer hx
  have heN : e ∈ Subgroup.normalizer (X : Set G) := by
    rw [hedef]
    exact (Subgroup.normalizer (X : Set G)).mul_mem
      ((Subgroup.normalizer (X : Set G)).mul_mem
        ((Subgroup.normalizer (X : Set G)).inv_mem hxN) hd'N) hxN
  have hswN : s * w ∈ Subgroup.normalizer (X : Set G) := by
    rw [← hde]; exact (Subgroup.normalizer (X : Set G)).mul_mem hdN heN
  have hP2 : IsPGroup 2 ↥(Subgroup.closure ({d, e} : Set G)) := by
    by_contra hnot
    have hdeOdd : Odd (orderOf (d * e)) :=
      seven_three_A h.isElemAbelian h.isTI h.isMulCommutative hU hWOm' hd heW hnot
    have hswOdd : Odd (orderOf (s * w)) := hde ▸ hdeOdd
    have hsX : s ∈ X :=
      s762C_mem_of_mul_self_eq_one_of_quotient (N := Subgroup.normalizer (X : Set G))
        Subgroup.le_normalizer le_rfl hsN hwX hs2 hswN hswOdd
    have hsJ : s ∈ J := s762C_mem_of_mul_self_eq_one h.relIndex_odd hsX hs2
    have hsd : d⁻¹ * d' = s := by
      rw [hsdef]
      have hdinv : d⁻¹ = d :=
        CFSG.CGT.Timmesfeld75.elemAbelian_inv
          (isElemAbelian_of_mem_omegaSet h.isElemAbelian hU) hd
      rw [hdinv]
    exact hne (hsd.symm ▸ hsJ)
  have hUrel : (U ⊓ J).relIndex U = 2 := by
    have hfirst := h.relIndex_eq_two hU hUA
    rw [← inf_iSub_eq_inf_J hU h.iSub_le h.le_pCore]
    exact hfirst.2
  have hU'_rel : (U' ⊓ J).relIndex U' = 2 := by
    have hfirst := h.relIndex_eq_two hU' hU'A
    rw [← inf_iSub_eq_inf_J hU' h.iSub_le h.le_pCore]
    exact hfirst.2
  have hU_le : U ≤ Subgroup.closure ({d, e} : Set G) ⊔ J :=
    (s762C_le_sup_zpowers_of_relIndex_eq_two inf_le_left hUrel hd
      (fun hdinf => hdJ (Subgroup.mem_inf.mp hdinf).2)).trans
      (sup_le (inf_le_right.trans le_sup_right)
        ((Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))).trans le_sup_left))
  have hU'_le : U' ≤ Subgroup.zpowers d' ⊔ J :=
    (s762C_le_sup_zpowers_of_relIndex_eq_two inf_le_left hU'_rel hd'
      (fun hd'inf => hd'J (Subgroup.mem_inf.mp hd'inf).2)).trans
      (sup_le (inf_le_right.trans le_sup_right) le_sup_left)
  have hJfix : conjSubgroup J x = J :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hHnormJ hxH)
  have hconjzp : conjSubgroup (Subgroup.zpowers d') x = Subgroup.zpowers e := by
    rw [hedef, CFSG.Quasithin.conjSubgroup, MonoidHom.map_zpowers]
    congr 1
    show MulAut.conj x⁻¹ d' = x⁻¹ * d' * x
    rw [MulAut.conj_apply, inv_inv]
  have hW_le : W ≤ Subgroup.closure ({d, e} : Set G) ⊔ J := by
    rw [hWdef]
    calc conjSubgroup U' x
        ≤ conjSubgroup (Subgroup.zpowers d' ⊔ J) x := Subgroup.map_mono hU'_le
      _ = conjSubgroup (Subgroup.zpowers d') x ⊔ conjSubgroup J x := by
          simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_sup]
      _ = Subgroup.zpowers e ⊔ J := by rw [hconjzp, hJfix]
      _ ≤ Subgroup.closure ({d, e} : Set G) ⊔ J :=
          sup_le ((Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))).trans
            le_sup_left) le_sup_right
  have hJ2 : IsPGroup 2 J :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).to_le h.le_pCore
  have hPnormJ : Subgroup.closure ({d, e} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
    refine (Subgroup.closure_le (K := Subgroup.normalizer (J : Set G))).mpr ?_
    rintro y (rfl | rfl)
    · exact hHnormJ (hUH hd)
    · exact hHnormJ (hWH' heW)
  have hPJ2 : IsPGroup 2 ↥(Subgroup.closure ({d, e} : Set G) ⊔ J) :=
    hP2.to_sup_of_normal_right' hJ2 hPnormJ
  have hkey : ⁅U, W⁆ = ⊥ := by
    rcases commutator_eq_bot_or_exists_conj h.isElemAbelian h.isTI h.isMulCommutative hU hWOm'
      with hbot | ⟨y, hy, hy'⟩
    · exact hbot
    · have hyH : y ∈ H := (sup_le hUH hWH') hy
      have hUOm : U ∈ omegaSet U H E := by rw [omegaSet_eq_of_mem hU]; exact hU
      have hOmH : ∀ Z ∈ omegaSet U H E, Z ≤ H := by
        intro Z hZ
        rw [omegaSet_eq_of_mem hU] at hZ
        exact h.omega_le_H Z hZ
      have hWy : conjSubgroup U y ≤ Subgroup.closure ({d, e} : Set G) ⊔ J := by
        rw [← hy']; exact hW_le
      have hP : IsPGroup 2 ↥(U ⊔ conjSubgroup U y ⊔ J) :=
        hPJ2.to_le (sup_le (sup_le hU_le hWy) le_sup_right)
      have hcomm := seven_three_one (V := U) (H := H) (E := E) (J := J)
        (isElemAbelian_of_mem_omegaSet h.isElemAbelian hU) (isTI_of_mem_omegaSet hU h.isTI)
        h.isMulCommutative h.le_H h.normal_E hUOm hOmH h.le_pCore h.normal_J hyH hP
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rw [hy'] at hv
      exact (hcomm u hu v hv).symm
  intro u hu v hv
  have hle : U ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hkey
  exact (Subgroup.mem_centralizer_iff.mp (hle hu) v (hWdef.symm ▸ hv)).symm

theorem Hyp76.centralizes_commutator (h : Hyp76 V H E J A X) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) (hUA : U ≤ A ⊔ J) {d d' : G} (hd : d ∈ U) (hdJ : d ∉ J)
    (hd' : d' ∈ dSetIn V H E J A) (hne : d⁻¹ * d' ∉ J) :
    ∀ u ∈ U, ∀ y ∈ ⁅X, Subgroup.zpowers d'⁆, u * y = y * u := by
  obtain ⟨U', hU', hU'A, hd'mem, hd'J⟩ := hd'
  have hd'2 : d' * d' = 1 :=
    elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.isElemAbelian hU') hd'mem
  have hcomm_le : ⁅X, Subgroup.zpowers d'⁆ ≤ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.commutator_le]
    intro g hg z hz
    rw [Subgroup.mem_zpowers_iff] at hz
    obtain ⟨n, rfl⟩ := hz
    rcases s762C_zpow_eq_one_or_self_of_mul_self_eq_one hd'2 n with h1 | h2
    · rw [h1]; simp [commutatorElement_def]
    · rw [h2]
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hga : g * d' * g⁻¹ ∈ conjSubgroup U' g⁻¹ := by
        rw [mem_conjSubgroup_iff]
        rw [show (g⁻¹) * (g * d' * g⁻¹) * (g⁻¹)⁻¹ = d' by group]
        exact hd'mem
      have hca : u * (g * d' * g⁻¹) = (g * d' * g⁻¹) * u :=
        h.commute_conj hU hU' hUA hU'A hd hdJ hd'mem hd'J hne (X.inv_mem hg) u hu _ hga
      have hcd : u * d'⁻¹ = d'⁻¹ * u :=
        h.commute_of_le_sup hU hU' hUA hU'A u hu d'⁻¹ (U'.inv_mem hd'mem)
      rw [commutatorElement_def]
      calc u * (g * d' * g⁻¹ * d'⁻¹)
          = (u * (g * d' * g⁻¹)) * d'⁻¹ := by group
        _ = ((g * d' * g⁻¹) * u) * d'⁻¹ := by rw [hca]
        _ = (g * d' * g⁻¹) * (u * d'⁻¹) := by group
        _ = (g * d' * g⁻¹) * (d'⁻¹ * u) := by rw [hcd]
        _ = (g * d' * g⁻¹ * d'⁻¹) * u := by group
  intro u hu y hy
  exact Subgroup.mem_centralizer_iff.mp (hcomm_le hy) u hu

end CFSG.LocalAnalysis.WeakClosure81
