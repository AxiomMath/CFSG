module

public import CFSG.Quasithin.Vol2.Ch10SecQ34LE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {A : Type*} [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime]

theorem relIndex_ne_zero' (H K : Subgroup A) : H.relIndex K ≠ 0 := by
  intro h
  have h1 := (H.subgroupOf K).card_mul_index
  rw [show (H.subgroupOf K).index = H.relIndex K from rfl, h, mul_zero] at h1
  exact (Nat.card_pos (α := ↥K)).ne' h1.symm

theorem mem_normalizer_of_odd_alt4 (hp2 : p ≠ 2) (e : A ≃* PSL(2, ZMod p)) {S Y R : Subgroup A}
    (hS : IsSylowTwoOf S ⊤) (hSY : S ≤ Subgroup.normalizer (Y : Set A))
    (eY : ↥Y ≃* alternatingGroup (Fin 4)) (hY3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) (hRS : R ≤ S)
    (hWR : pCoreOf 2 (Y ⊔ S) ≤ R) {a : A} (ha : a ∈ Subgroup.normalizer (R : Set A))
    (hodd : Odd (orderOf a)) : a ∈ Subgroup.normalizer (Y : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := hS.2.1
  have hY12 : Nat.card Y = 12 := by rw [Nat.card_congr eY.toEquiv, card_alt4]
  set V := pCoreOf 2 Y with hV
  have hV4 : Nat.card V = 4 := card_pCoreOf_eq_four hY12 hY3
  have hVY : V ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hVsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    have h4 : (⟨v, hVY hv⟩ : ↥Y) ^ 4 = 1 := by
      have h := pow_card_eq_one' (G := ↥V) (x := ⟨v, hv⟩)
      rw [hV4] at h
      have h' : v ^ 4 = 1 := by simpa using congrArg Subtype.val h
      exact Subtype.ext (by simpa using h')
    have h := alt4_sq_of_pow_four (eY ⟨v, hVY hv⟩) (by rw [← map_pow, h4, map_one])
    have h2 : (⟨v, hVY hv⟩ : ↥Y) ^ 2 = 1 := eY.injective (by rw [map_pow, h, map_one])
    exact congrArg Subtype.val h2
  have hVK : IsKleinFour ↥V := by
    have : Nontrivial ↥V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV4]; norm_num)
    refine ⟨hV4, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun v hv => ?_⟩
    exact orderOf_eq_prime (Subtype.ext (hVsq v v.2)) hv
  have hCV := centralizer_eq_of_kleinFour hp2 e hVK
  have hNV := card_normalizer_dvd hV4 hCV
  have hYNV : Y ≤ Subgroup.normalizer (V : Set A) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hSNV : S ≤ Subgroup.normalizer (V : Set A) :=
    hSY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hVR : V ≤ R := (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hVY.trans le_sup_left) (sup_le hYNV hSNV) hV2).trans hWR
  by_cases hRV : R = V
  · rw [hRV] at ha
    exact Subgroup.le_normalizer (mem_of_odd_of_le_normalizer hNV hYNV hY12 ha hodd)
  · obtain ⟨m, -, ⟨eS⟩⟩ := exists_dihedral_of_sylow hp2 e hS
    have hcS : Nat.card S = 2 * 2 ^ m := by
      rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
    have h4R : 4 ∣ Nat.card R := hV4 ▸ Subgroup.card_dvd_of_le hVR
    have hR4 : Nat.card R ≠ 4 := fun h =>
      hRV (Subgroup.eq_of_le_of_card_ge hVR (by rw [h, hV4])).symm
    have hS24 : Nat.card S ∣ 24 := (Subgroup.card_dvd_of_le hSNV).trans hNV
    have hRle : Nat.card R ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hRS)
    have hR0 : 0 < Nat.card R := Nat.card_pos
    have hm3 : m < 3 := by
      by_contra h
      have h16 : 16 ∣ Nat.card S := by
        rw [hcS, show 16 = 2 * 2 ^ 3 by norm_num]
        exact Nat.mul_dvd_mul_left 2 (Nat.pow_dvd_pow 2 (by omega))
      exact absurd (h16.trans hS24) (by norm_num)
    have hSle : Nat.card S ≤ 8 := by
      rw [hcS]
      interval_cases m <;> norm_num
    have hR8 : Nat.card R = 8 := by omega
    have hS8 : Nat.card S = 8 := by omega
    have hRS_eq : R = S := Subgroup.eq_of_le_of_card_ge hRS (by rw [hR8, hS8])
    have hm : 2 ^ m = 4 := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcS.symm.trans hS8)
    rw [hRS_eq] at ha
    have haC := mem_centralizer_of_dihedral (n := 2 ^ m) (by rw [hm]) eS hS2 ha hodd
    have haV : a ∈ V := hCV.le (Subgroup.centralizer_le (hVR.trans hRS) haC)
    rw [eq_one_of_odd_of_isPGroup hV2 haV hodd]
    exact Subgroup.one_mem _

theorem mem_normalizer_of_odd_three (hp5 : 5 ≤ p)
    (e : A ≃* PSL(2, ZMod p)) {S Y R : Subgroup A} (hS : IsSylowTwoOf S ⊤)
    (hSY : S ≤ Subgroup.normalizer (Y : Set A)) (hY : Nat.card Y = 3) (hRS : R ≤ S)
    (hWR : pCoreOf 2 (Y ⊔ S) ≤ R) (h8 : p % 8 = 1 ∨ p % 8 = 7) {a : A}
    (ha : a ∈ Subgroup.normalizer (R : Set A)) (hodd : Odd (orderOf a)) :
    a ∈ Subgroup.normalizer (Y : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : p ≠ 2 := by omega
  have hS2 : IsPGroup 2 S := hS.2.1
  obtain ⟨m, -, ⟨eS⟩⟩ := exists_dihedral_of_sylow hp2 e hS
  have hcS : Nat.card S = 2 * 2 ^ m := by rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
  have h8S := eight_dvd_card_sylow h8 e hS
  have hm4 : 4 ≤ 2 ^ m := by
    rw [hcS] at h8S
    have hpos : 0 < 2 ^ m := by positivity
    generalize 2 ^ m = M at h8S hpos
    omega
  have hYc : IsCyclic ↥Y := isCyclic_of_prime_card hY
  obtain ⟨y0, hy0⟩ := hYc.exists_generator
  have hoy : orderOf (y0 : A) = 3 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy0, hY]
  set U := S ⊓ Subgroup.centralizer (Y : Set A) with hU
  have hUS : U ≤ S := inf_le_left
  have hU2 : IsPGroup 2 U := hS2.to_le hUS
  have hidx : U.relIndex S ∣ 2 := relIndex_centralizer_dvd_two hY hSY
  have hYU : Y ≤ Subgroup.normalizer (U : Set A) := fun w hw =>
    mem_normalizer_of_forall_conj_mem fun u hu => by
      rw [Subgroup.mem_centralizer_iff.mp hu.2 w hw, mul_inv_cancel_right]
      exact hu
  have hSU : S ≤ Subgroup.normalizer (U : Set A) := fun s hs =>
    mem_normalizer_of_forall_conj_mem fun u hu => by
      refine ⟨S.mul_mem (S.mul_mem hs (hUS hu)) (S.inv_mem hs),
        Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hw' : s⁻¹ * w * s ∈ Y := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hSY hs)) w).mp hw
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hu.2 _ hw'
      calc w * (s * u * s⁻¹) = s * ((s⁻¹ * w * s) * u) * s⁻¹ := by group
        _ = s * (u * (s⁻¹ * w * s)) * s⁻¹ := by rw [hc]
        _ = s * u * s⁻¹ * w := by group
  have hUR : U ≤ R := (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hUS.trans le_sup_right) (sup_le hYU hSU) hU2).trans hWR
  have hCy := isCyclic_centralizer e (g := (y0 : A)) (by omega) (by
    rw [hoy]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega)
  have hUCy : U ≤ Subgroup.centralizer ({(y0 : A)} : Set A) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hu.2 _ y0.2).symm
  have hUc : IsCyclic ↥U := Subgroup.isCyclic_of_le hUCy
  have hcU : Nat.card U * U.relIndex S = Nat.card S := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv]
    exact (U.subgroupOf S).card_mul_index
  have hU4 : 4 ≤ Nat.card U := by
    obtain ⟨i, hi⟩ : ∃ i, U.relIndex S = i := ⟨_, rfl⟩
    have hi2 : i ≤ 2 := hi ▸ Nat.le_of_dvd (by norm_num) hidx
    rw [hi, hcS] at hcU
    generalize 2 ^ m = M at hcU hm4
    interval_cases i <;> omega
  have haU : a ∈ Subgroup.centralizer (U : Set A) := by
    have h1 := Subgroup.relIndex_mul_relIndex U R S hUR hRS
    by_cases hRS' : R.relIndex S = 1
    · have hRS_eq : R = S := le_antisymm hRS (Subgroup.relIndex_eq_one.mp hRS')
      rw [hRS_eq] at ha
      exact Subgroup.centralizer_le hUS (mem_centralizer_of_dihedral hm4 eS hS2 ha hodd)
    · have hUR1 : U.relIndex R = 1 := by
        have hne := relIndex_ne_zero' R S
        have hne' := relIndex_ne_zero' U R
        have h2 := Nat.le_of_dvd (by norm_num) (h1 ▸ hidx)
        rcases Nat.lt_or_ge (U.relIndex R) 2 with h | h
        · omega
        · exfalso
          have := Nat.mul_le_mul h (show 2 ≤ R.relIndex S by omega)
          omega
      have hRU : R = U := le_antisymm (Subgroup.relIndex_eq_one.mp hUR1) hUR
      rw [hRU] at ha
      exact mem_centralizer_of_cyclic hUc hU2 ha hodd
  obtain ⟨u0, hu0⟩ := hUc.exists_generator
  have hou : orderOf (u0 : A) = Nat.card U := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hu0]
  have hCu := isCyclic_centralizer e (g := (u0 : A)) (by omega) (by
    rw [hou]
    intro h
    have h2 : p ∣ 2 ^ (m + 1) := h.trans (by
      rw [pow_succ, mul_comm, ← hcS]
      exact Subgroup.card_dvd_of_le hUS)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h2)))
  have hau : a ∈ Subgroup.centralizer ({(u0 : A)} : Set A) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp haU _ u0.2).symm
  have hyu : (y0 : A) ∈ Subgroup.centralizer ({(u0 : A)} : Set A) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp u0.2.2 _ y0.2)
  have hcomm : a * y0 = y0 * a := congrArg Subtype.val
    (isMulCommutative_iff.mp (IsCyclic.isMulCommutative (α := ↥(Subgroup.centralizer
      ({(u0 : A)} : Set A)))) ⟨a, hau⟩ ⟨y0, hyu⟩)
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hy0 ⟨w, hw⟩)
  have hw : w = (y0 : A) ^ k := by rw [← Subgroup.coe_zpow, hk]
  rw [hw]
  exact (Commute.zpow_left (show Commute (y0 : A) a from hcomm.symm) k).eq

theorem mem_normalizer_of_odd (hp5 : 5 ≤ p)
    (e : A ≃* PSL(2, ZMod p)) {S Y R : Subgroup A} (hS : IsSylowTwoOf S ⊤)
    (hSY : S ≤ Subgroup.normalizer (Y : Set A)) (hY1 : Y ≠ ⊥) (hYO : oTwoUpper Y = Y)
    (hY3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) (hRS : R ≤ S) (hWR : pCoreOf 2 (Y ⊔ S) ≤ R)
    (h8 : p % 8 = 3 ∨ p % 8 = 5 → pCoreOf 2 Y ≠ ⊥) {a : A}
    (ha : a ∈ Subgroup.normalizer (R : Set A)) (hodd : Odd (orderOf a)) :
    a ∈ Subgroup.normalizer (Y : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases card_eq_three_or_alt4 hp5 e hY1 hYO hY3 with hY | heY
  · refine mem_normalizer_of_odd_three hp5 e hS hSY hY hRS hWR ?_ ha hodd
    have hO2 : pCoreOf 2 Y = ⊥ := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
      have hd : Nat.card ↥(pCoreOf 2 Y) ∣ 3 :=
        hY ▸ Subgroup.card_dvd_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      rw [hk] at hd
      rcases k with _ | k
      · rw [← Subgroup.card_eq_one, hk, pow_zero]
      · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hd) (by norm_num)
    have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two (by omega))
    by_contra hcon
    exact h8 (by omega) hO2
  · obtain ⟨eY⟩ := heY
    exact mem_normalizer_of_odd_alt4 (by omega) e hS hSY eY hY3 hRS hWR ha hodd

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
