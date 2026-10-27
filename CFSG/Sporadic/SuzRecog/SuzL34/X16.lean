module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoA5
import CFSG.Monster.B.Co2.IsInvA
public import CFSG.Sporadic.SuzRecog.SuzL34.Facts

public section

open CFSG.Sporadic.SuzRecog.SuzL34Cert
open CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzOddCore
open Subgroup

namespace CFSG.Sporadic.SuzRecog.SuzL34Cert

def xB0inv : Array ℕ :=
  #[0, 9, 5, 12, 14, 7, 11, 2, 1, 8, 4, 13, 15, 6, 10, 3]

def xB1inv : Array ℕ :=
  #[0, 9, 7, 14, 11, 2, 12, 5, 1, 8, 6, 15, 10, 3, 13, 4]

def xB2inv : Array ℕ :=
  #[0, 9, 13, 4, 7, 14, 10, 3, 1, 8, 12, 5, 6, 15, 11, 2]

def xB3inv : Array ℕ :=
  #[0, 9, 14, 7, 3, 10, 13, 4, 1, 8, 15, 6, 2, 11, 12, 5]

private def tb0inv : Array ℕ :=
  #[0, 1, 5, 4, 3, 2, 6, 7, 9, 8, 12, 13, 10, 11, 15, 14]

private def tb1inv : Array ℕ :=
  #[0, 1, 4, 5, 2, 3, 6, 7, 15, 14, 11, 10, 13, 12, 9, 8]

theorem isInvA_xA : isInvA 16 xA xA = true := by
  apply CFSG.Monster.B.Co2.isInvA_iff.2; intro i hi; interval_cases i <;> decide

theorem isInvA_xB0 : isInvA 16 xBs[0]! xB0inv = true := by
  apply CFSG.Monster.B.Co2.isInvA_iff.2; intro i hi; interval_cases i <;> decide

theorem isInvA_xB1 : isInvA 16 xBs[1]! xB1inv = true := by
  apply CFSG.Monster.B.Co2.isInvA_iff.2; intro i hi; interval_cases i <;> decide

theorem isInvA_xB2 : isInvA 16 xBs[2]! xB2inv = true := by
  apply CFSG.Monster.B.Co2.isInvA_iff.2; intro i hi; interval_cases i <;> decide

theorem isInvA_xB3 : isInvA 16 xBs[3]! xB3inv = true := by
  apply CFSG.Monster.B.Co2.isInvA_iff.2; intro i hi; interval_cases i <;> decide

private theorem isInvA_tb0 : isInvA 16 tbarTabs[0]! tb0inv = true := by
  apply CFSG.Monster.B.Co2.isInvA_iff.2; intro i hi; interval_cases i <;> decide

private theorem isInvA_tb1 : isInvA 16 tbarTabs[1]! tb1inv = true := by
  apply CFSG.Monster.B.Co2.isInvA_iff.2; intro i hi; interval_cases i <;> decide

private theorem isInvA_idA : isInvA 16 (idA 16) (idA 16) = true := by
  apply CFSG.Monster.B.Co2.isInvA_iff.2
  intro i hi
  simp [idA_get hi, hi]

private theorem tabPerm16_idA : tabPerm16 (idA 16) = 1 :=
  Rep.unique (rep_permC isInvA_idA).1 rep_idA

private theorem mul_self_eq_one_of_compA {t r : Array ℕ} (h : isInvA 16 t r = true)
    (hcomp : compA 16 t t = idA 16) : tabPerm16 t * tabPerm16 t = 1 := by
  have ht : Rep 16 t (tabPerm16 t) := (rep_permC h).1
  have h2 : Rep 16 (compA 16 t t) (tabPerm16 t * tabPerm16 t) := rep_compA ht ht
  rw [hcomp] at h2
  exact Rep.unique h2 rep_idA

private theorem pow_three_eq_one_of_compA {t r : Array ℕ} (h : isInvA 16 t r = true)
    (hcomp : compA 16 (compA 16 t t) t = idA 16) : tabPerm16 t ^ 3 = 1 := by
  have ht : Rep 16 t (tabPerm16 t) := (rep_permC h).1
  have h2 : Rep 16 (compA 16 t t) (tabPerm16 t * tabPerm16 t) := rep_compA ht ht
  have h3 : Rep 16 (compA 16 (compA 16 t t) t)
      ((tabPerm16 t * tabPerm16 t) * tabPerm16 t) := rep_compA h2 ht
  have hpow : tabPerm16 t ^ 3 = (tabPerm16 t * tabPerm16 t) * tabPerm16 t := by
    rw [pow_succ, pow_succ, pow_one]
  rw [hpow]
  rw [hcomp] at h3
  exact Rep.unique h3 rep_idA

private theorem mul_pow_five_eq_one_of_compA {t u rt ru : Array ℕ}
    (ht : isInvA 16 t rt = true) (hu : isInvA 16 u ru = true)
    (hcomp : compA 16
      (compA 16 (compA 16 (compA 16 t u) (compA 16 t u))
        (compA 16 (compA 16 t u) (compA 16 t u)))
      (compA 16 t u) = idA 16) :
    (tabPerm16 t * tabPerm16 u) ^ 5 = 1 := by
  let T := compA 16 t u
  let T2 := compA 16 T T
  let T4 := compA 16 T2 T2
  have hp : Rep 16 T (tabPerm16 t * tabPerm16 u) :=
    rep_compA (rep_permC ht).1 (rep_permC hu).1
  have hp2 : Rep 16 T2 ((tabPerm16 t * tabPerm16 u) ^ 2) := by
    have := rep_compA hp hp
    simpa [T2, pow_two] using this
  have hp4 : Rep 16 T4 ((tabPerm16 t * tabPerm16 u) ^ 4) := by
    have h := rep_compA hp2 hp2
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
    exact h
  have hp5 : Rep 16 (compA 16 T4 T) ((tabPerm16 t * tabPerm16 u) ^ 5) := by
    have h := rep_compA hp4 hp
    rw [show (5 : ℕ) = 4 + 1 by norm_num, pow_add, pow_one]
    exact h
  have hcomp' : compA 16 T4 T = idA 16 := hcomp
  rw [hcomp'] at hp5
  exact Rep.unique hp5 rep_idA

theorem tabPerm16_xA_mul_self : tabPerm16 xA * tabPerm16 xA = 1 :=
  mul_self_eq_one_of_compA isInvA_xA (by decide)

theorem tabPerm16_xB_pow_three {i : ℕ} (hi : i < 4) : tabPerm16 xBs[i]! ^ 3 = 1 := by
  interval_cases i
  · exact pow_three_eq_one_of_compA isInvA_xB0 (by decide)
  · exact pow_three_eq_one_of_compA isInvA_xB1 (by decide)
  · exact pow_three_eq_one_of_compA isInvA_xB2 (by decide)
  · exact pow_three_eq_one_of_compA isInvA_xB3 (by decide)

theorem tabPerm16_xA_mul_xB_pow_five {i : ℕ} (hi : i < 4) :
    (tabPerm16 xA * tabPerm16 xBs[i]!) ^ 5 = 1 := by
  interval_cases i
  · exact mul_pow_five_eq_one_of_compA isInvA_xA isInvA_xB0 (by decide)
  · exact mul_pow_five_eq_one_of_compA isInvA_xA isInvA_xB1 (by decide)
  · exact mul_pow_five_eq_one_of_compA isInvA_xA isInvA_xB2 (by decide)
  · exact mul_pow_five_eq_one_of_compA isInvA_xA isInvA_xB3 (by decide)

private theorem commute_of_compA {t u rt ru : Array ℕ}
    (ht : isInvA 16 t rt = true) (hu : isInvA 16 u ru = true)
    (hcomp : compA 16 t u = compA 16 u t) :
    tabPerm16 t * tabPerm16 u = tabPerm16 u * tabPerm16 t := by
  have h1 : Rep 16 (compA 16 t u) (tabPerm16 t * tabPerm16 u) :=
    rep_compA (rep_permC ht).1 (rep_permC hu).1
  have h2 : Rep 16 (compA 16 u t) (tabPerm16 u * tabPerm16 t) :=
    rep_compA (rep_permC hu).1 (rep_permC ht).1
  rw [hcomp] at h1
  exact Rep.unique h1 h2

private theorem ne_of_table_ne {t u rt ru : Array ℕ}
    (ht : isInvA 16 t rt = true) (hu : isInvA 16 u ru = true)
    {k : ℕ} (hk : k < 16) (hne : t[k]! ≠ u[k]!) :
    tabPerm16 t ≠ tabPerm16 u := by
  intro h
  have h1 : (tabPerm16 t ⟨k, hk⟩).val = (tabPerm16 u ⟨k, hk⟩).val :=
    congrArg (fun p => (p ⟨k, hk⟩).val) h
  rw [show (tabPerm16 t ⟨k, hk⟩).val = t[k]! from ((rep_permC ht).1 ⟨k, hk⟩).symm,
      show (tabPerm16 u ⟨k, hk⟩).val = u[k]! from ((rep_permC hu).1 ⟨k, hk⟩).symm] at h1
  exact hne h1

theorem card_Tbar16 : Nat.card Tbar16 = 4 := by
  let a := tabPerm16 tbarTabs[0]!
  let b := tabPerm16 tbarTabs[1]!
  have ha : a * a = 1 := mul_self_eq_one_of_compA isInvA_tb0 (by decide)
  have hb : b * b = 1 := mul_self_eq_one_of_compA isInvA_tb1 (by decide)
  have hab : a * b = b * a := commute_of_compA isInvA_tb0 isInvA_tb1 (by decide)
  have ha1 : a ≠ 1 := by
    simpa [a, tabPerm16_idA] using
      ne_of_table_ne isInvA_tb0 isInvA_idA (k := 2) (by norm_num) (by decide)
  have hb1 : b ≠ 1 := by
    simpa [b, tabPerm16_idA] using
      ne_of_table_ne isInvA_tb1 isInvA_idA (k := 2) (by norm_num) (by decide)
  have habne : a ≠ b :=
    ne_of_table_ne isInvA_tb0 isInvA_tb1 (k := 2) (by norm_num) (by decide)
  have hab1 : a * b ≠ 1 := by
    intro h
    apply habne
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    exact (eq_inv_of_mul_eq_one_left h).trans hb'
  have haab : a ≠ a * b := by
    intro h
    apply hb1
    have := congrArg (fun x => a⁻¹ * x) h
    simpa [← mul_assoc, ha] using this.symm
  have hbab : b ≠ a * b := by
    intro h
    apply ha1
    have := congrArg (fun x => x * b⁻¹) h
    simpa [mul_assoc, hb] using this.symm
  have hset : (Tbar16 : Set (Equiv.Perm (Fin 16))) = insert 1 (insert a (insert b {a * b})) := by
    ext g
    change g ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 16))) ↔
      g ∈ insert 1 (insert a (insert b {a * b}))
    simp [mem_closure_pair_iff ha hb hab]
  change Nat.card ↥(Tbar16 : Set (Equiv.Perm (Fin 16))) = 4
  have hfin : (Tbar16 : Set (Equiv.Perm (Fin 16))) =
      ↑({1, a, b, a * b} : Finset (Equiv.Perm (Fin 16))) := by
    rw [hset]
    simp
  rw [Nat.card_coe_set_eq, hfin, Set.ncard_coe_finset]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_singleton]
  all_goals simp [ha1, ha1.symm, hb1, hb1.symm, habne, habne.symm,
    hab1, hab1.symm, haab, haab.symm, hbab, hbab.symm]

noncomputable def a5RelsEquivAlternatingGroup :
    CFSG.CosetTable.PG 2 CFSG.Quasithin.L34Amalgam.a5Rels ≃*
      alternatingGroup (Fin 5) := by
  classical
  let a5a : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 3 4
  let a5b : Equiv.Perm (Fin 5) := Equiv.swap 1 0 * Equiv.swap 1 3
  have hsigna : Equiv.Perm.sign a5a = 1 := by
    change Equiv.Perm.sign (Equiv.swap 1 2 * Equiv.swap 3 4) = 1
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    norm_num
  have hisThree : Equiv.Perm.IsThreeCycle a5b := by
    change Equiv.Perm.IsThreeCycle (Equiv.swap 1 0 * Equiv.swap 1 3)
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := 1) (b := 0) (c := 3)
      (by decide) (by decide) (by decide)
  have hsignb : Equiv.Perm.sign a5b = 1 := hisThree.sign
  let A : alternatingGroup (Fin 5) :=
    ⟨a5a, by rw [Equiv.Perm.mem_alternatingGroup]; exact hsigna⟩
  let B : alternatingGroup (Fin 5) :=
    ⟨a5b, by rw [Equiv.Perm.mem_alternatingGroup]; exact hsignb⟩
  have hA2 : A * A = 1 := by
    apply Subtype.ext
    change a5a * a5a = 1
    decide
  have hB3 : B ^ 3 = 1 := by
    apply Subtype.ext
    change a5b ^ 3 = 1
    decide
  have hAB5 : (A * B) ^ 5 = 1 := by
    apply Subtype.ext
    change (a5a * a5b) ^ 5 = 1
    decide
  have hA_ne : A ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    change a5a = 1 at h'
    exact (by decide : a5a ≠ 1) h'
  have hB_ne : B ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    change a5b = 1 at h'
    exact (by decide : a5b ≠ 1) h'
  have hAB_ne : A * B ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    change a5a * a5b = 1 at h'
    exact (by decide : a5a * a5b ≠ 1) h'
  have hordA : orderOf A = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hA2 hA_ne
  have hordB : orderOf B = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hB3 hB_ne
  have hordAB : orderOf (A * B) = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime hAB5 hAB_ne
  have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hclosure : Subgroup.closure ({A, B} : Set (alternatingGroup (Fin 5))) = ⊤ := by
    let H := Subgroup.closure ({A, B} : Set (alternatingGroup (Fin 5)))
    have hmemA : A ∈ H := Subgroup.subset_closure (by simp)
    have hmemB : B ∈ H := Subgroup.subset_closure (by simp)
    have hmemAB : A * B ∈ H := H.mul_mem hmemA hmemB
    have h2 : 2 ∣ Nat.card H := by
      have := Subgroup.orderOf_dvd_natCard H hmemA
      rwa [hordA] at this
    have h3 : 3 ∣ Nat.card H := by
      have := Subgroup.orderOf_dvd_natCard H hmemB
      rwa [hordB] at this
    have h5 : 5 ∣ Nat.card H := by
      have := Subgroup.orderOf_dvd_natCard H hmemAB
      rwa [hordAB] at this
    have hdvd : Nat.card H ∣ 60 := by
      have := Subgroup.card_dvd_of_le (H := H) (K := ⊤) le_top
      rwa [Subgroup.card_top, hcardA5] at this
    have hne30 : Nat.card H ≠ 30 := by
      intro hcard30
      have hindex : H.index = 2 := by
        have hmul := Subgroup.card_mul_index H
        rw [hcard30, hcardA5] at hmul
        omega
      haveI : H.Normal := Subgroup.normal_of_index_eq_two hindex
      haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
      rcases Subgroup.Normal.eq_bot_or_eq_top H with hbot | htop
      · rw [hbot, Subgroup.card_bot] at hcard30
        omega
      · rw [htop, Subgroup.card_top, hcardA5] at hcard30
        omega
    have h6 : 6 ∣ Nat.card H := by
      have := Nat.lcm_dvd h2 h3
      norm_num at this ⊢
      exact this
    have h30 : 30 ∣ Nat.card H := by
      have := Nat.lcm_dvd h6 h5
      norm_num at this ⊢
      exact this
    have hcard60 : Nat.card H = 60 := by
      obtain ⟨k, hk⟩ := h30
      have hkpos : 0 < k := by
        by_contra h
        have hk0 : k = 0 := by omega
        rw [hk0, mul_zero] at hk
        exact Nat.card_pos.ne' hk
      have hle : 30 * k ≤ 60 := Nat.le_of_dvd (by norm_num) (hk ▸ hdvd)
      have hk2 : k ≤ 2 := by omega
      interval_cases k
      · exact absurd hk hne30
      · simpa using hk
    exact Subgroup.eq_top_of_card_eq H (by rw [hcard60, hcardA5])
  exact (CFSG.Quasithin.L34Amalgam.a5Equiv (C := ⊤) hA2 hB3 hAB5 hclosure (by
    rw [Subgroup.card_top, hcardA5])).trans Subgroup.topEquiv

noncomputable def x16EquivA5 (hF9 : F9Prop) {i : ℕ}
    (hi : i < 4) : ↥(X16 i) ≃* alternatingGroup (Fin 5) := by
  have hcard : Nat.card (X16 i) = 60 := by
    have h := hF9
    unfold F9Prop at h
    exact (h.1 i hi).1
  exact (CFSG.Quasithin.L34Amalgam.a5Equiv (C := X16 i) (a := tabPerm16 xA)
    (b := tabPerm16 xBs[i]!) tabPerm16_xA_mul_self (tabPerm16_xB_pow_three hi)
    (tabPerm16_xA_mul_xB_pow_five hi) rfl hcard).symm.trans a5RelsEquivAlternatingGroup

private theorem conj_mem_powers_of_card_twenty {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 20) {x : K} (hx : orderOf x = 5) :
    ∀ y : K, y * x * y⁻¹ ∈ ({x, x ^ 2, x ^ 3, x ^ 4} : Set K) := by
  classical
  let P := Subgroup.zpowers x
  have hPcard : Nat.card P = 5 := by
    rw [Nat.card_zpowers, hx]
  have hxP : x ∈ P := by
    change x ∈ Subgroup.zpowers x
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨1, by simp⟩
  have hPindex : P.index = 4 := by
    have hmul := Subgroup.card_mul_index P
    rw [hPcard, hK] at hmul
    omega
  have hcore : P.normalCore = ⊥ ∨ P.normalCore = P := by
    have hle : P.normalCore ≤ P := P.normalCore_le
    have hdvd : Nat.card P.normalCore ∣ 5 := by
      have := Subgroup.card_dvd_of_le hle
      rwa [hPcard] at this
    rcases Nat.prime_five.eq_one_or_self_of_dvd (Nat.card P.normalCore) hdvd with h1 | h5
    · left
      exact Subgroup.eq_bot_of_card_eq (H := P.normalCore) h1
    · right
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hPcard, h5])
  have hPnormal : P.Normal := by
    rcases hcore with hbot | htop
    · exfalso
      let φ := MulAction.toPermHom K (K ⧸ P)
      have hker : φ.ker = ⊥ := by
        rw [← Subgroup.normalCore_eq_ker, hbot]
      have hinj : Function.Injective φ := φ.ker_eq_bot_iff.mp hker
      have hcard_quot : Nat.card (K ⧸ P) = 4 := by
        rw [← Subgroup.index_eq_card, hPindex]
      have hdvd_range : Nat.card φ.range ∣ 24 := by
        have h := Subgroup.card_dvd_of_le (H := φ.range) (K := ⊤) le_top
        rw [Subgroup.card_top, Nat.card_perm, hcard_quot] at h
        norm_num at h
        exact h
      have hdvdK : Nat.card K ∣ 24 := by
        rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
        exact hdvd_range
      rw [hK] at hdvdK
      norm_num at hdvdK
    · rw [← htop]
      exact P.normalCore_normal
  intro y
  have hconj_mem : y * x * y⁻¹ ∈ P := hPnormal.conj_mem x hxP y
  have hconj_order : orderOf (y * x * y⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  change y * x * y⁻¹ ∈ Subgroup.zpowers x at hconj_mem
  rw [(isOfFinOrder_of_finite x).mem_zpowers_iff_mem_range_orderOf, hx] at hconj_mem
  simp only [Finset.mem_image, Finset.mem_range] at hconj_mem
  obtain ⟨k, hk, hkx⟩ := hconj_mem
  interval_cases k
  · exfalso
    rw [pow_zero] at hkx
    rw [← hkx] at hconj_order
    norm_num at hconj_order
  · left; simpa using hkx.symm
  · right; left; simpa using hkx.symm
  · right; right; left; simpa using hkx.symm
  · right; right; right; simpa using hkx.symm

theorem card_ne_twenty (hF11 : F11Prop) {i : ℕ} (hi : i < 4)
    {H : Subgroup (Equiv.Perm (Fin 16))} (hH : H ≤ X16 i) : Nat.card ↥H ≠ 20 := by
  intro hcard
  have h5dvd : 5 ∣ Nat.card ↥H := by rw [hcard]; norm_num
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  have hx' : orderOf ((⟨x, hH x.2⟩ : X16 i) : Equiv.Perm (Fin 16)) = 5 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx]
  have hF11' := hF11 i hi
  obtain ⟨V, hV⟩ := hF11'.2.2
  have hcount := hV.2.2.2.2.2.2.2.1 (⟨x, hH x.2⟩ : X16 i) hx'
  have hmap_mem : ∀ y : ↥H,
      (⟨y, hH y.2⟩ : X16 i) * ⟨x, hH x.2⟩ * (⟨y, hH y.2⟩ : X16 i)⁻¹ ∈
        ({⟨x, hH x.2⟩, (⟨x, hH x.2⟩ : X16 i) ^ 2, (⟨x, hH x.2⟩ : X16 i) ^ 3,
          (⟨x, hH x.2⟩ : X16 i) ^ 4} : Set (X16 i)) := by
    intro y
    have h := conj_mem_powers_of_card_twenty hcard hx y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    rcases h with h | h | h | h
    · left; apply Subtype.ext; simpa using congrArg Subtype.val h
    · right; left; apply Subtype.ext; simpa using congrArg Subtype.val h
    · right; right; left; apply Subtype.ext; simpa using congrArg Subtype.val h
    · right; right; right; apply Subtype.ext; simpa using congrArg Subtype.val h
  let S : Set (X16 i) :=
    {y : X16 i | (y * ⟨x, hH x.2⟩ * y⁻¹ : X16 i) ∈
      ({⟨x, hH x.2⟩, (⟨x, hH x.2⟩ : X16 i) ^ 2, (⟨x, hH x.2⟩ : X16 i) ^ 3,
        (⟨x, hH x.2⟩ : X16 i) ^ 4} : Set (X16 i))}
  have hS_card : Nat.card S = 10 := hcount
  have hinj : Function.Injective (fun y : ↥H =>
      (⟨⟨y, hH y.2⟩, hmap_mem y⟩ : S)) := by
    intro y z h
    have h1 : (⟨y, hH y.2⟩ : X16 i) = ⟨z, hH z.2⟩ :=
      congrArg (fun t : S => (t.1 : X16 i)) h
    have h2 : (y : Equiv.Perm (Fin 16)) = (z : Equiv.Perm (Fin 16)) :=
      congrArg (fun t : X16 i => (t : Equiv.Perm (Fin 16))) h1
    exact Subtype.ext h2
  have hle : Nat.card ↥H ≤ Nat.card S := Nat.card_le_card_of_injective _ hinj
  rw [hS_card] at hle
  omega

theorem exists_eq_X16 (hF9 : F9Prop) (hF11 : F11Prop) {X : Subgroup (Equiv.Perm (Fin 16))}
    (hX : Nat.card ↥X = 60) (hT : Tbar16 ≤ X) {g : Equiv.Perm (Fin 16)} (hgX : g ∈ X)
    (hg : ∀ a b, g (xor16 a b) = xor16 (g a) (g b)) (hg5 : orderOf g = 5) :
    ∃ i < 4, X = X16 i := by
  let H := Subgroup.closure ((Tbar16 : Set (Equiv.Perm (Fin 16))) ∪ {g})
  have hH_le_X : H ≤ X := by
    apply (Subgroup.closure_le (K := X)).mpr
    intro x hx
    rcases hx with hx | hx
    · exact hT hx
    · rw [Set.mem_singleton_iff] at hx
      rwa [hx]
  have hH_card_le : Nat.card ↥H ≤ 60 := by
    have hdvd := Subgroup.card_dvd_of_le hH_le_X
    rw [hX] at hdvd
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hF9' := hF9
  unfold F9Prop at hF9'
  have hdisj := hF9'.2 g hg hg5
  have hgX16 : ∃ i < 4, g ∈ X16 i := by
    rcases hdisj with h | h
    · exact h
    · exact absurd h (not_lt.mpr hH_card_le)
  obtain ⟨i, hi, hgX16⟩ := hgX16
  have hT_le_H : Tbar16 ≤ H := by
    apply (Subgroup.closure_le (K := H)).mpr
    intro x hx
    exact Subgroup.subset_closure (Or.inl (Subgroup.subset_closure hx))
  have hH_le_X16 : H ≤ X16 i := by
    apply (Subgroup.closure_le (K := X16 i)).mpr
    intro x hx
    rcases hx with hx | hx
    · exact (hF9'.1 i hi).2.1 hx
    · rw [Set.mem_singleton_iff] at hx
      rwa [hx]
  have h4 : 4 ∣ Nat.card ↥H := by
    have := Subgroup.card_dvd_of_le hT_le_H
    rwa [card_Tbar16] at this
  have hgH : g ∈ H := Subgroup.subset_closure (Or.inr (by simp))
  have h5 : 5 ∣ Nat.card ↥H := by
    have := Subgroup.orderOf_dvd_natCard H hgH
    rwa [hg5] at this
  have h20 : 20 ∣ Nat.card ↥H := by
    have := Nat.lcm_dvd h4 h5
    norm_num at this ⊢
    exact this
  have hdvd : Nat.card ↥H ∣ 60 := by
    have := Subgroup.card_dvd_of_le hH_le_X
    rwa [hX] at this
  have hne20 : Nat.card ↥H ≠ 20 := card_ne_twenty hF11 hi hH_le_X16
  have hcard60 : Nat.card ↥H = 60 := by
    obtain ⟨k, hk⟩ := h20
    have hkpos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0, mul_zero] at hk
      exact Nat.card_pos.ne' hk
    have hle : 20 * k ≤ 60 := Nat.le_of_dvd (by norm_num) (hk ▸ hdvd)
    have hk3 : k ≤ 3 := by omega
    interval_cases k
    · exact absurd (by simpa using hk) hne20
    · rw [hk] at hdvd
      norm_num at hdvd
    · simpa using hk
  have hH_eq_X16 : H = X16 i := by
    apply Subgroup.eq_of_le_of_card_ge hH_le_X16
    rw [hcard60, (hF9'.1 i hi).1]
  have hH_eq_X : H = X := by
    apply Subgroup.eq_of_le_of_card_ge hH_le_X
    rw [hcard60, hX]
  exact ⟨i, hi, by rw [← hH_eq_X, hH_eq_X16]⟩

end CFSG.Sporadic.SuzRecog.SuzL34Cert

end
