module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Hyp
public import CFSG.RankThree.PartTwo.Sec14.Ronan148VJ2Syl
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13BridgeA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

structure Gen8 (A : Subgroup (MulAut W)) (t z : MulAut W) (N : Subgroup (MulAut W))
    (k a : MulAut W) : Prop where
  hkN : k ∈ N
  hkz : k ∉ Subgroup.zpowers z
  hk3 : orderOf k = 3
  hkc : k * z = z * k
  hNeq : N = Subgroup.zpowers z ⊔ Subgroup.zpowers k
  haP : a ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆
  hak : a * k * a⁻¹ = k * z
  htk : t * k * t⁻¹ = k⁻¹

private theorem w16g_eight_inverted_element (h : Cfg133 A t 3) {z : MulAut W}
    {N : Subgroup (MulAut W)} (hD : Data8 A t z N)
    (hcomm : ⁅N, Subgroup.zpowers t⁆ ≠ ⊥) :
    ∃ k : MulAut W, k ∈ N ∧ k ∉ Subgroup.zpowers z ∧ orderOf k = 3 ∧
      k * z = z * k ∧ N = Subgroup.zpowers z ⊔ Subgroup.zpowers k ∧
      t * k * t⁻¹ = k⁻¹ := by
  classical
  have hn_exists : ∃ n ∈ N, t * n * t⁻¹ ≠ n := by
    by_contra hcon
    push Not at hcon
    apply hcomm
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have htn : Commute t n := by
      show t * n = n * t
      calc t * n = (t * n * t⁻¹) * t := by group
        _ = n * t := by rw [hcon n hn]
    exact (htn.zpow_left j).eq
  obtain ⟨n, hnN, htn_ne⟩ := hn_exists
  set n' : MulAut W := t * n * t⁻¹ with hn'def
  have hn'N : n' ∈ N := by
    rw [hn'def]
    exact hD.hNt n hnN
  have hn'_ne : n' ≠ n := by
    rw [hn'def]
    exact htn_ne
  let k : MulAut W := n * n'⁻¹
  have hkN : k ∈ N := by
    change n * n'⁻¹ ∈ N
    exact N.mul_mem hnN (N.inv_mem hn'N)
  have hNcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
    intro x hx y hy
    have hp := (w16g_isElemAbelianOfRank_comm_pow hD.hN).1 ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg Subtype.val hp
  have hk_ne_one : k ≠ 1 := by
    intro hk1
    change n * n'⁻¹ = 1 at hk1
    exact hn'_ne (mul_inv_eq_one.mp hk1).symm
  have hk3pow : k ^ 3 = 1 := by
    have hp := (w16g_isElemAbelianOfRank_comm_pow hD.hN).2 ⟨k, hkN⟩
    simpa using hp
  have hk3 : orderOf k = 3 := orderOf_eq_prime hk3pow hk_ne_one
  have htt : t * t = 1 := by
    have h2 := h.ht2
    rw [pow_two] at h2
    exact h2
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htn'_conj : t * n' * t⁻¹ = n := by
    rw [hn'def]
    calc t * (t * n * t⁻¹) * t⁻¹ = (t * t) * n * (t⁻¹ * t⁻¹) := by group
      _ = n := by rw [htt, ht_inv, htt]; group
  have htk : t * k * t⁻¹ = k⁻¹ := by
    change t * (n * n'⁻¹) * t⁻¹ = (n * n'⁻¹)⁻¹
    calc t * (n * n'⁻¹) * t⁻¹
        = (t * n * t⁻¹) * (t * n' * t⁻¹)⁻¹ := by group
      _ = n' * n⁻¹ := by rw [← hn'def, htn'_conj]
      _ = (n * n'⁻¹)⁻¹ := by group
  have hk_not_z : k ∉ Subgroup.zpowers z := by
    intro hkz
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hkz
    have hk_fixed : t * k * t⁻¹ = k := by
      rw [← hj]
      calc t * z ^ j * t⁻¹ = (t * z * t⁻¹) ^ j := by
             exact (conj_zpow (a := t) (b := z) (i := j)).symm
        _ = z ^ j := by rw [hD.htz]
    have hk_eq_inv : k = k⁻¹ := hk_fixed.symm.trans htk
    have hk2 : k ^ 2 = 1 := by
      have h := congrArg (fun x => k * x) hk_eq_inv
      simpa [pow_two, mul_inv_cancel] using h
    have h2dvd : orderOf k ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hk2
    rw [hk3] at h2dvd
    norm_num at h2dvd
  have hkc : k * z = z * k := hNcomm k hkN z hD.hzN
  have hNeq : N = Subgroup.zpowers z ⊔ Subgroup.zpowers k := by
    have hsup_le : Subgroup.zpowers z ⊔ Subgroup.zpowers k ≤ N :=
      sup_le (Subgroup.zpowers_le.mpr hD.hzN) (Subgroup.zpowers_le.mpr hkN)
    have hcard_sup : Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers k) = 3 ^ 2 :=
      w16g_card_sup_zpowers Nat.prime_three hD.hz3 hk3 hkc.symm hk_not_z
    have hcardN : Nat.card ↥N = 3 ^ 2 := by
      rw [w16g_card_of_isElemAbelianOfRank hD.hN]
    have hsup_eq : Subgroup.zpowers z ⊔ Subgroup.zpowers k = N := by
      apply Subgroup.eq_of_le_of_card_ge hsup_le
      rw [hcard_sup, hcardN]
    exact hsup_eq.symm
  exact ⟨k, hkN, hk_not_z, hk3, hkc, hNeq, htk⟩

private theorem w16g_eight_transvection {z : MulAut W} {N : Subgroup (MulAut W)}
    {k : MulAut W} (hD : Data8 A t z N) (hkN : k ∈ N)
    (hkz : k ∉ Subgroup.zpowers z) (hk3 : orderOf k = 3) (hkc : k * z = z * k)
    (hNeq : N = Subgroup.zpowers z ⊔ Subgroup.zpowers k) :
    ∃ a ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆, a * k * a⁻¹ = k * z := by
  classical
  set P : Subgroup (MulAut W) := ⁅pCoreOf 3 A, Subgroup.zpowers t⁆ with hPdef
  have hNP' : N ≤ P := by
    rw [hPdef]
    exact hD.hNP
  have hkP : k ∈ P := hNP' hkN
  have hPcard : Nat.card ↥P = 27 := by
    rw [hPdef, hD.hP.2.1]
    norm_num
  have hNcard : Nat.card ↥N = 9 := by
    rw [w16g_card_of_isElemAbelianOfRank hD.hN]
    norm_num
  obtain ⟨a₀, ha₀P, ha₀N⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148V.j2Syl_exists_mem_not_mem hPcard hNcard
  have ha0_not_comm : a₀ * k ≠ k * a₀ := by
    intro hcomm_ak
    have hz_mem_cent : z ∈ Subgroup.centralizer ({a₀} : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hD.hzc a₀ ha₀P
    have hk_mem_cent : k ∈ Subgroup.centralizer ({a₀} : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hcomm_ak
    have hNcent : N ≤ Subgroup.centralizer ({a₀} : Set (MulAut W)) := by
      rw [hNeq]
      exact sup_le (Subgroup.zpowers_le.mpr hz_mem_cent) (Subgroup.zpowers_le.mpr hk_mem_cent)
    have hcent : ∀ x ∈ N, a₀ * x = x * a₀ := by
      intro x hx
      exact Subgroup.mem_centralizer_iff.mp (hNcent hx) a₀ (Set.mem_singleton a₀)
    have hH : N ⊔ Subgroup.zpowers a₀ = P :=
      CFSG.RankThree.PartTwo.Sec14.Ronan148V.j2Syl_eq_of_nine_lt hPcard hNcard
        le_sup_left (sup_le hNP' (Subgroup.zpowers_le.mpr ha₀P))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers a₀)) ha₀N
    have hNelem : CFSG.Open.IsElemAbelian 3 N :=
      w16g_isElemAbelian_of_isElemAbelianOfRank hD.hN
    have ha0pow : a₀ ^ 3 = 1 := by
      have hmem : a₀ ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆ := hPdef ▸ ha₀P
      have hp := hD.hP.2.2 ⟨a₀, hmem⟩
      simpa using hp
    have hAelem : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers a₀) :=
      CFSG.Open.isElemAbelian_zpowers ha0pow
    have hcomm_NA : ∀ x ∈ N, ∀ y ∈ Subgroup.zpowers a₀, x * y = y * x := by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (((commute_iff_eq x a₀).mpr (hcent x hx).symm).zpow_right i).eq
    have hH_elem : CFSG.Open.IsElemAbelian 3 (N ⊔ Subgroup.zpowers a₀) :=
      hNelem.sup_of_commute hAelem hcomm_NA
    have hP_elem : CFSG.Open.IsElemAbelian 3 P := by
      rw [← hH]
      exact hH_elem
    have hPinst : CFSG.IsExtraspecial 3 ↥P := by
      rw [hPdef]
      exact hD.hP.1
    haveI : IsMulCommutative ↥P := hP_elem.1
    have hcenter_card : Nat.card (Subgroup.center ↥P) = 3 :=
      hPinst.center_order_p
    have hcenter_top : Subgroup.center ↥P = ⊤ := Subgroup.center_eq_top
    rw [hcenter_top, Subgroup.card_top, hPcard] at hcenter_card
    norm_num at hcenter_card
  let c : MulAut W := a₀ * k * a₀⁻¹ * k⁻¹
  have hcP : c ∈ P := by
    change a₀ * k * a₀⁻¹ * k⁻¹ ∈ P
    exact P.mul_mem (P.mul_mem (P.mul_mem ha₀P hkP) (P.inv_mem ha₀P)) (P.inv_mem hkP)
  have hc_ne_one : c ≠ 1 := by
    intro hc1
    apply ha0_not_comm
    change a₀ * k * a₀⁻¹ * k⁻¹ = 1 at hc1
    have h1 : a₀ * k * a₀⁻¹ = k := mul_inv_eq_one.mp hc1
    calc a₀ * k = (a₀ * k * a₀⁻¹) * a₀ := by group
      _ = k * a₀ := by rw [h1]
  have hPinst : CFSG.IsExtraspecial 3 ↥P := by
    rw [hPdef]
    exact hD.hP.1
  haveI : IsElementaryAbelian 3 (↥P ⧸ Subgroup.center ↥P) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian 3 ↥P
  haveI : IsMulCommutative (↥P ⧸ Subgroup.center ↥P) :=
    IsMulCommutative.of_comm fun a b => IsMulCommutative.is_comm.comm a b
  have hcomm_le_center : _root_.commutator ↥P ≤ Subgroup.center ↥P :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative (↥P ⧸ Subgroup.center ↥P))
  have hc_center : (⟨c, hcP⟩ : ↥P) ∈ Subgroup.center ↥P := by
    apply hcomm_le_center
    change (⟨c, hcP⟩ : ↥P) ∈ _root_.commutator ↥P
    have hc_eq : (⟨c, hcP⟩ : ↥P) =
        ⁅(⟨a₀, ha₀P⟩ : ↥P), (⟨k, hkP⟩ : ↥P)⁆ := by
      apply Subtype.ext
      simp [c, commutatorElement_def]
    rw [hc_eq]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hc_z : c ∈ Subgroup.zpowers z := by
    apply hD.hZP c hcP
    intro y hy
    have h1 := Subgroup.mem_center_iff.mp hc_center ⟨y, hy⟩
    simpa using congrArg Subtype.val h1
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hc_z
  have hz3z : z ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    have hp := pow_orderOf_eq_one z
    rwa [hD.hz3] at hp
  have hc_emod : c = z ^ (e % 3) := by
    rw [← he, zpow_eq_zpow_emod e hz3z]
  have he_pos : 0 ≤ e % 3 := Int.emod_nonneg e (by norm_num)
  have he_lt : e % 3 < 3 := Int.emod_lt_of_pos e (by norm_num)
  have hcases : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exfalso
    apply hc_ne_one
    rw [hc_emod, h0, zpow_zero]
  · refine ⟨a₀, ha₀P, ?_⟩
    have hc_eq_z : c = z := by rw [hc_emod, h1, zpow_one]
    change a₀ * k * a₀⁻¹ * k⁻¹ = z at hc_eq_z
    calc a₀ * k * a₀⁻¹ = (a₀ * k * a₀⁻¹ * k⁻¹) * k := by group
      _ = z * k := by rw [hc_eq_z]
      _ = k * z := hkc.symm
  · refine ⟨a₀⁻¹, P.inv_mem ha₀P, ?_⟩
    have hc_eq_z2 : c = z ^ 2 := by
      rw [hc_emod, h2]
      exact zpow_ofNat z 2
    change a₀ * k * a₀⁻¹ * k⁻¹ = z ^ 2 at hc_eq_z2
    have h1 : a₀ * k * a₀⁻¹ = k * z ^ 2 := by
      calc a₀ * k * a₀⁻¹ = (a₀ * k * a₀⁻¹ * k⁻¹) * k := by group
        _ = z ^ 2 * k := by rw [hc_eq_z2]
        _ = k * z ^ 2 := (((commute_iff_eq z k).mpr hkc.symm).pow_left 2).eq
    have hz3pow : z ^ 3 = 1 := by
      rw [← hD.hz3]
      exact pow_orderOf_eq_one z
    have hz_conj : a₀⁻¹ * z * a₀ = z := by
      calc a₀⁻¹ * z * a₀ = a₀⁻¹ * (z * a₀) := by group
        _ = a₀⁻¹ * (a₀ * z) := by rw [← hD.hzc a₀ ha₀P]
        _ = z := by group
    have hz2_conj : a₀⁻¹ * z ^ 2 * a₀ = z ^ 2 := by
      calc a₀⁻¹ * z ^ 2 * a₀ = (a₀⁻¹ * z * a₀) ^ 2 := by
             exact (conj_pow (a := a₀⁻¹) (b := z) (i := 2)).symm
        _ = z ^ 2 := by rw [hz_conj]
    have hconj : k = (a₀⁻¹ * k * a₀) * z ^ 2 := by
      calc k = a₀⁻¹ * (a₀ * k * a₀⁻¹) * a₀ := by group
        _ = a₀⁻¹ * (k * z ^ 2) * a₀ := by rw [h1]
        _ = (a₀⁻¹ * k * a₀) * (a₀⁻¹ * z ^ 2 * a₀) := by group
        _ = (a₀⁻¹ * k * a₀) * z ^ 2 := by rw [hz2_conj]
    change a₀⁻¹ * k * a₀ = k * z
    calc a₀⁻¹ * k * a₀ = (a₀⁻¹ * k * a₀) * z ^ 3 := by rw [hz3pow, mul_one]
      _ = ((a₀⁻¹ * k * a₀) * z ^ 2) * z := by group
      _ = k * z := by rw [← hconj]

theorem s13_eight_generators (h : Cfg133 A t 3) {z : MulAut W} {N : Subgroup (MulAut W)}
    (hD : Data8 A t z N) (hcomm : ⁅N, Subgroup.zpowers t⁆ ≠ ⊥) :
    ∃ k a : MulAut W, Gen8 A t z N k a := by
  obtain ⟨k, hkN, hkz, hk3, hkc, hNeq, htk⟩ := w16g_eight_inverted_element h hD hcomm
  obtain ⟨a, haP, hak⟩ := w16g_eight_transvection hD hkN hkz hk3 hkc hNeq
  exact ⟨k, a, ⟨hkN, hkz, hk3, hkc, hNeq, haP, hak, htk⟩⟩

end CFSG.LocalAnalysis.WeakClosure81
