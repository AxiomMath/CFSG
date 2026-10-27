module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPBar
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitSetup
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitBridge
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelRootSmall
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFiveX
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitSmall
import CFSG.LocalAnalysis.WeakClosure81.EightTailPShapeSz
import CFSG.LocalAnalysis.WeakClosure81.EightTailPShapeBender
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDetOrders
public import CFSG.RankThree.PartOne.S12K.OrdRigid

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def NotSpPSU (Y : Type) [Group Y] : Prop :=
  ¬ ∃ m n : ℕ, 3 < m ∧ (IsSpGp Y m n ∨ IsPSUGp Y m n)

private theorem w85g_card_of_isPSUGp {Y : Type} [Group Y] {m n : ℕ} (h : IsPSUGp Y m n) :
    3 ≤ m ∧ 1 ≤ n ∧ (m, 2 ^ n) ≠ (3, 2) ∧ Nat.card Y = ordTwistedA (m - 1) (2 ^ n) := by
  have h1 := CFSG.Blueprint.LieModel.admissible h
  obtain ⟨-, hf, hm3, hne⟩ := h1
  obtain ⟨⟨-, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) h
  refine ⟨hm3, hf, hne, ?_⟩
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hf hK
      (by omega : 2 ≤ m),
    ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ m), mul_comm (m - 1) m]

private theorem w85g_sixteen_dvd_ordTwistedA {u q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    (hu : 3 ≤ u) : 16 ∣ ordTwistedA u q := by
  rw [CFSG.Open.ordTwistedA]
  set g := Nat.gcd (u + 1) (q + 1) with hg
  set P := ∏ i ∈ Finset.Icc 2 (u + 1), (((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) with hP
  have hq1 : 1 ≤ q := by omega
  have hgP : g ∣ P := by
    refine dvd_trans (Nat.gcd_dvd_right (u + 1) (q + 1)) ?_
    have hmem : u + 1 ∈ Finset.Icc 2 (u + 1) := by
      rw [Finset.mem_Icc]; omega
    have hfac : (q + 1) ∣ (((q : ℤ) ^ (u + 1) - (-1 : ℤ) ^ (u + 1)).toNat) := by
      have hz : ((q : ℤ) + 1) ∣ (q : ℤ) ^ (u + 1) - (-1 : ℤ) ^ (u + 1) := by
        have := sub_dvd_pow_sub_pow (q : ℤ) (-1 : ℤ) (u + 1)
        simpa using this
      have hnn : 0 ≤ (q : ℤ) ^ (u + 1) - (-1 : ℤ) ^ (u + 1) := by
        have h1 : (1 : ℤ) ≤ (q : ℤ) ^ (u + 1) := one_le_pow₀ (by exact_mod_cast hq1)
        rcases neg_one_pow_eq_or ℤ (u + 1) with h | h <;> rw [h] <;> linarith
      have hz' : ((q + 1 : ℕ) : ℤ) ∣
          ((((q : ℤ) ^ (u + 1) - (-1 : ℤ) ^ (u + 1)).toNat : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hnn]
        exact hz
      exact (Int.natCast_dvd_natCast).mp hz'
    exact dvd_trans hfac (Finset.dvd_prod_of_mem _ hmem)
  obtain ⟨P', hP'⟩ := hgP
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hdiv : q ^ (u * (u + 1) / 2) * P / g = q ^ (u * (u + 1) / 2) * P' := by
    rw [hP']
    have h1 : q ^ (u * (u + 1) / 2) * (g * P') =
        g * (q ^ (u * (u + 1) / 2) * P') := by ring
    rw [h1]
    exact Nat.mul_div_right _ hgpos
  rw [hdiv]
  refine dvd_mul_of_dvd_left ?_ P'
  have h4 : 4 ≤ u * (u + 1) / 2 := by
    calc 4 = 8 / 2 := by norm_num
      _ ≤ u * (u + 1) / 2 := Nat.div_le_div_right (by nlinarith [hu])
  have h16 : 16 ∣ q ^ (u * (u + 1) / 2) := by
    have h1 : 2 ^ 4 ∣ q ^ 4 := pow_dvd_pow_of_dvd (even_iff_two_dvd.mp hqe) 4
    have h2 : q ^ 4 ∣ q ^ (u * (u + 1) / 2) := pow_dvd_pow q h4
    show 2 ^ 4 ∣ q ^ (u * (u + 1) / 2)
    exact dvd_trans h1 h2
  exact h16

private theorem w85g_sixteen_dvd_card_of_isSpGp {Y : Type} [Group Y] {m n : ℕ} (hm : 3 < m)
    (h : IsSpGp Y m n) : 16 ∣ Nat.card Y := by
  have h0 := h
  obtain ⟨k, hk, F, hFld, hFin, hFcard, ⟨e⟩⟩ := h
  have hk2 : 2 ≤ k := by omega
  have hn1 : 1 ≤ n := one_le_of_isSpGp h0
  have hcard := Nat.card_congr e.toEquiv
  rw [hcard, @CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp F hFld hFin k]
  refine dvd_mul_of_dvd_left ?_ _
  rw [hFcard, ← pow_mul]
  show 2 ^ 4 ∣ 2 ^ (n * k ^ 2)
  exact pow_dvd_pow 2 (by nlinarith)

private theorem w85g_sixteen_dvd_card_of_isPSUGp {Y : Type} [Group Y] {m n : ℕ} (hm : 3 < m)
    (h : IsPSUGp Y m n) : 16 ∣ Nat.card Y := by
  obtain ⟨-, hn1, -, hYc⟩ := w85g_card_of_isPSUGp h
  rw [hYc]
  have hq2 : 2 ≤ 2 ^ n := by
    have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow_iff.mpr (by omega)
    omega
  have hqe : Even (2 ^ n) :=
    even_iff_two_dvd.mpr (by simpa only [pow_one] using pow_dvd_pow 2 hn1)
  exact w85g_sixteen_dvd_ordTwistedA hq2 hqe (by omega)

private theorem w85g_four_not_dvd_card_quot_center_of_symGp {Y : Type} [Group Y] [Finite Y]
    {n : ℕ} (hn : n ≤ 3) (h : IsSymGp (Y ⧸ fusionOddCore Y) n) :
    ¬ 4 ∣ Nat.card (Y ⧸ Subgroup.center Y) := by
  intro h4
  have hc := Subgroup.card_mul_index (Subgroup.center Y)
  rw [Subgroup.index_eq_card (H := Subgroup.center Y)] at hc
  have h4Y : 4 ∣ Nat.card Y := by
    rw [← hc]
    exact dvd_mul_of_dvd_right h4 _
  have hc2 := Subgroup.card_mul_index (fusionOddCore Y)
  rw [Subgroup.index_eq_card (H := fusionOddCore Y)] at hc2
  obtain ⟨e⟩ := h
  have hq : Nat.card (Y ⧸ fusionOddCore Y) = n.factorial := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  have h6 : Nat.card (Y ⧸ fusionOddCore Y) ∣ 6 := by
    rw [hq]; interval_cases n <;> norm_num
  have hoddO : Odd (Nat.card (fusionOddCore Y)) :=
    CFSG.CGT.Timmesfeld75.odd_card_fusionOddCore Y
  have hcop : Nat.Coprime 4 (Nat.card (fusionOddCore Y)) := by
    rw [show (4:ℕ) = 2 ^ 2 by norm_num, Nat.coprime_pow_left_iff (by norm_num)]
    exact Nat.coprime_two_left.mpr hoddO
  rw [← hc2] at h4Y
  exact (by rw [hcop.dvd_mul_left]; norm_num : ¬ 4 ∣ Nat.card (fusionOddCore Y) * 6)
    (dvd_trans h4Y (Nat.mul_dvd_mul_left _ h6))

private theorem w85g_exists_sylow_weaklyClosed_of_card_two {X : Type} [Group X] [Finite X]
    {S : Subgroup X} (hS : Nat.card S = 2) (h4 : ¬ 4 ∣ Nat.card X) :
    ∃ P : Sylow 2 X, S ≤ (P : Subgroup X) ∧ IsWeaklyClosedIn S (P : Subgroup X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 1) (by rw [hS]; norm_num)
  obtain ⟨Q, hSQ⟩ := hSp.exists_le_sylow
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hk_ge1 : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hle := Subgroup.card_le_of_le hSQ
    rw [hS, hk, hk0, pow_zero] at hle
    omega
  have hk_le1 : k ≤ 1 := by
    by_contra h
    have hk2 : 2 ≤ k := by omega
    exact h4 (by
      refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card (Q : Subgroup X))
      rw [hk]
      exact ⟨2 ^ (k - 2), by
        rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega⟩)
  have hk1 : k = 1 := by omega
  have hQcard : Nat.card (Q : Subgroup X) = 2 := by rw [hk, hk1]; norm_num
  have hQS : S = (Q : Subgroup X) := Subgroup.eq_of_le_of_card_ge hSQ (by rw [hQcard, hS])
  refine ⟨Q, hSQ, ?_⟩
  rw [← hQS]
  intro g hg
  exact Subgroup.eq_of_le_of_card_ge hg (by
    rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective])

private theorem w85g_card_of_isSpGp {Y : Type} [Group Y] {k n : ℕ} (h : IsSpGp Y (2 * k) n) :
    Nat.card Y = (2 ^ n) ^ (k ^ 2) *
      ∏ i ∈ Finset.Icc 1 k, ((2 ^ n) ^ (2 * i) - 1) := by
  obtain ⟨k', hk', F, hFld, hFin, hFcard, ⟨e⟩⟩ := h
  have hk'k : k' = k := by omega
  rw [hk'k] at e
  rw [Nat.card_congr e.toEquiv,
    @CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp F hFld hFin k, hFcard]

private theorem w85g_card_of_isSpGp_two {Y : Type} [Group Y] {n : ℕ} (h : IsSpGp Y 2 n) :
    Nat.card Y = 2 ^ n * (2 ^ (2 * n) - 1) := by
  have h1 : IsSpGp Y (2 * 1) n := by simpa using h
  rw [w85g_card_of_isSpGp h1]
  rw [show Finset.Icc 1 1 = {1} by decide, Finset.prod_singleton]
  norm_num only [one_pow, Nat.reduceMul, pow_one]
  rw [show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul, mul_comm]]

private theorem w85g_ordA_one (n : ℕ) (hn : 1 ≤ n) :
    ordA 1 (2 ^ n) = 2 ^ n * (2 ^ (2 * n) - 1) := by
  rw [ordA]
  rw [show Finset.Icc 2 (1+1) = {2} by decide, Finset.prod_singleton]
  rw [show Nat.gcd (1+1) (2 ^ n - 1) = 1 by
    rw [show 1+1 = 2 by norm_num]
    exact Nat.coprime_two_left.mpr
      (Nat.Even.sub_odd Nat.one_le_two_pow (Even.pow_of_ne_zero even_two (by omega)) odd_one)]
  rw [Nat.div_one]
  rw [show (1:ℕ) * (1+1) / 2 = 1 by norm_num, pow_one]
  rw [show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul, mul_comm]]

private theorem w85g_ordBC_two_pow (k n : ℕ) (hn : 1 ≤ n) :
    ordBC k (2 ^ n) = 2 ^ (n * k ^ 2) * ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n) - 1) := by
  rw [ordBC]
  rw [show Nat.gcd 2 (2 ^ n - 1) = 1 from
    Nat.coprime_two_left.mpr
      (Nat.Even.sub_odd Nat.one_le_two_pow (Even.pow_of_ne_zero even_two (by omega)) odd_one)]
  rw [Nat.div_one]
  congr 1
  · rw [← pow_mul]; ring
  · apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, show n * (2 * i) = 2 * i * n by ring]

private theorem w85g_l2_order_ne_sp {n k n' : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) (hn' : 1 ≤ n') :
    2 ^ n * (2 ^ (2 * n) - 1) ≠
      2 ^ (n' * k ^ 2) * ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n') - 1) := by
  intro h
  exact CFSG.SeitzReduction.SymplecticPilot.ordA_ne_ordBC (r := 1) le_rfl hn hk hn'
    ((w85g_ordA_one n hn).trans (h.trans (w85g_ordBC_two_pow k n' hn').symm))

private theorem w85g_l2_order_ne_psu {n m' n' : ℕ} (hn : 1 ≤ n) (hm' : 4 ≤ m')
    (hn' : 1 ≤ n') :
    2 ^ n * (2 ^ (2 * n) - 1) ≠ ordTwistedA (m' - 1) (2 ^ n') := by
  intro h
  exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 1) le_rfl hn (by omega : 2 ≤ m' - 1) hn'
    ((w85g_ordA_one n hn).trans h)

theorem notSpPSU_of_isSpGp_two {Y : Type} [Group Y] {n : ℕ} (h : IsSpGp Y 2 n) : NotSpPSU Y := by
  have hn1 : 1 ≤ n := one_le_of_isSpGp h
  have hY : Nat.card Y = 2 ^ n * (2 ^ (2 * n) - 1) := w85g_card_of_isSpGp_two h
  rintro ⟨m, n', hm, hSp' | hPSU'⟩
  · have hSp'0 := hSp'
    obtain ⟨k, hk, F', hFld', hFin', hFcard', ⟨e'⟩⟩ := hSp'
    have hk2 : 2 ≤ k := by omega
    have hn'1 : 1 ≤ n' := one_le_of_isSpGp hSp'0
    have hSp'k : IsSpGp Y (2 * k) n' := by rw [hk] at hSp'0; exact hSp'0
    have hY' : Nat.card Y = 2 ^ (n' * k ^ 2) *
        ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n') - 1) := by
      rw [w85g_card_of_isSpGp (n := n') hSp'k]
      have hpow : (2 ^ n') ^ (k ^ 2) = 2 ^ (n' * k ^ 2) := by rw [← pow_mul]
      have hprod : (∏ i ∈ Finset.Icc 1 k, ((2 ^ n') ^ (2 * i) - 1)) =
          ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n') - 1) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [← pow_mul, show n' * (2 * i) = 2 * i * n' by ring]
      rw [hpow, hprod]
    exact w85g_l2_order_ne_sp hn1 hk2 hn'1 (hY.symm.trans hY')
  · obtain ⟨-, hn'1, -, hYc⟩ := w85g_card_of_isPSUGp hPSU'
    exact w85g_l2_order_ne_psu hn1 (by omega) hn'1 (hY.symm.trans hYc)

private theorem w85g_u3_order_ne_sp {n k n' : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) (hn' : 1 ≤ n') :
    ordTwistedA 2 (2 ^ n) ≠
      2 ^ (n' * k ^ 2) * ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n') - 1) := by
  intro h
  exact CFSG.SeitzReduction.SymplecticPilot.ordTwistedA_ne_ordBC (u := 2) le_rfl
    (by omega : 1 ≤ n) hk hn' (h.trans (w85g_ordBC_two_pow k n' hn').symm)

private theorem w85g_u3_order_ne_psu {n m' n' : ℕ} (hn : 2 ≤ n) (hm' : 4 ≤ m')
    (hn' : 1 ≤ n') : ordTwistedA 2 (2 ^ n) ≠ ordTwistedA (m' - 1) (2 ^ n') := by
  exact (CFSG.RankThree.PartOne.S12K.ordTwistedA_ne_ordTwistedA_two
    (n := m' - 1) (f := n') (g := n) (by omega : 3 ≤ m' - 1) hn' hn).symm

theorem notSpPSU_of_isPSUGp_three {Y : Type} [Group Y] {n : ℕ} (h : IsPSUGp Y 3 n) :
    NotSpPSU Y := by
  obtain ⟨-, hn1, hne, hY⟩ := w85g_card_of_isPSUGp h
  have hn2 : 2 ≤ n := by
    by_contra hn
    have hn1' : n = 1 := by omega
    exact hne (by rw [hn1']; norm_num)
  rintro ⟨m, n', hm, hSp' | hPSU'⟩
  · have hSp'0 := hSp'
    obtain ⟨k, hk, F', hFld', hFin', hFcard', ⟨e'⟩⟩ := hSp'
    have hk2 : 2 ≤ k := by omega
    have hn'1 : 1 ≤ n' := one_le_of_isSpGp hSp'0
    have hSp'k : IsSpGp Y (2 * k) n' := by rw [hk] at hSp'0; exact hSp'0
    have hY' : Nat.card Y = 2 ^ (n' * k ^ 2) *
        ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n') - 1) := by
      rw [w85g_card_of_isSpGp (n := n') hSp'k]
      have hpow : (2 ^ n') ^ (k ^ 2) = 2 ^ (n' * k ^ 2) := by rw [← pow_mul]
      have hprod : (∏ i ∈ Finset.Icc 1 k, ((2 ^ n') ^ (2 * i) - 1)) =
          ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n') - 1) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [← pow_mul, show n' * (2 * i) = 2 * i * n' by ring]
      rw [hpow, hprod]
    exact w85g_u3_order_ne_sp hn2 hk2 hn'1 (hY.symm.trans hY')
  · obtain ⟨-, hn'1, -, hYc⟩ := w85g_card_of_isPSUGp hPSU'
    exact w85g_u3_order_ne_psu hn2 (by omega) hn'1 (hY.symm.trans hYc)

theorem notSpPSU_of_isSzGp {Y : Type} [Group Y] {n : ℕ}
    (h : IsSzGp Y n) : NotSpPSU Y :=
  not_isSpGp_or_isPSUGp_of_isSzGp h

private theorem w85g_card_of_isPSL {Y : Type} [Group Y] {m n : ℕ} (hm : 3 ≤ m)
    (h : CFSG.Blueprint.LieModel Y .PSL m 2 n) :
    1 ≤ n ∧ Nat.card Y = ordA (m - 1) (2 ^ n) := by
  have h1 := CFSG.Blueprint.LieModel.admissible h
  obtain ⟨-, hf, -, -, -⟩ := h1
  obtain ⟨⟨-, -, -, -, -⟩, K, hFld, hFin, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) h
  refine ⟨hf, ?_⟩
  rw [Nat.card_congr e.toEquiv,
    @CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL K hFld hFin m (by omega), hK,
    ordA, Nat.sub_add_cancel (by omega : 1 ≤ m), mul_comm (m - 1) m]

private theorem w85g_linear_order_ne_sp {m n k n' : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hn' : 1 ≤ n') : ordA (m - 1) (2 ^ n) ≠
      2 ^ (n' * k ^ 2) * ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n') - 1) := by
  intro h
  exact CFSG.SeitzReduction.SymplecticPilot.ordA_ne_ordBC (r := m - 1) (by omega : 1 ≤ m - 1)
    hn hk hn' (h.trans (w85g_ordBC_two_pow k n' hn').symm)

private theorem w85g_linear_order_ne_psu {m n m' n' : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (hm' : 4 ≤ m') (hn' : 1 ≤ n') : ordA (m - 1) (2 ^ n) ≠ ordTwistedA (m' - 1) (2 ^ n') := by
  exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := m - 1) (by omega : 1 ≤ m - 1) hn
    (by omega : 2 ≤ m' - 1) hn'

theorem notSpPSU_of_linear {Y : Type} [Group Y] {m n : ℕ} (hm : 3 ≤ m)
    (h : CFSG.Blueprint.LieModel Y .PSL m 2 n) : NotSpPSU Y := by
  obtain ⟨hn1, hY⟩ := w85g_card_of_isPSL hm h
  rintro ⟨m', n', hm', hSp' | hPSU'⟩
  · have hSp'0 := hSp'
    obtain ⟨k, hk, F', hFld', hFin', hFcard', ⟨e'⟩⟩ := hSp'
    have hk2 : 2 ≤ k := by omega
    have hn'1 : 1 ≤ n' := one_le_of_isSpGp hSp'0
    have hSp'k : IsSpGp Y (2 * k) n' := by rw [hk] at hSp'0; exact hSp'0
    have hY' : Nat.card Y = 2 ^ (n' * k ^ 2) *
        ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n') - 1) := by
      rw [w85g_card_of_isSpGp (n := n') hSp'k]
      have hpow : (2 ^ n') ^ (k ^ 2) = 2 ^ (n' * k ^ 2) := by rw [← pow_mul]
      have hprod : (∏ i ∈ Finset.Icc 1 k, ((2 ^ n') ^ (2 * i) - 1)) =
          ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n') - 1) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [← pow_mul, show n' * (2 * i) = 2 * i * n' by ring]
      rw [hpow, hprod]
    exact w85g_linear_order_ne_sp hm hn1 hk2 hn'1 (hY.symm.trans hY')
  · obtain ⟨-, hn'1, -, hYc⟩ := w85g_card_of_isPSUGp hPSU'
    exact w85g_linear_order_ne_psu hm hn1 (by omega) hn'1 (hY.symm.trans hYc)

theorem notSpPSU_of_alt6 {Y : Type} [Group Y] (h : Nonempty (Y ≃* alternatingGroup (Fin 6))) :
    NotSpPSU Y := by
  obtain ⟨e⟩ := h
  have h360 : Nat.card Y = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  rintro ⟨m, n, hm, hSp | hPSU⟩
  · have h16 := w85g_sixteen_dvd_card_of_isSpGp hm hSp
    rw [h360] at h16
    norm_num at h16
  · have h16 := w85g_sixteen_dvd_card_of_isPSUGp hm hPSU
    rw [h360] at h16
    norm_num at h16

theorem notSpPSU_of_symGp_le_three {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : n ≤ 3)
    (hodd : Odd (Nat.card (Subgroup.center Y))) (h : IsSymGp (Y ⧸ fusionOddCore Y) n) :
    NotSpPSU (Y ⧸ Subgroup.center Y) := by
  have h4 := w85g_four_not_dvd_card_quot_center_of_symGp hn h
  rintro ⟨m, n', hm, hSp | hPSU⟩
  · exact h4 (dvd_trans (by norm_num : 4 ∣ 16) (w85g_sixteen_dvd_card_of_isSpGp hm hSp))
  · exact h4 (dvd_trans (by norm_num : 4 ∣ 16) (w85g_sixteen_dvd_card_of_isPSUGp hm hPSU))

theorem exists_sylow_weaklyClosed_of_bender {X : Type} [Group X]
    [Finite X] {n : ℕ} {S : Subgroup X} (hp : CFSG.pCore 2 X = ⊥)
    (h : (∃ m : ℕ, m ≤ 3 ∧ IsSpGp (X ⧸ Subgroup.center X) m n ∧ IsSymplecticRootGroup X m n S) ∨
      (IsPSUGp (X ⧸ Subgroup.center X) 3 n ∧ IsUnitaryRootGroup X 3 n S) ∨
      (IsSzGp (X ⧸ Subgroup.center X) n ∧ IsSuzukiRootGroup X S)) :
    ∃ P : Sylow 2 X, S ≤ (P : Subgroup X) ∧ IsWeaklyClosedIn S (P : Subgroup X) :=
  exists_sylow_weaklyClosed_of_bender_root hp h

theorem exists_sylow_weaklyClosed_of_isSpGp_two_one {X : Type} [Group X] [Finite X]
    {S : Subgroup X} (hS : Nat.card S = 2) (hodd : Odd (Nat.card (Subgroup.center X)))
    (h : IsSpGp (X ⧸ Subgroup.center X) 2 1) :
    ∃ P : Sylow 2 X, S ≤ (P : Subgroup X) ∧ IsWeaklyClosedIn S (P : Subgroup X) := by
  refine w85g_exists_sylow_weaklyClosed_of_card_two hS ?_
  obtain ⟨k, hk, F, hFld, hFin, hFcard, ⟨e⟩⟩ := h
  have hk1 : k = 1 := by omega
  subst hk1
  haveI := hFld
  haveI := hFin
  have hq : Nat.card (X ⧸ Subgroup.center X) = 6 := by
    refine (Nat.card_congr e.toEquiv).trans ?_
    rw [@CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp F hFld hFin 1]
    rw [hFcard]
    norm_num
  have hcard : Nat.card X = Nat.card (Subgroup.center X) * Nat.card (X ⧸ Subgroup.center X) := by
    rw [← Subgroup.card_mul_index (H := Subgroup.center X), Subgroup.index_eq_card]
  have hcop : Nat.Coprime 4 (Nat.card (Subgroup.center X)) := by
    rw [show (4:ℕ) = 2 ^ 2 by norm_num, Nat.coprime_pow_left_iff (by norm_num)]
    exact Nat.coprime_two_left.mpr hodd
  rw [hcard, hq]
  intro h4
  exact (by rw [hcop.dvd_mul_left]; norm_num : ¬ 4 ∣ Nat.card (Subgroup.center X) * 6) h4

theorem exists_sylow_weaklyClosed_of_symGp_le_three {X : Type} [Group X] [Finite X]
    {S : Subgroup X} {n : ℕ} (hS : Nat.card S = 2) (hn : n ≤ 3)
    (h : IsSymGp (X ⧸ fusionOddCore X) n) :
    ∃ P : Sylow 2 X, S ≤ (P : Subgroup X) ∧ IsWeaklyClosedIn S (P : Subgroup X) := by
  refine w85g_exists_sylow_weaklyClosed_of_card_two hS ?_
  obtain ⟨e⟩ := h
  haveI : (fusionOddCore X).Normal := fusionOddCore_normal X
  have hq : Nat.card (X ⧸ fusionOddCore X) = n.factorial := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  have hcard : Nat.card X = Nat.card (fusionOddCore X) * Nat.card (X ⧸ fusionOddCore X) := by
    rw [← Subgroup.card_mul_index (H := fusionOddCore X), Subgroup.index_eq_card]
  have hcop : Nat.Coprime 4 (Nat.card (fusionOddCore X)) := by
    rw [show (4:ℕ) = 2 ^ 2 by norm_num, Nat.coprime_pow_left_iff (by norm_num)]
    exact Nat.coprime_two_left.mpr (CFSG.CGT.Timmesfeld75.odd_card_fusionOddCore X)
  have h6 : Nat.card (X ⧸ fusionOddCore X) ∣ 6 := by
    rw [hq]
    interval_cases n <;> norm_num
  rw [hcard]
  intro h4
  exact (by rw [hcop.dvd_mul_left]; norm_num : ¬ 4 ∣ Nat.card (fusionOddCore X) * 6)
    (dvd_trans h4 (Nat.mul_dvd_mul_left _ h6))

structure ShapeData {G : Type} [Group G] [Finite G] (V H T : Subgroup G) {X : Type} [Group X]
    (φ : ↥(kGenIn V H) →* X) : Prop where
  hyp83 : Hyp83 V H T
  eq_sup : H = kGenIn V H ⊔ T
  bar : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ
  situation : BarSituation X (barSub (kGenIn V H) φ V)
  central : Nat.card (barSub (kGenIn V H) φ V) = 2 →
    CentralInSylow X (barSub (kGenIn V H) φ V)

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
  {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}

theorem ShapeData.finite (d : ShapeData V H T φ) : Finite X :=
  Finite.of_surjective φ d.bar.surjective

theorem ShapeData.kBarCenterShape (d : ShapeData V H T φ) {P : ∀ (Y : Type) [Group Y], Prop}
    (hP : P (X ⧸ Subgroup.center X)) : KBarCenterShape V H T P :=
  (d.hyp83.kBarCenterShape_iff d.eq_sup).2 (hasQuotShape_centerPre_of_isBarMap d.bar hP)

theorem ShapeData.odd_card_center (d : ShapeData V H T φ) :
    Odd (Nat.card (Subgroup.center X)) := by
  haveI := d.finite
  exact odd_card_center_of_pCore_eq_bot d.situation.pCore_eq_bot

private theorem w85g_isSpGp_of_mulEquiv {Y Z : Type} [Group Y] [Group Z] {m n : ℕ}
    (e : Y ≃* Z) (h : IsSpGp Z m n) : IsSpGp Y m n := by
  obtain ⟨k, hk, F, hF, hFin, hcard, ⟨e'⟩⟩ := h
  exact ⟨k, hk, F, hF, hFin, hcard, ⟨e.trans e'⟩⟩

private theorem w85g_conjSubgroup_map {Y Z : Type} [Group Y] [Group Z] (ψ : Y →* Z)
    (A : Subgroup Y) (x : Y) :
    conjSubgroup (A.map ψ) (ψ x) = (conjSubgroup A x).map ψ := by
  have h : (MulAut.conj (ψ x)⁻¹).toMonoidHom.comp ψ =
      ψ.comp (MulAut.conj x⁻¹).toMonoidHom := by
    ext a
    simp [MulAut.conj_apply]
  calc conjSubgroup (A.map ψ) (ψ x)
      = (A.map ψ).map (MulAut.conj (ψ x)⁻¹).toMonoidHom := rfl
    _ = A.map ((MulAut.conj (ψ x)⁻¹).toMonoidHom.comp ψ) :=
        Subgroup.map_map (K := A) (MulAut.conj (ψ x)⁻¹).toMonoidHom ψ
    _ = A.map (ψ.comp (MulAut.conj x⁻¹).toMonoidHom) := by rw [h]
    _ = (A.map (MulAut.conj x⁻¹).toMonoidHom).map ψ :=
        (Subgroup.map_map (K := A) ψ (MulAut.conj x⁻¹).toMonoidHom).symm
    _ = (conjSubgroup A x).map ψ := rfl

private theorem w85g_exists_sylow_barSub_T {h : Hyp83 V H T} (hKT : H = kGenIn V H ⊔ T)
    {Z : Type} [Group Z] {φ : ↥(kGenIn V H) →* Z} (hφ : Function.Surjective φ) :
    ∃ P : Sylow 2 Z, (P : Subgroup Z) = barSub (kGenIn V H) φ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : kGenIn V H ≤ H := kGenIn_le_H h.le_H
  have hKN : ((kGenIn V H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr
      (h.le_normalizer_kGenIn_of_eq_sup hKT)
  have hSyl : IsSylowIn 2 (T ⊓ kGenIn V H) (kGenIn V H) :=
    h.sylow_H.inf_normal hKH hKN
  let P₀ : Sylow 2 ↥(kGenIn V H) := hSyl.toSylow
  refine ⟨P₀.mapSurjective hφ, ?_⟩
  rw [Sylow.coe_mapSurjective, IsSylowIn.coe_toSylow]
  show ((T ⊓ kGenIn V H).subgroupOf (kGenIn V H)).map φ =
    (T.subgroupOf (kGenIn V H)).map φ
  rw [inf_subgroupOf_right]

private theorem w85g_le_of_le_sup_center {Y : Type} [Group Y] [Finite Y]
    (P : Sylow 2 Y) {Q : Subgroup Y} (hQ : IsPGroup 2 Q)
    (hQP : Q ≤ (P : Subgroup Y) ⊔ Subgroup.center Y) : Q ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (P : Subgroup Y) ⊔ Subgroup.center Y ≤
      Subgroup.normalizer ((P : Subgroup Y) : Set Y) :=
    sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer _)
  have hp := hQ.to_sup_of_normal_right' P.isPGroup' (hQP.trans hN)
  have := P.is_maximal' hp le_sup_right
  rw [← this]
  exact le_sup_left

theorem shape86WeakC_of_weakClosed (d : ShapeData V H T φ) (hn : NotSpPSU (X ⧸ Subgroup.center X))
    (P : Sylow 2 X) (hSP : barSub (kGenIn V H) φ V ≤ (P : Subgroup X))
    (hw : IsWeaklyClosedIn (barSub (kGenIn V H) φ V) (P : Subgroup X)) :
    Shape86WeakC V H T := by
  haveI := d.finite
  constructor
  · rintro ⟨m, n, hm, hSp | hPSU⟩
    · obtain ⟨Z, hZgrp, hZSp, ⟨e⟩⟩ :=
        nonempty_mulEquiv_of_kBarCenterShape d.hyp83 d.eq_sup hSp d.bar
      exact hn ⟨m, n, hm, Or.inl (w85g_isSpGp_of_mulEquiv e hZSp)⟩
    · obtain ⟨Z, hZgrp, hZPSU, ⟨e⟩⟩ :=
        nonempty_mulEquiv_of_kBarCenterShape d.hyp83 d.eq_sup hPSU d.bar
      exact hn ⟨m, n, hm, Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hZPSU)⟩
  · obtain ⟨Y, hYgrp, φ', ψ, hφ', hψsurj, hψcomp, hψker⟩ :=
      exists_central_quotient d.hyp83 d.eq_sup d.bar
    letI := hYgrp
    haveI : Finite Y := Finite.of_surjective ψ hψsurj
    have hVbar_p : IsPGroup 2 (barSub (kGenIn V H) φ V) :=
      CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian
        (isElemAbelian_barSub d.hyp83.elemAbelian φ)
    obtain ⟨P₀, hP₀⟩ := w85g_exists_sylow_barSub_T (h := d.hyp83) d.eq_sup d.bar.surjective
    have hVbar_le : barSub (kGenIn V H) φ V ≤ (P₀ : Subgroup X) := by
      rw [hP₀]
      rintro y ⟨k, hk, rfl⟩
      exact mem_barSub.mpr ⟨k, d.hyp83.le_T hk, rfl⟩
    have hw₀ : IsWeaklyClosedIn (barSub (kGenIn V H) φ V) (P₀ : Subgroup X) :=
      isWeaklyClosedIn_of_sylow hSP hVbar_le hw
    refine weaklyClosed_of_bar ⟨d.hyp83, d.eq_sup, hφ'⟩ ?_
    intro g hg
    obtain ⟨x, rfl⟩ := hψsurj g
    have hVhat : barSub (kGenIn V H) φ' V = (barSub (kGenIn V H) φ V).map ψ := by
      ext y
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact Subgroup.mem_map.mpr ⟨φ k, mem_barSub.mpr ⟨k, hk, rfl⟩, hψcomp k⟩
      · rintro ⟨z, hz, hzy⟩
        obtain ⟨k, hk, rfl⟩ := mem_barSub.mp hz
        exact ⟨k, hk, by rw [← hψcomp k]; exact hzy⟩
    have hThat : barSub (kGenIn V H) φ' T = (barSub (kGenIn V H) φ T).map ψ := by
      ext y
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact Subgroup.mem_map.mpr ⟨φ k, mem_barSub.mpr ⟨k, hk, rfl⟩, hψcomp k⟩
      · rintro ⟨z, hz, hzy⟩
        obtain ⟨k, hk, rfl⟩ := mem_barSub.mp hz
        exact ⟨k, hk, by rw [← hψcomp k]; exact hzy⟩
    have hg' : (conjSubgroup (barSub (kGenIn V H) φ V) x).map ψ ≤
        (barSub (kGenIn V H) φ T).map ψ := by
      have h := hg
      rw [hVhat, hThat, w85g_conjSubgroup_map ψ (barSub (kGenIn V H) φ V) x] at h
      exact h
    have hA : IsPGroup 2 (conjSubgroup (barSub (kGenIn V H) φ V) x) :=
      hVbar_p.map (MulAut.conj x⁻¹).toMonoidHom
    have hle' : conjSubgroup (barSub (kGenIn V H) φ V) x ≤
        (P₀ : Subgroup X) ⊔ Subgroup.center X := by
      have h1 : conjSubgroup (barSub (kGenIn V H) φ V) x ≤
          barSub (kGenIn V H) φ T ⊔ ψ.ker := by
        have h2 : conjSubgroup (barSub (kGenIn V H) φ V) x ≤
            ((barSub (kGenIn V H) φ T).map ψ).comap ψ :=
          (Subgroup.map_le_iff_le_comap).mp hg'
        rwa [Subgroup.comap_map_eq] at h2
      refine h1.trans ?_
      rw [← hP₀]
      exact sup_le_sup le_rfl hψker
    have hA_le : conjSubgroup (barSub (kGenIn V H) φ V) x ≤
        barSub (kGenIn V H) φ T := by
      have h2 := w85g_le_of_le_sup_center P₀ hA hle'
      rwa [hP₀] at h2
    have hA_eq := hw₀ x (by rw [hP₀]; exact hA_le)
    rw [hVhat, w85g_conjSubgroup_map ψ (barSub (kGenIn V H) φ V) x, hA_eq]

theorem shape86C'_of_isSpGp (d : ShapeData V H T φ) {m n : ℕ}
    (hSp : IsSpGp (X ⧸ Subgroup.center X) m n)
    (hr : rankBarV V H T = n ∨ rankBarV V H T = 1)
    (hw : m = 2 → rankBarV V H T = n →
      ∃ P : Sylow 2 X, barSub (kGenIn V H) φ V ≤ (P : Subgroup X) ∧
        IsWeaklyClosedIn (barSub (kGenIn V H) φ V) (P : Subgroup X)) :
    Hyp85Three' V H T ∨ Shape86Delta' V H T ∨ Shape86WeakC V H T := by
  haveI := d.finite
  have hSp0 := hSp
  obtain ⟨k, hk, F, hFld, hFin, hFcard, ⟨e⟩⟩ := hSp
  haveI := hFld
  haveI := hFin
  have hn1 : 1 ≤ n := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hFcard] at h1
    exact Nat.one_le_iff_ne_zero.2 (Nat.one_lt_two_pow_iff.1 h1)
  have hrank_pos : 1 ≤ rankBarV V H T := by
    rcases hr with h | h <;> omega
  rcases k with _ | k
  ·
    exfalso
    haveI : Subsingleton (X ⧸ Subgroup.center X) :=
      ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩
    have hcenter : Subgroup.center X = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      have h1 : (QuotientGroup.mk x : X ⧸ Subgroup.center X) = 1 := Subsingleton.elim _ _
      rwa [QuotientGroup.eq_one_iff] at h1
    have hcardX : Nat.card X = Nat.card (Subgroup.center X) := by
      rw [hcenter, Subgroup.card_top]
    have h2dvd : 2 ∣ Nat.card X := by
      refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card (barSub (kGenIn V H) φ V))
      rw [d.hyp83.card_barSub_eq_two_pow_rankBarV d.eq_sup d.bar]
      simpa only [pow_one] using pow_dvd_pow 2 hrank_pos
    rw [hcardX] at h2dvd
    exact d.odd_card_center.not_two_dvd_nat h2dvd
  rcases k with _ | k
  ·
    have hm2 : m = 2 := by omega
    rcases hr with hrn | hr1
    · obtain ⟨P, hSP, hw'⟩ := hw hm2 hrn
      exact Or.inr (Or.inr (shape86WeakC_of_weakClosed d
        (notSpPSU_of_isSpGp_two (hm2 ▸ hSp0)) P hSP hw'))
    · by_cases hn : n = 1
      · obtain ⟨P, hSP, hw'⟩ := hw hm2 (by omega)
        exact Or.inr (Or.inr (shape86WeakC_of_weakClosed d
          (notSpPSU_of_isSpGp_two (hm2 ▸ hSp0)) P hSP hw'))
      · exact Or.inr (Or.inl ⟨m, n, by omega, by omega, hr1,
          Or.inl (d.kBarCenterShape hSp0)⟩)
  ·
    have hm4 : 3 < m := by omega
    rcases hr with hrn | hr1
    · exact Or.inl (Or.inl ⟨m, n, hm4, d.kBarCenterShape hSp0, hrn⟩)
    · by_cases hn : n = 1
      · exact Or.inl (Or.inl ⟨m, n, hm4, d.kBarCenterShape hSp0, by omega⟩)
      · exact Or.inr (Or.inl ⟨m, n, by omega, by omega, hr1,
          Or.inl (d.kBarCenterShape hSp0)⟩)

theorem shape86C'_of_isPSUGp (d : ShapeData V H T φ) {m n : ℕ}
    (hPSU : IsPSUGp (X ⧸ Subgroup.center X) m n)
    (hr : rankBarV V H T = n ∨ rankBarV V H T = 1)
    (hw : m = 3 → rankBarV V H T = n →
      ∃ P : Sylow 2 X, barSub (kGenIn V H) φ V ≤ (P : Subgroup X) ∧
        IsWeaklyClosedIn (barSub (kGenIn V H) φ V) (P : Subgroup X)) :
    Hyp85Three' V H T ∨ Shape86Delta' V H T ∨ Shape86WeakC V H T := by
  have hadm := CFSG.Blueprint.LieModel.admissible hPSU
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨-, hn1, hm3, hne⟩ := hadm
  by_cases hm : m = 3
  · subst hm
    have hn : 1 < n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · have hn1' : n = 1 := by omega
        exact absurd (by rw [hn1']; norm_num : ((3:ℕ), 2 ^ n) = (3, 2)) hne
      · omega
    rcases hr with hrn | hr1
    · obtain ⟨P, hSP, hw'⟩ := hw rfl hrn
      exact Or.inr (Or.inr (shape86WeakC_of_weakClosed d
        (notSpPSU_of_isPSUGp_three hPSU) P hSP hw'))
    · exact Or.inr (Or.inl ⟨3, n, by omega, hn, hr1, Or.inr (d.kBarCenterShape hPSU)⟩)
  · have hm' : 3 < m := by omega
    rcases hr with hrn | hr1
    · exact Or.inl (Or.inr (Or.inl ⟨m, n, hm', d.kBarCenterShape hPSU, hrn⟩))
    · by_cases hn : n = 1
      · exact Or.inl (Or.inr (Or.inl ⟨m, n, hm', d.kBarCenterShape hPSU, by omega⟩))
      · exact Or.inr (Or.inl ⟨m, n, by omega, by omega, hr1,
          Or.inr (d.kBarCenterShape hPSU)⟩)

theorem not_isPSUGp_three_one {Y : Type} [Group Y] : ¬ IsPSUGp Y 3 1 := by
  intro h
  have h1 := CFSG.Blueprint.LieModel.admissible h
  have hne : (3, 2 ^ 1) ≠ (3, 2) := by
    simpa [CFSG.Open.StatedLieAdmissible] using h1.2.2
  exact hne (by norm_num)

private noncomputable def w85g_statedSp_one_equiv_sl2 (F : Type) [Field F] :
    ↥(StatedSp 1 F) ≃* Matrix.SpecialLinearGroup (Fin 2) F := by
  let r := CFSG.RankThree.GF2n.Stroth80.reindexGL (K := F)
    CFSG.RankThree.GF2n.Stroth80.sumFinTwo
  let e₂ : ↥(StatedSp 1 F) ≃* ↥(StatedSL 2 F) :=
    (Subgroup.equivMapOfInjective (StatedSp 1 F) r.toMonoidHom r.injective).trans
      (MulEquiv.subgroupCongr CFSG.RankThree.GF2n.Stroth80.map_reindexGL_statedSp_one)
  let e₃ : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(StatedSL 2 F) :=
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 2 F).symm)
  exact e₂.trans e₃.symm

theorem isSpGp_of_isL2WrSymGp_le_one {Y : Type} [Group Y] {n m : ℕ} (hm : m ≤ 1)
    (h : IsL2WrSymGp Y n m) : IsSpGp Y (2 * m) n := by
  interval_cases m
  · obtain ⟨F, hFld, hFin, hFcard, ⟨e⟩⟩ := h
    refine ⟨0, rfl, F, hFld, hFin, hFcard, ⟨e.trans ?_⟩⟩
    haveI : Subsingleton (Fin 0 → Matrix.SpecialLinearGroup (Fin 2) F) :=
      ⟨fun a b => funext fun i => Fin.elim0 i⟩
    haveI : Subsingleton (Equiv.Perm (Fin 0)) :=
      ⟨fun a b => Equiv.ext fun i => Fin.elim0 i⟩
    haveI : Subsingleton (WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) 0) :=
      ⟨fun a b => SemidirectProduct.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
    let f : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) 0 →* ↥(StatedSp 0 F) :=
      { toFun := fun _ => 1, map_one' := rfl, map_mul' := fun a b => by simp }
    exact MulEquiv.ofBijective f
      ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨1, Subsingleton.elim _ _⟩⟩
  · obtain ⟨F, hFld, hFin, hFcard, ⟨e⟩⟩ :=
      isL2Gp_of_isL2WrSymGp_one (n := n) (by simpa using h)
    exact ⟨1, rfl, F, hFld, hFin, hFcard,
      ⟨e.trans (w85g_statedSp_one_equiv_sl2 F).symm⟩⟩

theorem false_of_symGp_four_five {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : BarSituation X S) (h2 : Nat.card S = 2) (hc : CentralInSylow X S) {n : ℕ}
    (h : IsSymGp (X ⧸ fusionOddCore X) n) (h45 : n = 4 ∨ n = 5) : False := by
  obtain ⟨e⟩ := h
  have hodd : Odd (Nat.card (QuotientGroup.mk' (fusionOddCore X)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.CGT.Timmesfeld75.odd_card_fusionOddCore X
  obtain ⟨d, hdd, hd1, hSd, hclass⟩ :=
    barSituation_map_two hS h2 (QuotientGroup.mk' (fusionOddCore X))
      (QuotientGroup.mk'_surjective _) hodd
  have hcdz : CentralInSylow (X ⧸ fusionOddCore X) (Subgroup.zpowers d) := by
    rw [← hSd]
    exact centralInSylow_map _ (QuotientGroup.mk'_surjective _) S hc
  have hcdz' : CentralInSylow (Equiv.Perm (Fin n)) (Subgroup.zpowers (e d)) := by
    have h1 := centralInSylow_map e.toMonoidHom e.surjective (Subgroup.zpowers d) hcdz
    rwa [MonoidHom.map_zpowers] at h1
  have hdd' : e d * e d = 1 := by rw [← map_mul, hdd, map_one]
  have hoddidx : Odd (Subgroup.centralizer ({e d} : Set (Equiv.Perm (Fin n)))).index :=
    (centralInSylow_zpowers_iff_odd_index (e d) hdd').mp hcdz'
  have himage : e.toMonoidHom '' {y : X ⧸ fusionOddCore X | IsConj d y} =
      {y : Equiv.Perm (Fin n) | IsConj (e d) y} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      refine isConj_iff.mpr ⟨e c, ?_⟩
      simp only [← map_mul, ← map_inv, hc]
      rfl
    · rintro hy
      obtain ⟨c, hc⟩ := isConj_iff.mp hy
      refine ⟨e.symm y, isConj_iff.mpr ⟨e.symm c, ?_⟩, by simp⟩
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hc
  have hclass_top : Subgroup.closure {y : Equiv.Perm (Fin n) | IsConj (e d) y} = ⊤ := by
    rw [← himage, ← MonoidHom.map_closure, hclass.2.2]
    exact Subgroup.map_top_of_surjective _ e.surjective
  have hsign : Equiv.Perm.sign (e d) = -1 := by
    by_contra hne
    have h1 : Equiv.Perm.sign (e d) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (e d)) with h' | h'
      · exact h'
      · exact absurd h' hne
    have hle : Subgroup.closure {y : Equiv.Perm (Fin n) | IsConj (e d) y} ≤
        alternatingGroup (Fin n) := by
      rw [Subgroup.closure_le]
      rintro y hy
      obtain ⟨c, hc⟩ := isConj_iff.mp hy
      change Equiv.Perm.sign y = 1
      rw [← hc]
      simp only [map_mul, map_inv, h1]
      group
    rw [hclass_top] at hle
    have hsign_one : ∀ y : Equiv.Perm (Fin n), Equiv.Perm.sign y = 1 := fun y =>
      hle (Subgroup.mem_top y)
    have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have hswap := Equiv.Perm.sign_swap (α := Fin n) (x := ⟨0, by omega⟩)
      (y := ⟨1, by omega⟩) h01
    rw [hsign_one (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩)] at hswap
    norm_num at hswap
  exact gap5Perm_not_odd_index_four_five h45 hdd' hsign hoddidx

theorem hyp85Three'_of_symGp (d : ShapeData V H T φ) {n : ℕ}
    (h : IsSymGp (X ⧸ fusionOddCore X) n) (hn : 6 ≤ n) : Hyp85Three' V H T := by
  haveI := d.finite
  obtain ⟨e₀⟩ := h
  obtain ⟨Y, hYgrp, φ', ψ, hφ', hψsurj, -, hψker⟩ :=
    exists_central_quotient d.hyp83 d.eq_sup d.bar
  letI := hYgrp
  haveI : Finite Y := Finite.of_surjective ψ hψsurj
  have hodd : Odd (Nat.card ψ.ker) :=
    Odd.of_dvd_nat d.odd_card_center (Subgroup.card_dvd_of_le hψker)
  obtain ⟨π, hπs, -, hπodd, hπmax, -⟩ := gap5X_exists_pi ψ hψsurj hodd e₀
  have hπker : π.ker = fusionOddCore Y := by
    refine le_antisymm (CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hπodd) ?_
    exact hπmax (fusionOddCore Y) (fusionOddCore_normal Y)
      (CFSG.CGT.Timmesfeld75.odd_card_fusionOddCore Y)
  refine Or.inr (Or.inr ⟨n, by omega, Y, inferInstance, φ', hφ', ⟨?_⟩⟩)
  exact (QuotientGroup.quotientMulEquivOfEq hπker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective (φ := π) hπs)

theorem shape86C'_of_rootGroupShape (d : ShapeData V H T φ)
    {n : ℕ}
    (h : IsRootGroupShape X n (barSub (kGenIn V H) φ V)) :
    Hyp85Three' V H T ∨ Shape86Delta' V H T ∨ Shape86WeakC V H T := by
  haveI := d.finite
  have hrank : ∀ {S : Subgroup X}, S = barSub (kGenIn V H) φ V → Nat.card S = 2 ^ n →
      rankBarV V H T = n := by
    intro S hS hSn
    have h1 := d.hyp83.card_barSub_eq_two_pow_rankBarV d.eq_sup d.bar
    rw [← hS, hSn] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  rcases h with ⟨m, hSp, hroot⟩ | ⟨m, hPSU, hroot⟩ | ⟨hSz, hroot⟩
  · refine shape86C'_of_isSpGp d hSp (Or.inl (hrank rfl hroot.1)) fun hm _ => ?_
    exact exists_sylow_weaklyClosed_of_bender d.situation.pCore_eq_bot
      (Or.inl ⟨m, by omega, hSp, hroot⟩)
  · refine shape86C'_of_isPSUGp d hPSU (Or.inl (hrank rfl hroot.1)) fun hm _ => ?_
    subst hm
    exact exists_sylow_weaklyClosed_of_bender d.situation.pCore_eq_bot
      (Or.inr (Or.inl ⟨hPSU, hroot⟩))
  · obtain ⟨P, hSP, hw⟩ := exists_sylow_weaklyClosed_of_bender d.situation.pCore_eq_bot
      (Or.inr (Or.inr ⟨hSz, hroot⟩))
    exact Or.inr (Or.inr (shape86WeakC_of_weakClosed d (notSpPSU_of_isSzGp hSz) P hSP hw))

theorem shape86C'_of_linearShape (d : ShapeData V H T φ)
    (h : SevenElevenLinearShape X (barSub (kGenIn V H) φ V)) :
    Hyp85Three' V H T ∨ Shape86Delta' V H T ∨ Shape86WeakC V H T := by
  obtain ⟨m, n, hm, hL, -, P, hSP, hw⟩ := h
  exact Or.inr (Or.inr (shape86WeakC_of_weakClosed d (notSpPSU_of_linear hm hL) P hSP hw))

theorem shape86C'_of_aSixShape (d : ShapeData V H T φ)
    (h : SevenElevenASixShape X (barSub (kGenIn V H) φ V)) :
    Hyp85Three' V H T ∨ Shape86Delta' V H T ∨ Shape86WeakC V H T := by
  obtain ⟨⟨e⟩, -, P, hSP, hw⟩ := h
  exact Or.inr (Or.inr (shape86WeakC_of_weakClosed d (notSpPSU_of_alt6 ⟨e⟩) P hSP hw))

theorem shape86C'_of_four (g4 : W3Lem85TwoGap4) (d : ShapeData V H T φ)
    (hS2 : Nat.card (barSub (kGenIn V H) φ V) = 2) {m n : ℕ}
    (h4 : (IsSpGp (X ⧸ Subgroup.center X) m n ∧
        ∀ s ∈ barSub (kGenIn V H) φ V, s ≠ 1 → IsSymplecticTransvection X m n s) ∨
      (IsPSUGp (X ⧸ Subgroup.center X) m n ∧
        ∀ s ∈ barSub (kGenIn V H) φ V, s ≠ 1 → IsUnitaryTransvection X m n s) ∨
      IsOrthGp (X ⧸ Subgroup.center X) m n ∨ IsL2WrSymGp (X ⧸ Subgroup.center X) n m) :
    Hyp85Three' V H T ∨ Shape86Delta' V H T ∨ Shape86WeakC V H T := by
  haveI := d.finite
  have hr1 : rankBarV V H T = 1 := by
    have h1 := d.hyp83.card_barSub_eq_two_pow_rankBarV d.eq_sup d.bar
    rw [hS2] at h1
    exact (Nat.pow_right_injective le_rfl (h1.symm.trans (pow_one 2).symm))
  have hsp : ∀ {m n : ℕ}, IsSpGp (X ⧸ Subgroup.center X) m n →
      Hyp85Three' V H T ∨ Shape86Delta' V H T ∨ Shape86WeakC V H T := fun {m n} hSp =>
    shape86C'_of_isSpGp d hSp (Or.inr hr1) fun hm hrn => by
      subst hm
      have hn1 : n = 1 := hrn.symm.trans hr1
      subst hn1
      exact exists_sylow_weaklyClosed_of_isSpGp_two_one hS2 d.odd_card_center hSp
  rcases h4 with ⟨hSp, -⟩ | ⟨hPSU, -⟩ | hOrth | hWr
  · exact hsp hSp
  · refine shape86C'_of_isPSUGp d hPSU (Or.inr hr1) fun hm hrn => ?_
    subst hm
    have hn1 : n = 1 := hrn.symm.trans hr1
    subst hn1
    exact (not_isPSUGp_three_one hPSU).elim
  · exact (g4 X _ d.situation hS2 (Or.inl ⟨m, n, hOrth⟩) (d.central hS2)).elim
  · by_cases hm : 2 ≤ m
    · exact (g4 X _ d.situation hS2 (Or.inr ⟨n, m, hm, hWr⟩) (d.central hS2)).elim
    · exact hsp (isSpGp_of_isL2WrSymGp_le_one (by omega) hWr)

theorem shape86C'_of_symGp (d : ShapeData V H T φ)
    (hS2 : Nat.card (barSub (kGenIn V H) φ V) = 2) {n : ℕ}
    (h5 : IsSymGp (X ⧸ fusionOddCore X) n) :
    Hyp85Three' V H T ∨ Shape86Delta' V H T ∨ Shape86WeakC V H T := by
  haveI := d.finite
  by_cases hn3 : n ≤ 3
  · obtain ⟨P, hSP, hw⟩ := exists_sylow_weaklyClosed_of_symGp_le_three hS2 hn3 h5
    exact Or.inr (Or.inr (shape86WeakC_of_weakClosed d
      (notSpPSU_of_symGp_le_three hn3 d.odd_card_center h5) P hSP hw))
  · by_cases hn45 : n = 4 ∨ n = 5
    · exact (false_of_symGp_four_five d.situation hS2 (d.central hS2) h5 hn45).elim
    · exact Or.inl (hyp85Three'_of_symGp d h5 (by omega))

theorem shape86C'_of_alt (g4 : W3Lem85TwoGap4)
    (g6 : W3Lem85TwoGap6) (d : ShapeData V H T φ)
    (halt : SevenElevenAlt X (barSub (kGenIn V H) φ V)) :
    Hyp85Three' V H T ∨ Shape86Delta' V H T ∨ Shape86WeakC V H T := by
  haveI := d.finite
  rcases halt with ⟨⟨n', h1⟩, -⟩ | h2 | ⟨-, h3⟩ | ⟨hS2, m', n', h4⟩ | ⟨hS2, n', h5⟩ | ⟨hS2, h6⟩
  · exact shape86C'_of_rootGroupShape d h1
  · exact shape86C'_of_linearShape d h2
  · exact shape86C'_of_aSixShape d h3
  · exact shape86C'_of_four g4 d hS2 h4
  · exact shape86C'_of_symGp d hS2 h5
  · exact (g6 X _ d.situation hS2 h6 (d.central hS2)).elim

theorem exists_shapeData (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H) {V H T : Subgroup G}
    (hV : Hyp7 V) (hH : IsCalH V H) (hH0 : ¬ IsCalH0 V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) (hKT : H = kGenIn V H ⊔ T) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (φ : ↥(kGenIn V H) →* X), ShapeData V H T φ ∧
      SevenElevenAlt X (barSub (kGenIn V H) φ V) := by
  have h : Hyp83 V H T := Hyp83.of_hyp7 hV hH hH0 hT
  let X : Type := ↥(kGenIn V H) ⧸ CFSG.pCore 2 ↥(kGenIn V H)
  let φ : ↥(kGenIn V H) →* X := QuotientGroup.mk' (CFSG.pCore 2 ↥(kGenIn V H))
  have hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ := isBarMap_mk_pCore (kGenIn V H)
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  obtain ⟨φ', hφ', hS⟩ := exists_ambient_barMap h hKT hφ
  have hSit : BarSituation X (barSub (kGenIn V H) φ V) := by
    rw [← hS]
    exact barSituation_of_hyp711 (AmbientH.hyp711 h hKT) hφ'
  have hc : Nat.card (barSub (kGenIn V H) φ V) = 2 →
      CentralInSylow X (barSub (kGenIn V H) φ V) := fun hS2 => by
    rw [← hS]
    exact centralInSylow_of_hyp83 h hKT hφ' (by rw [hS]; exact hS2)
  have hAlt := ((h711 H) _ _ _ (AmbientH.hyp711 h hKT)).2 X φ' hφ'
  rw [hS] at hAlt
  exact ⟨X, inferInstance, inferInstance, φ, ⟨h, hKT, hφ, hSit, hc⟩, hAlt⟩

theorem w3Shape86C'_holds
    (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H) (g4 : W3Lem85TwoGap4) (g6 : W3Lem85TwoGap6) :
    W3Shape86C' G := by
  intro V H T hV hH hH0 hT hKT
  obtain ⟨X, _, _, φ, d, hAlt⟩ := exists_shapeData h711 hV hH hH0 hT hKT
  exact shape86C'_of_alt g4 g6 d hAlt

end CFSG.LocalAnalysis.WeakClosure81

end
