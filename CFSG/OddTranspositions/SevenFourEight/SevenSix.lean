module

public import CFSG.OddTranspositions.HypothesisC
import CFSG.OddTranspositions.HalphaQuotient
import CFSG.GH74.Uniqueness.Section171Group
import CFSG.OddTranspositions.SevenFourEight.InvertedPGroup
import CFSG.OddTranspositions.SixFiveInputs
import CFSG.OddTranspositions.SixNineUnconditional
import CFSG.Fischer.Classification.SRG.Conference
public import CFSG.Timmesfeld.Bridge.Asc72Triangle

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity
open scoped commutatorElement

private theorem ncard_conj_dvd {X : Type} [Group X] [Finite X] (Y : Subgroup X) (x : X) :
    {z | ∃ g ∈ Y, g * x * g⁻¹ = z}.ncard ∣ Nat.card Y :=
  Dvd.intro _ (CFSG.GH74.Uniqueness.ncard_conjOrbit_mul_card_cent Y x)

private theorem eq_one_of_pow_sub_one_eq_two_pow {p g t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hg : 1 ≤ g) (h : p ^ g - 1 = 2 ^ t) : g = 1 := by
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    omega
  have hdvd2 : ∀ {n : ℕ}, n ∣ p ^ g - 1 → ∃ k, n = 2 ^ k := by
    intro n hn
    rw [h] at hn
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
    exact ⟨k, hk⟩
  by_contra hg1
  rcases Nat.even_or_odd g with ⟨r, hr⟩ | ⟨r, hr⟩
  ·
    have hr1 : 1 ≤ r := by omega
    set a := p ^ r with ha
    have ha5 : 5 ≤ a := le_trans hp5 (by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ r := Nat.pow_le_pow_right (by omega) hr1)
    have hfac : p ^ g - 1 = (a - 1) * (a + 1) := by
      rw [hr, pow_add, ← ha]
      have : 1 ≤ a := by omega
      zify [this, Nat.one_le_iff_ne_zero.mpr (by positivity : a * a ≠ 0)]
      ring
    obtain ⟨c, hc⟩ := hdvd2 (n := a - 1) (hfac ▸ dvd_mul_right _ _)
    obtain ⟨b, hb⟩ := hdvd2 (n := a + 1) (hfac ▸ dvd_mul_left _ _)
    have hc2 : 2 ≤ c := by
      by_contra hc2
      interval_cases c <;> omega
    have hb2 : 2 ≤ b := by
      by_contra hb2
      interval_cases b <;> omega
    have h4c : 4 ∣ a - 1 := hc ▸ (pow_dvd_pow 2 hc2)
    have h4b : 4 ∣ a + 1 := hb ▸ (pow_dvd_pow 2 hb2)
    omega
  ·
    set S := ∑ i ∈ Finset.range g, p ^ i with hS
    have hSmul : S * (p - 1) = p ^ g - 1 := by
      have h1 : 1 ≤ p := by omega
      have h2 : 1 ≤ p ^ g := Nat.one_le_pow _ _ (by omega)
      zify [h1, h2]
      rw [hS]
      push_cast
      exact geom_sum_mul (p : ℤ) g
    obtain ⟨s, hs⟩ := hdvd2 (n := S) (hSmul ▸ dvd_mul_right _ _)
    have hSodd : S % 2 = 1 := by
      rw [hS, Finset.sum_nat_mod]
      have hpodd : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h2 | h2
        · exact absurd h2 hp2
        · exact h2
      have : ∀ i ∈ Finset.range g, p ^ i % 2 = 1 := fun i _ => by
        simp [Nat.pow_mod, hpodd]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      omega
    have hS2 : 1 + p ≤ S := by
      have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range g := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rw [Finset.mem_range]
        omega
      have := Finset.sum_le_sum_of_subset (f := fun i => p ^ i) hsub
      simpa using this
    rcases s with _ | s
    · rw [pow_zero] at hs
      omega
    · rw [hs, pow_succ] at hSodd
      omega

private theorem not_isSquare_five_mul_sq {m : ℤ} (hm : m ≠ 0) : ¬ IsSquare (5 * m ^ 2) := by
  rintro ⟨c, hc⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp [hm] at hc
  have h1 : padicValInt 5 (5 * m ^ 2) = 1 + 2 * padicValInt 5 m := by
    rw [padicValInt.mul (by norm_num) (pow_ne_zero 2 hm), sq, padicValInt.mul hm hm]
    have : padicValInt 5 (5 : ℤ) = 1 := by exact_mod_cast padicValInt.self (p := 5) (by norm_num)
    rw [this]
    ring
  have h2 : padicValInt 5 (c * c) = 2 * padicValInt 5 c := by
    rw [padicValInt.mul hc0 hc0]
    ring
  rw [hc, h2] at h1
  omega

private theorem ncard_eq_ncard_image_mul {α β : Type*} [Finite α] {f : α → β} {s : Set α}
    {m : ℕ} (h : ∀ a ∈ s, {b | b ∈ s ∧ f b = f a}.ncard = m) :
    s.ncard = (f '' s).ncard * m := by
  classical
  have := Fintype.ofFinite α
  have himg : (f '' s).ncard = (s.toFinset.image f).card := by
    rw [← Set.ncard_coe_finset, Finset.coe_image, Set.coe_toFinset]
  rw [Set.ncard_eq_toFinset_card' s, himg, Finset.card_eq_sum_card_image f s.toFinset]
  refine Finset.sum_const_nat fun b hb => ?_
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  rw [← h a (Set.mem_toFinset.mp ha), ← Set.ncard_coe_finset]
  congr 1
  ext b
  simp

section Local

variable {X : Type} [Group X] [Finite X] {Θ : Set X}

omit [Finite X] in
private theorem map_pCore_commutator_le :
    (CFSG.pCore 2 ↥(commutator X)).map (commutator X).subtype ≤ CFSG.pCore 2 X :=
  le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, CFSG.pCore_isPGroup.map _⟩

omit [Finite X] in
private theorem mem_pCore_of_sq_mem (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index)
    {c : X} (hc : c ∈ commutator X) (hc2 : c ^ 2 ∈ CFSG.pCore 2 X) : c ∈ CFSG.pCore 2 X := by
  obtain ⟨j, hj⟩ : Odd (CFSG.pCore 2 ↥(commutator X)).index :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hX')
  have hpow := Subgroup.pow_index_mem (CFSG.pCore 2 ↥(commutator X)) (⟨c, hc⟩ : commutator X)
  rw [hj] at hpow
  have hmem : c ^ (2 * j + 1) ∈ CFSG.pCore 2 X :=
    map_pCore_commutator_le (Subgroup.mem_map.mpr ⟨_, hpow, by simp⟩)
  have e : c = ((c ^ 2) ^ j)⁻¹ * c ^ (2 * j + 1) := by
    rw [← pow_mul, pow_succ, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hc2 j)) hmem

omit [Finite X] in
private theorem mul_mem_pCore_of_commute (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index) {a b : X} (ha : a ∈ Θ) (hb : b ∈ Θ)
    (hab : Commute a b) : a * b ∈ CFSG.pCore 2 X := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj ha hb)
  have ha2 := hS.oddT.mul_self_eq_one ha
  have hb2 := hS.oddT.mul_self_eq_one hb
  apply mem_pCore_of_sq_mem hX'
  · have e : a * (c * a * c⁻¹) = ⁅a, c⁆ := by
      rw [commutatorElement_def, hS.oddT.inv_eq ha]
      group
    rw [e, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top c)
  · have e : (a * (c * a * c⁻¹)) ^ 2 = a * a * ((c * a * c⁻¹) * (c * a * c⁻¹)) := by
      rw [sq, mul_assoc, ← mul_assoc (c * a * c⁻¹) a, ← hab.eq]
      group
    rw [e, ha2, hb2, one_mul]
    exact Subgroup.one_mem _

private theorem commute_trans (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index) {a b v : X} (ha : a ∈ Θ) (hb : b ∈ Θ)
    (hv : v ∈ Θ) (hav : Commute a v) (hbv : Commute b v) : Commute a b := by
  refine commute_of_mul_mem_of_isPGroup hS.oddT CFSG.pCore_isPGroup ha hb ?_
  have e : a * b = (a * v) * (b * v)⁻¹ := by
    rw [mul_inv_rev, hS.oddT.inv_eq hv, mul_assoc, ← mul_assoc v v, hS.oddT.mul_self_eq_one hv,
      one_mul, hS.oddT.inv_eq hb]
  rw [e]
  exact Subgroup.mul_mem _ (mul_mem_pCore_of_commute hS hX' ha hv hav)
    (Subgroup.inv_mem _ (mul_mem_pCore_of_commute hS hX' hb hv hbv))

private theorem exists_not_commute (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index)
    (hQ : ¬ CFSG.pCore 2 X ≤ Subgroup.center X) {x : X} (hx : x ∈ Θ) :
    ∃ y ∈ Θ, ¬ Commute x y := by
  by_contra hcon
  push Not at hcon
  have hpair : ∀ a ∈ Θ, ∀ b ∈ Θ, Commute a b := fun a ha b hb =>
    commute_trans hS hX' ha hb hx (hcon a ha).symm (hcon b hb).symm
  have h1 : (⊤ : Subgroup X) ≤ Subgroup.centralizer Θ := by
    rw [← hS.gen, Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hpair b hb a ha).eq
  have h2 : (⊤ : Subgroup X) ≤ Subgroup.center X := by
    rw [← hS.gen, Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact ((Subgroup.mem_centralizer_iff.mp (h1 (Subgroup.mem_top g))) a ha).symm
  exact hQ fun q _ => h2 (Subgroup.mem_top q)

private theorem setOf_commute_eq_conj (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index)
    (hQ : ¬ CFSG.pCore 2 X ≤ Subgroup.center X)
    (hsec : ∀ a b c : X, IsTriangle Θ a b c → orderOf (a * c * b) = 4) {x : X} (hx : x ∈ Θ) :
    {v | v ∈ Θ ∧ Commute v x} = {y | ∃ q ∈ CFSG.pCore 2 X, q * x * q⁻¹ = y} := by
  ext v
  constructor
  · rintro ⟨hv, hvx⟩
    by_cases hvx' : v = x
    · exact ⟨1, Subgroup.one_mem _, by rw [hvx']; group⟩
    obtain ⟨y, hy, hxy⟩ := exists_not_commute hS hX' hQ hx
    have hvy : ¬ Commute v y := fun h => hxy (commute_trans hS hX' hx hy hv hvx.symm h.symm)
    have htri : IsTriangle Θ x y v := ⟨hx, hv, hy, fun h => hvx' h.symm, hvx.symm, hxy, hvy⟩
    have hno : ∀ z ∈ Θ, z ∈ Subgroup.closure {x, y} → IsTriangle Θ x z v →
        ¬ IsThirdKind x z v := by
      intro z _ _ hz hthird
      obtain ⟨n, hnodd, _, hord⟩ := hthird
      rw [hsec x z v hz] at hord
      obtain ⟨k, hk⟩ := hnodd
      omega
    obtain ⟨g, hg, hgx⟩ :=
      (OddTransp.secondKind_structure hS.oddT hS.normal htri (hsec x y v htri) hno).conj
    refine ⟨g, ?_, hgx⟩
    have hQX : conjClosure (Subgroup.closure {x, y}) (x * v) ≤ CFSG.pCore 2 X := by
      rw [conjClosure, Subgroup.closure_le]
      rintro _ ⟨h, -, rfl⟩
      exact CFSG.pCore_normal.conj_mem _ (mul_mem_pCore_of_commute hS hX' hx hv hvx.symm) h
    exact ((Subgroup.commutator_mono hQX le_rfl).trans (Subgroup.commutator_le_left _ _)) hg
  · rintro ⟨q, hq, rfl⟩
    refine ⟨hS.normal q x hx, ?_⟩
    apply commute_of_mul_mem_of_isPGroup hS.oddT CFSG.pCore_isPGroup (hS.normal q x hx) hx
    have : q * x * q⁻¹ * x = q * (x * q⁻¹ * x⁻¹) := by rw [hS.oddT.inv_eq hx]; group
    rw [this]
    exact Subgroup.mul_mem _ hq (CFSG.pCore_normal.conj_mem _ (Subgroup.inv_mem _ hq) x)

omit [Finite X] in
private theorem setOf_pCore_conj_conj (h x : X) :
    {y | ∃ q ∈ CFSG.pCore 2 X, q * (h * x * h⁻¹) * q⁻¹ = y} =
      (fun z => h * z * h⁻¹) '' {y | ∃ q ∈ CFSG.pCore 2 X, q * x * q⁻¹ = y} := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(h⁻¹ * q * h) * x * (h⁻¹ * q * h)⁻¹, ⟨h⁻¹ * q * h, ?_, rfl⟩, by group⟩
    simpa using CFSG.pCore_normal.conj_mem q hq h⁻¹
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨h * q * h⁻¹, CFSG.pCore_normal.conj_mem q hq h, by group⟩

omit [Finite X] in
private theorem ncard_pCore_conj_eq (hS : Setup X Θ) {x y : X} (hx : x ∈ Θ) (hy : y ∈ Θ) :
    {z | ∃ q ∈ CFSG.pCore 2 X, q * y * q⁻¹ = z}.ncard =
      {z | ∃ q ∈ CFSG.pCore 2 X, q * x * q⁻¹ = z}.ncard := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp (hS.isConj hx hy)
  rw [setOf_pCore_conj_conj]
  exact Set.ncard_image_of_injective _ fun a b hab => by simpa using hab

private theorem two_le_ncard_pCore_conj (hS : Setup X Θ)
    (hQ : ¬ CFSG.pCore 2 X ≤ Subgroup.center X) {x : X} (hx : x ∈ Θ) :
    2 ≤ {z | ∃ q ∈ CFSG.pCore 2 X, q * x * q⁻¹ = z}.ncard := by
  by_contra hlt
  have hfix : ∀ y ∈ Θ, ∀ q ∈ CFSG.pCore 2 X, q * y * q⁻¹ = y := by
    intro y hy q hq
    have hle : {z | ∃ q ∈ CFSG.pCore 2 X, q * y * q⁻¹ = z}.ncard ≤ 1 := by
      rw [ncard_pCore_conj_eq hS hx hy]
      omega
    exact (Set.ncard_le_one).mp hle _ ⟨q, hq, rfl⟩ _ ⟨1, Subgroup.one_mem _, by group⟩
  apply hQ
  intro q hq
  have hc : (⊤ : Subgroup X) ≤ Subgroup.centralizer {q} := by
    rw [← hS.gen, Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    calc y * q = q * y * q⁻¹ * q := by rw [hfix y hy q hq]
      _ = q * y := by group
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subgroup.mem_centralizer_singleton_iff.mp (hc (Subgroup.mem_top g))

private theorem inter_centralizer_eq (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index)
    (hQ : ¬ CFSG.pCore 2 X ≤ Subgroup.center X)
    (hsec : ∀ a b c : X, IsTriangle Θ a b c → orderOf (a * c * b) = 4) {a : X} (ha : a ∈ Θ) :
    Θ ∩ (Subgroup.centralizer {a} : Set X) = {y | ∃ q ∈ CFSG.pCore 2 X, q * a * q⁻¹ = y} := by
  rw [← setOf_commute_eq_conj hS hX' hQ hsec ha]
  ext v
  exact and_congr_right fun _ => Subgroup.mem_centralizer_singleton_iff

private theorem mul_self_eq_one_of_mem_commutator (hS : Setup X Θ) {a z : X} (ha : a ∈ Θ)
    (hz : z ∈ ⁅CFSG.pCore 2 X, Subgroup.zpowers a⁆) : z * z = 1 := by
  set T : Set X := {y | y ∈ Θ ∧ y * a ∈ CFSG.pCore 2 X} with hTdef
  have hT : ∀ y ∈ T, ∀ y' ∈ T, Commute y y' := by
    intro y hy y' hy'
    apply commute_of_mul_mem_of_isPGroup hS.oddT CFSG.pCore_isPGroup hy.1 hy'.1
    have e : y * y' = (y * a) * (y' * a)⁻¹ := by
      rw [mul_inv_rev, hS.oddT.inv_eq hy'.1]
      group
    rw [e]
    exact Subgroup.mul_mem _ hy.2 (Subgroup.inv_mem _ hy'.2)
  have hle : ⁅CFSG.pCore 2 X, Subgroup.zpowers a⁆ ≤ Subgroup.closure T := by
    rw [Subgroup.commutator_le]
    intro q hq x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, hS.oddT.orderOf_eq_two ha]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [Nat.cast_ofNat, h, zpow_zero, commutatorElement_one_right]
      exact Subgroup.one_mem _
    · rw [Nat.cast_ofNat, h, zpow_one, commutatorElement_def, hS.oddT.inv_eq ha]
      refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨hS.normal q a ha, ?_⟩)
        (Subgroup.subset_closure ⟨ha, by rw [hS.oddT.mul_self_eq_one ha]; exact Subgroup.one_mem _⟩)
      have : q * a * q⁻¹ * a = q * (a * q⁻¹ * a⁻¹) := by rw [hS.oddT.inv_eq ha]; group
      rw [this]
      exact Subgroup.mul_mem _ hq (CFSG.pCore_normal.conj_mem _ (Subgroup.inv_mem _ hq) a)
  have h1 : Subgroup.closure T ≤ Subgroup.centralizer T := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y' hy'
    exact (hT y' hy' y hy).eq
  have h2 : Subgroup.closure T ≤ Subgroup.centralizer (Subgroup.closure T : Set X) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (h1 hg) y hy).symm
  have hzT := hle hz
  clear hz
  induction hzT using Subgroup.closure_induction with
  | mem y hy => exact hS.oddT.mul_self_eq_one hy.1
  | one => exact mul_one 1
  | mul g h hg hh ihg ihh =>
    have hgh : g * h = h * g := Subgroup.mem_centralizer_iff.mp (h2 hh) g hg
    calc g * h * (g * h) = g * g * (h * h) := by
          rw [mul_assoc, ← mul_assoc h g, ← hgh]
          group
      _ = 1 := by rw [ihg, ihh, one_mul]
  | inv g hg ih => rw [← mul_inv_rev, ih, inv_one]

private theorem mk_eq_mk_iff (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index) {a b : X} (ha : a ∈ Θ) (hb : b ∈ Θ) :
    QuotientGroup.mk' (CFSG.pCore 2 X) a = QuotientGroup.mk' (CFSG.pCore 2 X) b ↔
      Commute a b := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hS.oddT.inv_eq ha]
  exact ⟨commute_of_mul_mem_of_isPGroup hS.oddT CFSG.pCore_isPGroup ha hb,
    mul_mem_pCore_of_commute hS hX' ha hb⟩

private theorem orderOf_mk_mul_mk (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index) {p : ℕ} (hpp : p.Prime)
    (hp : ∀ a ∈ Θ, ∀ b ∈ Θ, ¬ Commute a b → orderOf (a * b) = p) {a b : X} (ha : a ∈ Θ)
    (hb : b ∈ Θ) (hab : ¬ Commute a b) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) a * QuotientGroup.mk' (CFSG.pCore 2 X) b) = p := by
  have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) a *
      QuotientGroup.mk' (CFSG.pCore 2 X) b) ∣ p := by
    rw [← map_mul, ← hp a ha b hb hab]
    exact orderOf_map_dvd _ (a * b)
  rcases (Nat.dvd_prime hpp).mp hdvd with h1 | h1
  · refine absurd ((mk_eq_mk_iff hS hX' ha hb).mp ?_) hab
    rw [orderOf_eq_one_iff] at h1
    calc QuotientGroup.mk' (CFSG.pCore 2 X) a =
          QuotientGroup.mk' (CFSG.pCore 2 X) a * QuotientGroup.mk' (CFSG.pCore 2 X) b *
            QuotientGroup.mk' (CFSG.pCore 2 X) b := by
          rw [mul_assoc, ← map_mul, hS.oddT.mul_self_eq_one hb, map_one, mul_one]
      _ = QuotientGroup.mk' (CFSG.pCore 2 X) b := by rw [h1, one_mul]
  · exact h1

private theorem not_mem_pCore (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index)
    (hQ : ¬ CFSG.pCore 2 X ≤ Subgroup.center X) {x : X} (hx : x ∈ Θ) :
    x ∉ CFSG.pCore 2 X := by
  intro hxQ
  obtain ⟨y, hy, hxy⟩ := exists_not_commute hS hX' hQ hx
  obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj hx hy)
  exact hxy (commute_of_mul_mem_of_isPGroup hS.oddT CFSG.pCore_isPGroup hx hy
    (Subgroup.mul_mem _ hxQ (CFSG.pCore_normal.conj_mem x hxQ c)))

private theorem odd_card_commutator_quotient
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index) :
    Odd (Nat.card (commutator (X ⧸ CFSG.pCore 2 X))) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨o, ho⟩, hord⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
  rw [Subgroup.orderOf_mk] at hord
  have hmap : (commutator X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) =
      commutator (X ⧸ CFSG.pCore 2 X) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      commutator_def]
  rw [← hmap] at ho
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp ho
  have hc2 : c ^ 2 ∈ CFSG.pCore 2 X := by
    have h := pow_orderOf_eq_one (QuotientGroup.mk' (CFSG.pCore 2 X) c)
    rwa [hord, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) c = 1 :=
    (QuotientGroup.eq_one_iff c).mpr (mem_pCore_of_sq_mem hX' hc hc2)
  rw [h1, orderOf_one] at hord
  exact absurd hord (by norm_num)

omit [Finite X] in
private theorem commutator_sup_zpowers_eq_top (hS : Setup X Θ) {x : X} (hx : x ∈ Θ) :
    commutator (X ⧸ CFSG.pCore 2 X) ⊔
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 X) x) = ⊤ := by
  rw [eq_top_iff, ← image_closure_eq_top_quotient (CFSG.pCore 2 X) hS.gen, Subgroup.closure_le]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj hx hz)
  have e : QuotientGroup.mk' (CFSG.pCore 2 X) (c * x * c⁻¹) =
      ⁅QuotientGroup.mk' (CFSG.pCore 2 X) c, QuotientGroup.mk' (CFSG.pCore 2 X) x⁆ *
        QuotientGroup.mk' (CFSG.pCore 2 X) x := by
    rw [commutatorElement_def, map_mul, map_mul, map_inv]
    group
  rw [SetLike.mem_coe, e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  rw [commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

omit [Finite X] in
private theorem image_eq_setOf_isConj (hS : Setup X Θ) {x : X} (hx : x ∈ Θ) :
    QuotientGroup.mk' (CFSG.pCore 2 X) '' Θ =
      {y | IsConj (QuotientGroup.mk' (CFSG.pCore 2 X) x) y} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact MonoidHom.map_isConj _ (hS.isConj hx hz)
  · intro hy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hy
    obtain ⟨c', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) c
    exact ⟨c' * x * c'⁻¹, hS.normal c' x hx, by simp only [map_mul, map_inv]⟩

private theorem isPGroup_commutator_quotient (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index) {p : ℕ} (hpp : p.Prime)
    (hp : ∀ a ∈ Θ, ∀ b ∈ Θ, ¬ Commute a b → orderOf (a * b) = p) {x : X} (hx : x ∈ Θ) :
    IsPGroup p (commutator (X ⧸ CFSG.pCore 2 X)) := by
  have hx2 : QuotientGroup.mk' (CFSG.pCore 2 X) x * QuotientGroup.mk' (CFSG.pCore 2 X) x = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one hx, map_one]
  have hgen : Subgroup.closure {y | IsConj (QuotientGroup.mk' (CFSG.pCore 2 X) x) y} = ⊤ := by
    rw [← image_eq_setOf_isConj hS hx]
    exact image_closure_eq_top_quotient _ hS.gen
  have hodd := odd_card_commutator_quotient hX'
  refine isPGroup_of_forall_inverted hodd hx2 (commutator_sup_zpowers_eq_top hS hx) hgen hpp ?_
  intro o ho hinv
  obtain ⟨n, hn⟩ := CFSG.GH74.Uniqueness.exists_pow_conj_of_inverted
    (hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ho)) hinv hx2
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) (o ^ n)
  have hzΘ : c * x * c⁻¹ ∈ Θ := hS.normal c x hx
  have ho' : o = QuotientGroup.mk' (CFSG.pCore 2 X) (c * x * c⁻¹) *
      QuotientGroup.mk' (CFSG.pCore 2 X) x := by
    rw [map_mul, map_mul, map_inv, hc, ← hn, mul_assoc, hx2, mul_one]
  by_cases hcom : Commute (c * x * c⁻¹) x
  · left
    rw [ho', (mk_eq_mk_iff hS hX' hzΘ hx).mpr hcom, hx2]
  · right
    rw [ho']
    exact orderOf_mk_mul_mk hS hX' hpp hp hzΘ hx hcom

private theorem card_quotient_eq_two_mul (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index)
    (hQ : ¬ CFSG.pCore 2 X ≤ Subgroup.center X) {x : X} (hx : x ∈ Θ) :
    Nat.card (X ⧸ CFSG.pCore 2 X) = 2 * Nat.card (commutator (X ⧸ CFSG.pCore 2 X)) := by
  have hx1 : QuotientGroup.mk' (CFSG.pCore 2 X) x ≠ 1 := fun h =>
    not_mem_pCore hS hX' hQ hx ((QuotientGroup.eq_one_iff x).mp h)
  have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) x) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, hS.oddT.mul_self_eq_one hx, map_one]) hx1
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 X) x))
    (K := commutator (X ⧸ CFSG.pCore 2 X)) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  rw [sup_comm, commutator_sup_zpowers_eq_top hS hx, Subgroup.card_top, Nat.card_zpowers,
    hord] at h
  have hinf : Nat.card (Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 X) x) ⊓
      commutator (X ⧸ CFSG.pCore 2 X) : Subgroup _) = 1 := by
    have h2 := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers
      (QuotientGroup.mk' (CFSG.pCore 2 X) x) ⊓ commutator (X ⧸ CFSG.pCore 2 X) ≤ _)
    rw [Nat.card_zpowers, hord] at h2
    have hodd := (odd_card_commutator_quotient hX').of_dvd_nat (Subgroup.card_dvd_of_le
      (inf_le_right : Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 X) x) ⊓
        commutator (X ⧸ CFSG.pCore 2 X) ≤ _))
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h' | h'
    · exact h'
    · rw [h'] at hodd
      exact absurd hodd (by decide)
  rw [hinf, mul_one] at h
  exact h

private theorem ncard_image_dvd_card_commutator (hS : Setup X Θ) {x : X} (hx : x ∈ Θ) :
    (QuotientGroup.mk' (CFSG.pCore 2 X) '' Θ).ncard ∣
      Nat.card (commutator (X ⧸ CFSG.pCore 2 X)) := by
  have heq : QuotientGroup.mk' (CFSG.pCore 2 X) '' Θ =
      {z | ∃ g ∈ commutator (X ⧸ CFSG.pCore 2 X),
        g * QuotientGroup.mk' (CFSG.pCore 2 X) x * g⁻¹ = z} := by
    rw [image_eq_setOf_isConj hS hx]
    ext z
    constructor
    · intro hz
      obtain ⟨c, rfl⟩ := isConj_iff.mp hz
      have hmem : c ∈ ((commutator (X ⧸ CFSG.pCore 2 X) ⊔
          Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 X) x) : Subgroup _) : Set _) := by
        rw [commutator_sup_zpowers_eq_top hS hx]
        trivial
      rw [Subgroup.normal_mul] at hmem
      obtain ⟨o, ho, w, hw, rfl⟩ := Set.mem_mul.mp hmem
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact ⟨o, ho, by group⟩
    · rintro ⟨g, -, rfl⟩
      exact isConj_iff.mpr ⟨g, rfl⟩
  rw [heq]
  exact ncard_conj_dvd _ _

private theorem ncard_eq_ncard_image_mul_ncard (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index)
    (hQ : ¬ CFSG.pCore 2 X ≤ Subgroup.center X)
    (hsec : ∀ a b c : X, IsTriangle Θ a b c → orderOf (a * c * b) = 4) {x : X} (hx : x ∈ Θ) :
    Θ.ncard = (QuotientGroup.mk' (CFSG.pCore 2 X) '' Θ).ncard *
      {z | ∃ q ∈ CFSG.pCore 2 X, q * x * q⁻¹ = z}.ncard := by
  refine ncard_eq_ncard_image_mul fun y hy => ?_
  have : {v | v ∈ Θ ∧ QuotientGroup.mk' (CFSG.pCore 2 X) v =
      QuotientGroup.mk' (CFSG.pCore 2 X) y} = {v | v ∈ Θ ∧ Commute v y} := by
    ext v
    exact and_congr_right fun hv => mk_eq_mk_iff hS hX' hv hy
  rw [this, setOf_commute_eq_conj hS hX' hQ hsec hy, ncard_pCore_conj_eq hS hx hy]

private theorem ncard_le_ncard_image_of_pairwise (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index) {S : Set X} (hSΘ : S ⊆ Θ)
    (hS' : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ Commute a b) :
    S.ncard ≤ (QuotientGroup.mk' (CFSG.pCore 2 X) '' Θ).ncard :=
  Set.ncard_le_ncard_of_injOn _ (fun a ha => ⟨a, hSΘ ha, rfl⟩) fun a ha b hb hab =>
    by_contra fun hne => hS' a ha b hb hne ((mk_eq_mk_iff hS hX' (hSΘ ha) (hSΘ hb)).mp hab)

private theorem pCore_sup_closure_eq_top (hS : Setup X Θ) {p : ℕ}
    (hp : ∀ a ∈ Θ, ∀ b ∈ Θ, ¬ Commute a b → orderOf (a * b) = p) {a b : X} (ha : a ∈ Θ)
    (hb : b ∈ Θ) (hab : ¬ Commute a b)
    (hq : (QuotientGroup.mk' (CFSG.pCore 2 X) '' Θ).ncard = p) :
    CFSG.pCore 2 X ⊔ Subgroup.closure {a, b} = ⊤ := by
  have ha2 := hS.oddT.mul_self_eq_one ha
  have hb2 := hS.oddT.mul_self_eq_one hb
  have hodd : Odd (orderOf (a * b)) := hS.oddT.odd_of_not_commute ha hb hab
  have hrΘ : ∀ i : ℕ, (a * b) ^ i * a ∈ Θ := by
    intro i
    obtain ⟨j, hj⟩ := OddTransp.exists_zpow_conj_eq ha2 hb2 hodd i
    rw [← zpow_natCast, ← hj]
    exact hS.normal _ a ha
  have hrcl : ∀ i : ℕ, (a * b) ^ i * a ∈ Subgroup.closure {a, b} := fun i =>
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) i) (Subgroup.subset_closure (by simp))
  have hinj : Set.InjOn (fun i : ℕ => QuotientGroup.mk' (CFSG.pCore 2 X) ((a * b) ^ i * a))
      (Finset.range p : Set ℕ) := by
    intro i hi j hj hij
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq, hS.oddT.inv_eq (hrΘ i)] at hij
    have hmem : (a * b) ^ i * a * ((a * b) ^ j * a) ∈
        Subgroup.closure {a, b} ⊓ CFSG.pCore 2 X :=
      ⟨Subgroup.mul_mem _ (hrcl i) (hrcl j), hij⟩
    rw [inf_closure_pair_eq_bot hS CFSG.pCore_normal CFSG.pCore_isPGroup ha hb hab,
      Subgroup.mem_bot] at hmem
    have h2 : (a * b) ^ i = (a * b) ^ j := mul_right_cancel (hS.oddT.eq_of_mul_eq_one (hrΘ i) hmem)
    rw [pow_inj_mod, hp a ha b hb hab] at h2
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h2
  have himg : (fun i : ℕ => QuotientGroup.mk' (CFSG.pCore 2 X) ((a * b) ^ i * a)) ''
      (Finset.range p : Set ℕ) = QuotientGroup.mk' (CFSG.pCore 2 X) '' Θ := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · rintro _ ⟨i, -, rfl⟩
      exact ⟨_, hrΘ i, rfl⟩
    · rw [hq, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]
  rw [eq_top_iff, ← hS.gen, Subgroup.closure_le]
  intro z hz
  obtain ⟨i, -, hi⟩ : QuotientGroup.mk' (CFSG.pCore 2 X) z ∈
      (fun i : ℕ => QuotientGroup.mk' (CFSG.pCore 2 X) ((a * b) ^ i * a)) ''
        (Finset.range p : Set ℕ) := himg ▸ ⟨z, hz, rfl⟩
  simp only [QuotientGroup.mk'_apply, QuotientGroup.eq] at hi
  have e : z = (a * b) ^ i * a * (((a * b) ^ i * a)⁻¹ * z) := by group
  rw [SetLike.mem_coe, e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hrcl i)) (Subgroup.mem_sup_left hi)

private theorem card_quotient_le (hS : Setup X Θ)
    (hX' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index) {p : ℕ} (hpp : p.Prime)
    (hp : ∀ a ∈ Θ, ∀ b ∈ Θ, ¬ Commute a b → orderOf (a * b) = p) {a b : X} (ha : a ∈ Θ)
    (hb : b ∈ Θ) (hab : ¬ Commute a b) (htop : CFSG.pCore 2 X ⊔ Subgroup.closure {a, b} = ⊤) :
    Nat.card (X ⧸ CFSG.pCore 2 X) ≤ 2 * p := by
  have hcl : Subgroup.closure ({QuotientGroup.mk' (CFSG.pCore 2 X) a,
      QuotientGroup.mk' (CFSG.pCore 2 X) b} : Set (X ⧸ CFSG.pCore 2 X)) = ⊤ := by
    rw [← Set.image_pair, ← MonoidHom.map_closure, eq_top_iff,
      ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (CFSG.pCore 2 X)), ← htop,
      Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have ha2 : QuotientGroup.mk' (CFSG.pCore 2 X) a * QuotientGroup.mk' (CFSG.pCore 2 X) a = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one ha, map_one]
  have hb2 : QuotientGroup.mk' (CFSG.pCore 2 X) b * QuotientGroup.mk' (CFSG.pCore 2 X) b = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one hb, map_one]
  set c := QuotientGroup.mk' (CFSG.pCore 2 X) a * QuotientGroup.mk' (CFSG.pCore 2 X) b with hc
  have hsub : (Set.univ : Set (X ⧸ CFSG.pCore 2 X)) ⊆ (Subgroup.zpowers c : Set _) ∪
      (fun g => g * QuotientGroup.mk' (CFSG.pCore 2 X) a) '' (Subgroup.zpowers c : Set _) := by
    intro g _
    obtain ⟨k, hk | hk⟩ := closure_pair_normal_form ha2 hb2 (hcl ▸ Subgroup.mem_top g)
    · exact Or.inl (Subgroup.mem_zpowers_iff.mpr ⟨k, hk.symm⟩)
    · exact Or.inr ⟨c ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩, hk.symm⟩
  have hle := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  rw [Set.ncard_univ, Set.ncard_image_of_injective _ (mul_left_injective _),
    ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_zpowers,
    orderOf_mk_mul_mk hS hX' hpp hp ha hb hab] at hle
  omega

end Local

section Transport

variable {G : Type} [Group G] {D : Set G}

private theorem commSet_inter_conj (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (g a b : G) :
    commSet D (g * a * g⁻¹) ∩ commSet D (g * b * g⁻¹) = cimg g (commSet D a ∩ commSet D b) := by
  rw [commSet_conj hN, commSet_conj hN, cimg, cimg, cimg,
    Set.image_inter fun x y hxy => by simpa using hxy]

private theorem ncard_commSet_inter_conj (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D)
    (g a b : G) : (commSet D (g * a * g⁻¹) ∩ commSet D (g * b * g⁻¹)).ncard =
      (commSet D a ∩ commSet D b).ncard := by
  rw [commSet_inter_conj hN]
  exact Set.ncard_image_of_injective _ fun x y hxy => by simpa using hxy

private theorem ncard_commSet_conj (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (g a : G) :
    (commSet D (g * a * g⁻¹)).ncard = (commSet D a).ncard := by
  rw [commSet_conj hN]
  exact Set.ncard_image_of_injective _ fun x y hxy => by simpa using hxy

private theorem commute_trans_conj (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) {a : G}
    (hK : ∀ b ∈ commSet D a, ∀ c ∈ commSet D a, ∀ v ∈ commSet D a, Commute b v → Commute c v →
      Commute b c) (g : G) :
    ∀ b ∈ commSet D (g * a * g⁻¹), ∀ c ∈ commSet D (g * a * g⁻¹),
      ∀ v ∈ commSet D (g * a * g⁻¹), Commute b v → Commute c v → Commute b c := by
  intro b hb c hc v hv hbv hcv
  rw [commSet_conj hN, mem_cimg] at hb hc hv
  have hbv' : Commute (g⁻¹ * b * g) (g⁻¹ * v * g) := by
    simpa using (Commute.conj_iff g⁻¹).mpr hbv
  have hcv' : Commute (g⁻¹ * c * g) (g⁻¹ * v * g) := by
    simpa using (Commute.conj_iff g⁻¹).mpr hcv
  have h : Commute (g⁻¹ * b * g⁻¹⁻¹) (g⁻¹ * c * g⁻¹⁻¹) := by
    simpa using hK _ hb _ hc _ hv hbv' hcv'
  exact (Commute.conj_iff g⁻¹).mp h

end Transport

section Global

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem DalphaStar_eq_commSet_of_alpha_eq (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) :
    DalphaStar D hC.alpha = commSet D hC.d := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxD, hxu⟩ := hC.DalphaStar_subset_commute hx
    have hxE : x ∈ hC.E := by rwa [hC.DalphaStar_alpha] at hx
    exact ⟨hxD, hxu, (OddLocal.subset_commSet hC.setup.normal hC.hE hxE).2.2⟩
  · rintro ⟨hxD, hxu, hne⟩
    rcases (Set.ext_iff.mp hC.eq_alpha_union x).mp hxD with (h | h) | h
    · rw [hα] at h
      exact absurd h hne
    · exact h
    · rw [hC.AalphaStar_eq_diff_alpha] at h
      exact absurd hxu h.1.2

theorem AalphaStar_eq_of_alpha_eq (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) :
    AalphaStar D hC.alpha = {y | y ∈ D ∧ ¬ Commute y hC.d} := by
  rw [hC.AalphaStar_eq_diff_alpha, hα]
  ext y
  simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, fun hy => h.2 (hy ▸ Commute.refl _)⟩⟩

private theorem setup_DstarH (hC : HypothesisC D) : Setup (Halpha D hC.alpha) (DstarH hC) :=
  ⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩

omit [Finite G] in
private theorem commute_coe_iff {K : Subgroup G} {a b : K} : Commute (a : G) b ↔ Commute a b :=
  ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

private theorem mem_Halpha_of_mem_commSet (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) {x : G}
    (hx : x ∈ commSet D hC.d) : x ∈ Halpha D hC.alpha :=
  Subgroup.subset_closure ((DalphaStar_eq_commSet_of_alpha_eq hC hα).symm ▸ hx)

private theorem mem_DstarH_of_mem_commSet (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    {x : Halpha D hC.alpha} (hx : (x : G) ∈ commSet D hC.d) : x ∈ DstarH hC := by
  rw [mem_DstarH_iff, DalphaStar_eq_commSet_of_alpha_eq hC hα]
  exact hx

private theorem coe_mem_commSet_of_mem_DstarH (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    {x : Halpha D hC.alpha} (hx : x ∈ DstarH hC) : (x : G) ∈ commSet D hC.d := by
  rw [← DalphaStar_eq_commSet_of_alpha_eq hC hα]
  exact hx

private theorem image_val_DstarH (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) :
    Subtype.val '' DstarH hC = commSet D hC.d := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact coe_mem_commSet_of_mem_DstarH hC hα hy
  · intro hx
    exact ⟨⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩, mem_DstarH_of_mem_commSet hC hα hx, rfl⟩

private theorem orderOf_mul_DstarH (hC : HypothesisC D) {p : ℕ}
    (hp : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p) :
    ∀ a ∈ DstarH hC, ∀ b ∈ DstarH hC, ¬ Commute a b → orderOf (a * b) = p := by
  intro a ha b hb hab
  rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
  exact hp _ (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp ha)) _
    (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hb))
    fun h => hab (commute_coe_iff.mp h)

private theorem secondKind_DstarH (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4) :
    ∀ a b c : Halpha D hC.alpha, IsTriangle (DstarH hC) a b c → orderOf (a * c * b) = 4 := by
  rintro a b c ⟨ha, hc, hb, hac, hcomm, hab, hcb⟩
  have hD : ∀ {x : Halpha D hC.alpha}, x ∈ DstarH hC → (x : G) ∈ D := fun hx =>
    DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hx)
  have h := hsecond a b c ⟨hD ha, hD hc, hD hb, fun h => hac (Subtype.ext h),
    commute_coe_iff.mpr hcomm, fun h => hab (commute_coe_iff.mp h),
    fun h => hcb (commute_coe_iff.mp h)⟩
  rwa [← Subgroup.coe_mul, ← Subgroup.coe_mul, Subgroup.orderOf_coe] at h

omit [Finite G] in
private theorem setOf_map_conj_eq_image {K : Subgroup G} (P : Subgroup K) (v : K) :
    {y | ∃ q ∈ P.map K.subtype, q * (v : G) * q⁻¹ = y} =
      Subtype.val '' {y | ∃ q ∈ P, q * v * q⁻¹ = y} := by
  ext y
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q * v * q⁻¹, ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, ⟨q, hq, rfl⟩, rfl⟩

theorem commute_of_commute_of_mem_commSet (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index) :
    ∀ a ∈ commSet D hC.d, ∀ b ∈ commSet D hC.d, ∀ v ∈ commSet D hC.d,
      Commute a v → Commute b v → Commute a b := by
  intro a ha b hb v hv hav hbv
  have h := commute_trans (setup_DstarH hC) hH'
    (mem_DstarH_of_mem_commSet (x := ⟨a, mem_Halpha_of_mem_commSet hC hα ha⟩) hC hα ha)
    (mem_DstarH_of_mem_commSet (x := ⟨b, mem_Halpha_of_mem_commSet hC hα hb⟩) hC hα hb)
    (mem_DstarH_of_mem_commSet (x := ⟨v, mem_Halpha_of_mem_commSet hC hα hv⟩) hC hα hv)
    (commute_coe_iff.mp hav) (commute_coe_iff.mp hbv)
  exact commute_coe_iff.mpr h

theorem setOf_commute_eq_pCore_conj (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hα : hC.alpha = {hC.d})
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index)
    (hQ : ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha))
    {v : G} (hv : v ∈ commSet D hC.d) :
    {c | c ∈ commSet D hC.d ∧ Commute c v} =
      {y | ∃ q ∈ (CFSG.pCore 2 ↥(Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
        q * v * q⁻¹ = y} := by
  set v' : Halpha D hC.alpha := ⟨v, mem_Halpha_of_mem_commSet hC hα hv⟩
  have hX := setOf_commute_eq_conj (setup_DstarH hC) hH' hQ (secondKind_DstarH hC hsecond)
    (mem_DstarH_of_mem_commSet (x := v') hC hα hv)
  have h1 : {c | c ∈ commSet D hC.d ∧ Commute c v} =
      Subtype.val '' {c | c ∈ DstarH hC ∧ Commute c v'} := by
    ext c
    constructor
    · rintro ⟨hc, hcv⟩
      exact ⟨⟨c, mem_Halpha_of_mem_commSet hC hα hc⟩,
        ⟨mem_DstarH_of_mem_commSet hC hα hc, commute_coe_iff.mp hcv⟩, rfl⟩
    · rintro ⟨c, ⟨hc, hcv⟩, rfl⟩
      exact ⟨coe_mem_commSet_of_mem_DstarH hC hα hc, commute_coe_iff.mpr hcv⟩
  rw [h1, hX]
  exact (setOf_map_conj_eq_image _ v').symm

theorem not_commute_of_mem_commSet_inter (hC : HypothesisC D)
    (hα : hC.alpha = {hC.d})
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index) :
    ∀ w ∈ D, ¬ Commute w hC.d → ∀ r ∈ commSet D hC.d ∩ commSet D w,
      ∀ r' ∈ commSet D hC.d ∩ commSet D w, r ≠ r' → ¬ Commute r r' := by
  intro w hw hwu r hr r' hr' hne hcomm
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hr'.1.1)
  have hK := commute_trans_conj hC.setup.normal (commute_of_commute_of_mem_commSet hC hα hH') g
  have hu : hC.d ∈ commSet D (g * hC.d * g⁻¹) :=
    ⟨hC.hd, hr'.1.2.1.symm, fun h => hr'.1.2.2 h.symm⟩
  have hwr : w ∈ commSet D (g * hC.d * g⁻¹) := ⟨hw, hr'.2.2.1.symm, fun h => hr'.2.2.2 h.symm⟩
  have hrr : r ∈ commSet D (g * hC.d * g⁻¹) := ⟨hr.1.1, hcomm, hne⟩
  exact hwu (hK w hwr _ hu r hrr hr.2.2.1.symm hr.1.2.1.symm)

private theorem ncard_eq_one_add_add (hC : HypothesisC D) :
    D.ncard = 1 + (commSet D hC.d).ncard + {y | y ∈ D ∧ ¬ Commute y hC.d}.ncard := by
  have hD : D = insert hC.d (commSet D hC.d ∪ {y | y ∈ D ∧ ¬ Commute y hC.d}) := by
    ext x
    constructor
    · intro hx
      by_cases hxu : x = hC.d
      · exact Or.inl hxu
      · by_cases hc : Commute x hC.d
        · exact Or.inr (Or.inl ⟨hx, hc, hxu⟩)
        · exact Or.inr (Or.inr ⟨hx, hc⟩)
    · rintro (rfl | ⟨hx, -⟩ | ⟨hx, -⟩)
      · exact hC.hd
      · exact hx
      · exact hx
  have hnot : hC.d ∉ commSet D hC.d ∪ {y | y ∈ D ∧ ¬ Commute y hC.d} := by
    rintro (⟨-, -, h⟩ | ⟨-, h⟩)
    · exact h rfl
    · exact h (Commute.refl _)
  have hdisj : Disjoint (commSet D hC.d) {y | y ∈ D ∧ ¬ Commute y hC.d} :=
    Set.disjoint_left.mpr fun x hx hx' => hx'.2 hx.2.1
  have h := congrArg Set.ncard hD
  rw [Set.ncard_insert_of_notMem hnot, Set.ncard_union_eq hdisj] at h
  omega

omit [Finite G] in
private theorem conj_mem_commSet (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) {a b g : G}
    (hg : g * a = a * g) (hb : b ∈ commSet D a) : g * b * g⁻¹ ∈ commSet D a := by
  have hga : g * a * g⁻¹ = a := by rw [hg, mul_inv_cancel_right]
  have h := commSet_conj hN g a
  rw [hga] at h
  rw [h]
  exact ⟨b, hb, rfl⟩

omit [Finite G] in
private theorem mem_centralizer_of_mem_cenGen {u g : G}
    (hg : g ∈ Subgroup.closure ((D : Set G) ∩ Subgroup.centralizer ({u} : Set G))) :
    g * u = u * g :=
  Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.closure_le _).mpr (fun _ hy => hy.2) hg)

private theorem ncard_commSet_inter_eq (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hα : hC.alpha = {hC.d}) {w w' : G} (hw : w ∈ D) (hwu : ¬ Commute w hC.d) (hw' : w' ∈ D)
    (hw'u : ¬ Commute w' hC.d) :
    (commSet D hC.d ∩ commSet D w').ncard = (commSet D hC.d ∩ commSet D w).ncard := by
  have hA := AalphaStar_eq_of_alpha_eq hC hα
  obtain ⟨x, hx, rfl⟩ := cenGen_transitive_AalphaStar_unconditional hC hsecond w
    (by rw [hA]; exact ⟨hw, hwu⟩) w' (by rw [hA]; exact ⟨hw', hw'u⟩)
  have hxu : x * hC.d * x⁻¹ = hC.d := by
    rw [mem_centralizer_of_mem_cenGen hx, mul_inv_cancel_right]
  conv_lhs => rw [← hxu]
  exact ncard_commSet_inter_conj hC.setup.normal x hC.d w

omit [Finite G] in
private theorem commSet_inter_eq_diff {u v : G} :
    commSet D u ∩ commSet D v = {c | c ∈ commSet D u ∧ Commute c v} \ {v} := by
  ext c
  constructor
  · rintro ⟨hc, -, hcv, hne⟩
    exact ⟨⟨hc, hcv⟩, hne⟩
  · rintro ⟨⟨hc, hcv⟩, hne⟩
    exact ⟨hc, hc.1, hcv, hne⟩

omit [Finite G] in
private theorem ncard_commSet_inter_of_mem {u v : G} {m : ℕ} (hv : v ∈ commSet D u)
    (hm : {c | c ∈ commSet D u ∧ Commute c v}.ncard = m) :
    (commSet D u ∩ commSet D v).ncard = m - 1 := by
  rw [commSet_inter_eq_diff, Set.ncard_sdiff_singleton_of_mem
    (show v ∈ {c | c ∈ commSet D u ∧ Commute c v} from ⟨hv, Commute.refl v⟩), hm]

omit [Finite G] in
private theorem ncard_commSet_eq (hC : HypothesisC D) {x : G} (hx : x ∈ D) :
    (commSet D x).ncard = (commSet D hC.d).ncard := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hx)
  exact ncard_commSet_conj hC.setup.normal g hC.d

private theorem ncard_not_commute_inter (hC : HypothesisC D) {m : ℕ} (hm : 1 ≤ m) {v : G}
    (hv : v ∈ commSet D hC.d) (hlam : (commSet D hC.d ∩ commSet D v).ncard = m - 1) :
    {w | w ∈ {y | y ∈ D ∧ ¬ Commute y hC.d} ∧ Commute v w}.ncard =
      (commSet D hC.d).ncard - m := by
  have heq : {w | w ∈ {y | y ∈ D ∧ ¬ Commute y hC.d} ∧ Commute v w} =
      commSet D v \ insert hC.d (commSet D hC.d ∩ commSet D v) := by
    ext w
    constructor
    · rintro ⟨⟨hwD, hwu⟩, hvw⟩
      refine ⟨⟨hwD, hvw.symm, fun h => hwu (h ▸ hv.2.1)⟩, ?_⟩
      rintro (rfl | ⟨hw, -⟩)
      · exact hwu (Commute.refl _)
      · exact hwu hw.2.1
    · rintro ⟨⟨hwD, hwv, hne⟩, hnot⟩
      refine ⟨⟨hwD, fun hwu => hnot ?_⟩, hwv.symm⟩
      by_cases hwu' : w = hC.d
      · exact Or.inl hwu'
      · exact Or.inr ⟨⟨hwD, hwu, hwu'⟩, ⟨hwD, hwv, hne⟩⟩
  have hsub : insert hC.d (commSet D hC.d ∩ commSet D v) ⊆ commSet D v := by
    rintro x (rfl | ⟨-, hx⟩)
    · exact ⟨hC.hd, hv.2.1.symm, fun h => hv.2.2 h.symm⟩
    · exact hx
  have hnot : hC.d ∉ commSet D hC.d ∩ commSet D v := fun h => h.1.2.2 rfl
  rw [heq, Set.ncard_diff hsub, Set.ncard_insert_of_notMem hnot, hlam,
    ncard_commSet_eq hC hv.1]
  omega

private theorem ncard_mul_eq_ncard_mul {S T : Set G} {a b : ℕ}
    (hS : ∀ v ∈ S, {w | w ∈ T ∧ Commute v w}.ncard = a)
    (hT : ∀ w ∈ T, {v | v ∈ S ∧ Commute v w}.ncard = b) : S.ncard * a = T.ncard * b := by
  classical
  have := Fintype.ofFinite G
  rw [Set.ncard_eq_toFinset_card' S, Set.ncard_eq_toFinset_card' T]
  refine Finset.card_mul_eq_card_mul (fun v w => Commute v w) (fun v hv => ?_) (fun w hw => ?_)
  · rw [← hS v (Set.mem_toFinset.mp hv), ← Set.ncard_coe_finset]
    congr 1
    ext w
    simp [Finset.bipartiteAbove]
  · rw [← hT w (Set.mem_toFinset.mp hw), ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp [Finset.bipartiteBelow]

omit [Finite G] in
private theorem setOf_commute_eq_inter {u w : G} (hwu : ¬ Commute w u) :
    {v | v ∈ commSet D u ∧ Commute v w} = commSet D u ∩ commSet D w := by
  ext v
  constructor
  · rintro ⟨hv, hvw⟩
    exact ⟨hv, hv.1, hvw, fun h => hwu (h ▸ hv.2.1)⟩
  · rintro ⟨hv, -, hvw, -⟩
    exact ⟨hv, hvw⟩

private theorem ncard_not_commute_dvd (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hα : hC.alpha = {hC.d}) {w : G} (hw : w ∈ D) (hwu : ¬ Commute w hC.d) :
    {y | y ∈ D ∧ ¬ Commute y hC.d}.ncard ∣ 2 * Nat.card (Halpha D hC.alpha) := by
  set K := Subgroup.closure ((D : Set G) ∩ Subgroup.centralizer ({hC.d} : Set G)) with hK
  have hA := AalphaStar_eq_of_alpha_eq hC hα
  have horb : {y | y ∈ D ∧ ¬ Commute y hC.d} = {z | ∃ g ∈ K, g * w * g⁻¹ = z} := by
    ext z
    constructor
    · intro hz
      exact cenGen_transitive_AalphaStar_unconditional hC hsecond w
        (by rw [hA]; exact ⟨hw, hwu⟩) z (by rw [hA]; exact hz)
    · rintro ⟨g, hg, rfl⟩
      refine ⟨hC.setup.normal g w hw, fun h => hwu ?_⟩
      have hgu : g * hC.d * g⁻¹ = hC.d := by
        rw [mem_centralizer_of_mem_cenGen hg, mul_inv_cancel_right]
      rw [← hgu] at h
      exact (Commute.conj_iff g).mp h
  have hset : ((D : Set G) ∩ Subgroup.centralizer ({hC.d} : Set G)) =
      {hC.d} ∪ commSet D hC.d := by
    ext x
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff,
      Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxu⟩
      by_cases h : x = hC.d
      · exact Or.inl h
      · exact Or.inr ⟨hx, hxu, h⟩
    · rintro (rfl | ⟨hx, hxu, -⟩)
      · exact ⟨hC.hd, rfl⟩
      · exact ⟨hx, hxu⟩
  have hKH : K = Subgroup.zpowers hC.d ⊔ Halpha D hC.alpha := by
    rw [hK, hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, Halpha,
      DalphaStar_eq_commSet_of_alpha_eq hC hα]
  have hHu : Halpha D hC.alpha ≤ Subgroup.centralizer {hC.d} := by
    rw [Halpha, DalphaStar_eq_commSet_of_alpha_eq hC hα, Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr hx.2.1
  have hu : hC.d ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hHu hh)
  have hcard := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hu))
  rw [Nat.card_zpowers, hC.setup.oddT.orderOf_eq_two hC.hd, ← hKH] at hcard
  rw [horb]
  exact (ncard_conj_dvd K w).trans (Dvd.intro _ hcard)

private theorem ncard_commSet_inter_dvd (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index) {w : G} (hw : w ∈ D)
    (hwu : ¬ Commute w hC.d) {e : G} (he : e ∈ commSet D hC.d ∩ commSet D w) :
    (commSet D hC.d ∩ commSet D w).ncard ∣ Nat.card (Halpha D hC.alpha) := by
  set S := commSet D hC.d ∩ commSet D w with hSdef
  set Y := Subgroup.closure S with hY
  have hYH : Y ≤ Halpha D hC.alpha := by
    rw [hY, Subgroup.closure_le]
    intro x hx
    exact mem_Halpha_of_mem_commSet hC hα hx.1
  have hYc : ∀ g ∈ Y, g * hC.d = hC.d * g ∧ g * w = w * g := by
    intro g hg
    have : Y ≤ Subgroup.centralizer {hC.d} ⊓ Subgroup.centralizer {w} := by
      rw [hY, Subgroup.closure_le]
      intro x hx
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hx.1.2.1,
        Subgroup.mem_centralizer_singleton_iff.mpr hx.2.2.1⟩
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mp (this hg).1,
      Subgroup.mem_centralizer_singleton_iff.mp (this hg).2⟩
  have horb : S = {z | ∃ g ∈ Y, g * e * g⁻¹ = z} := by
    ext z
    constructor
    · intro hz
      by_cases hze : z = e
      · exact ⟨1, Subgroup.one_mem _, by rw [hze]; group⟩
      · obtain ⟨g, hg, hgz⟩ := hC.setup.oddT.exists_conj he.1.1 hz.1.1
          (not_commute_of_mem_commSet_inter hC hα hH' w hw hwu e he z hz (Ne.symm hze))
        refine ⟨g, (Subgroup.closure_mono ?_) hg, hgz⟩
        rintro x (rfl | rfl)
        · exact he
        · exact hz
    · rintro ⟨g, hg, rfl⟩
      exact ⟨conj_mem_commSet hC.setup.normal (hYc g hg).1 he.1,
        conj_mem_commSet hC.setup.normal (hYc g hg).2 he.2⟩
  rw [horb]
  exact (ncard_conj_dvd Y e).trans (Subgroup.card_dvd_of_le hYH)

private theorem ncard_setOf_commute_eq (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hα : hC.alpha = {hC.d})
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index)
    (hQ : ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha))
    {x₀ : Halpha D hC.alpha} (hx₀ : x₀ ∈ DstarH hC) {v : G} (hv : v ∈ commSet D hC.d) :
    {c | c ∈ commSet D hC.d ∧ Commute c v}.ncard =
      {z | ∃ q ∈ CFSG.pCore 2 ↥(Halpha D hC.alpha), q * x₀ * q⁻¹ = z}.ncard := by
  rw [setOf_commute_eq_pCore_conj hC hsecond hα hH' hQ hv,
    show {y | ∃ q ∈ (CFSG.pCore 2 ↥(Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
        q * v * q⁻¹ = y} = Subtype.val '' {y | ∃ q ∈ CFSG.pCore 2 ↥(Halpha D hC.alpha),
          q * (⟨v, mem_Halpha_of_mem_commSet hC hα hv⟩ : Halpha D hC.alpha) * q⁻¹ = y} from
      setOf_map_conj_eq_image (CFSG.pCore 2 ↥(Halpha D hC.alpha))
        ⟨v, mem_Halpha_of_mem_commSet hC hα hv⟩,
    Set.ncard_image_of_injective _ Subtype.val_injective]
  exact ncard_pCore_conj_eq (setup_DstarH hC) hx₀ (mem_DstarH_of_mem_commSet hC hα hv)

omit [Finite G] in
private theorem exists_not_commute_u (hC : HypothesisC D) {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (hxy : ¬ Commute x y) : ∃ w ∈ D, ¬ Commute w hC.d := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hx)
  refine ⟨g⁻¹ * y * g, by simpa using hC.setup.normal g⁻¹ y hy, fun h => hxy ?_⟩
  have h' := (Commute.conj_iff g).mpr h
  rw [hg, show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h'
  exact h'.symm

private theorem ncard_le_of_pairwise_not_commute (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index) {S : Set G}
    (hS : S ⊆ commSet D hC.d) (hS' : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ Commute a b) :
    S.ncard ≤ (QuotientGroup.mk' (CFSG.pCore 2 ↥(Halpha D hC.alpha)) '' DstarH hC).ncard := by
  have himg : Subtype.val '' (Subtype.val ⁻¹' S : Set (Halpha D hC.alpha)) = S :=
    Set.image_preimage_eq_of_subset fun x hx => ⟨⟨x, mem_Halpha_of_mem_commSet hC hα (hS hx)⟩, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  exact ncard_le_ncard_image_of_pairwise (setup_DstarH hC) hH'
    (fun x hx => mem_DstarH_of_mem_commSet hC hα (hS hx))
    fun a ha b hb hab hc => hS' a ha b hb (fun h => hab (Subtype.ext h)) (commute_coe_iff.mpr hc)

private theorem le_ncard_commSet_inter (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index) {p : ℕ}
    (hp : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p) {w : G} (hw : w ∈ D)
    (hwu : ¬ Commute w hC.d) {e e' : G} (he : e ∈ commSet D hC.d ∩ commSet D w)
    (he' : e' ∈ commSet D hC.d ∩ commSet D w) (hne : e ≠ e') :
    p ≤ (commSet D hC.d ∩ commSet D w).ncard := by
  have hnc := not_commute_of_mem_commSet_inter hC hα hH' w hw hwu e he e' he' hne
  have hD := hC.setup.oddT
  have hord : orderOf (e * e') = p := hp e he.1.1 e' he'.1.1 hnc
  have hcl : Subgroup.closure ({e, e'} : Set G) ≤
      Subgroup.centralizer {hC.d} ⊓ Subgroup.centralizer {w} := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr he.1.2.1,
        Subgroup.mem_centralizer_singleton_iff.mpr he.2.2.1⟩
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr he'.1.2.1,
        Subgroup.mem_centralizer_singleton_iff.mpr he'.2.2.1⟩
  have hmem : ∀ i : ℕ, (e * e') ^ i * e ∈ commSet D hC.d ∩ commSet D w := by
    intro i
    obtain ⟨j, hj⟩ := OddTransp.exists_zpow_conj_eq (hD.mul_self_eq_one he.1.1)
      (hD.mul_self_eq_one he'.1.1) (hD.odd_of_not_commute he.1.1 he'.1.1 hnc) i
    rw [← zpow_natCast, ← hj]
    have hg := hcl (show (e * e') ^ j ∈ Subgroup.closure ({e, e'} : Set G) from
      zpow_mem (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) j)
    exact ⟨conj_mem_commSet hC.setup.normal (Subgroup.mem_centralizer_singleton_iff.mp hg.1) he.1,
      conj_mem_commSet hC.setup.normal (Subgroup.mem_centralizer_singleton_iff.mp hg.2) he.2⟩
  have hinj : Set.InjOn (fun i : ℕ => (e * e') ^ i * e) (Finset.range p : Set ℕ) := by
    intro i hi j hj hij
    have h2 : (e * e') ^ i = (e * e') ^ j := mul_right_cancel hij
    rw [pow_inj_mod, hord] at h2
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h2
  calc p = ((fun i : ℕ => (e * e') ^ i * e) '' (Finset.range p : Set ℕ)).ncard := by
        rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]
    _ ≤ _ := Set.ncard_le_ncard (by rintro _ ⟨i, -, rfl⟩; exact hmem i)

private theorem ncard_image_DstarH_eq (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hα : hC.alpha = {hC.d}) {p : ℕ} (hpp : p.Prime) (hp3 : p ≠ 3)
    (hp : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p)
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index)
    (hQ : ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha)) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(Halpha D hC.alpha)) '' DstarH hC).ncard = p ∧
      ∃ t, p - 1 = 2 ^ t := by
  have hSH := setup_DstarH hC
  have hpH := orderOf_mul_DstarH hC hp
  obtain ⟨x₀, hx₀⟩ := hSH.nonempty
  obtain ⟨y₀, hy₀, hxy⟩ := exists_not_commute hSH hH' hQ hx₀
  set nq := (QuotientGroup.mk' (CFSG.pCore 2 ↥(Halpha D hC.alpha)) '' DstarH hC).ncard with hnq
  set m := {z | ∃ q ∈ CFSG.pCore 2 ↥(Halpha D hC.alpha), q * x₀ * q⁻¹ = z}.ncard with hm
  have hm2 : 2 ≤ m := two_le_ncard_pCore_conj hSH hQ hx₀
  have hk : (commSet D hC.d).ncard = nq * m := by
    rw [← image_val_DstarH hC hα, Set.ncard_image_of_injective _ Subtype.val_injective,
      ncard_eq_ncard_image_mul_ncard hSH hH' hQ (secondKind_DstarH hC hsecond) hx₀]
  have hpodd : Odd p := by
    have := hSH.oddT.odd_of_not_commute hx₀ hy₀ hxy
    rwa [hpH x₀ hx₀ y₀ hy₀ hxy] at this
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨f, hf⟩ := (isPGroup_commutator_quotient hSH hH' hpp hpH hx₀).exists_card_eq
  obtain ⟨g, -, hg⟩ := (Nat.dvd_prime_pow hpp).mp (hf ▸ ncard_image_dvd_card_commutator hSH hx₀)
  rw [← hnq] at hg
  have hnq2 : 2 ≤ nq := by
    have : 1 < nq := (Set.one_lt_ncard_iff (Set.toFinite _)).mpr ⟨_, _, ⟨x₀, hx₀, rfl⟩,
      ⟨y₀, hy₀, rfl⟩, fun h => hxy ((mk_eq_mk_iff hSH hH' hx₀ hy₀).mp h)⟩
    omega
  have hg1 : 1 ≤ g := by
    rcases g with _ | g
    · rw [hg, pow_zero] at hnq2
      omega
    · omega
  have hHprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card (Halpha D hC.alpha) → r = 2 ∨ r = p := by
    intro r hr hrH
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Halpha D hC.alpha)).exists_card_eq
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(Halpha D hC.alpha)),
      card_quotient_eq_two_mul hSH hH' hQ hx₀, hf, ha] at hrH
    rcases (Nat.Prime.dvd_mul hr).mp hrH with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hpp).mp (hr.dvd_of_dvd_pow h))
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
  obtain ⟨w₀, hw₀, hw₀u⟩ := exists_not_commute_u hC
    (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hx₀))
    (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hy₀))
    (fun h => hxy (commute_coe_iff.mp h))
  set μ := (commSet D hC.d ∩ commSet D w₀).ncard with hμ
  have hhig : (commSet D hC.d).ncard * ((commSet D hC.d).ncard - m) =
      {y | y ∈ D ∧ ¬ Commute y hC.d}.ncard * μ := by
    refine ncard_mul_eq_ncard_mul (fun v hv => ?_) (fun w hw => ?_)
    · exact ncard_not_commute_inter hC (by omega) hv (ncard_commSet_inter_of_mem hv
        (ncard_setOf_commute_eq hC hsecond hα hH' hQ hx₀ hv))
    · rw [setOf_commute_eq_inter hw.2]
      exact ncard_commSet_inter_eq hC hsecond hα hw₀ hw₀u hw.1 hw.2
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, mul_zero, hk] at hhig
    rcases Nat.mul_eq_zero.mp hhig with h | h
    · rcases Nat.mul_eq_zero.mp h with h | h <;> omega
    · have : nq * m ≤ m := Nat.sub_eq_zero_iff_le.mp h
      nlinarith
  obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero hμ0
  have hμH := ncard_commSet_inter_dvd hC hα hH' hw₀ hw₀u he
  have hl := ncard_not_commute_dvd hC hsecond hα hw₀ hw₀u
  have hdvd : nq - 1 ∣ {y | y ∈ D ∧ ¬ Commute y hC.d}.ncard * μ := by
    rw [← hhig, hk, ← Nat.sub_one_mul]
    exact Dvd.intro (nq * m * m) (by ring)
  have hpow2 : nq - 1 = 2 ^ (nq - 1).primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd (by omega) fun {r} hr hrd => ?_
    have hrp : r ≠ p := by
      rintro rfl
      have h1 : r ∣ nq := hg ▸ dvd_pow_self r (by omega)
      have h2 := Nat.dvd_sub h1 hrd
      rw [Nat.sub_sub_self (by omega)] at h2
      exact hr.one_lt.ne' (Nat.dvd_one.mp h2)
    rcases (Nat.Prime.dvd_mul hr).mp (hrd.trans hdvd) with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp (h.trans hl) with h' | h'
      · exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h'
      · exact (hHprime r hr h').resolve_right hrp
    · exact (hHprime r hr (h.trans hμH)).resolve_right hrp
  have h2 : p ^ g - 1 = 2 ^ (nq - 1).primeFactorsList.length := by
    rw [← hg]
    exact hpow2
  have hnqp : nq = p := by rw [hg, eq_one_of_pow_sub_one_eq_two_pow hpp hp2 hp3 hg1 h2, pow_one]
  exact ⟨hnqp, _, hnqp ▸ hpow2⟩

omit [Finite G] in
private theorem ncard_commSet_inter_of_mem_commSet (hC : HypothesisC D) {c : ℕ}
    (h : ∀ v ∈ commSet D hC.d, (commSet D hC.d ∩ commSet D v).ncard = c) {x y : G} (hx : x ∈ D)
    (hy : y ∈ commSet D x) : (commSet D x ∩ commSet D y).ncard = c := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hx)
  rw [commSet_conj hC.setup.normal, mem_cimg] at hy
  rw [show y = g * (g⁻¹ * y * g) * g⁻¹ by group, ncard_commSet_inter_conj hC.setup.normal]
  exact h _ hy

omit [Finite G] in
private theorem ncard_commSet_inter_of_not_commute (hC : HypothesisC D) {c : ℕ}
    (h : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).ncard = c) {x y : G}
    (hx : x ∈ D) (hy : y ∈ D) (hxy : ¬ Commute x y) : (commSet D x ∩ commSet D y).ncard = c := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hx)
  rw [show y = g * (g⁻¹ * y * g) * g⁻¹ by group, ncard_commSet_inter_conj hC.setup.normal]
  refine h _ (by simpa using hC.setup.normal g⁻¹ y hy) fun hc => hxy ?_
  have := (Commute.conj_iff g).mpr hc.symm
  rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this

private theorem ncard_offDiag {α : Type*} [Finite α] (s : Set α) :
    s.offDiag.ncard = s.ncard * s.ncard - s.ncard := by
  classical
  have := Fintype.ofFinite α
  rw [← Set.coe_toFinset s, ← Finset.coe_offDiag, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Finset.offDiag_card]

private theorem dvd_ncard_mul_of_lines {k m : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (T1 : ∀ x ∈ D, (commSet D x).ncard = k)
    (T2 : ∀ x ∈ D, ∀ y ∈ commSet D x, (commSet D x ∩ commSet D y).ncard = m - 1)
    (T4 : ∀ x ∈ D, ∀ a ∈ commSet D x, ∀ b ∈ commSet D x, ∀ v ∈ commSet D x,
      Commute a v → Commute b v → Commute a b) :
    (m + 1) * m ∣ D.ncard * k := by
  set F : Set (G × G) := {z | z.1 ∈ D ∧ z.2 ∈ commSet D z.1} with hF
  set L : G × G → Set G := fun z => {c | c ∈ D ∧ Commute c z.1 ∧ Commute c z.2} with hL
  have hLeq : ∀ z ∈ F, L z = insert z.1 (insert z.2 (commSet D z.1 ∩ commSet D z.2)) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    ext c
    simp only [hL, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_inter_iff]
    constructor
    · rintro ⟨hc, hcx, hcy⟩
      by_cases h1 : c = x
      · exact Or.inl h1
      · by_cases h2 : c = y
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨⟨hc, hcx, h1⟩, ⟨hc, hcy, h2⟩⟩)
    · rintro (rfl | rfl | ⟨⟨hc, hcx, -⟩, ⟨-, hcy, -⟩⟩)
      · exact ⟨hx, Commute.refl _, hy.2.1.symm⟩
      · exact ⟨hy.1, hy.2.1, Commute.refl _⟩
      · exact ⟨hc, hcx, hcy⟩
  have hxL : ∀ z ∈ F, z.1 ∈ L z ∧ z.2 ∈ L z := fun z hz =>
    ⟨⟨hz.1, Commute.refl _, hz.2.2.1.symm⟩, ⟨hz.2.1, hz.2.2.1, Commute.refl _⟩⟩
  have hLcard : ∀ z ∈ F, (L z).ncard = m + 1 := by
    intro z hz
    have h1 : z.2 ∉ commSet D z.1 ∩ commSet D z.2 := fun h => h.2.2.2 rfl
    have h2 : z.1 ∉ insert z.2 (commSet D z.1 ∩ commSet D z.2) := by
      rintro (h | h)
      · exact hz.2.2.2 h.symm
      · exact h.1.2.2 rfl
    rw [hLeq z hz, Set.ncard_insert_of_notMem h2, Set.ncard_insert_of_notMem h1,
      T2 _ hz.1 _ hz.2]
    omega
  have hLcomm : ∀ z ∈ F, ∀ c ∈ L z, ∀ c' ∈ L z, Commute c c' := by
    rintro ⟨x, y⟩ hz c ⟨hc, hcx, hcy⟩ c' ⟨hc', hc'x, hc'y⟩
    by_cases h1 : c = x
    · subst h1
      exact hc'x.symm
    by_cases h2 : c = y
    · subst h2
      exact hc'y.symm
    by_cases h3 : c' = x
    · subst h3
      exact hcx
    by_cases h4 : c' = y
    · subst h4
      exact hcy
    exact T4 x hz.1 c ⟨hc, hcx, h1⟩ c' ⟨hc', hc'x, h3⟩ y hz.2 hcy hc'y
  have hFst : F.ncard = D.ncard * k := by
    have h := ncard_eq_ncard_image_mul (s := F) (f := Prod.fst) (m := k) fun z hz => by
      rw [show {b | b ∈ F ∧ b.1 = z.1} = Prod.mk z.1 '' commSet D z.1 from ?_,
        Set.ncard_image_of_injective _ (Prod.mk_right_injective z.1), T1 _ hz.1]
      ext ⟨a, b⟩
      simp only [hF, Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨-, hb⟩, rfl⟩
        exact ⟨b, hb, rfl, rfl⟩
      · rintro ⟨y, hy, rfl, rfl⟩
        exact ⟨⟨hz.1, hy⟩, rfl⟩
    have himg : Prod.fst '' F = D := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz.1
      · intro hx
        obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero
          (show (commSet D x).ncard ≠ 0 by rw [T1 x hx]; omega)
        exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    rw [h, himg]
  have hFL : F.ncard = (L '' F).ncard * ((m + 1) * m) := by
    refine ncard_eq_ncard_image_mul fun z hz => ?_
    have hfib : {b | b ∈ F ∧ L b = L z} = (L z).offDiag := by
      ext ⟨c, d⟩
      constructor
      · rintro ⟨hcd, hL'⟩
        have h := hxL _ hcd
        rw [hL'] at h
        exact ⟨h.1, h.2, fun h' => hcd.2.2.2 h'.symm⟩
      · rintro ⟨hc, hd, hne⟩
        have hcdF : (c, d) ∈ F := ⟨hc.1, hd.1, (hLcomm z hz c hc d hd).symm, fun h => hne h.symm⟩
        refine ⟨hcdF, (Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)).symm⟩
        · intro e he
          exact ⟨he.1, hLcomm z hz e he c hc, hLcomm z hz e he d hd⟩
        · rw [hLcard z hz, hLcard _ hcdF]
    rw [hfib, ncard_offDiag, hLcard z hz, ← Nat.mul_sub_one, Nat.add_sub_cancel]
  rw [← hFst, hFL]
  exact dvd_mul_left _ _

private theorem false_of_mu_eq_one (hC : HypothesisC D) {p m t : ℕ} (hpp : p.Prime)
    (hm2 : 2 ≤ m) (hmeven : Even m) (hp1 : p - 1 = 2 ^ t)
    (hk : (commSet D hC.d).ncard = p * m)
    (hlam : ∀ v ∈ commSet D hC.d, (commSet D hC.d ∩ commSet D v).ncard = m - 1)
    (hmu : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).ncard = 1)
    (hK2 : ∀ a ∈ commSet D hC.d, ∀ b ∈ commSet D hC.d, ∀ v ∈ commSet D hC.d,
      Commute a v → Commute b v → Commute a b)
    (hl : {y | y ∈ D ∧ ¬ Commute y hC.d}.ncard = p * m * (p * m - m)) : False := by
  have hp2 := hpp.two_le
  have T1 : ∀ x ∈ D, (commSet D x).ncard = p * m := fun x hx =>
    (ncard_commSet_eq hC hx).trans hk
  have T2 : ∀ x ∈ D, ∀ y ∈ commSet D x, (commSet D x ∩ commSet D y).ncard = m - 1 :=
    fun x hx y hy => ncard_commSet_inter_of_mem_commSet hC hlam hx hy
  have T3 : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → (commSet D x ∩ commSet D y).ncard = 1 :=
    fun x hx y hy hxy => ncard_commSet_inter_of_not_commute hC hmu hx hy hxy
  have T4 : ∀ x ∈ D, ∀ a ∈ commSet D x, ∀ b ∈ commSet D x, ∀ v ∈ commSet D x,
      Commute a v → Commute b v → Commute a b := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hx)
    exact commute_trans_conj hC.setup.normal hK2 g
  have hn : D.ncard = 1 + p * m + p * m * ((p - 1) * m) := by
    rw [ncard_eq_one_add_add hC, hk, hl, Nat.sub_one_mul]
  have hnZ : (D.ncard : ℤ) = 1 + p * m + p * m * ((p - 1) * m) := by
    rw [hn]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  have hlines := dvd_ncard_mul_of_lines (by omega) (by nlinarith) T1 T2 T4
  have hdvd : m + 1 ∣ D.ncard * p :=
    Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < m) (by rwa [mul_assoc])
  have hdvdZ : ((m + 1 : ℕ) : ℤ) ∣ (((p - 1) ^ 2 * p : ℕ) : ℤ) := by
    have h1 : ((m : ℤ) + 1) ∣ (D.ncard : ℤ) * p := by
      exact_mod_cast Int.natCast_dvd_natCast.mpr hdvd
    have h2 : (D.ncard : ℤ) * p = (m + 1) * (p * (p * (p - 1) * m + 1 - (p - 1) ^ 2)) +
        (p - 1) ^ 2 * p := by
      rw [hnZ]
      ring
    rw [h2] at h1
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    exact (dvd_add_right (dvd_mul_right _ _)).mp h1
  have hcop : Nat.Coprime (m + 1) ((p - 1) ^ 2) := by
    rw [hp1, ← pow_mul]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hmeven.add_one)
  have hpm : p = m + 1 := by
    rcases (Nat.dvd_prime hpp).mp (hcop.dvd_of_dvd_mul_left (Int.natCast_dvd_natCast.mp hdvdZ))
      with h | h
    · omega
    · exact h.symm
  classical
  have : Fintype D := Fintype.ofFinite D
  let Γ : SimpleGraph D :=
    { Adj := fun a b => a ≠ b ∧ Commute (a : G) b
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  have hnb : ∀ v : D, Subtype.val '' Γ.neighborSet v = commSet D v := by
    intro v
    ext x
    constructor
    · rintro ⟨w, ⟨hne, hc⟩, rfl⟩
      exact ⟨w.2, hc.symm, fun h => hne (Subtype.ext h).symm⟩
    · rintro ⟨hx, hc, hne⟩
      exact ⟨⟨x, hx⟩, ⟨fun h => hne (congrArg Subtype.val h).symm, hc.symm⟩, rfl⟩
  have hcn : ∀ v w : D,
      Fintype.card (Γ.commonNeighbors v w) = (commSet D v ∩ commSet D w).ncard := by
    intro v w
    rw [Set.fintypeCard_eq_ncard, SimpleGraph.commonNeighbors,
      ← Set.ncard_image_of_injective _ Subtype.val_injective,
      Set.image_inter Subtype.val_injective, hnb, hnb]
  have hsrg : Γ.IsSRGWith D.ncard (p * m) (m - 1) 1 := by
    refine ⟨Set.fintypeCard_eq_ncard D, fun v => ?_, fun v w hvw => ?_, fun v w hne hnadj => ?_⟩
    · rw [← SimpleGraph.ncard_neighborSet, ← Set.ncard_image_of_injective _ Subtype.val_injective,
        hnb, T1 _ v.2]
    · rw [hcn]
      exact T2 _ v.2 _ ⟨w.2, hvw.2.symm, fun h => hvw.1 (Subtype.ext h).symm⟩
    · rw [hcn]
      exact T3 _ v.2 _ w.2 fun h => hnadj ⟨hne, h⟩
  have hn0 : 0 < D.ncard := by
    rw [hn]
    omega
  obtain ⟨-, hconf⟩ := hsrg.conference_of_not_isSquare hn0 (by
    intro hsq
    refine not_isSquare_five_mul_sq (m := m) (by exact_mod_cast (show m ≠ 0 by omega)) ?_
    convert hsq using 1
    rw [hpm, Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    ring)
  rw [Nat.cast_sub (by omega : 1 ≤ m)] at hconf
  push_cast at hconf
  have h1 : (0 : ℤ) ≤ ((D.ncard : ℤ) - 1) * ((m : ℤ) - 1 - 1) :=
    mul_nonneg (by have : (1 : ℤ) ≤ D.ncard := by exact_mod_cast hn0
                   linarith) (by have : (2 : ℤ) ≤ m := by exact_mod_cast hm2
                                 linarith)
  have h2 : (0 : ℤ) < 2 * ((p : ℤ) * m) := by
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp2
    have : (2 : ℤ) ≤ m := by exact_mod_cast hm2
    positivity
  linarith

theorem pCore_sup_closure_eq_top_of_sevenFive (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hα : hC.alpha = {hC.d}) {p : ℕ} (hpp : p.Prime) (hp3 : p ≠ 3)
    (hp : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p)
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index)
    (hQ : ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha))
    {x y : Halpha D hC.alpha} (hx : (x : G) ∈ commSet D hC.d) (hy : (y : G) ∈ commSet D hC.d)
    (hxy : ¬ Commute (x : G) y) :
    CFSG.pCore 2 ↥(Halpha D hC.alpha) ⊔ Subgroup.closure ({x, y} : Set (Halpha D hC.alpha)) =
      ⊤ :=
  pCore_sup_closure_eq_top (setup_DstarH hC) (orderOf_mul_DstarH hC hp)
    (mem_DstarH_of_mem_commSet hC hα hx) (mem_DstarH_of_mem_commSet hC hα hy)
    (fun h => hxy (commute_coe_iff.mpr h))
    (ncard_image_DstarH_eq hC hsecond hα hpp hp3 hp hH' hQ).1

theorem card_quotient_pCore_Halpha_of_sevenFive (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hα : hC.alpha = {hC.d}) {p : ℕ} (hpp : p.Prime) (hp3 : p ≠ 3)
    (hp : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p)
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index)
    (hQ : ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha)) :
    Nat.card (↥(Halpha D hC.alpha) ⧸ CFSG.pCore 2 ↥(Halpha D hC.alpha)) = 2 * p := by
  have hSH := setup_DstarH hC
  have hpH := orderOf_mul_DstarH hC hp
  obtain ⟨x₀, hx₀⟩ := hSH.nonempty
  obtain ⟨y₀, hy₀, hxy⟩ := exists_not_commute hSH hH' hQ hx₀
  have hq := (ncard_image_DstarH_eq hC hsecond hα hpp hp3 hp hH' hQ).1
  have h1 := card_quotient_le hSH hH' hpp hpH hx₀ hy₀ hxy
    (pCore_sup_closure_eq_top hSH hpH hx₀ hy₀ hxy hq)
  have h2 := card_quotient_eq_two_mul hSH hH' hQ hx₀
  have h3 : p ≤ Nat.card (commutator
      (↥(Halpha D hC.alpha) ⧸ CFSG.pCore 2 ↥(Halpha D hC.alpha))) := by
    rw [← hq]
    exact Nat.le_of_dvd Nat.card_pos (ncard_image_dvd_card_commutator hSH hx₀)
  omega

theorem center_Halpha_eq_inf_of_sevenFive (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hα : hC.alpha = {hC.d}) {p : ℕ} (hpp : p.Prime) (hp3 : p ≠ 3)
    (hp : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p)
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index)
    (hQ : ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha))
    {x y : Halpha D hC.alpha} (hx : (x : G) ∈ commSet D hC.d) (hy : (y : G) ∈ commSet D hC.d)
    (hxy : ¬ Commute (x : G) y) :
    Subgroup.center ↥(Halpha D hC.alpha) =
      ⁅CFSG.pCore 2 ↥(Halpha D hC.alpha), Subgroup.zpowers x⁆ ⊓
        ⁅CFSG.pCore 2 ↥(Halpha D hC.alpha), Subgroup.zpowers y⁆ :=
  (sixFiveGlobal_unconditional (setup_DstarH hC) rfl (mem_DstarH_of_mem_commSet hC hα hx)
    (mem_DstarH_of_mem_commSet hC hα hy) (fun h => hxy (commute_coe_iff.mpr h))
    (pCore_sup_closure_eq_top_of_sevenFive hC hsecond hα hpp hp3 hp hH' hQ hx hy hxy)).2.1

private theorem exists_not_commute_Halpha (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index)
    (hQ : ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha)) :
    ∃ x y : Halpha D hC.alpha, (x : G) ∈ commSet D hC.d ∧ (y : G) ∈ commSet D hC.d ∧
      ¬ Commute (x : G) y := by
  obtain ⟨x₀, hx₀⟩ := (setup_DstarH hC).nonempty
  obtain ⟨y₀, hy₀, hxy⟩ := exists_not_commute (setup_DstarH hC) hH' hQ hx₀
  exact ⟨x₀, y₀, coe_mem_commSet_of_mem_DstarH hC hα hx₀, coe_mem_commSet_of_mem_DstarH hC hα hy₀,
    fun h => hxy (commute_coe_iff.mp h)⟩

theorem mul_self_eq_one_of_mem_center_Halpha (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hα : hC.alpha = {hC.d}) {p : ℕ} (hpp : p.Prime) (hp3 : p ≠ 3)
    (hp : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p)
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index)
    (hQ : ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha)) :
    ∀ z ∈ Subgroup.center ↥(Halpha D hC.alpha), (z : G) * z = 1 := by
  intro z hz
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_not_commute_Halpha hC hα hH' hQ
  rw [center_Halpha_eq_inf_of_sevenFive hC hsecond hα hpp hp3 hp hH' hQ hx hy hxy] at hz
  exact congrArg Subtype.val
    (mul_self_eq_one_of_mem_commutator (setup_DstarH hC) (mem_DstarH_of_mem_commSet hC hα hx) hz.1)

theorem sevenSix_of_sevenFive (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hα : hC.alpha = {hC.d}) {p : ℕ} (hpp : p.Prime) (hp3 : p ≠ 3)
    (hp : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p)
    (hH' : ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index)
    (hQ : ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha)) :
    ∃ m : ℕ, 2 ≤ m ∧
      (∀ v ∈ commSet D hC.d,
        {y | ∃ q ∈ (CFSG.pCore 2 ↥(Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype, q * v * q⁻¹ = y}.ncard = m ∧
          (commSet D hC.d ∩ commSet D v).ncard = m - 1) ∧
      (commSet D hC.d).ncard = p * m ∧
      {y | y ∈ D ∧ ¬ Commute y hC.d}.ncard = m ^ 2 * (p - 1) ∧
      (∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).ncard = p) ∧
      Nat.card ↥(Halpha D hC.alpha) = 2 * p * m ^ 2 * Nat.card (Subgroup.center ↥(Halpha D hC.alpha)) := by
  have hSH := setup_DstarH hC
  obtain ⟨x₀, hx₀⟩ := hSH.nonempty
  obtain ⟨y₀, hy₀, hxy⟩ := exists_not_commute hSH hH' hQ hx₀
  have hx₀G := coe_mem_commSet_of_mem_DstarH hC hα hx₀
  have hy₀G := coe_mem_commSet_of_mem_DstarH hC hα hy₀
  have hxyG : ¬ Commute (x₀ : G) y₀ := fun h => hxy (commute_coe_iff.mp h)
  set m := {z | ∃ q ∈ CFSG.pCore 2 ↥(Halpha D hC.alpha), q * x₀ * q⁻¹ = z}.ncard with hm
  obtain ⟨hq, t, ht⟩ := ncard_image_DstarH_eq hC hsecond hα hpp hp3 hp hH' hQ
  have hfib : ∀ v ∈ commSet D hC.d, {c | c ∈ commSet D hC.d ∧ Commute c v}.ncard = m :=
    fun v hv => ncard_setOf_commute_eq hC hsecond hα hH' hQ hx₀ hv
  have hlam : ∀ v ∈ commSet D hC.d, (commSet D hC.d ∩ commSet D v).ncard = m - 1 :=
    fun v hv => ncard_commSet_inter_of_mem hv (hfib v hv)
  have hm2 : 2 ≤ m := two_le_ncard_pCore_conj hSH hQ hx₀
  have hk : (commSet D hC.d).ncard = p * m := by
    rw [← image_val_DstarH hC hα, Set.ncard_image_of_injective _ Subtype.val_injective,
      ncard_eq_ncard_image_mul_ncard hSH hH' hQ (secondKind_DstarH hC hsecond) hx₀, hq]
  obtain ⟨-, -, hcardQ⟩ := sixFiveGlobal_unconditional hSH rfl hx₀ hy₀ hxy
    (pCore_sup_closure_eq_top_of_sevenFive hC hsecond hα hpp hp3 hp hH' hQ hx₀G hy₀G hxyG)
  rw [inter_centralizer_eq hSH hH' hQ (secondKind_DstarH hC hsecond) hx₀, ← hm] at hcardQ
  have hcardH : Nat.card ↥(Halpha D hC.alpha) =
      2 * p * m ^ 2 * Nat.card (Subgroup.center ↥(Halpha D hC.alpha)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(Halpha D hC.alpha)),
      card_quotient_pCore_Halpha_of_sevenFive hC hsecond hα hpp hp3 hp hH' hQ, hcardQ]
    ring
  have hmeven : Even m := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Halpha D hC.alpha)).exists_card_eq
    have hdvd : m ∣ 2 ^ a := by
      rw [← ha, hcardQ]
      exact Dvd.intro (m * Nat.card (Subgroup.center ↥(Halpha D hC.alpha))) (by ring)
    obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases s with _ | s
    · rw [hs, pow_zero] at hm2
      omega
    · exact ⟨2 ^ s, by rw [hs, pow_succ]; ring⟩
  obtain ⟨w₀, hw₀, hw₀u⟩ := exists_not_commute_u hC hx₀G.1 hy₀G.1 hxyG
  set μ := (commSet D hC.d ∩ commSet D w₀).ncard with hμdef
  have hμ : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).ncard = μ :=
    fun w hw hwu => ncard_commSet_inter_eq hC hsecond hα hw₀ hw₀u hw hwu
  have hhig : (commSet D hC.d).ncard * ((commSet D hC.d).ncard - m) =
      {y | y ∈ D ∧ ¬ Commute y hC.d}.ncard * μ := by
    refine ncard_mul_eq_ncard_mul (fun v hv => ?_) (fun w hw => ?_)
    · exact ncard_not_commute_inter hC (by omega) hv (hlam v hv)
    · rw [setOf_commute_eq_inter hw.2]
      exact hμ w hw.1 hw.2
  rw [hk] at hhig
  have hpm : m < p * m := by nlinarith [hpp.two_le]
  have hμ1 : 1 ≤ μ := by
    by_contra h0
    have hpos : 0 < p * m * (p * m - m) :=
      Nat.mul_pos (Nat.mul_pos hpp.pos (by omega)) (Nat.sub_pos_of_lt hpm)
    rw [show μ = 0 by omega, mul_zero] at hhig
    omega
  have hμle : μ ≤ p := by
    rw [← hq]
    exact ncard_le_of_pairwise_not_commute hC hα hH' (fun x hx => hx.1)
      (not_commute_of_mem_commSet_inter hC hα hH' w₀ hw₀ hw₀u)
  have hμp : μ = p := by
    rcases Nat.lt_or_ge μ 2 with h | h
    · exfalso
      have hμ1' : μ = 1 := by omega
      rw [hμ1', mul_one] at hhig
      exact false_of_mu_eq_one hC hpp hm2 hmeven ht hk hlam
        (fun w hw hwu => (hμ w hw hwu).trans hμ1') (commute_of_commute_of_mem_commSet hC hα hH')
        hhig.symm
    · obtain ⟨e, e', he, he', hne⟩ :=
        (Set.one_lt_ncard_iff (s := commSet D hC.d ∩ commSet D w₀) (Set.toFinite _)).mp
          (by rw [← hμdef]; omega)
      exact le_antisymm hμle (le_ncard_commSet_inter hC hα hH' hp hw₀ hw₀u he he' hne)
  have hl : {y | y ∈ D ∧ ¬ Commute y hC.d}.ncard = m ^ 2 * (p - 1) := by
    rw [hμp, ← Nat.sub_one_mul] at hhig
    refine Nat.eq_of_mul_eq_mul_right hpp.pos ?_
    rw [← hhig]
    ring
  refine ⟨m, hm2, fun v hv => ⟨?_, hlam v hv⟩, hk, hl,
    fun w hw hwu => (hμ w hw hwu).trans hμp, hcardH⟩
  rw [← setOf_commute_eq_pCore_conj hC hsecond hα hH' hQ hv]
  exact hfib v hv

end Global

end CFSG.OddTranspositions
