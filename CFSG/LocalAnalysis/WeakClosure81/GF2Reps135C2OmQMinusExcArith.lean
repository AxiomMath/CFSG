module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.BitIndices
import CFSG.RepresentationTheory.SL2NatSum.ChooseTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private lemma c2slomqmea_mul_mh (f : ℕ) :
    (2 ^ f - 1) * (2 ^ f + 1) = 2 ^ (2 * f) - 1 := by
  rw [mul_comm, ← Nat.mul_self_sub_mul_self_eq (2 ^ f) 1]
  norm_num
  rw [← pow_add, ← two_mul]

private lemma c2slomqmea_lt_two_pow {f C : ℕ}
    (hCQ : C < (2 ^ f - 1) * (2 ^ f + 1)) : C < 2 ^ (2 * f) := by
  rw [c2slomqmea_mul_mh] at hCQ
  exact hCQ.trans_le (Nat.sub_one_lt (Nat.two_pow_pos (2 * f)).ne').le

private lemma c2slomqmea_m_odd {f : ℕ} (hf : 1 ≤ f) : Odd (2 ^ f - 1) := by
  have heven : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  exact Nat.Even.sub_odd Nat.one_le_two_pow heven odd_one

private lemma c2slomqmea_h_odd {f : ℕ} (hf : 1 ≤ f) : Odd (2 ^ f + 1) := by
  have heven : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  exact heven.add_one

private lemma c2slomqmea_m_coprime_pow {f : ℕ} (hf : 1 ≤ f) (r : ℕ) :
    Nat.Coprime (2 ^ f - 1) (2 ^ r) :=
  (Nat.coprime_two_right.mpr (c2slomqmea_m_odd hf)).pow_right r

private lemma c2slomqmea_h_coprime_pow {f : ℕ} (hf : 1 ≤ f) (r : ℕ) :
    Nat.Coprime (2 ^ f + 1) (2 ^ r) :=
  (Nat.coprime_two_right.mpr (c2slomqmea_h_odd hf)).pow_right r

private lemma c2slomqmea_m_h_coprime {f : ℕ} (hf : 1 ≤ f) :
    Nat.Coprime (2 ^ f - 1) (2 ^ f + 1) := by
  have h : 2 ^ f + 1 = 2 + (2 ^ f - 1) := by
    have := Nat.two_pow_pos f
    omega
  rw [h, Nat.coprime_add_self_right]
  exact Nat.coprime_two_right.mpr (c2slomqmea_m_odd hf)

private lemma c2slomqmea_bits_lt {f C : ℕ} (hC : C < 2 ^ (2 * f)) :
    ∀ u ∈ C.bitIndices, u < 2 * f := by
  intro u hu
  have hle : 2 ^ u ≤ C := Nat.two_pow_le_of_mem_bitIndices hu
  by_contra hcon
  have h2 : 2 * f ≤ u := by omega
  have hpow : 2 ^ (2 * f) ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) h2
  omega

private lemma c2slomqmea_bit_indices_ne_nil {C : ℕ} (hC1 : 1 ≤ C) :
    C.bitIndices ≠ [] := by
  intro h
  have hsum := Nat.sum_map_two_pow_bitIndices C
  rw [h] at hsum
  simp at hsum
  omega

private lemma c2slomqmea_two_mem {C : ℕ} (hC1 : 1 ≤ C) (hpow : ∀ u, C ≠ 2 ^ u) :
    ∃ u ∈ C.bitIndices, ∃ v ∈ C.bitIndices, u ≠ v := by
  have hne : C.bitIndices ≠ [] := c2slomqmea_bit_indices_ne_nil hC1
  have hpos : 0 < C.bitIndices.length := List.length_pos_iff.mpr hne
  have hne1 : C.bitIndices.length ≠ 1 := by
    intro hlen
    obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp hlen
    have hsum := Nat.sum_map_two_pow_bitIndices C
    rw [hu] at hsum
    simp at hsum
    exact hpow u hsum.symm
  have hlen : 2 ≤ C.bitIndices.length := by omega
  have hcard : 1 < C.bitIndices.toFinset.card := by
    rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
  exact ⟨u, by simpa using hu, v, by simpa using hv, huv⟩

private lemma c2slomqmea_sum_toFinset {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (l : List α) (g : α → β) (hl : l.Nodup) :
    l.toFinset.sum g = (l.map g).sum := by
  revert hl
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro hl
    rw [List.nodup_cons] at hl
    rw [List.toFinset_cons, Finset.sum_insert (by simpa [List.mem_toFinset] using hl.1),
      List.map_cons, List.sum_cons, ih hl.2]

private lemma c2slomqmea_odd_choose_two_pow {C u : ℕ} (h : C.testBit u = true) :
    Odd (C.choose (2 ^ u)) := by
  have hle : 2 ^ u ≤ C := Nat.ge_two_pow_of_testBit h
  have hdecomp : 2 ^ u + (C - 2 ^ u) = C := Nat.add_sub_of_le hle
  rw [← hdecomp]
  refine (CFSG.RepresentationTheory.SL2NatSum.odd_choose_add_iff (2 ^ u) (C - 2 ^ u)).mpr ?_
  have hx : (C - 2 ^ u).testBit u = false := by
    have ht := Nat.testBit_two_pow_add_eq (C - 2 ^ u) u
    rw [hdecomp, h] at ht
    simpa using ht.symm
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow]
  by_cases hj : j = u
  · subst j; simp [hx]
  · have hju : u ≠ j := fun h => hj h.symm
    simp [hju]

private lemma c2slomqmea_m_not_modEq_of_lt {f u v : ℕ} (huv : u < v) (hv : v < f) :
    ¬ Nat.ModEq (2 ^ f - 1) (2 ^ u) (2 ^ v) := by
  intro h
  have hle : 2 ^ u ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) huv.le
  have hdiv : 2 ^ f - 1 ∣ 2 ^ v - 2 ^ u := (Nat.modEq_iff_dvd' hle).mp h
  have hfactor : 2 ^ v - 2 ^ u = 2 ^ u * (2 ^ (v - u) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le huv.le]
  rw [hfactor] at hdiv
  have hdiv' : 2 ^ f - 1 ∣ 2 ^ (v - u) - 1 :=
    (c2slomqmea_m_coprime_pow (by omega : 1 ≤ f) u).dvd_of_dvd_mul_left hdiv
  have hpos : 0 < 2 ^ (v - u) - 1 := by
    have : 1 < 2 ^ (v - u) := Nat.one_lt_two_pow (by omega)
    omega
  have hlt : 2 ^ (v - u) - 1 < 2 ^ f - 1 := by
    have h1 : 2 ^ (v - u) ≤ 2 ^ (f - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (f - 1) < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have := Nat.le_of_dvd hpos hdiv'
  omega

private lemma c2slomqmea_m_modEq_mod {f u v : ℕ} (hu : u < 2 * f) (hv : v < 2 * f)
    (h : Nat.ModEq (2 ^ f - 1) (2 ^ u) (2 ^ v)) : u % f = v % f := by
  have hmod : Nat.ModEq (2 ^ f - 1) (2 ^ f) 1 :=
    ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr dvd_rfl).symm
  have hpu : Nat.ModEq (2 ^ f - 1) (2 ^ u) (2 ^ (u % f)) := by
    have hpow : 2 ^ u = 2 ^ (u % f) * (2 ^ f) ^ (u / f) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    rw [hpow]
    simpa using Nat.ModEq.mul (Nat.ModEq.refl (2 ^ (u % f))) (hmod.pow (u / f))
  have hpv : Nat.ModEq (2 ^ f - 1) (2 ^ v) (2 ^ (v % f)) := by
    have hpow : 2 ^ v = 2 ^ (v % f) * (2 ^ f) ^ (v / f) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    rw [hpow]
    simpa using Nat.ModEq.mul (Nat.ModEq.refl (2 ^ (v % f))) (hmod.pow (v / f))
  have h2 : Nat.ModEq (2 ^ f - 1) (2 ^ (u % f)) (2 ^ (v % f)) :=
    hpu.symm.trans (h.trans hpv)
  by_contra hne
  rcases lt_or_gt_of_ne hne with huv | hvu
  · exact c2slomqmea_m_not_modEq_of_lt huv (Nat.mod_lt _ (by omega)) h2
  · exact c2slomqmea_m_not_modEq_of_lt hvu (Nat.mod_lt _ (by omega)) h2.symm

private lemma c2slomqmea_h_not_dvd_pow_sub_one {f w : ℕ} (hf : 2 ≤ f) (hw0 : 0 < w)
    (hw2 : w < 2 * f) : ¬ (2 ^ f + 1) ∣ 2 ^ w - 1 := by
  intro hdvd
  rcases lt_trichotomy w f with hwf | hwf | hwf
  · have hpos : 0 < 2 ^ w - 1 := by
      have : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
      omega
    have hlt : 2 ^ w - 1 < 2 ^ f + 1 := by
      have h1 : 2 ^ w ≤ 2 ^ (f - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (f - 1) < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have := Nat.le_of_dvd hpos hdvd
    omega
  · subst w
    have h2 : 2 ^ f + 1 ∣ 2 := by
      have h1 : 2 ^ f + 1 ∣ 2 ^ f + 1 := dvd_rfl
      have h3 : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by
        have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        omega
      have := Nat.dvd_sub h1 hdvd
      rwa [h3] at this
    have := Nat.le_of_dvd (by norm_num) h2
    have hge : 3 ≤ 2 ^ f + 1 := by
      have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    omega
  · have hsplit : w = f + (w - f) := by omega
    have hdvd2 : (2 ^ f + 1) ∣ 2 ^ w + 2 ^ (w - f) := by
      have heq : (2 ^ f + 1) * 2 ^ (w - f) = 2 ^ w + 2 ^ (w - f) := by
        rw [add_mul, one_mul, ← pow_add, ← hsplit]
      rw [← heq]
      exact dvd_mul_right _ _
    have h3 : (2 ^ w + 2 ^ (w - f)) - (2 ^ w - 1) = 2 ^ (w - f) + 1 := by
      have hAc : 2 ^ w + 2 ^ (w - f) = (2 ^ w - 1) + (2 ^ (w - f) + 1) := by
        rw [← Nat.sub_add_cancel Nat.one_le_two_pow]
        omega
      rw [hAc, Nat.add_sub_cancel_left]
    have hdvd3 : 2 ^ f + 1 ∣ 2 ^ (w - f) + 1 := by
      have := Nat.dvd_sub hdvd2 hdvd
      rwa [h3] at this
    have hpos : 0 < 2 ^ (w - f) + 1 := by positivity
    have hlt : 2 ^ (w - f) + 1 < 2 ^ f + 1 := by
      have : 2 ^ (w - f) < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have := Nat.le_of_dvd hpos hdvd3
    omega

private lemma c2slomqmea_h_not_modEq_of_lt {f u v : ℕ} (hf : 2 ≤ f) (huv : u < v)
    (hv : v < 2 * f) : ¬ Nat.ModEq (2 ^ f + 1) (2 ^ u) (2 ^ v) := by
  intro h
  have hle : 2 ^ u ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) huv.le
  have hdiv : 2 ^ f + 1 ∣ 2 ^ v - 2 ^ u := (Nat.modEq_iff_dvd' hle).mp h
  have hfactor : 2 ^ v - 2 ^ u = 2 ^ u * (2 ^ (v - u) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le huv.le]
  rw [hfactor] at hdiv
  have hdiv' : 2 ^ f + 1 ∣ 2 ^ (v - u) - 1 :=
    (c2slomqmea_h_coprime_pow (by omega : 1 ≤ f) u).dvd_of_dvd_mul_left hdiv
  exact c2slomqmea_h_not_dvd_pow_sub_one hf (by omega) (by omega) hdiv'

private lemma c2slomqmea_h_pow_inj {f u v : ℕ} (hf : 2 ≤ f) (hu : u < 2 * f)
    (hv : v < 2 * f) (h : Nat.ModEq (2 ^ f + 1) (2 ^ u) (2 ^ v)) : u = v := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with huv | hvu
  · exact c2slomqmea_h_not_modEq_of_lt hf huv hv h
  · exact c2slomqmea_h_not_modEq_of_lt hf hvu hu h.symm

private lemma c2slomqmea_bad_m {f C : ℕ} (hf : 2 ≤ f) (hC1 : 1 ≤ C)
    (hCQ : C < (2 ^ f - 1) * (2 ^ f + 1)) (hpow : ∀ u, C ≠ 2 ^ u) :
    ∃ u ∈ C.bitIndices, ((2 ^ u : ℕ) : ZMod (2 ^ f - 1)) ≠ (C : ZMod (2 ^ f - 1)) := by
  by_contra hcon
  push Not at hcon
  have hC_lt : C < 2 ^ (2 * f) := c2slomqmea_lt_two_pow hCQ
  have hbits_lt : ∀ u ∈ C.bitIndices, u < 2 * f := c2slomqmea_bits_lt hC_lt
  obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := c2slomqmea_two_mem hC1 hpow
  set r := u₁ % f with hr_def
  have hmod_all : ∀ u ∈ C.bitIndices, u % f = r := by
    intro u hu
    have heq : ((2 ^ u : ℕ) : ZMod (2 ^ f - 1)) = ((2 ^ u₁ : ℕ) : ZMod (2 ^ f - 1)) := by
      rw [hcon u hu, hcon u₁ hu₁]
    have hmod : Nat.ModEq (2 ^ f - 1) (2 ^ u) (2 ^ u₁) :=
      (ZMod.natCast_eq_natCast_iff (2 ^ u) (2 ^ u₁) (2 ^ f - 1)).mp heq
    have := c2slomqmea_m_modEq_mod (hbits_lt u hu) (hbits_lt u₁ hu₁) hmod
    simpa [hr_def] using this
  have hsubset : C.bitIndices.toFinset ⊆ ({r, r + f} : Finset ℕ) := by
    intro u hu
    have hu' : u ∈ C.bitIndices := by simpa using hu
    have hlt := hbits_lt u hu'
    have hmod := hmod_all u hu'
    have hq : u / f = 0 ∨ u / f = 1 := by
      have hlt2 : u / f < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by omega : 0 < f)]
        omega
      rcases Nat.lt_or_ge (u / f) 1 with h | h
      · left; exact Nat.lt_one_iff.mp h
      · right; exact le_antisymm (Nat.lt_succ_iff.mp hlt2) h
    have hdecomp : u = f * (u / f) + u % f := (Nat.div_add_mod u f).symm
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hq with hq | hq
    · left; rw [hdecomp, hq, hmod]; omega
    · right; rw [hdecomp, hq, hmod]; omega
  have hcard2 : C.bitIndices.toFinset.card = 2 := by
    have hge : 2 ≤ C.bitIndices.toFinset.card := by
      have h1 : 1 < C.bitIndices.toFinset.card :=
        Finset.one_lt_card.mpr ⟨u₁, by simpa using hu₁, u₂, by simpa using hu₂, hne⟩
      omega
    have hle : C.bitIndices.toFinset.card ≤ 2 :=
      (Finset.card_le_card hsubset).trans Finset.card_le_two
    omega
  have hset : C.bitIndices.toFinset = ({r, r + f} : Finset ℕ) :=
    Finset.eq_of_subset_of_card_le hsubset (by rw [hcard2]; exact Finset.card_le_two)
  have hr : r ∈ C.bitIndices := by
    have : r ∈ C.bitIndices.toFinset := by rw [hset]; simp
    simpa using this
  have hCsum : C = 2 ^ r + 2 ^ (r + f) := by
    have h1 := Nat.sum_map_two_pow_bitIndices C
    rw [← c2slomqmea_sum_toFinset C.bitIndices (fun u => 2 ^ u) Nat.bitIndices_nodup] at h1
    rw [hset, Finset.sum_pair (by omega : r ≠ r + f)] at h1
    exact h1.symm
  have hCz : (C : ZMod (2 ^ f - 1)) = 2 * ((2 ^ r : ℕ) : ZMod (2 ^ f - 1)) := by
    have hpow : ((2 ^ (r + f) : ℕ) : ZMod (2 ^ f - 1)) =
        ((2 ^ r : ℕ) : ZMod (2 ^ f - 1)) := by
      rw [pow_add, Nat.cast_mul]
      have hf1 : ((2 ^ f : ℕ) : ZMod (2 ^ f - 1)) = 1 := by
        have hM : 2 ^ f = (2 ^ f - 1) + 1 := by
          have := Nat.two_pow_pos f
          omega
        rw [hM, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
      rw [hf1, mul_one]
    rw [hCsum, Nat.cast_add, hpow]
    ring
  have hx : ((2 ^ r : ℕ) : ZMod (2 ^ f - 1)) =
      2 * ((2 ^ r : ℕ) : ZMod (2 ^ f - 1)) := (hcon r hr).trans hCz
  have hzero : ((2 ^ r : ℕ) : ZMod (2 ^ f - 1)) = 0 := by
    have h2 := congrArg (fun t => t - ((2 ^ r : ℕ) : ZMod (2 ^ f - 1))) hx
    rw [sub_self, two_mul, add_sub_cancel_left] at h2
    exact h2.symm
  have hdiv : 2 ^ f - 1 ∣ 2 ^ r :=
    (ZMod.natCast_eq_zero_iff (2 ^ r) (2 ^ f - 1)).mp hzero
  have hone : 2 ^ f - 1 ∣ 1 :=
    (c2slomqmea_m_coprime_pow (by omega : 1 ≤ f) r).dvd_of_dvd_mul_right
      (by simpa using hdiv)
  have hle1 : 2 ^ f - 1 ≤ 1 := Nat.le_of_dvd (by norm_num) hone
  have hge : 3 ≤ 2 ^ f - 1 := by
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  omega

private lemma c2slomqmea_bad_h {f C : ℕ} (hf : 2 ≤ f) (hC1 : 1 ≤ C)
    (hCQ : C < (2 ^ f - 1) * (2 ^ f + 1)) (hpow : ∀ u, C ≠ 2 ^ u)
    (d : ZMod (2 ^ f + 1)) :
    ∃ u ∈ C.bitIndices, ((2 ^ u : ℕ) : ZMod (2 ^ f + 1)) ≠ d := by
  have hC_lt : C < 2 ^ (2 * f) := c2slomqmea_lt_two_pow hCQ
  have hbits_lt : ∀ u ∈ C.bitIndices, u < 2 * f := c2slomqmea_bits_lt hC_lt
  obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := c2slomqmea_two_mem hC1 hpow
  have hInj : ∀ u v, u ∈ C.bitIndices → v ∈ C.bitIndices →
      ((2 ^ u : ℕ) : ZMod (2 ^ f + 1)) = ((2 ^ v : ℕ) : ZMod (2 ^ f + 1)) → u = v := by
    intro u v hu hv heq
    have hmod : Nat.ModEq (2 ^ f + 1) (2 ^ u) (2 ^ v) :=
      (ZMod.natCast_eq_natCast_iff (2 ^ u) (2 ^ v) (2 ^ f + 1)).mp heq
    exact c2slomqmea_h_pow_inj hf (hbits_lt u hu) (hbits_lt v hv) hmod
  by_cases hd : ((2 ^ u₁ : ℕ) : ZMod (2 ^ f + 1)) = d
  · refine ⟨u₂, hu₂, ?_⟩
    intro h
    have heq : ((2 ^ u₂ : ℕ) : ZMod (2 ^ f + 1)) =
        ((2 ^ u₁ : ℕ) : ZMod (2 ^ f + 1)) := h.trans hd.symm
    exact hne.symm (hInj u₂ u₁ hu₂ hu₁ heq)
  · exact ⟨u₁, hu₁, hd⟩

theorem omq_minus_exists_digit {f : ℕ} (hf : 2 ≤ f) {m h : ℕ} (hm : m = 2 ^ f - 1)
    (hh : h = 2 ^ f + 1) {C : ℕ} (hC1 : 1 ≤ C) (hCQ : C < m * h) (hpow : ∀ u : ℕ, C ≠ 2 ^ u) :
    (∃ u : ℕ, Odd (Nat.choose C (2 ^ u)) ∧ ((2 ^ u : ℕ) : ZMod m) ≠ (C : ZMod m)) ∧
      ∀ d : ZMod h, ∃ u : ℕ, Odd (Nat.choose C (2 ^ u)) ∧ ((2 ^ u : ℕ) : ZMod h) ≠ d := by
  subst m
  subst h
  constructor
  · obtain ⟨u, hu, hbad⟩ := c2slomqmea_bad_m hf hC1 hCQ hpow
    exact ⟨u, c2slomqmea_odd_choose_two_pow (Nat.mem_bitIndices.mp hu), hbad⟩
  · intro d
    obtain ⟨u, hu, hbad⟩ := c2slomqmea_bad_h hf hC1 hCQ hpow d
    exact ⟨u, c2slomqmea_odd_choose_two_pow (Nat.mem_bitIndices.mp hu), hbad⟩

theorem omq_minus_not_pow_two {f κ : ℕ} (hf : 2 ≤ f) (hκ1 : 1 ≤ κ) (hκ3 : κ ≤ 3) {m h : ℕ}
    (hm : m = 2 ^ f - 1) (hh : h = 2 ^ f + 1) {a : ZMod m} {d : ZMod h} {C : ℕ}
    (hCa : (C : ZMod m) = 2 * a) (hCd : (C : ZMod h) = 2 * d)
    (ha : ((2 ^ κ - 1 : ℕ) : ZMod m) * a = 0) (hd : ((2 ^ κ - 1 : ℕ) : ZMod h) * d = 0) :
    ∀ u : ℕ, C ≠ 2 ^ u := by
  subst m
  subst h
  intro u hC
  have hkm : ((2 ^ κ - 1 : ℕ) : ZMod (2 ^ f - 1)) * (C : ZMod (2 ^ f - 1)) = 0 := by
    rw [hCa]
    calc ((2 ^ κ - 1 : ℕ) : ZMod (2 ^ f - 1)) * (2 * a)
        = 2 * (((2 ^ κ - 1 : ℕ) : ZMod (2 ^ f - 1)) * a) := by ring
      _ = 0 := by rw [ha, mul_zero]
  have hkh : ((2 ^ κ - 1 : ℕ) : ZMod (2 ^ f + 1)) * (C : ZMod (2 ^ f + 1)) = 0 := by
    rw [hCd]
    calc ((2 ^ κ - 1 : ℕ) : ZMod (2 ^ f + 1)) * (2 * d)
        = 2 * (((2 ^ κ - 1 : ℕ) : ZMod (2 ^ f + 1)) * d) := by ring
      _ = 0 := by rw [hd, mul_zero]
  have hKm : (((2 ^ κ - 1) * C : ℕ) : ZMod (2 ^ f - 1)) = 0 := by
    push_cast
    exact hkm
  have hKh : (((2 ^ κ - 1) * C : ℕ) : ZMod (2 ^ f + 1)) = 0 := by
    push_cast
    exact hkh
  have hdivm : 2 ^ f - 1 ∣ (2 ^ κ - 1) * C :=
    (ZMod.natCast_eq_zero_iff ((2 ^ κ - 1) * C) (2 ^ f - 1)).mp hKm
  have hdivh : 2 ^ f + 1 ∣ (2 ^ κ - 1) * C :=
    (ZMod.natCast_eq_zero_iff ((2 ^ κ - 1) * C) (2 ^ f + 1)).mp hKh
  have hdm : 2 ^ f - 1 ∣ 2 ^ κ - 1 := by
    rw [hC] at hdivm
    exact (c2slomqmea_m_coprime_pow (by omega : 1 ≤ f) u).dvd_of_dvd_mul_right hdivm
  have hdh : 2 ^ f + 1 ∣ 2 ^ κ - 1 := by
    rw [hC] at hdivh
    exact (c2slomqmea_h_coprime_pow (by omega : 1 ≤ f) u).dvd_of_dvd_mul_right hdivh
  have hprod : (2 ^ f - 1) * (2 ^ f + 1) ∣ 2 ^ κ - 1 :=
    (c2slomqmea_m_h_coprime (by omega : 1 ≤ f)).mul_dvd_of_dvd_of_dvd hdm hdh
  have hKpos : 0 < 2 ^ κ - 1 := by
    have : 1 < 2 ^ κ := Nat.one_lt_two_pow (by omega)
    omega
  have hle := Nat.le_of_dvd hKpos hprod
  have hKle : 2 ^ κ - 1 ≤ 7 := by
    have : 2 ^ κ ≤ 8 := by
      calc 2 ^ κ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hκ3
        _ = 8 := by norm_num
    omega
  have hge : 15 ≤ (2 ^ f - 1) * (2 ^ f + 1) := by
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have h1 : 3 ≤ 2 ^ f - 1 := by omega
    have h2 : 5 ≤ 2 ^ f + 1 := by omega
    calc 15 = 3 * 5 := by norm_num
      _ ≤ (2 ^ f - 1) * (2 ^ f + 1) := Nat.mul_le_mul h1 h2
  omega

end CFSG.LocalAnalysis.WeakClosure81
