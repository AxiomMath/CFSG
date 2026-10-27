module

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.G11.Harris.L2

theorem shift_iter_mem {n d : ℕ} {J : Finset ℕ} (hshift : J.image (fun i => (i + d) % n) = J)
    {i : ℕ} (hi : i ∈ J) (hin : i < n) : ∀ k : ℕ, (i + k * d) % n ∈ J := by
  intro k
  induction k with
  | zero => simpa [Nat.mod_eq_of_lt hin] using hi
  | succ k ih =>
    have h1 : ((i + k * d) % n + d) % n ∈ J := by
      rw [← hshift]
      exact Finset.mem_image_of_mem _ ih
    have h2 : ((i + k * d) % n + d) % n = (i + (k + 1) * d) % n := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_mul, one_mul, add_assoc]
    rwa [h2] at h1

theorem orbit_inj_aux {n d i : ℕ} (hn : 0 < n) {k k' : ℕ} (hle : k ≤ k')
    (hk' : k' < n / Nat.gcd n d) (hkk : (i + k * d) % n = (i + k' * d) % n) : k = k' := by
  set g := Nat.gcd n d with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left d hn
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  have hgd : g ∣ d := Nat.gcd_dvd_right n d
  set s := n / g with hs
  have hsg : s * g = n := Nat.div_mul_cancel hgn
  have hsub : (i + k' * d) - (i + k * d) = (k' - k) * d := by
    rw [Nat.sub_mul, Nat.add_sub_add_left]
  have hdvd : n ∣ (k' - k) * d := by
    rw [← hsub]
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hkk.symm)
  have hcop : Nat.Coprime s (d / g) := by
    rw [hs]
    exact Nat.coprime_div_gcd_div_gcd hg0
  have hdvd' : s ∣ (k' - k) * (d / g) := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c, ?_⟩
    have h2 : (k' - k) * d = (k' - k) * (d / g) * g := by
      rw [Nat.mul_assoc, Nat.div_mul_cancel hgd]
    have h3 : n * c = s * c * g := by rw [← hsg]; ring
    rw [h2, h3] at hc
    exact Nat.eq_of_mul_eq_mul_right hg0 hc
  have hs' : s ∣ k' - k := hcop.dvd_of_dvd_mul_right hdvd'
  have hlt : k' - k < s := by omega
  have h0 : k' - k = 0 := Nat.eq_zero_of_dvd_of_lt hs' hlt
  omega

theorem le_card_mul_gcd {n d : ℕ} (hn : 0 < n) {J : Finset ℕ} (hJne : J.Nonempty)
    (hJn : ∀ i ∈ J, i < n) (hshift : J.image (fun i => (i + d) % n) = J) :
    n ≤ J.card * Nat.gcd n d := by
  obtain ⟨i, hi⟩ := hJne
  set g := Nat.gcd n d with hg
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  set s := n / g with hs
  have hsg : s * g = n := Nat.div_mul_cancel hgn
  have hinj : Set.InjOn (fun k : ℕ => (i + k * d) % n) (Finset.range s : Set ℕ) := by
    intro k hk k' hk' hkk
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    rcases le_total k k' with hle | hle
    · exact orbit_inj_aux hn hle hk' hkk
    · exact (orbit_inj_aux hn hle hk hkk.symm).symm
  have hsub : (Finset.range s).image (fun k : ℕ => (i + k * d) % n) ⊆ J := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    exact shift_iter_mem hshift hi (hJn i hi) k
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  calc n = s * g := hsg.symm
    _ ≤ J.card * g := Nat.mul_le_mul_right g hcard

theorem four_mul_le_two_pow {w : ℕ} (hw : 4 ≤ w) : 4 * w ≤ 2 ^ w := by
  induction w, hw using Nat.le_induction with
  | base => norm_num
  | succ w hw ih =>
    rw [pow_succ]
    have : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    omega

theorem l2_numerics {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) {J : Finset ℕ} (hJne : J.Nonempty)
    (hJn : ∀ i ∈ J, i < n) (hshift : J.image (fun i => (i + d) % n) = J)
    (hdim : d * 2 ^ J.card ≤ 2 * n + 2) :
    (J.card = 1 ∧ d = n) ∨ (J.card = 2 ∧ n = 2 * d) ∨ (J.card = 3 ∧ n = 3 ∧ d = 1) := by
  have hkey := le_card_mul_gcd (by omega : 0 < n) hJne hJn hshift
  set g := Nat.gcd n d with hg
  have hgd : g ∣ d := Nat.gcd_dvd_right n d
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  have hgle : g ≤ d := Nat.le_of_dvd (by omega) hgd
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left d (by omega)
  have hw1 : 1 ≤ J.card := Finset.card_pos.mpr hJne
  rcases Nat.lt_or_ge J.card 4 with hw4 | hw4
  · interval_cases hw : J.card
    ·
      left
      refine ⟨rfl, ?_⟩
      have hgn' : g = n := le_antisymm (Nat.le_of_dvd (by omega) hgn) (by omega)
      have hnd : n ∣ d := hgn' ▸ hgd
      obtain ⟨c, hc⟩ := hnd
      norm_num at hdim
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith
    ·
      right; left
      refine ⟨rfl, ?_⟩
      norm_num at hdim
      have hg2 : g ≠ n := by
        intro h; omega
      obtain ⟨c, hc⟩ := hgn
      have hc2 : c = 2 := by
        rcases c with _ | _ | _ | c
        · omega
        · omega
        · rfl
        · nlinarith
      obtain ⟨e, he⟩ := hgd
      have he1 : e = 1 := by
        rcases e with _ | _ | e
        · omega
        · rfl
        · nlinarith
      subst hc2 he1
      omega
    ·
      right; right
      refine ⟨rfl, ?_⟩
      norm_num at hdim
      omega
  · exfalso
    have h1 := four_mul_le_two_pow hw4
    have h2 : n ≤ J.card * d := hkey.trans (Nat.mul_le_mul_left _ hgle)
    nlinarith

end CFSG.Quasithin.G11.Harris.L2
