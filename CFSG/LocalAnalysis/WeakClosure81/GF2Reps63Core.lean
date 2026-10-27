module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps63Dihedral
public import CFSG.GroupTheory.FixedCentralProductDescent

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

private theorem pow_mul_inv_conj {G : Type*} [Group G] {a y : G} (ha : a * a = 1)
    (hy : y * (a * y * a) = (a * y * a) * y) (j : ℕ) :
    (a * y * a * y⁻¹) ^ j = a * y ^ j * a * (y ^ j)⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hcomm : Commute (a * y * a) y⁻¹ :=
    (show Commute y (a * y * a) from hy).symm.inv_right
  calc
    (a * y * a * y⁻¹) ^ j = ((a * y * a) * y⁻¹) ^ j := rfl
    _ = (a * y * a) ^ j * (y⁻¹) ^ j := hcomm.mul_pow j
    _ = (a * y * a) ^ j * (y ^ j)⁻¹ := by rw [inv_pow]
    _ = a * y ^ j * a * (y ^ j)⁻¹ := by
          rw [show a * y * a = a * y * a⁻¹ by rw [ha'], conj_pow, ha']

private theorem fixes_pow_of_not_central {G : Type*} [Group G] {V : Type*} [CommGroup V]
    (σ : G →* MulAut V) {L : Subgroup G} {a : G} (ha : a * a = 1)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x)
    (hdisj : ∀ g ∈ L, (¬ ∀ y ∈ L, g * y = y * g) →
      commV (zpowers (σ a)) ⊓ commV (zpowers (σ (g * a * g⁻¹))) = ⊥)
    {y : G} (hyL : y ∈ L) {k : ℕ}
    (hnc : ¬ ∀ z ∈ L, y ^ k * z = z * y ^ k) :
    ∀ v : V, ((σ (a * y * a * y⁻¹)) ^ k) v = v → (σ (a * y * a * y⁻¹)) v = v := by
  have hdisj' : commV (zpowers (σ a)) ⊓
      commV (zpowers ((σ y) ^ k * σ a * ((σ y) ^ k)⁻¹)) = ⊥ := by
    simpa only [map_mul, map_pow, map_inv] using hdisj (y ^ k) (pow_mem hyL k) hnc
  have hcomm : Commute y (a * y * a) := hLa y hyL y hyL
  have haσ : σ a * σ a = 1 := by rw [← map_mul, ha, map_one]
  have hcommσ : Commute (σ y) (σ a * σ y * σ a) := by
    change σ y * (σ a * σ y * σ a) = (σ a * σ y * σ a) * σ y
    simpa only [map_mul] using congrArg σ hcomm
  have hmap : σ (a * y * a * y⁻¹) = σ a * (σ y * σ a * (σ y)⁻¹) := by
    simp only [map_mul, map_inv, mul_assoc]
  intro v hv
  rw [hmap] at hv ⊢
  exact fixes_of_commV_inf (a := σ a) (w := σ y) (k := k) haσ hcommσ hdisj' hv

private theorem odd_dvd_of_dvd_two_pow_mul {r f n' : ℕ} (hr : Odd r)
    (h : r ∣ 2 ^ f * n') : r ∣ n' := by
  have hcop : Nat.Coprime r (2 ^ f) := (Nat.coprime_two_right.mpr hr).pow_right f
  exact (hcop.dvd_mul_left).mp h

private theorem eq_one_of_odd_dvd_two_pow {r f : ℕ} (hr : Odd r) (h : r ∣ 2 ^ f) : r = 1 := by
  have hcop : Nat.Coprime r (2 ^ f) := (Nat.coprime_two_right.mpr hr).pow_right f
  exact Nat.dvd_one.mp (hcop.dvd_of_dvd_mul_right (by simpa using h))

private theorem not_dvd_two_mul_of_odd {r n : ℕ} (hn : Odd n) : ¬ 2 * r ∣ n := by
  intro h
  exact hn.not_two_dvd_nat (dvd_trans (show 2 ∣ 2 * r from ⟨r, rfl⟩) h)

private theorem not_dvd_two_pow_mul_two_of_two_le {e r n' : ℕ} (he : 2 ≤ e)
    (hrn : r ∣ n') (hn' : Odd n') : ¬ 2 ^ e * r ∣ n' * 2 := by
  intro h
  have h2e : 2 ^ e ∣ n' * 2 := dvd_trans (show 2 ^ e ∣ 2 ^ e * r from ⟨r, rfl⟩) h
  have hcop : Nat.Coprime (2 ^ e) n' := (Nat.coprime_two_left.mpr hn').pow_left e
  have h2 : 2 ^ e ∣ 2 := by
    rw [mul_comm] at h2e
    exact hcop.dvd_of_dvd_mul_right h2e
  have hle : 2 ^ e ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  have h4 : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by omega) he
  omega

private theorem false_of_two_le_e {G : Type*} [Group G] {U : Type*} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) (σ : G →* MulAut U) {L : Subgroup G} {a w : G}
    {m e f r n' : ℕ}
    (ha : a * a = 1)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x)
    (hdisj : ∀ g ∈ L, (¬ ∀ y ∈ L, g * y = y * g) →
      commV (zpowers (σ a)) ⊓ commV (zpowers (σ (g * a * g⁻¹))) = ⊥)
    (hker : ∀ y ∈ L, σ (a * y⁻¹ * a * y) = 1 → ∀ z ∈ L, y * z = z * y)
    (hw : w ∈ L) (hwm : ∀ k : ℕ, (∀ z ∈ L, w ^ k * z = z * w ^ k) ↔ m ∣ k)
    (hm_eq : m = 2 ^ e * r) (hN_eq : orderOf w = 2 ^ f * n')
    (hr_odd : Odd r) (hn' : Odd n') (hrn : r ∣ n') (he : 2 ≤ e) : False := by
  let y := w ^ n'
  have hyL : y ∈ L := pow_mem hw n'
  have hnc : ¬ ∀ z ∈ L, y ^ 2 * z = z * y ^ 2 := by
    intro hc
    have hc' : ∀ z ∈ L, w ^ (n' * 2) * z = z * w ^ (n' * 2) := by
      simpa [y, pow_mul] using hc
    have hdvd : m ∣ n' * 2 := (hwm (n' * 2)).mp hc'
    exact (not_dvd_two_pow_mul_two_of_two_le he hrn hn') (by simpa [hm_eq] using hdvd)
  have hfix := fixes_pow_of_not_central σ ha hLa hdisj hyL hnc
  have hy1 : y ^ 2 ^ f = 1 := by
    dsimp only [y]
    rw [← pow_mul, Nat.mul_comm n' (2 ^ f), ← hN_eq, pow_orderOf_eq_one]
  have hc1 : (a * y * a * y⁻¹) ^ 2 ^ f = 1 := by
    rw [pow_mul_inv_conj ha (hLa y hyL y hyL), hy1]
    simp [ha]
  have hr : (σ (a * y * a * y⁻¹)) ^ 2 ^ f = 1 := by
    rw [← map_pow, hc1, map_one]
  have hone : σ (a * y * a * y⁻¹) = 1 := eq_one_of_fixes_sq hU hr hfix
  have hcomm_inv : ∀ z ∈ L, y⁻¹ * z = z * y⁻¹ :=
    hker y⁻¹ (inv_mem hyL) (by simpa using hone)
  have hcomm : ∀ z ∈ L, y * z = z * y := by
    intro z hz
    exact Commute.inv_left_iff.mp (hcomm_inv z hz)
  have hdvd : m ∣ n' := (hwm n').mp (by simpa [y] using hcomm)
  exact (not_dvd_two_pow_mul_two_of_two_le he hrn hn')
    (by simpa [hm_eq] using dvd_mul_of_dvd_left hdvd 2)

private theorem false_of_e_eq_one {G : Type*} [Group G] {U : Type*} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) (σ : G →* MulAut U) {L : Subgroup G} {a w : G}
    {m e f r n' : ℕ}
    (ha : a * a = 1)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x)
    (hdisj : ∀ g ∈ L, (¬ ∀ y ∈ L, g * y = y * g) →
      commV (zpowers (σ a)) ⊓ commV (zpowers (σ (g * a * g⁻¹))) = ⊥)
    (hker : ∀ y ∈ L, σ (a * y⁻¹ * a * y) = 1 → ∀ z ∈ L, y * z = z * y)
    (hw : w ∈ L) (hwm : ∀ k : ℕ, (∀ z ∈ L, w ^ k * z = z * w ^ k) ↔ m ∣ k)
    (hm_eq : m = 2 ^ e * r) (hN_eq : orderOf w = 2 ^ f * n')
    (hr_odd : Odd r) (hn' : Odd n') (hm2 : m ≠ 2) (he : e = 1) : False := by
  let c := a * w * a * w⁻¹
  have hnc : ¬ ∀ z ∈ L, w ^ n' * z = z * w ^ n' := by
    intro hc
    have hdvd : m ∣ n' := (hwm n').mp hc
    rw [hm_eq, he, pow_one] at hdvd
    exact not_dvd_two_mul_of_odd hn' hdvd
  have hfixes : ∀ v, ((σ c) ^ n') v = v → (σ c) v = v := by
    simpa [c] using fixes_pow_of_not_central σ ha hLa hdisj hw (k := n') hnc
  have hcN : c ^ orderOf w = 1 := by
    dsimp [c]
    rw [pow_mul_inv_conj ha (hLa w hw w hw), pow_orderOf_eq_one]
    simp [ha]
  have hσN : (σ c) ^ orderOf w = 1 := by
    rw [← map_pow, hcN, map_one]
  let s := (σ c) ^ n'
  let t := (σ c) ^ 2 ^ f
  have hs : s ^ 2 ^ f = 1 := by
    dsimp [s]
    rw [← pow_mul, Nat.mul_comm n' (2 ^ f), ← hN_eq, hσN]
  have ht : t ^ n' = 1 := by
    dsimp [t]
    rw [← pow_mul, ← hN_eq, hσN]
  have hst : s * t = t * s := (Commute.pow_pow_self (σ c) n' (2 ^ f)).eq
  have hodd : Odd (orderOf t) :=
    hn'.of_dvd_nat (orderOf_dvd_of_pow_eq_one ht)
  have hfix' : ∀ v, s v = v → t v = v := by
    intro v hv
    have hcv : (σ c) v = v := hfixes v (by simpa [s] using hv)
    have hpow : ((σ c) ^ 2 ^ f) v = v :=
      CFSG.GroupTheory.mulAut_pow_apply_eq_self hcv (2 ^ f)
    simpa [t] using hpow
  have ht1 : t = 1 := eq_one_of_fixes_of_odd hU hst hs hodd hfix'
  have harg : σ (a * w ^ 2 ^ f * a * (w ^ 2 ^ f)⁻¹) = 1 := by
    rw [← pow_mul_inv_conj ha (hLa w hw w hw), map_pow]
    simpa [t, c] using ht1
  have hcomm_inv : ∀ z ∈ L, (w ^ 2 ^ f)⁻¹ * z = z * (w ^ 2 ^ f)⁻¹ :=
    hker (w ^ 2 ^ f)⁻¹ (inv_mem (pow_mem hw (2 ^ f))) (by simpa using harg)
  have hcomm : ∀ z ∈ L, w ^ 2 ^ f * z = z * w ^ 2 ^ f := by
    intro z hz
    exact Commute.inv_left_iff.mp (hcomm_inv z hz)
  have hdvd : m ∣ 2 ^ f := (hwm (2 ^ f)).mp hcomm
  have hr_dvd : r ∣ 2 ^ f := by
    have hrm : r ∣ m := ⟨2 ^ e, by rw [hm_eq, mul_comm]⟩
    exact hrm.trans hdvd
  have hr1 : r = 1 := eq_one_of_odd_dvd_two_pow hr_odd hr_dvd
  exact hm2 (by rw [hm_eq, he, hr1, pow_one, mul_one])

theorem false_of_commV_inf_eq_bot {G : Type*} [Group G] [Finite G] {U : Type*} [CommGroup U]
    [Finite U] (hU : ∀ u : U, u ^ 2 = 1) (σ : G →* MulAut U) {L : Subgroup G} {a : G}
    (ha : a * a = 1) (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x)
    (hdisj : ∀ g ∈ L, (¬ ∀ y ∈ L, g * y = y * g) →
      commV (zpowers (σ a)) ⊓ commV (zpowers (σ (g * a * g⁻¹))) = ⊥)
    (hker : ∀ y ∈ L, σ (a * y⁻¹ * a * y) = 1 → ∀ z ∈ L, y * z = z * y)
    {w : G} (hw : w ∈ L) {m : ℕ} (hm : Even m) (hm2 : m ≠ 2)
    (hwm : ∀ k : ℕ, (∀ z ∈ L, w ^ k * z = z * w ^ k) ↔ m ∣ k) : False := by
  have hNpos : 0 < orderOf w := orderOf_pos w
  have hmN : m ∣ orderOf w := (hwm (orderOf w)).mp (by
    intro z hz
    rw [pow_orderOf_eq_one w]
    simp)
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmN hNpos
  obtain ⟨e, r, hr_odd, hm_eq⟩ := Nat.exists_eq_two_pow_mul_odd hmpos.ne'
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with he0 | he
    · exfalso
      have hm_odd : Odd m := by
        rw [hm_eq, he0, pow_zero, one_mul]
        exact hr_odd
      exact (Nat.not_even_iff_odd.mpr hm_odd) hm
    · exact he
  obtain ⟨f, n', hn'_odd, hN_eq⟩ := Nat.exists_eq_two_pow_mul_odd hNpos.ne'
  have hrN : r ∣ orderOf w :=
    (show r ∣ m from ⟨2 ^ e, by rw [hm_eq, mul_comm]⟩).trans hmN
  have hrn : r ∣ n' := by
    apply odd_dvd_of_dvd_two_pow_mul hr_odd
    rwa [hN_eq] at hrN
  by_cases he2 : 2 ≤ e
  · exact false_of_two_le_e hU σ ha hLa hdisj hker hw hwm hm_eq hN_eq
      hr_odd hn'_odd hrn he2
  · have he1 : e = 1 := by omega
    exact false_of_e_eq_one hU σ ha hLa hdisj hker hw hwm hm_eq hN_eq
      hr_odd hn'_odd hm2 he1

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
