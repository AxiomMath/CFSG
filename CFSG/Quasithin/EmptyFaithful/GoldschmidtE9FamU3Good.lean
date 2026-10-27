module

public import CFSG.Quasithin.EmptyFaithful.T1521SU3Zc

public section

namespace CFSG.Quasithin.U31521

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Goldschmidt
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)
open CFSG.ProperTwoGeneratedCore.RootCenter CFSG.ComponentClassification.AschbacherToolkit

variable {X : Type} [Group X]

section Good

variable [Finite X]

theorem exists_goodElt9 {n : ℕ} (hn3 : 3 ≤ n) (hX : IsPSU 3 2 n X)
    (R : Sylow 2 X) {β : MulAut X} (hβ : β ∈ autStab (R : Subgroup X)) (hβ2 : β ^ 2 = 1) :
    ∃ r w : X, r ∈ (R : Subgroup X) ∧ w ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
      Odd (orderOf w) ∧ ((MulAut.conj r)⁻¹ * β) w = w ∧
      ∀ z ∈ sylowCenter (R : Subgroup X), w ^ 3 * z = z * w ^ 3 → z = 1 := by
  have hn : 2 ≤ n := by omega
  obtain ⟨e⟩ := nonempty_equiv_psu3_of_isPSU hn hX
  obtain ⟨D, hD⟩ := G3a.exists_borelSetup (bender_of_isPSU hn hX) R
  obtain ⟨hZc, hTc, hDc⟩ := hD.orders_psu3 hn e
  have hcase : (Nat.card (R : Subgroup X) = Nat.card (sylowCenter (R : Subgroup X)) ^ 2 ∧
        Nat.card D = Nat.card (sylowCenter (R : Subgroup X)) - 1) ∨
      (Nat.card (R : Subgroup X) = Nat.card (sylowCenter (R : Subgroup X)) ^ 3 ∧
        Nat.card D = (Nat.card (sylowCenter (R : Subgroup X)) ^ 2 - 1) /
          Nat.gcd 3 (Nat.card (sylowCenter (R : Subgroup X)) + 1)) := by
    right
    rw [hZc, hTc, hDc]
    exact ⟨rfl, rfl⟩
  obtain ⟨T', hT'ne, hDT'⟩ := hD.exists_fixed
  have hDeq := hD.normalizer_inf_eq hT'ne hDT'
  have hβS : β • R = R := Bender.Omega.smul_eq_of_mapsTo (fun s hs => (mem_autStab.mp hβ s).2 hs)
  obtain ⟨r, hr, hrT'⟩ := Bender.Omega.exists_conj_adjust hD.se hD.card hT'ne β hβS
  set β' : MulAut X := (MulAut.conj r)⁻¹ * β with hβ'
  have hβ'R : β' • R = R := by
    rw [hβ', mul_smul, hβS, inv_smul_eq_iff, Bender.Omega.conj_smul_self hr]
  have hβ'stab : β' ∈ autStab (R : Subgroup X) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (conj_mem_autStab hr)) hβ
  have hβ'D : ∀ d ∈ D, β' d ∈ D := by
    intro d hd
    rw [← hDeq] at hd ⊢
    have h1 := Bender.Omega.mem_normalizer_smul (α := β') hd.1
    have h2 := Bender.Omega.mem_normalizer_smul (α := β') hd.2
    rw [hβ'R] at h1
    rw [hrT'] at h2
    exact ⟨h1, h2⟩
  have hβ'2 : β' ^ 2 = 1 := by
    set y : X := (β r * r)⁻¹ with hy
    have hc : β * MulAut.conj r * β⁻¹ = MulAut.conj (β r) := mul_conj_mul_inv β r
    have hc' : β * (MulAut.conj r)⁻¹ * β⁻¹ = (MulAut.conj (β r))⁻¹ := by
      rw [← hc]
      group
    have hb2 : β * β = 1 := by rw [← pow_two]; exact hβ2
    have h1 : β' ^ 2 = MulAut.conj y := by
      calc β' ^ 2 = (MulAut.conj r)⁻¹ * (β * (MulAut.conj r)⁻¹ * β⁻¹) * (β * β) := by
            rw [hβ', pow_two]
            group
        _ = (MulAut.conj r)⁻¹ * (MulAut.conj (β r))⁻¹ := by rw [hc', hb2, mul_one]
        _ = MulAut.conj y := by
            rw [hy, map_inv, map_mul, mul_inv_rev]
    have hyR : y ∈ (R : Subgroup X) :=
      (R : Subgroup X).inv_mem ((R : Subgroup X).mul_mem ((mem_autStab.mp hβ r).2 hr) hr)
    have hyD : ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
      intro d hd
      have := hβ'D _ (hβ'D d hd)
      rw [← MulAut.mul_apply, ← pow_two, h1, MulAut.conj_apply] at this
      exact this
    have hyc : ∀ d ∈ D, d * y = y * d := by
      intro d hd
      have h2 : y * d * y⁻¹ * d⁻¹ ∈ D := D.mul_mem (hyD d hd) (D.inv_mem hd)
      have h3 : y * (d * y⁻¹ * d⁻¹) ∈ (R : Subgroup X) :=
        (R : Subgroup X).mul_mem hyR ((Subgroup.mem_normalizer_iff.mp (hD.le hd) y⁻¹).mp
          ((R : Subgroup X).inv_mem hyR))
      have h4 : y * d * y⁻¹ * d⁻¹ = y * (d * y⁻¹ * d⁻¹) := by group
      have h5 : y * d * y⁻¹ * d⁻¹ ∈ (R : Subgroup X) ⊓ D := ⟨h4 ▸ h3, h2⟩
      rw [hD.inf, Subgroup.mem_bot] at h5
      have : y * d = d * y := by
        have h6 : y * d * y⁻¹ = d := by
          calc y * d * y⁻¹ = (y * d * y⁻¹ * d⁻¹) * d := by group
            _ = d := by rw [h5, one_mul]
        calc y * d = (y * d * y⁻¹) * y := by group
          _ = d * y := by rw [h6]
      exact this.symm
    have hy1 : y = 1 := hD.eq_one_of_commute hyR hyc
    rw [h1, hy1, map_one]
  have hβ'Z : ∀ u ∈ sylowCenter (R : Subgroup X), β' u = u := fun u hu =>
    centralizes_center_of_sq_eq_one hn hX R hβ'stab hβ'2 (mem_sylowCenter.mp hu).1
      (fun y hy => ((mem_sylowCenter.mp hu).2 y hy).symm)
  obtain ⟨x, hxD, hxgen⟩ := hD.exists_gen
  have hxodd : Odd (orderOf x) := hD.odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hxD)
  set w : X := x * β' x with hw
  have hwD : w ∈ D := D.mul_mem hxD (hβ'D x hxD)
  have hwfix : β' w = w := by
    rw [hw, map_mul, show β' (β' x) = x from by
      rw [← MulAut.mul_apply, ← pow_two, hβ'2, MulAut.one_apply]]
    exact (hD.comm (hβ'D x hxD) hxD)
  have hwZ : ∀ z ∈ sylowCenter (R : Subgroup X), w * z * w⁻¹ = (x * x) * z * (x * x)⁻¹ := by
    intro z hz
    have hxz' : x * z * x⁻¹ ∈ sylowCenter (R : Subgroup X) := hD.conj_mem_center hxD hz
    have h1 : (β' x) * z * (β' x)⁻¹ = x * z * x⁻¹ := by
      have := hβ'Z _ hxz'
      rw [map_mul, map_mul, hβ'Z z hz, map_inv] at this
      exact this
    calc w * z * w⁻¹ = x * ((β' x) * z * (β' x)⁻¹) * x⁻¹ := by rw [hw]; group
      _ = x * (x * z * x⁻¹) * x⁻¹ := by rw [h1]
      _ = (x * x) * z * (x * x)⁻¹ := by group
  have hxx : x * x ∈ D := D.mul_mem hxD hxD
  have hpowstep : ∀ (y z' : X) (k : ℕ),
      y * (y ^ k * z' * (y ^ k)⁻¹) * y⁻¹ = y ^ (k + 1) * z' * (y ^ (k + 1))⁻¹ := by
    intro y z' k
    rw [pow_succ']
    group
  have hwpow : ∀ k : ℕ, ∀ z ∈ sylowCenter (R : Subgroup X),
      w ^ k * z * (w ^ k)⁻¹ = (x * x) ^ k * z * ((x * x) ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro z _; simp
    | succ k ih =>
      intro z hz
      have hz' : (x * x) ^ k * z * ((x * x) ^ k)⁻¹ ∈ sylowCenter (R : Subgroup X) :=
        hD.conj_mem_center (D.pow_mem hxx k) hz
      calc w ^ (k + 1) * z * (w ^ (k + 1))⁻¹
          = w * (w ^ k * z * (w ^ k)⁻¹) * w⁻¹ := (hpowstep w z k).symm
        _ = w * ((x * x) ^ k * z * ((x * x) ^ k)⁻¹) * w⁻¹ := by rw [ih z hz]
        _ = (x * x) * ((x * x) ^ k * z * ((x * x) ^ k)⁻¹) * (x * x)⁻¹ := hwZ _ hz'
        _ = (x * x) ^ (k + 1) * z * ((x * x) ^ (k + 1))⁻¹ := hpowstep (x * x) z k
  have hwodd : Odd (orderOf w) := hD.odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hwD)
  refine ⟨r, w, hr, hD.le hwD, hwodd, hwfix, fun z hz hwz => ?_⟩
  by_contra hz1
  have hx6z : x ^ 6 * z = z * x ^ 6 := by
    have h1 := hwpow 3 z hz
    have h2 : w ^ 3 * z * (w ^ 3)⁻¹ = z := by rw [hwz]; group
    rw [h2, ← sq, ← pow_mul, show 2 * 3 = 6 from rfl] at h1
    calc x ^ 6 * z = (x ^ 6 * z * (x ^ 6)⁻¹) * x ^ 6 := by group
      _ = z * x ^ 6 := by rw [← h1]
  have hx6K : x ^ 6 ∈ D ⊓ Subgroup.centralizer (sylowCenter (R : Subgroup X) : Set X) :=
    ⟨D.pow_mem hxD 6, hD.mem_centralizer_center (D.pow_mem hxD 6) hz hz1 hx6z⟩
  set K : Subgroup X := D ⊓ Subgroup.centralizer (sylowCenter (R : Subgroup X) : Set X) with hK
  have hcard := hD.card_eq_mul
  rw [hZc] at hcard
  have hordx : orderOf x = Nat.card D := by
    have hgen : ∀ y : ↥D, y ∈ Subgroup.zpowers (⟨x, hxD⟩ : ↥D) := by
      intro y
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hxgen y y.2)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
    have := orderOf_eq_card_of_forall_mem_zpowers hgen
    rwa [Subgroup.orderOf_mk] at this
  have hdvd : orderOf (x ^ 6) ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hx6K
  rw [orderOf_pow' x (by norm_num : (6 : ℕ) ≠ 0), hordx] at hdvd
  have hNpos : 0 < Nat.card D := Nat.card_pos
  obtain ⟨t, ht⟩ := hdvd
  have hg : Nat.gcd (Nat.card D) 6 ∣ Nat.card D := Nat.gcd_dvd_left _ _
  have hA : Nat.gcd (Nat.card D) 6 * (Nat.card D / Nat.gcd (Nat.card D) 6) = Nat.card D :=
    Nat.mul_div_cancel' hg
  have hApos : 0 < Nat.card D / Nat.gcd (Nat.card D) 6 :=
    Nat.div_pos (Nat.le_of_dvd hNpos hg) (Nat.gcd_pos_of_pos_left _ hNpos)
  have hgm : Nat.gcd (Nat.card D) 6 = (2 ^ n - 1) * t := by
    refine Nat.eq_of_mul_eq_mul_right hApos ?_
    calc Nat.gcd (Nat.card D) 6 * (Nat.card D / Nat.gcd (Nat.card D) 6) = Nat.card D := hA
      _ = (2 ^ n - 1) * Nat.card K := hcard
      _ = (2 ^ n - 1) * (Nat.card D / Nat.gcd (Nat.card D) 6 * t) := by rw [ht]
      _ = (2 ^ n - 1) * t * (Nat.card D / Nat.gcd (Nat.card D) 6) := by ring
  have hm6 : 2 ^ n - 1 ∣ 6 := (Dvd.intro t hgm.symm).trans (Nat.gcd_dvd_right _ _)
  have h7 : 7 ≤ 2 ^ n - 1 := by
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  exact absurd (Nat.le_of_dvd (by norm_num) hm6) (by omega)

end Good

end CFSG.Quasithin.U31521
