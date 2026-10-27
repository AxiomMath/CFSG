module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Subgroup

private lemma two_pow_eq_one_iff_dvd_sub_one {p e : ℕ} :
    (2 : ZMod p) ^ e = 1 ↔ p ∣ 2 ^ e - 1 := by
  have hcast : ((2 ^ e : ℕ) : ZMod p) = (2 : ZMod p) ^ e := Nat.cast_pow 2 e
  rw [← hcast, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff (2 ^ e) 1 p, Nat.ModEq.comm,
    Nat.modEq_iff_dvd' (a := 1) (b := 2 ^ e) (n := p) Nat.one_le_two_pow]

theorem lt_dParam_of_two_pow_sub_one_le {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime)
    (h : 2 ^ (k + 1) - 1 ≤ p) : k < dParam p := by
  have hp3 : 3 ≤ p := by
    have h2 : 2 ≤ k + 1 := by omega
    have h4 : 4 ≤ 2 ^ (k + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) h2
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hdvd : dParam p ∣ p - 1 := by
    unfold dParam
    exact ZMod.orderOf_dvd_card_sub_one h2
  by_contra hle
  have hle' : dParam p ≤ k := Nat.le_of_not_lt hle
  have hdpos : 0 < dParam p := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hpdvd : p ∣ 2 ^ dParam p - 1 :=
    (two_pow_eq_one_iff_dvd_sub_one).1 (pow_dParam p)
  have hpos : 0 < 2 ^ dParam p - 1 := by
    have hge : 2 ≤ 2 ^ dParam p := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ dParam p := Nat.pow_le_pow_right (by norm_num) hdpos
    omega
  have hlt : 2 ^ dParam p - 1 < p := by
    have h1 : 2 ^ dParam p - 1 ≤ 2 ^ k - 1 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) hle') 1
    have h2 : 2 ^ k - 1 < 2 ^ (k + 1) - 1 :=
      Nat.sub_lt_sub_right Nat.one_le_two_pow
        (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))
    omega
  have := Nat.le_of_dvd hpos hpdvd
  omega

theorem eq_of_dvd_two_pow_sub_one {k p e : ℕ} (hk : k = 1 ∨ k = 2) (hp : p.Prime)
    (hpk : 2 ^ (k + 1) - 1 ≤ p) (he1 : 1 ≤ e) (he2 : e ≤ 2 * k) (hev : Even e)
    (hdvd : p ∣ 2 ^ e - 1) : k = 1 ∧ p = 3 ∧ e = 2 := by
  rcases hk with rfl | rfl
  · have he : e = 2 := by
      obtain ⟨j, hj⟩ := hev
      omega
    rw [he] at hdvd ⊢
    have hp3 : p = 3 := by
      have hd : p ∣ 3 := by norm_num at hdvd ⊢; exact hdvd
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd
    exact ⟨rfl, hp3, rfl⟩
  · exfalso
    have hp7 : 7 ≤ p := by
      have h : 2 ^ (2 + 1) - 1 = 7 := by norm_num
      omega
    obtain ⟨j, hj⟩ := hev
    have he_cases : e = 2 ∨ e = 4 := by omega
    rcases he_cases with rfl | rfl
    · have hd : p ∣ 3 := by norm_num at hdvd ⊢; exact hdvd
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd
      omega
    · have hd : p ∣ 15 := by norm_num at hdvd ⊢; exact hdvd
      rw [show (15 : ℕ) = 3 * 5 by norm_num] at hd
      rcases (hp.dvd_mul).1 hd with h3 | h5
      · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
        omega
      · have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5
        omega

theorem exists_generator_of_card_eq_prime {H : Type*} [Group H] {X : Subgroup H} {p : ℕ}
    (hp : p.Prime) (hX : Nat.card X = p) : ∃ x : H, orderOf x = p ∧ X = Subgroup.zpowers x := by
  have hp0 : Nat.card X ≠ 0 := by rw [hX]; exact hp.ne_zero
  haveI : Finite X := Nat.finite_of_card_ne_zero hp0
  have h2 : 1 < Nat.card X := by rw [hX]; exact hp.one_lt
  haveI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp h2
  obtain ⟨y, hy⟩ := exists_ne (1 : X)
  have hx_ne : (y : H) ≠ 1 := fun h => hy (Subtype.ext h)
  have hdvd : orderOf (y : H) ∣ p := by
    rw [← hX]
    exact Subgroup.orderOf_dvd_natCard X y.2
  have horder : orderOf (y : H) = p := by
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hx_ne
    · exact hp'
  refine ⟨(y : H), horder, ?_⟩
  have hle : Subgroup.zpowers (y : H) ≤ X := by
    rw [Subgroup.zpowers_le]; exact y.2
  have hcard : Nat.card X ≤ Nat.card (Subgroup.zpowers (y : H)) := by
    rw [Nat.card_zpowers, horder, hX]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem mul_mul_inv_eq_inv_of_not_commute {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x b : H} (hx : orderOf x = p) (hb : orderOf b = 2)
    (hbx : b * x * b⁻¹ ∈ Subgroup.zpowers x) (hnc : b * x ≠ x * b) :
    b * x * b⁻¹ = x⁻¹ := by
  have hb2 : b ^ 2 = 1 := by simpa [hb] using pow_orderOf_eq_one b
  have hbb : b * b = 1 := by rw [← pow_two]; exact hb2
  have hbinv : b⁻¹ = b := (inv_eq_iff_mul_eq_one).2 hbb
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hbx
  have hleft : b * (b * x * b⁻¹) * b⁻¹ = x := by
    rw [hbinv]
    calc b * (b * x * b) * b = (b * b) * x * (b * b) := by group
      _ = x := by rw [hbb]; simp
  have hright : (b * x * b⁻¹) ^ j = x ^ (j * j) := by
    rw [← hj, zpow_mul]
  have hconj : b * (b * x * b⁻¹) * b⁻¹ = (b * x * b⁻¹) ^ j := by
    conv_lhs => rw [← hj]
    exact (conj_zpow (i := j) (a := b) (b := x)).symm
  have hxx : x ^ (j * j) = x := by
    rw [← hright, ← hconj, hleft]
  have hpdvd : (p : ℤ) ∣ j * j - 1 := by
    rw [← hx, orderOf_dvd_iff_zpow_eq_one, zpow_sub_one, hxx, mul_inv_cancel]
  have hfac : j * j - 1 = (j - 1) * (j + 1) := by ring
  rw [hfac] at hpdvd
  rcases Int.Prime.dvd_mul' hp hpdvd with h | h
  · exfalso
    apply hnc
    have h1 : x ^ (j - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hx]; exact h
    have hx1 : x ^ j = x := by
      conv_lhs => rw [show j = (j - 1) + 1 by ring]
      rw [zpow_add_one, h1, one_mul]
    have hbxb : b * x * b⁻¹ = x := by rw [← hj, hx1]
    conv_rhs => rw [← hbxb]
    group
  · have h1 : x ^ (j + 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hx]; exact h
    have h2 : x ^ j * x = 1 := by rwa [zpow_add_one] at h1
    rw [← hj, ← mul_eq_one_iff_eq_inv]
    exact h2

theorem card_eq_two_mul_card_inf_centralizer {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : H} (hx : orderOf x = p) {B : Subgroup H} [Finite B]
    (hBab : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a) (hB2 : ∀ a ∈ B, a ^ 2 = 1)
    (hBx : ∀ a ∈ B, a * x * a⁻¹ ∈ Subgroup.zpowers x) {b : H} (hbB : b ∈ B)
    (hbx : b * x ≠ x * b) :
    Nat.card B = 2 * Nat.card ↥(B ⊓ Subgroup.centralizer ({x} : Set H)) := by
  set D : Subgroup H := B ⊓ Subgroup.centralizer ({x} : Set H) with hD
  have hmemD : ∀ c : H, c ∈ D ↔ c ∈ B ∧ c * x = x * c := by
    intro c
    rw [hD, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hcB, hc⟩
      exact ⟨hcB, (hc x (Set.mem_singleton x)).symm⟩
    · rintro ⟨hcB, hc⟩
      exact ⟨hcB, fun h hh => by rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hc.symm⟩
  have hK : ∀ a ∈ B, a * x ≠ x * a → a * x * a⁻¹ = x⁻¹ := by
    intro a ha hane
    have ha1 : a ≠ 1 := by
      intro h; exact hane (by rw [h, one_mul, mul_one])
    have hord : orderOf a = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (hB2 a ha) ha1
    exact mul_mul_inv_eq_inv_of_not_commute hp hp2 hx hord (hBx a ha) hane
  have hrel : D.relIndex B = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨b, hbB, fun c hc => ?_⟩
    rw [xor_def]
    by_cases hcD : c ∈ D
    · right
      refine ⟨hcD, fun hcbD => ?_⟩
      have hbD : b ∈ D := by
        have h1 : c⁻¹ * (c * b) ∈ D := D.mul_mem (D.inv_mem hcD) hcbD
        simpa using h1
      exact hbx ((hmemD b).1 hbD).2
    · left
      have hcne : c * x ≠ x * c := fun h => hcD ((hmemD c).2 ⟨hc, h⟩)
      have hbD : b ∉ D := fun hbD => hbx ((hmemD b).1 hbD).2
      have hc_inv : c * x * c⁻¹ = x⁻¹ := hK c hc hcne
      have hb_inv : b * x * b⁻¹ = x⁻¹ := hK b hbB hbx
      have hconj : c * b * x * (c * b)⁻¹ = x := by
        calc c * b * x * (c * b)⁻¹ = c * (b * x * b⁻¹) * c⁻¹ := by group
          _ = c * x⁻¹ * c⁻¹ := by rw [hb_inv]
          _ = (c * x * c⁻¹)⁻¹ := by group
          _ = x := by rw [hc_inv, inv_inv]
      have hcomm : c * b * x = x * (c * b) := by
        conv_rhs => rw [← hconj]
        group
      exact ⟨(hmemD (c * b)).2 ⟨B.mul_mem hc hbB, hcomm⟩, hcD⟩
  have hDB : D ≤ B := by rw [hD]; exact inf_le_left
  have hcard := Subgroup.relIndex_mul_card (H := D) (K := B)
  rw [hrel, inf_of_le_left hDB] at hcard
  rw [← hcard, hD]

private lemma fixV_invariant {W : Type} [CommGroup W] {G X : Subgroup (MulAut W)}
    (hXnorm : ∀ g ∈ G, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    ∀ g ∈ G, ∀ y ∈ fixV X, g y ∈ fixV X := by
  intro g hg y hy
  rw [mem_fixV] at hy ⊢
  intro x hx
  have hg' : g⁻¹ ∈ G := G.inv_mem hg
  have hx' : g⁻¹ * x * g ∈ X := hXnorm g⁻¹ hg' x hx
  calc x (g y) = g ((g⁻¹ * x * g) y) := by
        simp only [MulAut.mul_apply, MulAut.apply_inv_self]
    _ = g y := by rw [hy _ hx']

theorem fixV_eq_bot_of_normal {W : Type} [CommGroup W] {G X : Subgroup (MulAut W)}
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hXnorm : ∀ g ∈ G, ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hX : X ≠ ⊥) : fixV X = ⊥ := by
  rcases hirr (fixV X) (fixV_invariant hXnorm) with h | h
  · exact h
  · exfalso
    apply hX
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    ext w
    have hw : w ∈ fixV X := by rw [h]; exact Subgroup.mem_top w
    exact (mem_fixV.mp hw) x hx

theorem pCoreOf_eq_bot_of_irreducible {W : Type} [CommGroup W] [Finite W] [Nontrivial W]
    (hW : ∀ w : W, w ^ 2 = 1) {G : Subgroup (MulAut W)}
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤) :
    pCoreOf 2 G = ⊥ := by
  set Q : Subgroup (MulAut W) := pCoreOf 2 G with hQ
  have hQnorm : G ≤ Subgroup.normalizer (Q : Set (MulAut W)) := by
    rw [hQ]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G
  have hQnormmem : ∀ g ∈ G, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
    intro g hg q hq
    exact ((Subgroup.mem_normalizer_iff.mp (hQnorm hg)) q).mp hq
  have hQp : IsPGroup 2 Q := by
    rw [hQ]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hfix : (MulAction.fixedPoints Q W : Set W) = (fixV Q : Set W) := by
    ext w
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, mem_fixV, Subgroup.smul_def,
      MulAut.smul_def]
    exact ⟨fun h q hq => h ⟨q, hq⟩, fun h q => h q q.2⟩
  have h1mem : (1 : W) ∈ MulAction.fixedPoints Q W := by
    rw [MulAction.mem_fixedPoints]
    intro q
    simp [Subgroup.smul_def, MulAut.smul_def]
  have hW2 : 2 ∣ Nat.card W := by
    obtain ⟨w, hw⟩ := exists_ne (1 : W)
    have hord : orderOf w = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (hW w) hw
    exact hord ▸ orderOf_dvd_natCard w
  have hcong : Nat.card W ≡ Nat.card (MulAction.fixedPoints Q W) [MOD 2] :=
    hQp.card_modEq_card_fixedPoints W
  have hFdvd : 2 ∣ Nat.card (MulAction.fixedPoints Q W) :=
    Nat.modEq_zero_iff_dvd.mp (hcong.symm.trans (Nat.modEq_zero_iff_dvd.mpr hW2))
  have hFpos : 0 < Nat.card (MulAction.fixedPoints Q W) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, h1mem⟩⟩, inferInstance⟩
  have hFge2 : 2 ≤ Nat.card (MulAction.fixedPoints Q W) := Nat.le_of_dvd hFpos hFdvd
  have hcardfix : Nat.card (fixV Q) = Nat.card (MulAction.fixedPoints Q W) :=
    Nat.card_congr (Set.equivOfEq hfix.symm)
  have hfixne : fixV Q ≠ ⊥ := by
    intro hbot
    have hle : 2 ≤ Nat.card (fixV Q) := by rw [hcardfix]; exact hFge2
    rw [hbot] at hle
    have : Nat.card (⊥ : Subgroup W) = 1 := Nat.card_unique
    omega
  rcases hirr (fixV Q) (fixV_invariant hQnormmem) with hbot | htop
  · exact absurd hbot hfixne
  · rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    ext w
    have hw : w ∈ fixV Q := by rw [htop]; exact Subgroup.mem_top w
    exact (mem_fixV.mp hw) q hq

end CFSG.LocalAnalysis.WeakClosure81
