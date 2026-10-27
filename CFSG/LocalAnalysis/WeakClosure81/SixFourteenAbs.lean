module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenGrp
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem index_eq_two_pow_rkIdx (hW : ∀ w : W, w ^ 2 = 1) (H : Subgroup W) :
    H.index = 2 ^ rkIdx H := by
  have h1 : Nat.card H * H.index = Nat.card W := H.card_mul_index
  rw [card_eq_two_pow hW H, card_eq_two_pow_rk hW, ← rk_add_rkIdx H, pow_add] at h1
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h1

theorem fixV_ne_top_of_ne_bot {D : Subgroup (MulAut W)} (hD : D ≠ ⊥) : fixV D ≠ ⊤ := by
  intro htop
  apply hD
  rw [Subgroup.eq_bot_iff_forall]
  intro d hd
  ext w
  have hw : w ∈ fixV D := by rw [htop]; exact Subgroup.mem_top w
  exact mem_fixV.1 hw d hd

theorem fixV_invariant_of_commute {D : Subgroup (MulAut W)} {x : MulAut W}
    (hD : ∀ d ∈ D, d * x = x * d) :
    ∀ z ∈ Subgroup.zpowers x, ∀ y ∈ fixV D, z y ∈ fixV D := by
  intro z hz y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rw [mem_fixV] at hy ⊢
  intro d hd
  have hc : d * x ^ i = x ^ i * d := Commute.zpow_right (hD d hd) i
  calc d ((x ^ i) y) = (d * x ^ i) y := rfl
    _ = (x ^ i * d) y := by rw [hc]
    _ = (x ^ i) (d y) := rfl
    _ = (x ^ i) y := by rw [hy d hd]

theorem dvd_two_pow_sub_one_of_modEq {p a e : ℕ} (ha : a ≡ 1 [MOD p])
    (hae : a * 2 ^ e ≡ 1 [MOD p]) : p ∣ 2 ^ e - 1 := by
  have h1 : a * 2 ^ e ≡ 1 * 2 ^ e [MOD p] := ha.mul_right _
  rw [one_mul] at h1
  have h2 : 2 ^ e ≡ 1 [MOD p] := h1.symm.trans hae
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 h2.symm

theorem rkIdx_eq_two_of_modEq (hW : ∀ w : W, w ^ 2 = 1) {Y Z : Subgroup W} (hZY : Z ≤ Y)
    (hZ : rkIdx Z = 2) (hY : Y ≠ ⊤) (hWmod : Nat.card W ≡ 1 [MOD 3])
    (hYmod : Nat.card Y ≡ 1 [MOD 3]) : rkIdx Y = 2 := by
  have hle : rkIdx Y ≤ 2 := hZ ▸ rkIdx_anti hZY
  have hpos : 1 ≤ rkIdx Y := by
    by_contra h0
    have h0' : rkIdx Y = 0 := by omega
    apply hY
    rw [← Subgroup.index_eq_one, index_eq_two_pow_rkIdx hW Y, h0', pow_zero]
  by_contra hne
  have h1 : rkIdx Y = 1 := by omega
  have h2 : Nat.card Y * 2 = Nat.card W := by
    have := Y.card_mul_index
    rwa [index_eq_two_pow_rkIdx hW Y, h1, pow_one] at this
  have h3 : Nat.card Y * 2 ≡ 1 * 2 [MOD 3] := hYmod.mul_right 2
  rw [h2] at h3
  have h4 : 1 ≡ 1 * 2 [MOD 3] := hWmod.symm.trans h3
  exact absurd h4 (by decide)

theorem card_data_of_dihedral (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x b : MulAut W} (hx : orderOf x = p) (hb : orderOf b = 2) (hxb : b * x * b⁻¹ = x⁻¹)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {Ut At : Subgroup W}
    (hTU : fixV (Subgroup.zpowers b) ≤ Ut) (hUA : ∀ u ∈ Ut, b u * u⁻¹ ∈ At)
    (hAU : ∀ w : W, b w * w⁻¹ ∈ At → w ∈ Ut) {Bb : Subgroup (MulAut W)} (hbB : b ∈ Bb)
    (hBA : ∀ a ∈ At, ∀ β ∈ Bb, β a = a) (hBcard : Nat.card Bb * Ut.index = At.index) :
    At ≤ fixV (Subgroup.zpowers b) ∧ Nat.card W = Nat.card (fixV (Subgroup.zpowers b)) ^ 2 ∧
      Nat.card Bb = Nat.card (fixV (Subgroup.zpowers b)) ∧
      At.relIndex (fixV (Subgroup.zpowers b)) = Ut.index := by
  have hAT : At ≤ fixV (Subgroup.zpowers b) := fun a ha =>
    mem_fixV_zpowers_iff.2 (hBA a ha b hbB)
  obtain ⟨hTc, hWT⟩ := fixV_zpowers_eq_commSub_and_card hW hp hp2 hx hb hxb hfix
  have hbb : b * b = 1 := by
    have : b ^ 2 = 1 := by simpa [hb] using pow_orderOf_eq_one b
    rwa [pow_two] at this
  have hU := card_eq_card_mul_card hbb (hTc ▸ hAT) hTU hUA hAU
  set T := fixV (Subgroup.zpowers b) with hT
  have h1 : Nat.card Ut * Ut.index = Nat.card W := Ut.card_mul_index
  have h2 : Nat.card At * At.index = Nat.card W := At.card_mul_index
  have hpos1 : 0 < Nat.card At := Nat.card_pos
  have hpos2 : 0 < Ut.index := Nat.pos_of_ne_zero Ut.index_ne_zero_of_finite
  have hposT : 0 < Nat.card T := Nat.card_pos
  have h3 : Nat.card At * Ut.index = Nat.card T := by
    have : Nat.card T * (Nat.card At * Ut.index) = Nat.card T * Nat.card T := by
      calc Nat.card T * (Nat.card At * Ut.index) = Nat.card Ut * Ut.index := by rw [hU]; ring
        _ = Nat.card W := h1
        _ = Nat.card T * Nat.card T := by rw [hWT]; ring
    exact Nat.eq_of_mul_eq_mul_left hposT this
  have h4 : Nat.card Bb = Nat.card T := by
    have : Nat.card At * Ut.index * Nat.card Bb = Nat.card At * Ut.index * Nat.card T := by
      calc Nat.card At * Ut.index * Nat.card Bb
          = Nat.card At * (Nat.card Bb * Ut.index) := by ring
        _ = Nat.card At * At.index := by rw [hBcard]
        _ = Nat.card W := h2
        _ = Nat.card T * Nat.card T := by rw [hWT]; ring
        _ = Nat.card At * Ut.index * Nat.card T := by rw [h3]
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos1 hpos2) this
  refine ⟨hAT, hWT, h4, ?_⟩
  have h5 : At.relIndex T * Nat.card ↥(At ⊓ T) = Nat.card T := Subgroup.relIndex_mul_card At T
  rw [inf_eq_left.2 hAT] at h5
  have h6 : At.relIndex T * Nat.card At = Ut.index * Nat.card At := by
    rw [h5, ← h3, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos1 h6

theorem hyp139_data_of_dihedral (hW : ∀ w : W, w ^ 2 = 1) {k p : ℕ} (hk : k = 1 ∨ k = 2)
    (hp : p.Prime) (hpk : 2 ^ (k + 1) - 1 ≤ p) {x b : MulAut W} (hx : orderOf x = p)
    (hb : orderOf b = 2) (hxb : b * x * b⁻¹ = x⁻¹) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    {Ut At : Subgroup W} (hTU : fixV (Subgroup.zpowers b) ≤ Ut)
    (hUA : ∀ u ∈ Ut, b u * u⁻¹ ∈ At) (hAU : ∀ w : W, b w * w⁻¹ ∈ At → w ∈ Ut)
    (hUk : rkIdx Ut ≤ k) {Bb : Subgroup (MulAut W)} (hBab : IsElemAbelian2 Bb) (hbB : b ∈ Bb)
    (hBx : ∀ a ∈ Bb, a * x * a⁻¹ ∈ Subgroup.zpowers x) (hBA : ∀ a ∈ At, ∀ β ∈ Bb, β a = a)
    (hBcard : Nat.card Bb * Ut.index = At.index)
    (hkT : k < rkIdx (fixV (Subgroup.zpowers b))) :
    k = 1 ∧ p = 3 ∧ ∃ (n : ℕ) (Y : Subgroup W), Nat.card W = 4 ^ n ∧ 2 ≤ n ∧
      Nat.card ↥(Bb ⊓ Subgroup.centralizer ({x} : Set (MulAut W))) = 2 ^ (n - 1) ∧
      Y ≤ fixV (Bb ⊓ Subgroup.centralizer ({x} : Set (MulAut W))) ∧
      (∀ z ∈ Subgroup.zpowers x, ∀ y ∈ Y, z y ∈ Y) ∧ rkIdx Y = 2 := by
  have hp3 : 3 ≤ p := by
    have h4 : 2 ^ 2 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hAT, hWT, hBT, hrel⟩ :=
    card_data_of_dihedral hW hp hp2 hx hb hxb hfix hTU hUA hAU hbB hBA hBcard
  set T := fixV (Subgroup.zpowers b) with hT
  set n := rk ↥T with hn
  have hTcard : Nat.card T = 2 ^ n := card_eq_two_pow hW T
  have hWcard : Nat.card W = 4 ^ n := by
    rw [hWT, hTcard, ← pow_mul, mul_comm, pow_mul]
    norm_num
  have hrkT : rkIdx T = n := by
    have h1 : Nat.card T * T.index = Nat.card W := T.card_mul_index
    rw [hWT, sq] at h1
    have h2 : T.index = Nat.card T := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    unfold rkIdx
    rw [h2, hTcard, padicValNat.prime_pow]
  have hn2 : 2 ≤ n := by omega
  have hrkW : rk W = 2 * n := by
    have := rk_add_rkIdx T
    omega
  have hBcard' : Nat.card Bb = 2 ^ n := hBT.trans hTcard
  haveI hFin : Finite Bb := Nat.finite_of_card_ne_zero (by rw [hBcard']; positivity)
  have hbx : b * x ≠ x * b := by
    intro hc
    have h1 : b * x * b⁻¹ = x := by rw [hc]; group
    rw [h1] at hxb
    have hx2 : x ^ 2 = 1 := by
      have : x * x = 1 := mul_eq_one_iff_eq_inv.2 hxb
      rwa [← pow_two] at this
    have : p ∣ 2 := by rw [← hx]; exact orderOf_dvd_of_pow_eq_one hx2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hDc := card_eq_two_mul_card_inf_centralizer hp hp2 hx hBab.1 hBab.2 hBx hbB hbx
  have hDcard : Nat.card ↥(Bb ⊓ Subgroup.centralizer ({x} : Set (MulAut W))) = 2 ^ (n - 1) := by
    rw [hBcard'] at hDc
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hm, pow_succ] at hDc
    rw [hm, Nat.add_sub_cancel]
    omega
  set D := Bb ⊓ Subgroup.centralizer ({x} : Set (MulAut W)) with hD
  have hDx : ∀ d ∈ D, d * x = x * d := fun d hd =>
    (Subgroup.mem_centralizer_iff.1 hd.2 x (Set.mem_singleton x)).symm
  have hDne : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hDcard
    have h2 : 2 ^ 1 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hYtop : fixV D ≠ ⊤ := fixV_ne_top_of_ne_bot hDne
  have hYx : ∀ z ∈ Subgroup.zpowers x, ∀ y ∈ fixV D, z y ∈ fixV D :=
    fixV_invariant_of_commute hDx
  have hYx' : ∀ y ∈ fixV D, x y ∈ fixV D := fun y hy => hYx x (Subgroup.mem_zpowers x) y hy
  have hAY : At ≤ fixV D := fun a ha => mem_fixV.2 fun d hd => hBA a ha d hd.1
  set Z := orbitClosure x At with hZ
  have hZx : ∀ z ∈ Z, x z ∈ Z := fun z hz => apply_mem_orbitClosure x At hz
  have hZb : ∀ z ∈ Z, b z ∈ Z := fun z hz => apply_mem_orbitClosure_of_inverts hx hxb hAT hz
  have hZY : Z ≤ fixV D := orbitClosure_le hAY hYx'
  have he_ge : 1 ≤ rkIdx Z := by
    by_contra h0
    have h0' : rkIdx Z = 0 := by omega
    have hZtop : Z = ⊤ := by
      rw [← Subgroup.index_eq_one, index_eq_two_pow_rkIdx hW Z, h0', pow_zero]
    apply hYtop
    rw [eq_top_iff, ← hZtop]
    exact hZY
  have he_le : rkIdx Z ≤ 2 * k := by
    have h1 := index_orbitClosure_le hW hp hp2 hx hb hxb hfix hAT
    rw [hrel, index_eq_two_pow_rkIdx hW Ut, index_eq_two_pow_rkIdx hW Z] at h1
    have h2 : 2 ^ rkIdx Z ≤ 2 ^ (2 * k) := by
      calc 2 ^ rkIdx Z ≤ (2 ^ rkIdx Ut) ^ 2 := h1
        _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hUk) 2
        _ = 2 ^ (2 * k) := by rw [← pow_mul, mul_comm]
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have he_even : Even (rkIdx Z) := by
    have h1 := rk_add_rkIdx Z
    obtain ⟨r, hr⟩ := even_rk_of_invariant hW hp hp2 hx hb hxb hfix hZx hZb
    exact ⟨n - r, by omega⟩
  have hmodW : Nat.card W ≡ 1 [MOD p] := by
    have := card_modEq_one_of_fixV_eq_bot hp hx hfix (Y := ⊤) (fun y _ => Subgroup.mem_top _)
    simpa using this
  have hmodZ : Nat.card Z ≡ 1 [MOD p] := card_modEq_one_of_fixV_eq_bot hp hx hfix hZx
  have hdvd : p ∣ 2 ^ rkIdx Z - 1 := by
    refine dvd_two_pow_sub_one_of_modEq hmodZ ?_
    have h1 : Nat.card Z * 2 ^ rkIdx Z = Nat.card W := by
      have := Z.card_mul_index
      rwa [index_eq_two_pow_rkIdx hW Z] at this
    rw [h1]
    exact hmodW
  obtain ⟨hk1, hp3', he2⟩ := eq_of_dvd_two_pow_sub_one hk hp hpk he_ge he_le he_even hdvd
  refine ⟨hk1, hp3', n, fixV D, hWcard, hn2, hDcard, le_rfl, hYx, ?_⟩
  have hmodY : Nat.card (fixV D) ≡ 1 [MOD p] :=
    card_modEq_one_of_fixV_eq_bot hp hx hfix hYx'
  rw [hp3'] at hmodW hmodY
  exact rkIdx_eq_two_of_modEq hW hZY he2 hYtop hmodW hmodY

end CFSG.LocalAnalysis.WeakClosure81
