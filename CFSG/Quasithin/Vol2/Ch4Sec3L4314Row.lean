module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.H13.VolIA38SLThree
public import CFSG.Monster.B.Mathieu.M22Order
public import CFSG.Monster.B.Mathieu.M24Order
import CFSG.Quasithin.Background.A3Structure39Odd
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Blueprint CFSG.Timmesfeld.Orders
open CFSG.Assembly.LowTwoRank (StatedSL projectiveSpecialLinearGroupEquivStatedProj
  specialLinearGroupEquivStatedSL)

namespace L4314Row

theorem odd_two_pow_sub_one' {e : ℕ} (he : 1 ≤ e) : Odd (2 ^ e - 1) := by
  have h2 : Even (2 ^ e) := (Nat.even_pow' (by omega)).mpr even_two
  exact Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one

theorem eq_of_two_pow_mul_eq {a b r s : ℕ} (hr : Odd r) (hs : Odd s)
    (h : 2 ^ a * r = 2 ^ b * s) : r = s := by
  have h1 : r ∣ s * 2 ^ b := ⟨2 ^ a, by rw [mul_comm s, ← h, mul_comm]⟩
  have h2 : s ∣ r * 2 ^ a := ⟨2 ^ b, by rw [mul_comm r, h, mul_comm]⟩
  have hr' : Nat.Coprime r (2 ^ b) := (Nat.coprime_two_right.mpr hr).pow_right b
  have hs' : Nat.Coprime s (2 ^ a) := (Nat.coprime_two_right.mpr hs).pow_right a
  exact Nat.dvd_antisymm (hr'.dvd_of_dvd_mul_right h1) (hs'.dvd_of_dvd_mul_right h2)

theorem odd_D {m : ℕ} (hm : 1 ≤ m) : Odd (((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1)) := by
  rw [← pow_mul, ← pow_mul]
  exact (odd_two_pow_sub_one' (by omega)).mul (odd_two_pow_sub_one' (by omega))

theorem D_cases {m : ℕ} (hm : 2 ≤ m) :
    ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) = 945 ∨
      ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) = 32193 ∨
      1044225 ≤ ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) := by
  rcases Nat.lt_or_ge m 4 with h | h
  · interval_cases m
    · left; norm_num
    · right; left; norm_num
  · right; right
    have h16 : 16 ≤ 2 ^ m := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
    have h3 : 4096 ≤ (2 ^ m) ^ 3 := by
      calc 4096 = 16 ^ 3 := by norm_num
        _ ≤ (2 ^ m) ^ 3 := Nat.pow_le_pow_left h16 3
    have h2 : 256 ≤ (2 ^ m) ^ 2 := by
      calc 256 = 16 ^ 2 := by norm_num
        _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h16 2
    calc 1044225 = 4095 * 255 := by norm_num
      _ ≤ ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) := Nat.mul_le_mul (by omega) (by omega)

theorem D_ne {m r : ℕ} (hm : 2 ≤ m) (hr : r < 945 ∨ r = 3465 ∨ r = 10395 ∨ r = 239085) :
    ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) ≠ r := by
  rcases D_cases hm with h | h | h <;> omega

theorem le_of_prime_dvd_D {m p : ℕ} (hm : 1 ≤ m) (hp : p.Prime)
    (h : p ∣ ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1)) : p ≤ (2 ^ m) ^ 2 + 2 ^ m + 1 := by
  set q := 2 ^ m with hq
  have hq1 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have e3 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    zify [this, (by omega : 1 ≤ q)]
    ring
  have e2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [this, (by omega : 1 ≤ q)]
    ring
  rw [e3, e2] at h
  have hpos : 0 < q ^ 2 + q + 1 := by positivity
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h <;> rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · have := Nat.le_of_dvd (by omega) h
    omega
  · exact Nat.le_of_dvd hpos h
  · have := Nat.le_of_dvd (by omega) h
    omega
  · have := Nat.le_of_dvd (by omega) h
    omega

theorem false_of_sl2_order {m p : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : 2 ^ (3 * m) ∣ p * (p ^ 2 - 1))
    (hpD : p ∣ ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1)) : False := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hord := VolI.two_mul_ordA_one_of_odd hpodd
  have hdvd : 2 ^ (3 * m - 1) ∣ CFSG.Open.ordA 1 p := by
    have h3 : 2 ^ (3 * m) = 2 * 2 ^ (3 * m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [← hord, h3] at h2
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h2
  have hle := VolI.two_pow_le_of_dvd_ordA_one hpodd hp3 hdvd
  have hle2 := le_of_prime_dvd_D (by omega) hp hpD
  set q := 2 ^ m with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have e : 2 * 2 ^ (3 * m - 1) = q ^ 3 := by
    rw [← pow_succ', hq, ← pow_mul]
    congr 1
    omega
  have h5 : q ^ 3 ≤ 2 * (q ^ 2 + q + 2) := by omega
  nlinarith

section Orders

variable {X : Type} [Group X]

theorem card_of_isAlt {k : ℕ} (hk : 2 ≤ k) (h : IsAlt k X) :
    Nat.card X = Nat.factorial k / 2 := by
  obtain ⟨e⟩ := h
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]

theorem card_of_isHat {S : Type} [Group S] (h : IsHat X S) :
    Nat.card X = Nat.card S * 3 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, h3, Nat.card_congr e.toEquiv]

theorem card_of_isPSL {k p e : ℕ} (hk : 0 < k) (h : IsPSL k p e X) :
    Nat.card X = ((p ^ e) ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 2 k, ((p ^ e) ^ i - 1)) /
      k.gcd (p ^ e - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl hk h

theorem card_of_isSL2 {p : ℕ} (hp : p.Prime) (h : IsSL2 p X) :
    Nat.card X = p * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.OrderReductions.LinearOrders.card_specialLinear (ZMod p) 2 (by norm_num),
    Nat.card_zmod]
  simp

theorem two_mul_card_of_isPSL_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsPSL 2 p 1 X) :
    2 * Nat.card X = p * (p ^ 2 - 1) :=
  CFSG.Open.StatedAPI.two_mul_card_of_statedClassicalModel_psl_two_prime hp hp2 h

theorem card_isE2 {k : ℕ} (h : IsE2 k X) : Nat.card X = 2 ^ k := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin k → ZMod 2) = 2 ^ k
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem card_isZ4Cubed (h : IsZ4Cubed X) : Nat.card X = 2 ^ 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin 3 → ZMod 4) = 2 ^ 6
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem card_isZ4StarExtra2 [Finite X] (h : IsZ4StarExtra2 X) : ∃ k, Nat.card X = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Z, E, hZ, -, hE, hZc, hZE, -⟩ := h
  have hZn : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hp : IsPGroup 2 ↥(Z ⊔ E) :=
    IsPGroup.to_sup_of_normal_left (IsPGroup.of_card (n := 2) (by rw [hZ]; norm_num))
      (IsPGroup.of_card hE.2)
  rw [hZE] at hp
  exact IsPGroup.iff_card.mp (hp.of_equiv Subgroup.topEquiv)

theorem card_alt5 (h : IsAlt 5 X) : Nat.card X = 2 ^ 2 * 15 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

theorem card_alt6 (h : IsAlt 6 X) : Nat.card X = 2 ^ 3 * 45 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

theorem card_alt7 (h : IsAlt 7 X) : Nat.card X = 2 ^ 3 * 315 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

theorem card_hat6 (h : IsHat X (alternatingGroup (Fin 6))) : Nat.card X = 2 ^ 3 * 135 := by
  rw [card_of_isHat h, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_L32 (h : IsPSL 3 2 1 X) : Nat.card X = 2 ^ 3 * 21 := by
  rw [card_of_isPSL (by norm_num) h]
  decide

theorem card_L42 (h : IsPSL 4 2 1 X) : Nat.card X = 2 ^ 6 * 315 := by
  rw [card_of_isPSL (by norm_num) h]
  decide

theorem card_L34 (h : IsPSL 3 2 2 X) : Nat.card X = 2 ^ 6 * 315 := by
  rw [card_of_isPSL (by norm_num) h]
  decide

theorem card_M22 (h : IsSporadic .M22 X) :
    Nat.card X = 2 ^ 7 * 3465 := by
  obtain ⟨e⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, hc⟩ := CFSG.Monster.B.Mathieu.fam_M22_order
  rw [Nat.card_congr e.toEquiv]
  exact hc

theorem card_hatM22
    (h : IsHat X (NativeSporadic.Carrier .M22)) : Nat.card X = 2 ^ 7 * 10395 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hc⟩ := CFSG.Monster.B.Mathieu.fam_M22_order
  rw [card_of_isHat h]
  change Nat.card ↥NativeSporadic.M22 * 3 = _
  rw [hc]
  norm_num

theorem card_M24 (h : IsSporadic .M24 X) :
    Nat.card X = 2 ^ 10 * 239085 := by
  obtain ⟨e⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, hc⟩ := CFSG.Monster.B.Mathieu.fam_M24_order
  rw [Nat.card_congr e.toEquiv]
  exact hc

end Orders

end L4314Row

open L4314Row

structure A312SL3Data {Q : Type} [Group Q] (B : Subgroup Q) (m : ℕ) : Prop where
  two_le : 2 ≤ m
  iso : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ m ∧
    Nonempty (ModO2 B ≃* ↥(StatedSL 3 F))

namespace A312SL3Data

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} {m : ℕ}

omit [Finite Q] in
theorem card_modO2 (hD : A312SL3Data B m) :
    Nat.card (ModO2 B) = 2 ^ (3 * m) * (((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hD.iso
  have hq2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by have := hD.two_le; omega)
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv,
    VolI.card_SL_three hF hq2, ← pow_mul, mul_comm m 3]

theorem card_eq (hD : A312SL3Data B m) :
    ∃ a : ℕ, Nat.card ↥B = 2 ^ (a + 3 * m) * (((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(CFSG.pCore 2 ↥B) := CFSG.pCore_isPGroup
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP
  refine ⟨a, ?_⟩
  have h1 := (CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup
  have h2 : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) =
      2 ^ (3 * m) * (((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1)) := hD.card_modO2
  rw [h1, h2, ha, pow_add]
  ring

theorem odd_part (hD : A312SL3Data B m) {k r : ℕ} (hr : Odd r) (h : Nat.card ↥B = 2 ^ k * r) :
    ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) = r := by
  obtain ⟨a, ha⟩ := hD.card_eq
  exact eq_of_two_pow_mul_eq (odd_D (by have := hD.two_le; omega)) hr (ha.symm.trans h)

omit [Finite Q] in
theorem odd_part_modO2 (hD : A312SL3Data B m) {k r : ℕ} (hr : Odd r)
    (h : Nat.card (ModO2 B) = 2 ^ k * r) : ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) = r :=
  eq_of_two_pow_mul_eq (odd_D (by have := hD.two_le; omega)) hr (hD.card_modO2.symm.trans h)

theorem false_of_card (hD : A312SL3Data B m) {k r : ℕ} (hr : Odd r)
    (hr' : r < 945 ∨ r = 3465 ∨ r = 10395 ∨ r = 239085) (h : Nat.card ↥B = 2 ^ k * r) : False :=
  D_ne hD.two_le hr' (hD.odd_part hr h)

omit [Finite Q] in
theorem false_of_card_modO2 (hD : A312SL3Data B m) {k r : ℕ} (hr : Odd r)
    (hr' : r < 945 ∨ r = 3465 ∨ r = 10395 ∨ r = 239085)
    (h : Nat.card (ModO2 B) = 2 ^ k * r) : False :=
  D_ne hD.two_le hr' (hD.odd_part_modO2 hr h)

theorem false_of_ext (hD : A312SL3Data B m) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, Nat.card V = 2 ^ k)
    {y r : ℕ} (hr : Odd r) (hr' : r < 945 ∨ r = 3465 ∨ r = 10395 ∨ r = 239085)
    (hPY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = 2 ^ y * r) : False := by
  obtain ⟨V, hVn, hV, hY⟩ := h
  obtain ⟨k, hk⟩ := hPV _ hV
  refine hD.false_of_card hr hr' (k := k + y) ?_
  rw [V.card_eq_card_quotient_mul_card_subgroup, hPY _ hY, hk, pow_add]
  ring

theorem two_pow_dvd (hD : A312SL3Data B m) : 2 ^ (3 * m) ∣ Nat.card ↥B := by
  obtain ⟨a, ha⟩ := hD.card_eq
  rw [ha, pow_add]
  exact ⟨2 ^ a * (((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1)), by ring⟩

theorem dvd_D (hD : A312SL3Data B m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ Nat.card ↥B) :
    p ∣ ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) := by
  obtain ⟨a, ha⟩ := hD.card_eq
  rw [ha] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  · exact h

theorem false_of_sl2_quotient (hD : A312SL3Data B m) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : Odd n) (h : Nat.card ↥B = n * (p * (p ^ 2 - 1))) : False := by
  have h2 : 2 ^ (3 * m) ∣ p * (p ^ 2 - 1) := by
    have := hD.two_pow_dvd
    rw [h] at this
    exact ((Nat.coprime_two_left.mpr hn).pow_left _).dvd_of_dvd_mul_left this
  have hpB : p ∣ Nat.card ↥B := by
    rw [h]
    exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
  exact false_of_sl2_order hD.two_le hp hp2 h2 (hD.dvd_D hp hp2 hpB)

omit [Finite Q] in
theorem false_of_a38
    (hD : A312SL3Data B m) (h : A38Types (ModO2 B)) : False := by
  obtain ⟨F, _, _, hF, he⟩ := hD.iso
  have := VolI.a38TypesSLThree_holds (ModO2 B) F m (by rw [Nat.card_eq_fintype_card, hF]) he h
  have := hD.two_le
  omega

omit [Finite Q] in
theorem pV_E2 {k : ℕ} : ∀ (V : Type) [Group V] [Finite V], IsE2 k V → ∃ j, Nat.card V = 2 ^ j :=
  fun _ _ _ hV => ⟨k, card_isE2 hV⟩

omit [Finite Q] in
theorem pV_extra {k : ℕ} :
    ∀ (V : Type) [Group V] [Finite V], IsExtraspecial2 k V → ∃ j, Nat.card V = 2 ^ j :=
  fun _ _ _ hV => ⟨1 + 2 * k, hV.2⟩

omit [Finite Q] in
theorem false_C2_C5
    (hD : A312SL3Data B m)
    (h : A312C2 B L ∨ A312C3 B L ∨ A312C4 B L ∨ A312C5 B L) : False := by
  rcases h with ⟨⟨n, hn⟩, -⟩ | ⟨f, hf, -⟩ | h | h
  · exact hD.false_of_a38 (Or.inl ⟨n, hn⟩)
  · exact hD.false_of_a38 (Or.inr (Or.inl ⟨f, hf⟩))
  · exact hD.false_of_card_modO2 (by decide) (by norm_num) (card_L32 h.1)
  · exact hD.false_of_card_modO2 (by decide) (by norm_num) (card_L42 h.1)

theorem false_C6_C7_C11_C15 (hD : A312SL3Data B m)
    (h : A312C6 B L ∨ A312C7 B L ∨ A312C11 B L ∨ A312C15 B L) : False := by
  rcases h with ⟨hB | hB, -⟩ | (⟨hB, -⟩ | ⟨hB, -⟩) | ⟨hB, -⟩ | ⟨hB, -⟩
  · exact hD.false_of_card (by decide) (by norm_num) (card_alt5 hB)
  · exact hD.false_of_card (by decide) (by norm_num) (card_L32 hB)
  · exact hD.false_of_card (by decide) (by norm_num) (card_alt6 hB)
  · exact hD.false_of_card (by decide) (by norm_num) (card_hat6 hB)
  · exact hD.false_of_card (by decide) (by norm_num) (card_alt6 hB)
  · exact hD.false_of_card (by decide) (by norm_num) (card_alt5 hB)

theorem false_C8_C9_C10 (hD : A312SL3Data B m)
    (h : A312C8 B L ∨ A312C9 B L ∨ A312C10 B L) : False := by
  rcases h with (⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩) | (⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩) |
    ⟨p, hp, hp3, ⟨V, hV, ⟨e⟩, hY⟩, -⟩
  ·
    have hp2 : p ≠ 2 := by omega
    have h2 := two_mul_card_of_isPSL_two hp hp2 hB
    have hdvd : 2 ^ (3 * m) ∣ p * (p ^ 2 - 1) := by
      rw [← h2]
      exact hD.two_pow_dvd.mul_left 2
    have hpB : p ∣ Nat.card ↥B := by
      have h3 : p ∣ 2 * Nat.card ↥B := by
        rw [h2]
        exact Dvd.intro _ rfl
      exact (Nat.Coprime.dvd_of_dvd_mul_left
        ((Nat.coprime_primes hp Nat.prime_two).2 hp2) h3)
    exact false_of_sl2_order hD.two_le hp hp2 hdvd (hD.dvd_D hp hp2 hpB)
  · exact hD.false_of_card (by decide) (by norm_num) (card_alt5 hB)
  ·
    exact hD.false_of_sl2_quotient hp (by omega) odd_one (by rw [card_of_isSL2 hp hB, one_mul])
  · exact hD.false_of_card (by decide) (by norm_num) (card_alt6 hB)
  · exact hD.false_of_card (by decide) (by norm_num) (card_hat6 hB)
  ·
    have : NeZero p := ⟨hp.ne_zero⟩
    have hcard : Nat.card ↥V = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 2 → ZMod p) = p ^ 2
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hodd : Odd (p ^ 2) := (hp.odd_of_ne_two (by omega)).pow
    refine hD.false_of_sl2_quotient hp (by omega) hodd ?_
    rw [V.card_eq_card_quotient_mul_card_subgroup, card_of_isSL2 hp hY, hcard, mul_comm]

theorem false_C12_C20
    (hD : A312SL3Data B m)
    (h : A312C12 B L ∨ A312C13 B L ∨ A312C14 B L ∨ A312C16 B L ∨ A312C17 B L ∨ A312C18 B L ∨
      A312C19 B L ∨ A312C20 B L) : False := by
  rcases h with h | h | h | h | h | h | h | h
  · rcases h with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_alt5 hY
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_alt6 hY
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_alt5 hY
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_hat6 hY
  · obtain ⟨hB | hB | hB | hB | hB | hB | hB, -⟩ := h
    · exact hD.false_of_card (by decide) (by norm_num) (card_M22 hB)
    · exact hD.false_of_card (by decide) (by norm_num) (card_L34 hB)
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_alt7 hY
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_L32 hY
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_L32 hY
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_alt6 hY
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_alt5 hY
  · obtain ⟨hB | hB | hB | hB, -⟩ := h
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_L42 hY
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_L32 hY
    · exact hD.false_of_ext hB pV_extra (by decide) (by norm_num) fun _ _ hY => card_L32 hY
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_hat6 hY
  · exact hD.false_of_ext h.1 pV_extra (by decide) (by norm_num) fun _ _ hY => card_alt5 hY
  · obtain ⟨-, hB | hB | hB | hB | hB | hB⟩ := h
    · exact hD.false_of_ext hB pV_extra (by decide) (by norm_num) fun _ _ hY => card_hatM22 hY
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_M24 hY
    · exact hD.false_of_card_modO2 (by decide) (by norm_num) (card_alt5 hB)
    · exact hD.false_of_card_modO2 (by decide) (by norm_num) (card_hat6 hB)
    · exact hD.false_of_card_modO2 (by decide) (by norm_num) (card_L42 hB)
    · exact hD.false_of_card_modO2 (by decide) (by norm_num) (card_L32 hB)
  · obtain ⟨hB | hB, -⟩ := h
    · exact hD.false_of_ext hB (fun _ _ _ hV => card_isZ4StarExtra2 hV) (by decide) (by norm_num)
        fun _ _ hY => card_alt5 hY
    · exact hD.false_of_ext hB (fun _ _ _ hV => ⟨6, card_isZ4Cubed hV⟩) (by decide) (by norm_num)
        fun _ _ hY => card_L32 hY
  · obtain ⟨hB | hB, -⟩ := h
    · exact hD.false_of_ext hB pV_extra (by decide) (by norm_num) fun _ _ hY => card_L32 hY
    · exact hD.false_of_ext hB pV_E2 (by decide) (by norm_num) fun _ _ hY => card_hat6 hY
  · obtain ⟨hB | hB, -⟩ := h
    · exact hD.false_of_card_modO2 (by decide) (by norm_num) (card_alt5 hB)
    · exact hD.false_of_card_modO2 (by decide) (by norm_num) (card_L32 hB)

omit [Finite Q] in
theorem relIndex_sup_eq' {A D : Subgroup Q} (h : A ≤ Subgroup.normalizer (D : Set Q)) :
    D.relIndex (A ⊔ D) = D.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A D h).toEquiv.symm

theorem false_of_nonquasi (hD : A312SL3Data B m) (hBL : B ≤ L) (h : A312Nonquasi B L) : False := by
  set O : Subgroup Q := (CFSG.oddCore ↥L).map L.subtype with hOdef
  have hOL : O ≤ L := Subgroup.map_subtype_le _
  have hLO : L ≤ Subgroup.normalizer (O : Set Q) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hOL).mp ?_
    have he : O.subgroupOf L = CFSG.oddCore ↥L :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [he]
    infer_instance
  have hOcard : Nat.card ↥O = Nat.card ↥(CFSG.oddCore ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hOodd : Odd (Nat.card ↥O) := by
    rw [hOcard]
    exact A38.odd_card_oddCore _
  have hpos : 0 < Nat.card ↥O := Nat.card_pos
  have hB := Subgroup.relIndex_mul_card O B
  have hodd : Odd (Nat.card ↥(O ⊓ B)) := hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hsup := relIndex_sup_eq' (hBL.trans hLO)
  have hBO : O.relIndex (B ⊔ O) * Nat.card ↥O = Nat.card ↥(B ⊔ O) := by
    have := Subgroup.relIndex_mul_card O (B ⊔ O)
    rwa [inf_eq_left.mpr le_sup_right] at this
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨-, hLB, p, hp, hp2, hSL⟩ | ⟨-, -, N, hN, hNeq, hN5⟩
  ·
    have h2 := (CFSG.oddCore ↥L).card_eq_card_quotient_mul_card_subgroup
    rw [card_of_isSL2 hp hSL, ← hOcard] at h2
    rw [← hOdef] at hLB
    rw [hLB] at h2
    have hrel : O.relIndex (B ⊔ O) = p * (p ^ 2 - 1) :=
      Nat.eq_of_mul_eq_mul_right hpos (hBO.trans h2)
    refine hD.false_of_sl2_quotient hp hp2 hodd ?_
    rw [← hB, ← hsup, hrel, mul_comm]
  ·
    have h2 := N.card_eq_card_quotient_mul_card_subgroup
    rw [card_of_isSL2 (by norm_num) hN5] at h2
    have h3 : Nat.card ↥N = Nat.card ↥O := by
      rw [hNeq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    rw [h3] at h2
    have hrel : O.relIndex (B ⊔ O) = 120 := Nat.eq_of_mul_eq_mul_right hpos (hBO.trans h2)
    have hcard : Nat.card ↥B = Nat.card ↥(O ⊓ B) * 120 := by
      rw [← hB, ← hsup, hrel, mul_comm]
    have hdvd := hD.two_pow_dvd
    rw [hcard] at hdvd
    have h4 : 2 ^ (3 * m) ∣ 120 :=
      ((Nat.coprime_two_left.mpr hodd).pow_left _).dvd_of_dvd_mul_left hdvd
    have h64 : 2 ^ 6 ∣ 2 ^ (3 * m) := Nat.pow_dvd_pow 2 (by have := hD.two_le; omega)
    have := h64.trans h4
    norm_num at this

end A312SL3Data

theorem not_a312Case_of_sl3
    {Q : Type} [Group Q] [Finite Q]
    {B L : Subgroup Q} {m : ℕ} (hD : A312SL3Data B m) : ¬ A312Case B L := by
  intro h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact hD.false_C2_C5 (Or.inl h)
  · exact hD.false_C2_C5 (Or.inr (Or.inl h))
  · exact hD.false_C2_C5 (Or.inr (Or.inr (Or.inl h)))
  · exact hD.false_C2_C5 (Or.inr (Or.inr (Or.inr h)))
  · exact hD.false_C6_C7_C11_C15 (Or.inl h)
  · exact hD.false_C6_C7_C11_C15 (Or.inr (Or.inl h))
  · exact hD.false_C8_C9_C10 (Or.inl h)
  · exact hD.false_C8_C9_C10 (Or.inr (Or.inl h))
  · exact hD.false_C8_C9_C10 (Or.inr (Or.inr h))
  · exact hD.false_C6_C7_C11_C15 (Or.inr (Or.inr (Or.inl h)))
  · exact hD.false_C12_C20 (Or.inl h)
  · exact hD.false_C12_C20 (Or.inr (Or.inl h))
  · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inl h)))
  · exact hD.false_C6_C7_C11_C15 (Or.inr (Or.inr (Or.inr h)))
  · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

theorem not_a312Nonquasi_of_sl3 {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} {m : ℕ}
    (hD : A312SL3Data B m) (hBL : B ≤ L) : ¬ A312Nonquasi B L :=
  hD.false_of_nonquasi hBL

end CFSG.Quasithin.H13.Ch4
