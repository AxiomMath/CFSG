module

public import CFSG.Quasithin.Background.F918Z8Sz6Ec
public import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section FieldAux

variable {Y : Type} [CommGroup Y]

theorem suz_field_stab [Finite Y] {I : Subgroup Y} {t : MulAut Y} (h : ∀ w ∈ I, t w ∈ I) :
    t ∈ stabSub I := by
  intro u
  refine ⟨fun hu => ?_, h u⟩
  have hmap : I.map (t : Y ≃* Y).toMonoidHom = I := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact h w hw
    · rw [Subgroup.card_map_of_injective (t : Y ≃* Y).injective]
  rw [← hmap] at hu
  obtain ⟨w, hw, hwu⟩ := hu
  have : w = u := t.injective hwu
  rwa [← this]

theorem suz_field_dvd [Finite Y] {W : Subgroup Y} {P : Subgroup (MulAut Y)} {N : ℕ}
    {t : MulAut Y}
    (hfree : ∀ k : ℕ, ¬ (N ∣ k) → W ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥)
    {I J : Subgroup Y} (hJI : J < I) (hIM : I ≤ W ⊓ fixV P) {k : ℕ}
    (hk : t ^ k ∈ centSec I J) : N ∣ k := by
  by_contra hNk
  have hbot := hfree k hNk
  have key : ∀ w ∈ I, (t ^ k) w * w⁻¹ ∈ J := hk.2
  let f : ↥I → ↥J := fun w => ⟨(t ^ k) (w : Y) * (w : Y)⁻¹, key w w.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h0 : (t ^ k) (a : Y) * (a : Y)⁻¹ = (t ^ k) (b : Y) * (b : Y)⁻¹ :=
      congrArg Subtype.val hab
    have hab' : (t ^ k) (a : Y) / (a : Y) = (t ^ k) (b : Y) / (b : Y) := by
      rwa [div_eq_mul_inv, div_eq_mul_inv]
    have h1 := div_eq_div_iff_div_eq_div.1 hab'
    have hc : (a : Y) / (b : Y) ∈ I := I.div_mem a.2 b.2
    have hfixc : (t ^ k) ((a : Y) / (b : Y)) = (a : Y) / (b : Y) := by
      rw [map_div]
      exact h1
    have hc' : (a : Y) / (b : Y) ∈ W ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) := by
      refine ⟨hIM hc, fun x hx => ?_⟩
      have hle : Subgroup.zpowers (t ^ k) ≤
          MulAction.stabilizer (MulAut Y) ((a : Y) / (b : Y)) :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hfixc)
      exact MulAction.mem_stabilizer_iff.1 (hle hx)
    rw [hbot, Subgroup.mem_bot, div_eq_one] at hc'
    exact Subtype.ext hc'
  have hcard : Nat.card ↥I ≤ Nat.card ↥J := Nat.card_le_card_of_injective f hf
  exact hJI.ne (Subgroup.eq_of_le_of_card_ge hJI.le hcard)

theorem suz_field_two_pow {n m : ℕ} (h : 2 ^ n - 1 ∣ 2 ^ m - 1) : n ∣ m := by
  have hg : (2 ^ n - 1).gcd (2 ^ m - 1) = 2 ^ n - 1 := Nat.gcd_eq_left h
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hg
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (n.gcd m) := Nat.one_le_two_pow
  have h3 : n.gcd m = n := Nat.pow_right_injective (le_refl 2) (show 2 ^ n.gcd m = 2 ^ n by omega)
  rw [← h3]
  exact Nat.gcd_dvd_right n m

theorem suz_field_arith {n m : ℕ} (hm : 1 ≤ m) (hnm : n ∣ m) :
    (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) ∣
      ∏ i : Fin 4, ((2 ^ m) ^ 4 - (2 ^ m) ^ (i : ℕ)) := by
  obtain ⟨k, rfl⟩ := hnm
  have hk : 1 ≤ k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  rw [pow_mul 2 n k]
  generalize 2 ^ n = q
  have h1 : q ^ 2 ∣ (q ^ k) ^ 3 := by
    rw [← pow_mul]
    exact pow_dvd_pow q (by omega)
  have h2 : q - 1 ∣ q ^ k - 1 := Nat.sub_one_dvd_pow_sub_one q k
  have h3 : q ^ 2 + 1 ∣ (q ^ k) ^ 4 - 1 := by
    have e : q ^ 4 - 1 = (q ^ 2 + 1) * (q ^ 2 - 1) := by
      have := Nat.sq_sub_sq (q ^ 2) 1
      rwa [one_pow, ← pow_mul] at this
    have h4 : q ^ 4 - 1 ∣ (q ^ k) ^ 4 - 1 := by
      have e4 : (q ^ k) ^ 4 = (q ^ 4) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
      rw [e4]
      exact Nat.sub_one_dvd_pow_sub_one (q ^ 4) k
    exact (Dvd.intro _ e.symm).trans h4
  have e3 : (q ^ k) ^ 4 - (q ^ k) ^ 3 = (q ^ k) ^ 3 * (q ^ k - 1) := by
    rw [Nat.mul_sub_one, ← pow_succ]
  have hprod : ∏ i : Fin 4, ((q ^ k) ^ 4 - (q ^ k) ^ (i : ℕ)) =
      ((q ^ k) ^ 4 - 1) * ((q ^ k) ^ 4 - q ^ k) * ((q ^ k) ^ 4 - (q ^ k) ^ 2) *
        ((q ^ k) ^ 3 * (q ^ k - 1)) := by
    rw [Fin.prod_univ_four, ← e3]
    simp
  rw [hprod]
  have h5 : q ^ 2 * (q - 1) * (q ^ 2 + 1) ∣ ((q ^ k) ^ 3 * (q ^ k - 1)) * ((q ^ k) ^ 4 - 1) :=
    mul_dvd_mul (mul_dvd_mul h1 h2) h3
  exact h5.trans ⟨((q ^ k) ^ 4 - q ^ k) * ((q ^ k) ^ 4 - (q ^ k) ^ 2), by ring⟩

end FieldAux

section Field

variable {Y : Type} [CommGroup Y] [Finite Y] {Λ : Subgroup (MulAut Y)}

set_option linter.unusedVariables false in
theorem suz_field_proved {W : Subgroup Y} {n m : ℕ}
    (hΛ : Nat.card ↥Λ = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1)) (hn3 : 3 ≤ n)
    {P : Subgroup (MulAut Y)} {t : MulAut Y} (htord : orderOf t = 2 ^ n - 1)
    (hfree : ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → W ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥)
    {X : Subgroup (MulAut Y)} {I J : Subgroup Y} (hJI : J < I) (hIM : I ≤ W ⊓ fixV P)
    (htI : ∀ w ∈ I, t w ∈ I) (htJ : ∀ w ∈ J, t w ∈ J) (hXI : X ≤ stabSub I)
    (hXJ : X ≤ stabSub J) (hXt : ∀ x ∈ X, t * x = x * t)
    (hnat : BinaryNaturalSL (autSec X I J) ⊤ ⊥ 3 m) :
    1 ≤ m ∧ Nat.card ↥Λ ∣ ∏ i : Fin 4, ((2 ^ m) ^ 4 - (2 ^ m) ^ (i : ℕ)) := by
  have hm : 1 ≤ m := by
    obtain ⟨K, hK, hKfin, hcard, -⟩ := hnat
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hcard] at h1
    exact Nat.pos_of_ne_zero (Nat.one_lt_two_pow_iff.1 h1)
  refine ⟨hm, ?_⟩
  have hI : t ∈ stabSub I := suz_field_stab htI
  have hJ : t ∈ stabSub J := suz_field_stab htJ
  have hTI : Subgroup.zpowers t ≤ stabSub I := Subgroup.zpowers_le.2 hI
  have hTJ : Subgroup.zpowers t ≤ stabSub J := Subgroup.zpowers_le.2 hJ
  let τ : ↥(Subgroup.zpowers t) := ⟨t, Subgroup.mem_zpowers t⟩
  let γ : MulAut (Sec I J) := B5.secHom (Subgroup.zpowers t) hTI hTJ τ
  have hcomm : ∀ l ∈ autSec X I J, γ * l = l * γ := by
    intro l hl
    rw [← B5.range_secHom X hXI hXJ] at hl
    obtain ⟨x, rfl⟩ := hl
    refine MulEquiv.ext fun s => ?_
    induction s using QuotientGroup.induction_on with
    | H w =>
      show (QuotientGroup.mk ⟨t ((x : MulAut Y) w), _⟩ : Sec I J) =
        QuotientGroup.mk ⟨(x : MulAut Y) (t w), _⟩
      congr 1
      exact Subtype.ext (by simpa using congrArg (fun g : MulAut Y => g (w : Y)) (hXt x x.2))
  have hpow : γ ^ (2 ^ m - 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (natSL3_comm_order_proved hnat hcomm)
  have hker : t ^ (2 ^ m - 1) ∈ centSec I J := by
    have h1 : (τ ^ (2 ^ m - 1) : ↥(Subgroup.zpowers t)) ∈
        (B5.secHom (Subgroup.zpowers t) hTI hTJ).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hpow
    simpa using (B5.mem_ker_secHom _ hTI hTJ _).1 h1
  have hN : 2 ^ n - 1 ∣ 2 ^ m - 1 := suz_field_dvd hfree hJI hIM hker
  rw [hΛ]
  exact suz_field_arith hm (suz_field_two_pow hN)

end Field

end CFSG.Quasithin
