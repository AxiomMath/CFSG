module

public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin.H13

theorem isPGroup_zpowers_of_pow {Q : Type*} [Group Q] {x : Q} {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hx
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

theorem exists_ne_one_fixed {Q : Type*} [Group Q] [Finite Q] (hQ : 2 ∣ Nat.card Q) (y : MulAut Q)
    {k : ℕ} (hy : y ^ 2 ^ k = 1) : ∃ q : Q, q ≠ 1 ∧ y q = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := isPGroup_zpowers_of_pow hy
  have h1 : (1 : Q) ∈ MulAction.fixedPoints ↥(Subgroup.zpowers y) Q := fun g => map_one _
  obtain ⟨b, hb, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point Q hQ h1
  exact ⟨b, fun h => hne h.symm, hb ⟨y, Subgroup.mem_zpowers y⟩⟩

variable {V : Type*} [CommGroup V] [Finite V]

theorem eq_one_of_le_centralizer (hV : IsPGroup 2 V) {L : Subgroup (MulAut V)}
    (hcomm : commV L = ⊤) (hlt : fixV L < ⊤)
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ w ∈ J, l w ∈ J) → fixV L ≤ J → J = fixV L ∨ J = ⊤)
    {x : MulAut V} (hx : ∀ l ∈ L, l * x = x * l) {k : ℕ} (hxk : x ^ 2 ^ k = 1) : x = 1 := by
  set C := fixV L with hC
  have hxC : ∀ c ∈ C, x c ∈ C := by
    intro c hc l hl
    have h1 : (l * x) c = (x * l) c := by rw [hx l hl]
    change l (x c) = x (l c) at h1
    rw [h1, hc l hl]
  have hxinvC : ∀ c ∈ C, x⁻¹ c ∈ C := by
    intro c hc l hl
    have hx' : l * x⁻¹ = x⁻¹ * l := by
      calc l * x⁻¹ = x⁻¹ * (x * l) * x⁻¹ := by group
        _ = x⁻¹ * (l * x) * x⁻¹ := by rw [hx l hl]
        _ = x⁻¹ * l := by group
    have h1 : (l * x⁻¹) c = (x⁻¹ * l) c := by rw [hx']
    change l (x⁻¹ c) = x⁻¹ (l c) at h1
    rw [h1, hc l hl]
  have hxS : x ∈ stabSub C := fun u => ⟨fun h => by
    have := hxinvC _ h
    simpa using this, fun h => hxC u h⟩
  set J : Subgroup V :=
    { carrier := {v | x v * v⁻¹ ∈ C}
      mul_mem' := fun {a b} ha hb => by
        change x (a * b) * (a * b)⁻¹ ∈ C
        have : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
          rw [map_mul, mul_inv]
          exact mul_mul_mul_comm _ _ _ _
        rw [this]
        exact C.mul_mem ha hb
      one_mem' := by
        change x 1 * 1⁻¹ ∈ C
        rw [map_one, inv_one, mul_one]
        exact C.one_mem
      inv_mem' := fun {a} ha => by
        change x a⁻¹ * a⁻¹⁻¹ ∈ C
        have : x a⁻¹ * a⁻¹⁻¹ = (x a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv_rev, inv_inv, mul_comm]
        rw [this]
        exact C.inv_mem ha } with hJ
  have hJinv : ∀ l ∈ L, ∀ w ∈ J, l w ∈ J := by
    intro l hl w hw
    change x (l w) * (l w)⁻¹ ∈ C
    have h1 : x (l w) = l (x w) := by
      have := congrArg (fun f : MulAut V => f w) (hx l hl)
      exact this.symm
    rw [h1, ← map_inv, ← map_mul]
    have hw' : x w * w⁻¹ ∈ C := hw
    rw [hw' l hl]
    exact hw'
  have hCJ : C ≤ J := by
    intro c hc
    change x c * c⁻¹ ∈ C
    exact C.mul_mem (hxC c hc) (C.inv_mem hc)
  have hJtop : J = ⊤ := by
    rcases hirr J hJinv hCJ with h | h
    · exfalso
      have hQ : 2 ∣ Nat.card (V ⧸ C) := by
        have hne : Nontrivial (V ⧸ C) := by
          obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hlt
          exact ⟨⟨QuotientGroup.mk v, 1, fun h' => hv ((QuotientGroup.eq_one_iff v).1 h')⟩⟩
        have hQ2 : IsPGroup 2 (V ⧸ C) := hV.to_quotient C
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ2
        have : n ≠ 0 := by
          rintro rfl
          rw [pow_zero] at hn
          exact (Finite.one_lt_card_iff_nontrivial.2 hne).ne' hn
        rw [hn]
        exact dvd_pow_self 2 this
      have hy : (quotHom C ⟨x, hxS⟩) ^ 2 ^ k = 1 := by
        rw [← map_pow]
        have : (⟨x, hxS⟩ : ↥(stabSub C)) ^ 2 ^ k = 1 := Subtype.ext hxk
        rw [this, map_one]
      obtain ⟨q, hq1, hqx⟩ := exists_ne_one_fixed hQ _ hy
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
      have hvJ : v ∈ J := by
        change x v * v⁻¹ ∈ C
        rw [quotHom_mk] at hqx
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hqx, QuotientGroup.mk_inv,
          mul_inv_cancel]
      rw [h] at hvJ
      exact hq1 ((QuotientGroup.eq_one_iff v).2 hvJ)
    · exact h
  set K : Subgroup V :=
    { carrier := {w | x w = w}
      mul_mem' := fun {a b} ha hb => by
        change x (a * b) = a * b
        rw [map_mul]
        change x a = a at ha
        change x b = b at hb
        rw [ha, hb]
      one_mem' := map_one x
      inv_mem' := fun {a} ha => by
        change x a⁻¹ = a⁻¹
        change x a = a at ha
        rw [map_inv, ha] } with hK
  have hgen : commV L ≤ K := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨l, hl, v, rfl⟩
    change x (l v * v⁻¹) = l v * v⁻¹
    have hvJ : v ∈ J := by rw [hJtop]; trivial
    have hc : x v * v⁻¹ ∈ C := hvJ
    have h1 : x (l v) = l (x v) := by
      have := congrArg (fun f : MulAut V => f v) (hx l hl)
      exact this.symm
    have h2 : l (x v * v⁻¹) = x v * v⁻¹ := hc l hl
    have h3 : l (x v) = (x v * v⁻¹) * l v := by
      calc l (x v) = l (x v * v⁻¹ * v) := by rw [inv_mul_cancel_right]
        _ = l (x v * v⁻¹) * l v := by rw [map_mul]
        _ = (x v * v⁻¹) * l v := by rw [h2]
    rw [map_mul, map_inv, h1, h3, mul_right_comm (x v * v⁻¹), mul_right_comm (x v) v⁻¹,
      mul_inv_cancel, one_mul, mul_comm]
  ext v
  have hv : v ∈ commV L := by rw [hcomm]; trivial
  exact hgen hv

end CFSG.Quasithin.H13
